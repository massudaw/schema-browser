{-# LANGUAGE DeriveGeneric #-}
module PatchSync where

import Types.Patch
import qualified Types.Index as G
import Utils
import Reactive.Threepenny
import Control.Exception
import Network.Socket hiding (send,recv)
import Network.Socket.ByteString
import Pipes.Parse
import Control.Monad.State.Strict
import Control.Concurrent (threadDelay)
import Control.Concurrent.STM
import Control.Concurrent.STM.TQueue
import qualified Data.ByteString.Lazy as BS
import Debug.Trace
import qualified Data.HashMap.Strict as HM

import Schema
import SchemaQuery
import RuntimeTypes
import Control.Monad
import GHC.Generics
import Types
import qualified Data.Text as T
import Data.Text (Text)
import qualified Data.Binary as B
import Pipes
import qualified Pipes.Binary as P
import Pipes.Concurrent hiding (send,recv)
import qualified Pipes.Prelude as P
import Pipes.Network.TCP hiding (listen,accept,connect,send,recv)

data ServerMessage
  = Pull (TBIndex Showable)
  | Push (RowPatch Text Showable)
  deriving(Eq,Show,Ord,Generic)

instance B.Binary ServerMessage where

data ServerConfig
  = ServerConfig
  { serverPort :: Int
  , serverAddr :: String
  }deriving(Show)

openSocket conf =  do
  let hints = defaultHints { addrFlags = [AI_NUMERICHOST, AI_NUMERICSERV], addrSocketType = Stream }
  addr:_ <- getAddrInfo (Just hints) (Just (serverAddr conf)) (Just $show (serverPort conf ))
  sock@(MkSocket _ fam stype _ _) <- socket (addrFamily addr) (addrSocketType addr) (addrProtocol addr)
  return (sock,addr)

openSocketConnect conf = do
  (sock ,addr) <- openSocket conf
  connect sock (addrAddress addr)
  return sock

openSocketListen conf = do
  (sock,addr) <- openSocket conf
  bind sock (addrAddress addr)
  listen sock 10
  return sock

decoder smvar  = forever go
  where
    go = do
      i <- peek
      traverse (\a -> do
        lift$ print a
        if (a /= "")
          then do
            i <- P.decode
            either (\_  -> unDraw a ) (\e -> void . lift . runDynamic $ do
              (t,inf,tb,o) <- out $ e
              transactionNoLog inf  $ applyBackend o
              transaction (meta inf ) $ applyBackend (liftPatchRow (meta inf) "master_modification_table" $ CreateRow t)
              return ()
             ) i

          else
            void draw) i

    out (Push (CreateRow t)) = do
      let
        (s,tb, mod ) = decodeTableModification t
      inf <- liftIO $atomically$ justError ("no schema " ++ show s).  HM.lookup s <$> (readTVar .globalRef  =<< readTVar smvar)
      let
        table = lookTable inf  tb
      ref <- prerefTable inf table
      let
        TableModification _ _ p = mod inf
      liftIO $ atomically $ putPatchSTM (patchVar ref) [p]
      return (t,inf,table ,p)



patchServer conf smvar = do
  putStrLn $ "RunServer " ++ show conf
  sock <- openSocketListen conf
  meta <- metaInf smvar
  forever $ (do
    (socka,addr) <- accept sock
    print $ "Accepted Socket " ++ show addr
    (latest,inp) <- input smvar
    i <- recv socka 4096
    let Pull (G.Idex [last]) = B.decode (BS.fromStrict i)
    putStrLn $ "Sync Index "  ++ show  last
    let pred = (WherePredicate $ (AndColl [PrimColl (liftAccess meta "master_modification_table" $IProd Nothing "modification_id",Left (last,GreaterThan False))]))
    ((dbref,(_,l)),v)<-runDynamic $ transaction meta $ selectFrom "master_modification_table" Nothing Nothing [] pred
    q <- atomically $ dupTChan (patchVar (iniRef dbref))
    let master = (lookTable meta "master_modification_table")
        val = (reverse $ G.toList $ l)
    print val
    runEffect $ each ( fmap (Push . CreateRow . mapKey' keyValue)  val )>-> P.map traceShowId >-> for cat P.encode >->  toSocket socka
    forkIO $ void $ execStateT (decoder  smvar)(fromSocket socka 4096 )
    (runEffect $ fromInput inp >-> sequenceP >-> for cat P.encode >-> toSocket socka ) `catch` (\e -> print ("broken client",e::SomeException))
    return ())`catch` (\e -> print ("accepted socket",e :: SomeException))

sequenceP = forever $ do
      x <- await
      mapM yield  x

input smvar = do
  meta <- metaInf smvar
  (masterdbref ,_)<- runDynamic $ prerefTable meta (lookTable meta "master_modification_table")
  ((dbref ,(_,ini)),_)<- runDynamic $ transactionNoLog meta $ selectFrom "master_modification_table" Nothing Nothing [] (WherePredicate $AndColl[])
  let dat = G.getEntries ini
      latest = maybe (G.Idex [TB1 (SNumeric 0)]) (maximum) $ nonEmpty (fmap G.leafPred dat)
  q <- atomically $ dupTChan(patchVar (iniRef dbref))
  return (latest , Input $ do
      i <-readTChan q
      return $ fmap (Push . firstPatchRow (keyValue . recoverKey meta)) <$> Just i)


patchClient conf smvar = do
  putStrLn $ "RunClient" ++ show conf
  meta <- metaInf smvar
  (latest,inp) <- input smvar
  let
    -- pull changes

  forever $ do
    sock <- openSocketConnect conf
    putStrLn $ "Sync Token " ++ show latest
    send sock (BS.toStrict $ B.encode (Pull latest))
    forkIO $ void $ execStateT (decoder smvar) (fromSocket sock 4096 )

    (runEffect $ fromInput inp >-> sequenceP >-> for cat P.encode >-> toSocket sock ) `catch` (\e -> print ("broken client",e::SomeException))
    threadDelay (60*10^6)




