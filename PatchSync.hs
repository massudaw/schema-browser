{-# LANGUAGE DeriveGeneric #-}
module PatchSync where

import Types.Patch
import Utils
import Reactive.Threepenny
import Control.Exception
import Network.Socket
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
import Pipes.Concurrent
import qualified Pipes.Prelude as P
import Pipes.Network.TCP hiding (listen,accept,connect)

data ServerMessage
  = Pull Int
  | Push [RowPatch Text Showable]
  deriving(Eq,Show,Ord,Generic)

data ServerConfig
  = ServerConfig
  { serverPort :: Int
  , serverAddr :: String
  }deriving(Show)

openSocketConnect conf = do
  let hints = defaultHints { addrFlags = [AI_NUMERICHOST, AI_NUMERICSERV], addrSocketType = Stream }
  addr:_ <- getAddrInfo (Just hints) (Just (serverAddr conf)) (Just $show (serverPort conf ))
  sock@(MkSocket _ fam stype _ _) <- socket (addrFamily addr) (addrSocketType addr) (addrProtocol addr)
  connect sock (addrAddress addr)
  return sock

openSocketListen conf = do
  let hints = defaultHints { addrFlags = [AI_NUMERICHOST, AI_NUMERICSERV], addrSocketType = Stream }
  addr:_ <- getAddrInfo (Just hints) (Just (serverAddr conf)) (Just $show (serverPort conf ))
  sock@(MkSocket _ fam stype _ _) <- socket (addrFamily addr) (addrSocketType addr) (addrProtocol addr)
  bind sock (addrAddress addr)
  listen sock 10
  return sock

decoder smvar = do
      i <- peek
      traverse (\a -> do
          lift$ print a
          if (a /= "")
            then do
              lift $ putStrLn "Try decoding"
              i <- P.decode
              either (\_  -> unDraw a ) (\e -> do
                lift $ putStrLn $"Decoded " ++ show  e
                (inf,tb,o) <- lift . atomically . out smvar $ e
                lift $ putStrLn $ "executing mod "  ++ show o
                lift $ runDynamic $ transactionNoLog inf  $ applyBackend o
                return ()
                                        ) i

            else
              void draw) i
      decoder smvar

out smvar = (\i -> (\(CreateRow t) -> do
      let (s,tb, mod ) = decodeTableModification t
      inf <- justError "no schema " .  HM.lookup s <$> readTMVar (globalRef smvar)
      let
        table = lookTable inf  tb
      ref <- refTableSTM inf table
      let
        TableModification _ _ p = mod inf
      putPatchSTM (patchVar ref) [p]
      return (inf,table ,p)
          ) $(i :: RowPatch Text Showable))


patchServer conf smvar = do
  putStrLn $ "RunServer " ++ show conf
  sock <- openSocketListen conf
  meta <- metaInf smvar
  dbref <- prerefTable meta (lookTable meta "modification_table")
  q <- atomically $ dupTChan(patchVar dbref)

  forever $ (do
    (socka,addr) <- accept sock
    print $ "Accepted Socket " ++ show addr
    forkIO $ void $ execStateT (decoder smvar)(fromSocket socka 4096 )
    inp <- input smvar
    (runEffect $ fromInput inp >-> sequenceP >-> for cat P.encode >-> toSocket socka ) `catch` (\e -> print ("broken client",e::SomeException))
    return ())`catch` (\e -> print ("accepted socket",e :: SomeException))

sequenceP = forever $ do
      x <- await
      mapM yield  x

input smvar = do
  meta <- metaInf smvar
  dbref <- prerefTable meta (lookTable meta "modification_table")
  q <- atomically $ dupTChan(patchVar dbref)
  return $ Input $ do
      i <-readTChan q
      return $ fmap (firstPatchRow (keyValue . recoverKey meta)) <$> Just i


patchClient conf smvar = do
  putStrLn $ "RunClient" ++ show conf
  inp <- input smvar
  let
    -- pull changes
  forever $ do
    sock <- openSocketConnect conf
    forkIO $ void $ execStateT (decoder smvar) (fromSocket sock 4096 )
    (runEffect $ fromInput inp >-> sequenceP >-> for cat P.encode >-> toSocket sock ) `catch` (\e -> print ("broken client",e::SomeException))
    threadDelay (60*10^6)




