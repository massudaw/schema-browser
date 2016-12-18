{-# LANGUAGE ScopedTypeVariables,FlexibleContexts,OverloadedStrings #-}
module Main (main) where
import TP.Main
import TP.Browser(addServer,deleteServer,deleteClient,addClientLogin,deleteClientLogin)
import PatchSync
import Safe
import Control.Concurrent.STM
import Debug.Trace
import Rmtc
import Data.Unique
import Types
import Types.Patch (RowPatch(..))
import qualified Types.Index as G
import qualified Data.Foldable as F
import TP.QueryWidgets(lookAttr')
import System.Process (rawSystem)
import Poller
import Postgresql.Backend (connRoot)
import Prelude hiding (head)
import Control.Monad.Reader
import Control.Concurrent
import System.Environment
import Utils
import Schema
import Plugins

import RuntimeTypes
import Reactive.Threepenny
import Graphics.UI.Threepenny.Core hiding (get,delete,apply)
import Graphics.UI.Threepenny.Internal (wId)
import Data.Monoid hiding (Product(..))

import qualified Data.Text as T
import Database.PostgreSQL.Simple.Internal
import qualified Data.Map as M
import qualified Data.ByteString as BS

import qualified Data.HashMap.Strict as HM


main :: IO ()
main = do
  args <- getArgs
  smvar   <- createVar
  let
    db = argsToState args
    amap = authMap smvar db (user db , pass db )
  print "Dyn Load Plugins"
  print "Load Metadata"
  (metas ,lm)<- runDynamic $keyTablesInit  smvar ("metadata", T.pack $ user db) amap []

  print "Load Plugins"
  regplugs <- plugs smvar amap db plugList
  print "Start Server"
  (ref ,ls)<- runDynamic $ addServer metas


  print "Load Polling Process"
  poller smvar amap db regplugs False
  -- pollRmtc smvar amap (T.pack $ user db)

  cp <- lookupEnv "SYNC_SERVER_PORT"
  ch <- lookupEnv "SYNC_SERVER_HOST"
  traverse (forkIO .flip patchClient smvar) (ServerConfig <$> (join $ readMay <$> cp)<*> ch)


  sp <- lookupEnv "SYNC_PORT"
  sh <- lookupEnv "SYNC_HOST"
  traverse (forkIO . flip patchServer  smvar) (ServerConfig <$> (join $ readMay <$> sp)<*> sh)


  print "Load GUI Server"
  let
    initGUI = do
      Just (TableModification _ _ (CreateRow c)) <- addClientLogin metas
      let [(SerialTB1 (Just (TB1 (SNumeric i))))] = traceShowId $ F.toList ((\(Idex i ) -> i) $ G.getIndex c)
      return i
    finalizeGUI w = void $ closeDynamic $ do
        liftIO$ print ("delete client " <> show (wId w))
        deleteClient metas (fromIntegral $ wId w)
        deleteClientLogin metas (wId w)


  startGUI (defaultConfig { jsStatic = Just "static", jsCustomHTML = Just "index.html" })  (setup smvar args regplugs ) initGUI finalizeGUI
  mapM writeSchema  . HM.toList =<< atomically (readTMVar (globalRef smvar))
  print "Finish Server"
  runDynamic $ traverse (deleteServer metas) ref
  sequence lm
  sequence ls

  return ()


