{-# LANGUAGE TypeFamilies, Rank2Types, FlexibleContexts,
  UndecidableInstances, ScopedTypeVariables, OverloadedStrings #-}

module Main
  ( main
  ) where
import Control.Concurrent
import Control.Concurrent.STM
import Control.Exception
import Control.Monad.Reader
import qualified Data.Foldable as F
import Data.Unique
import Debug.Trace
-- import PatchSync
import Plugins (plugList)
import Plugins.Schema
import Poller
import Postgresql.Backend (connRoot)
import Prelude hiding (head)
import Rmtc
import Safe
import Schema
import SchemaQuery
import System.Environment
import System.Process (rawSystem)
import System.Remote.Monitoring
import TP.Browser
       (addClientLogin, addServer, deleteClient, deleteClientLogin,
        deleteServer)
import TP.Main
import TP.QueryWidgets
import Types
import qualified Types.Index as G
import Types.Patch (RowPatch(..))

import Data.Monoid hiding (Product(..))
import Graphics.UI.Threepenny.Core hiding (apply, delete, get)
import Graphics.UI.Threepenny.Internal (wId)
import Reactive.Threepenny
import RuntimeTypes

import qualified Data.ByteString as BS
import qualified Data.Map as M
import qualified Data.Text as T
import Database.PostgreSQL.Simple.Internal

import qualified Data.HashMap.Strict as HM

main :: IO ()
main = do
  args <- getArgs
  smvar <- createVar
  let db = argsToState args
      amap = authMap smvar db (user db, pass db)
  print "Dyn Load Plugins"
  print "Load Metadata"
  (metas, lm) <-
    runDynamic $keyTablesInit smvar ("metadata", T.pack $ user db) amap []
  print "Start Server"
  (ref, ls) <- runDynamic $ addServer metas
  print "Load Plugins"
  (plugListLoad, pfin) <-
    runDynamic $ do
      keyTablesInit smvar ("code", T.pack $ user db) amap []
      addPlugins plugList smvar
  regplugs <- plugs smvar amap db plugListLoad
  print "Load Polling Process"
  poller smvar amap db regplugs False
  --cp <- lookupEnv "SYNC_SERVER_PORT"
  --ch <- lookupEnv "SYNC_SERVER_HOST"
  --traverse
  --  (forkIO . flip patchClient smvar)
  --  (ServerConfig <$> join (readMay <$> cp) <*> ch)
  --sp <- lookupEnv "SYNC_PORT"
  --sh <- lookupEnv "SYNC_HOST"
  --traverse
  --  (forkIO . flip patchServer smvar)
  --  (ServerConfig <$> join (readMay <$> sp) <*> sh)
  print "Load GUI Server"
  let initGUI = do
        Just (TableModification _ _ _ _ (CreateRow c)) <- addClientLogin metas
        let [LeftTB1 (Just (TB1 (SNumeric i)))] =
              F.toList ((\(Idex i) -> i) $ G.getIndex (lookMeta metas "clients")c)
        liftIO $ putStrLn $ "Initialize Client: " ++ show i
        return i
      finalizeGUI w =
        void $
        closeDynamic $ do
          liftIO $ print ("delete client " <> show (wId w))
          deleteClient metas (fromIntegral $ wId w)
          deleteClientLogin metas (wId w)
  forkServer "localhost" 8000
  startGUI
    (defaultConfig {jsStatic = Just "static", jsCustomHTML = Just "index.html"})
    (setup smvar args regplugs)
    initGUI
    finalizeGUI `catch`
    (\e -> do
       putStrLn $ "Finish Server"
       putStrLn $ "Exit Cause: " ++ show (e :: SomeException)
       runDynamic $ traverse (deleteServer metas) ref
       mapM writeSchema . HM.toList =<<
         atomically (readTVar . globalRef =<< readTVar smvar)
       sequence_ pfin
       sequence_ lm
       sequence_ ls)
  return ()
