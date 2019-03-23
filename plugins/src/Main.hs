{-# LANGUAGE TypeFamilies, Rank2Types, FlexibleContexts,
  UndecidableInstances, ScopedTypeVariables, OverloadedStrings #-}
module Main ( main
  ) where
import Control.Exception
import Query
import Control.Monad.Reader
import qualified Data.Foldable as F
import Types.Patch
import Plugins (plugList)
import Plugins.Schema
import Poller
import Schema
import SchemaQuery
import System.Environment
import ClientAccess (addClientLogin)
import TP.Main
import TP.QueryWidgets
import Types

import Graphics.UI.Threepenny.Core
import RuntimeTypes

import qualified Data.Map as M


main :: IO ()
main = do
  print "Start Server"
  db <- argsToState <$> getArgs
  smvar <- createVar
  let
      amap = authMap
  print "Load Metadata"
  (metas, lm) <-
    runDynamic $keyTablesInit smvar ("metadata", postgresUser ) amap
  print "Load Plugins"
  (plugListLoad, pfin) <-
    runDynamic $ do
      keyTablesInit smvar ("code", postgresUser) amap
      addPlugins plugList smvar
  print "Register Plugins"
  regplugs <- plugs smvar amap db plugListLoad
  mapM print regplugs

  -- print "Load Polling Process"
  -- poller smvar amap db regplugs False
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
        RowPatch (ix,CreateRow c) <- addClientLogin metas
        let [LeftTB1 (Just (TB1 (SNumeric i)))] =
               (\(Idex i) -> F.toList i) ix
        liftIO $ putStrLn $ "Initialize Client: " ++ show i
        return i
  startGUI
    (defaultConfig {jsStatic = Just "static", jsCustomHTML = Just "index.html"})
    (setup smvar db regplugs)
    initGUI `catch`
    (\e -> do
       putStrLn "Finish Server"
       putStrLn $ "Exit Cause: " ++ show (e :: SomeException)
       -- mapM writeSchema . F.toList =<<
         -- atomically (readTVar . globalRef =<< readTVar smvar)
       sequence_ pfin
       sequence_ lm
       )
  return ()


getState = do
  argsToState <$> getArgs

withSelector s m  = do
  db <- getState
  smvar <- createVar
  let
    amap = authMap

  (metas, lm) <-
    runDynamic $ keyTablesInit smvar ("metadata", postgresUser) amap
  (plugListLoad, pfin) <-
    runDynamic $ do
      keyTablesInit smvar ("code", postgresUser) amap
      addPlugins plugList smvar
  regplugs <- plugs smvar amap db plugListLoad
  (inf,fin) <- runDynamic $ keyTables smvar  (s,postgresUser) amap
  startGUI defaultConfig {jsStatic = Just "static", jsCustomHTML = Just "index.html"} (\w -> do
    let
      table = lookTable inf m
    ref <- ui $ refTables inf  table
    crud <- crudUITable inf table ref   M.empty [] (allRec' (tableMap inf) table) (pure Nothing)
    addBody [getElement crud]
                                                                 ) (return 1)





