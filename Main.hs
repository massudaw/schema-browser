{-# LANGUAGE FlexibleContexts,OverloadedStrings #-}
module Main where
import TP.Main
import TP.Browser(addServer,deleteServer,deleteClient,addClientLogin,deleteClientLogin)
import Data.Unique
import Types
import qualified Types.Index as G
import qualified Data.Foldable as F
import TP.QueryWidgets(lookAttr')
import System.Process (rawSystem)
import Poller
import Plugins
import Postgresql.Backend (connRoot)
import Prelude hiding (head)
import Control.Monad.Reader
import Control.Concurrent
import System.Environment
import Utils
import Schema

import RuntimeTypes
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
  smvar   <- newMVar HM.empty
  let db = argsToState args
  -- Load Metadata
  conn <- connectPostgreSQL (connRoot db)
  let
    amap = authMap smvar db (user db , pass db )

  print "Load Metadata"
  (metas ,_)<- runDynamic $keyTables  smvar conn  ("metadata", T.pack $ user db) amap plugList
  print "Start Server"
  ref <- addServer metas

  print "Load Plugins"
  plugs smvar amap db plugList

  print "Load Polling Process"
  poller smvar amap db plugList False

  print "Load GUI Server"
  forkIO $ threadDelay 50000 >> rawSystem "chromium" ["http://localhost:8025"] >> return ()
  let
    initGUI = do
        Just (TableModification _ _ (_,G.Idex c,_)) <- addClientLogin metas
        let [(SerialTB1 (Just (TB1 (SNumeric i))))] = F.toList c
        return i
    finalizeGUI w = do
        print ("delete client" <> show (wId w))
        deleteClientLogin metas (wId w)
        deleteClient metas (fromIntegral $ wId w)


  startGUI (defaultConfig { jsStatic = Just "static", jsCustomHTML = Just "index.html" })  (setup smvar args plugList ) initGUI finalizeGUI
  print "Finish Server"
  traverse (deleteServer metas) ref
  return ()
