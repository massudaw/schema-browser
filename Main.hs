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
  let db = argsToState args
  -- Load Metadata
  let
    amap = authMap smvar db (user db , pass db )

  print "Load Metadata"
  (metas ,lm)<- runDynamic $keyTablesInit  smvar ("metadata", T.pack $ user db) amap []

  print "Load Plugins"
  regplugs <- plugs smvar amap db plugList
  _ <- runDynamic $keyTablesInit  smvar ("gmail", T.pack $ user db) amap regplugs
  _ <- runDynamic $keyTablesInit  smvar ("incendio", T.pack $ user db) amap regplugs

  print "Start Server"
  (ref ,ls)<- runDynamic $ addServer metas


  print "Load Polling Process"
  poller smvar amap db regplugs False

  print "Load GUI Server"
  let
    initGUI = do
      Just (TableModification _ _ (_,G.Idex c,_)) <- addClientLogin metas
      let [(SerialTB1 (Just (TB1 (SNumeric i))))] = F.toList c
      return i
    finalizeGUI w = void $ closeDynamic $ do
        liftIO$ print ("delete client " <> show (wId w))
        deleteClient metas (fromIntegral $ wId w)
        deleteClientLogin metas (wId w)


  startGUI (defaultConfig { jsStatic = Just "static", jsCustomHTML = Just "index.html" })  (setup smvar args regplugs ) initGUI finalizeGUI
  print "Finish Server"
  runDynamic $ traverse (deleteServer metas) ref
  sequence lm
  sequence ls

  return ()


