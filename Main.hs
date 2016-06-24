{-# LANGUAGE FlexibleContexts,OverloadedStrings #-}
module Main where
import TP.Browser
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
import Data.Monoid hiding (Product(..))

import qualified Data.Text as T
import Database.PostgreSQL.Simple
import Database.PostgreSQL.Simple.Internal
import qualified Data.Map as M
import qualified Data.ByteString as BS



main :: IO ()
main = do
  args <- getArgs
  print "Start Server"
  smvar   <- newMVar M.empty
  let db = argsToState (tail args)
  -- Load Metadata
  conn <- connectPostgreSQL (connRoot db)

  let
    amap = authMap smvar db (user db , pass db )

  print "Load Metadata"
  metas <- keyTables  smvar conn  ("metadata", T.pack $ user db) amap plugList

  print "Load Plugins"
  plugs smvar amap db plugList

  print "Load Polling Process"
  poller smvar amap db plugList False

  print "Load GUI Server"
  forkIO $ threadDelay 50000 >> rawSystem "chromium" ["http://localhost:8025"] >> return ()
  startGUI (defaultConfig { jsStatic = Just "static", jsCustomHTML = Just "index.html" , jsPort = fmap read $ safeHead args })  (setup smvar  (tail args))
      {-(\w ->  liftIO $ do
          print ("delete client" <> show (sToken w))
          deleteClient metas (sToken w) )-}
  print "Finish Server"
  print "Start Dump State"
  print "Finish Dump State"

  return ()
