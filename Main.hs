{-# LANGUAGE FlexibleContexts,OverloadedStrings #-}
import TP.Browser
import Control.Concurrent.STM
import Poller
import Plugins
import PostgresQuery (connRoot)
import Data.String
import Prelude hiding (head)
import Control.Monad.Reader
import Control.Concurrent
import System.Environment
import Utils
import qualified Types.Index as G
import Schema

import RuntimeTypes
import Graphics.UI.Threepenny.Core hiding (get,delete,apply)
import Data.Monoid hiding (Product(..))

import qualified Data.Text as T
import Database.PostgreSQL.Simple
import Database.PostgreSQL.Simple.Internal
import qualified Data.Map as M
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as BSL
import RuntimeTypes
import Types
import Data.Binary (encode,decode)
import System.Directory

import qualified Reactive.Threepenny as R


main :: IO ()
main = do
  args <- getArgs
  print "Start Server"
  smvar   <- newMVar M.empty
  let db = argsToState (tail args)
  -- Load Metadata
  conn <- connectPostgreSQL (connRoot db)

  print "Initialize Sql Script"
  f <- BS.readFile "sql/init_usage.sql"
  exec conn f
  let
    amap = authMap smvar db (user db , pass db )

  print "Load Metadata"
  metas <- keyTables  smvar conn  ("metadata", T.pack $ user db) amap plugList

  print "Load Plugins"
  plugs smvar amap db plugList

  print "Load Polling Process"
  poller smvar amap db plugList False

  print "Load GUI Server"
  startGUI (defaultConfig { tpStatic = Just "static", tpCustomHTML = Just "index.html" , tpPort = fmap read $ safeHead args })  (setup smvar  (tail args)) (\w ->  liftIO $ do
          print ("delete client" <> show (sToken w))
          deleteClient metas (sToken w) )
  print "Finish Server"
  dumpSnapshot smvar
  print "Dump State"

testPoller plug = do
  let bstate = (BrowserState "localhost" "5432" "incendio" "postgres" "queijo" Nothing Nothing Nothing )
      db = bstate
  smvar <- newMVar M.empty
  conn <- connectPostgreSQL (connRoot db)
  let
    amap = authMap smvar db (user db , pass db )
  print "Load Metadata"
  metas <- keyTables  smvar conn  ("metadata", T.pack $ user db) amap plugList


  poller smvar  (\_ -> return (undefined ,undefined)) bstate [plug] True


