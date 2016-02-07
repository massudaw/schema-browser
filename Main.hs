{-# LANGUAGE FlexibleContexts,OverloadedStrings #-}
import TP.Browser
import Poller
import Plugins
import PostgresQuery (connRoot)
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

  print "Initialize Sql Script"
  f <- BS.readFile "sql/init_usage.sql"
  i <- exec conn f
  print i
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
  print "Start Dump State"
  -- dumpSnapshot smvar
  print "Finish Dump State"

  -- getLine
  return ()
