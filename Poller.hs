{-# LANGUAGE OverloadedStrings #-}
module Poller
  (poller
  ,plugs
  ) where

import qualified NonEmpty as Non
import Control.Concurrent.Async
import Types
import qualified Types.Index as G
import Data.Either
import Step
import qualified Data.Set as S
import SchemaQuery
import PostgresQuery (postgresOps,connRoot)
import Prelude hiding (head)
import Control.Monad.Reader
import Control.Concurrent
import Data.Functor.Apply
import Utils
import Schema
import Patch
import Data.Maybe
import Reactive.Threepenny
import Data.Traversable (traverse)
import qualified Data.List as L
import Data.Time

import RuntimeTypes
import Data.Monoid hiding (Product(..))

import qualified Data.Foldable as F
import qualified Data.Text as T


import Database.PostgreSQL.Simple
import qualified Data.Map as M

import GHC.Stack


plugs schm db plugs = do
  conn <- connectPostgreSQL (connRoot db)
  inf <- keyTables schm conn conn ("metadata",T.pack $ user db ) Nothing postgresOps plugs
  (db ,(s,t)) <- transaction inf $ eventTable  inf (lookTable inf "plugins") Nothing Nothing [] []
  let els = L.filter (not . (`L.elem` G.toList t)) $ (\o->  liftTable' inf "plugins" $ tblist (_tb  <$> [Attr "name" (TB1 $ SText $ _name o) ])) <$> plugs
  p <-transaction inf $ do
     elsFKS <- mapM (loadFKS inf ) els
     mapM (\table -> fullDiffInsert  (meta inf)  table) elsFKS
  putMVar (patchVar db) (tableDiff <$> catMaybes p)



index tb item = snd $ justError ("no item" <> show item) $ indexTable (IProd True [item]) (tableNonRef' tb)

testPoller plug = do
  smvar <- newMVar M.empty
  poller smvar  (BrowserState "localhost" "5432" "incendio" "postgres" "queijo" Nothing Nothing) [plug] True

poller schm db plugs is_test = do
  conn <- connectPostgreSQL (connRoot db)
  metas <- keyTables  schm conn  conn ("metadata", T.pack $ user db) Nothing postgresOps plugs
  (dbpol,(_,polling))<- transaction metas $ eventTable metas (lookTable metas "polling")  Nothing Nothing [] []
  let
    project tb =  (schema,intervalms,p)
      where
        TB1 (SText schema )= index tb "schema_name"
        TB1 (SNumeric intervalms) = index tb "poll_period_ms"
        TB1 (SText p) = index tb "poll_name"
    enabled = G.toList polling
    poll tb  = do
      let plug = L.find ((==pname ). _name ) plugs
          (schema,intervalms ,pname ) = project tb
      flip traverse plug $ \p -> do
          let f = pluginStatic p
              elemp = pluginAction p
              pname = _name p
              a = _bounds p
          pid <- forkIO $ (void $ forever $ do
            (_,(_,polling))<- transaction metas $ eventTable metas (lookTable metas "polling")  Nothing Nothing [] []
            let curr = justError "" $ G.lookup (tbpred tb) polling
                tbpred = G.Idex (S.fromList $ rawPK $ lookTable metas "polling" )
                TB1 (STimestamp startLocal) = index curr "start_time"
                TB1 (STimestamp endLocal) = index curr "end_time"
                start = localTimeToUTC utc startLocal
                end = localTimeToUTC utc endLocal
            current <- getCurrentTime
            putStrLn $ "LAST RUN " <> show (schema,pname,start,end)
            let intervalsec = intervalms `div` 10^3
            if  is_test || diffUTCTime current start  >  fromIntegral intervalsec
            then do
                putStrLn $ "START " <> T.unpack pname  <> " - " <> show current
                inf <- keyTables  schm conn  conn (schema, T.pack $ user db) Nothing postgresOps plugs
                let fetchSize = 1000
                (dbplug ,(l,listRes)) <- transaction inf $ eventTable inf (lookTable inf a) Nothing (Just fetchSize) [][]
                let sizeL = justLook [] l
                    lengthPage s pageSize  = (s  `div` pageSize) +  if s `mod` pageSize /= 0 then 1 else 0
                i <- concat <$> mapM (\ix -> do
                    (_,(_,listResAll)) <- transaction inf $ eventTable inf (lookTable inf a) (Just ix) (Just fetchSize) [][]
                    let listRes = L.take fetchSize . G.toList $ listResAll

                    let evb = filter (\i -> tdInput i  && tdOutput1 i ) listRes
                        tdInput i =  isJust  $ checkTable  (fst f) i
                        tdOutput1 i =   not $ isJust  $ checkTable  (snd f) i

                    i <-  mapConcurrently (mapM (\inp -> catchPluginException inf a pname (getPKM inp) $ do
                        o  <- fmap (liftTable' inf a) <$>   elemp (Just $ mapKey' keyValue inp)
                        let diff' =   join $ (\i j -> diff (j ) (i)) <$>  o <*> Just inp
                        v <- maybe (return Nothing )  (\i -> transaction inf $ (editEd $ schemaOps inf) inf (justError "no test" o) inp ) diff'
                        (traverse (putMVar (patchVar dbplug). pure) . fmap tableDiff) v
                        return v
                          )
                      ) . L.transpose . chuncksOf 20 $ evb
                    return $ concat i
                    ) [0..(lengthPage (fst sizeL) fetchSize -1)]
                end <- getCurrentTime
                putStrLn $ "END " <>T.unpack pname <> " - " <> show end
                let polling_log = lookTable (meta inf) "polling_log"
                dbplog <-  refTable (meta inf) polling_log
                let table = tblist
                        [ attrT ("poll_name",TB1 (SText pname))
                        , attrT ("schema_name",TB1 (SText schema))
                        , _tb $ IT (attrT ("diffs",LeftTB1 $ Just$ ArrayTB1 $ Non.fromList $ [TB1 ()])) (LeftTB1 $ ArrayTB1  . Non.fromList <$> (
                                  nonEmpty  . catMaybes $
                                      fmap (TB1 . tblist  ) .  either (\r ->Just $ [attrT ("except", LeftTB1 $ Just $ TB1 (SNumeric r) ),attrT ("modify",LeftTB1 $Nothing)]) (fmap (\r -> [attrT ("modify", LeftTB1 $ Just $ TB1 (SNumeric (justError "no id" $ tableId $  r))   ),attrT ("except",LeftTB1 $Nothing)])) <$> i))
                        , attrT ("duration",srange (time current) (time end))]
                    time  = TB1 . STimestamp . utcToLocalTime utc
                    table2 = tblist
                        [ attrT ("poll_name",TB1 (SText pname))
                        , attrT ("schema_name",TB1 (SText schema))
                        , attrT ("start_time",time current)
                        , attrT ("end_time",time end)]

                (p2,p) <- transaction (meta inf) $ do
                    fktable2 <- loadFKS (meta inf) (liftTable' (meta inf) "polling"  table2)
                    p2 <- fullDiffEdit (meta inf) curr fktable2
                    fktable <- loadFKS (meta inf) (liftTable' (meta inf) "polling_log"  table)
                    p <-fullDiffInsert  (meta inf) fktable
                    return (fktable2,p)
                traverse (putMVar (patchVar dbplog) .pure ) (fmap tableDiff  p)
                traverse (putMVar (patchVar dbpol). pure) (maybeToList $ diff curr p2)
                threadDelay (intervalms*10^3)
            else do
                threadDelay (round $ (*10^6) $  diffUTCTime current start ) )

          return ()
  mapM poll  enabled

