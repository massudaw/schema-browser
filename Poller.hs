{-# LANGUAGE FlexibleContexts,OverloadedStrings , NoMonomorphismRestriction #-}
module Poller
  (poller
  ,plugs
  ) where

import qualified NonEmpty as Non
import Control.Concurrent.Async
import Types
import qualified Types.Index as G
import Control.Monad.Writer
import Step.Client (indexTable)
import Data.Either
import Step.Host
import SchemaQuery
import Prelude hiding (head)
import Control.Monad.Reader
import Control.Concurrent
import Data.Functor.Apply
import Control.Concurrent.STM
import Utils
import Schema
import Types.Patch
import Data.Maybe
import Reactive.Threepenny
import Debug.Trace
import Data.Traversable (traverse)
import qualified Data.List as L
import Data.Time

import RuntimeTypes
import Data.Monoid hiding (Product(..))

import qualified Data.Text as T
import qualified Data.Map as M



plugs schm authmap db plugs = do
  inf <- metaInf schm
  transaction inf  $ do
      (db ,(_,t)) <- selectFrom "plugins"  Nothing Nothing [] []
      let els = L.filter (not . (`L.elem` G.toList t)) $ (\o->  liftTable' inf "plugins" $ tblist (_tb  <$> [Attr "name" (TB1 $ SText $ _name o) ])) <$> plugs
      elsFKS <- mapM loadFKS  els
      mapM fullDiffInsert  elsFKS



index tb item = snd $ justError ("no item" <> show item) $ indexTable (IProd True [item]) (tableNonRef' tb)

checkTime polling tb = do
    let curr = justError (show $ tbpred tb) $ G.lookup (tbpred tb) polling
        tbpred = G.Idex . getPKM
        TB1 (STimestamp startLocal) = index curr "start_time"
        TB1 (STimestamp endLocal) = index curr "end_time"
        start = localTimeToUTC utc startLocal
        end = localTimeToUTC utc endLocal
    current <- getCurrentTime
    return $ (start,end,curr,current)

poller schm authmap db plugs is_test = do
  metas <- metaInf schm
  let conn = rootconn metas
  (dbpol,(_,polling))<- transaction metas $ selectFrom "polling" Nothing Nothing [] []
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
      inf <- keyTables  schm conn  (schema, T.pack $ user db) authmap plugs
      flip traverse plug $ \p -> do
          let f = pluginStatic p
              elemp = pluginAction p
              pname = _name p
              a = _bounds p
          let iter polling = do
                  (start,end,curr,current) <- checkTime polling tb
                  putStrLn $ "LAST RUN " <> show (schema,pname,start,end)
                  let intervalsec = intervalms `div` 10^3
                  if  is_test || diffUTCTime current start  >  fromIntegral intervalsec
                  then do
                      putStrLn $ "START " <> T.unpack pname  <> " - " <> show current
                      let fetchSize = 1000
                      (_ ,(l,_ )) <- transaction inf $ selectFrom a  Nothing (Just fetchSize) [][]
                      let sizeL = justLook [] l
                          lengthPage s pageSize  = (s  `div` pageSize) +  if s `mod` pageSize /= 0 then 1 else 0
                      i <- concat <$> mapM (\ix -> do
                          (_,(_,listResAll)) <- transaction inf $ selectFrom a  (Just ix) (Just fetchSize) [][]
                          let listRes = L.take fetchSize . G.toList $ listResAll

                          let evb = filter (\i -> tdInput i  && tdOutput1 i ) listRes
                              tdInput i =  isJust  $ checkTable  (fst f) i
                              tdOutput1 i =   not $ isJust  $ checkTable  (snd f) i

                          i <-  mapM (mapM (\inp -> catchPluginException inf a pname (getPKM inp) $ transaction inf $ do
                              ov  <- fmap (liftTable' inf a) <$>   liftIO ( elemp (Just $ mapKey' keyValue inp))
                              let c = ov
                              let diff' = join $ diff <$> Just inp <*> c
                              liftIO$ print diff'
                              v <- maybe (return Nothing )  (\i -> do
                                 p <- fullDiffEdit inp (justError "no test" c)
                                 tell [TableModification (Just 10)(lookTable inf a) i ]
                                 return $ Just (TableModification (Just 10) (lookTable inf a)i )
                                 ) diff'
                              return v)
                            ) .  chuncksOf 20 $ evb
                          return $ concat i
                          ) [0..(lengthPage (fst sizeL) fetchSize -1)]
                      end <- getCurrentTime
                      putStrLn $ "END " <>T.unpack pname <> " - " <> show end
                      let polling_log = lookTable metas "polling_log"
                      dbplog <-  refTable metas polling_log
                      let table = tblist
                              [ attrT ("poll_name",TB1 (SText pname))
                              , attrT ("schema_name",TB1 (SText schema))
                              , _tb $ IT "diffs" (LeftTB1 $ ArrayTB1  . Non.fromList <$> (
                                        nonEmpty  . catMaybes $
                                            fmap (TB1 . tblist  ) .  either (\r ->Just $ [attrT ("except", LeftTB1 $ Just $ TB1 (SNumeric r) ),attrT ("modify",LeftTB1 $Nothing)]) (fmap (\r -> [attrT ("modify", LeftTB1 $ Just $ TB1 (SNumeric (justError "no id" $ tableId $  r))   ),attrT ("except",LeftTB1 $Nothing)])) <$> i))
                              , attrT ("duration",srange (time current) (time end))]
                          time  = TB1 . STimestamp . utcToLocalTime utc
                          table2 = tblist
                              [ attrT ("poll_name",TB1 (SText pname))
                              , attrT ("schema_name",TB1 (SText schema))
                              , attrT ("start_time",time current)
                              , attrT ("end_time",time end)]

                      {-(p2,p) <- transaction metas  $ do
                          fktable2 <- loadFKS  (liftTable' metas "polling"  table2)
                          p2 <- fullDiffEdit curr fktable2
                          fktable <- loadFKS  (liftTable' metas  "polling_log"  table)
                          p <-fullDiffInsert  fktable
                          return (fktable2,p)-}
                      threadDelay (intervalms*10^3)
                  else do
                      threadDelay (round $ (*10^6) $  diffUTCTime current start )

          pid <- forkIO (void $ iter polling >> (forever $  do
              (_,(_,polling))<- transaction metas $ selectFrom "polling"   Nothing Nothing [] []
              iter polling ))
          return ()
  mapM poll  enabled

