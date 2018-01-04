{-# LANGUAGE FlexibleContexts,OverloadedStrings , NoMonomorphismRestriction #-}
module Poller
  (poller
  ,plugs
  ) where

import qualified NonEmpty as Non
import Control.Concurrent.Async
import Control.Arrow
import Types
import qualified Types.Index as G
import Control.Monad.Writer
import Step.Client (indexTable)
import Data.Interval(Extended(..),interval,upperBound,lowerBound)
import Graphics.UI.Threepenny.Timer hiding(interval)
import Data.Either
import Step.Host
import SchemaQuery
import Prelude hiding (head)
import Control.Monad.Reader
import Control.Concurrent
import Data.Functor.Apply
import Control.Concurrent.STM
import Utils
import TP.Widgets (diffEvent)
import Schema
import Types.Patch
import Data.Maybe
import Reactive.Threepenny hiding (apply)
import Debug.Trace
import Data.Traversable (traverse)
import qualified Data.List as L
import Data.Time

import RuntimeTypes
import Data.Monoid hiding (Product(..))

import qualified Data.Text as T
import qualified Data.Map as M
import qualified Data.HashMap.Strict as HM



plugs schm authmap db plugs = do
  inf <- metaInf schm
  regplugs <- fmap fst $ runDynamic $ transactionNoLog inf  $ do
      (db ,(_,t)) <- selectFrom "plugins"  Nothing Nothing [] $ mempty
      let
        regplugs = catMaybes $ findplug <$> plugs
        findplug :: PrePlugins -> Maybe Plugins
        findplug p = (,p). round . unTB1 . flip index "oid" . G.leafValue<$>  listToMaybe (G.getEntries $ G.queryCheck (pred ,rawPK (lookTable inf "plugins")) t)
          where
            pred :: TBPredicate Key Showable
            pred = WherePredicate $ AndColl [PrimColl (liftAccess inf "plugins" $ keyRef "name" , Left (txt $ _name p,Equals))]
      return regplugs
  atomically $ do
    schmRef <-readTVar schm
    modifyTVar (globalRef schmRef) (HM.alter  (fmap(\i -> i {plugins=regplugs})) "metadata")
  return regplugs



index tb item = snd $ justError ("no item" <> show (item,tb)) $ indexTable [keyRef item] (tableNonRef' tb)
index2 tb item = justError ("no item" <> show (item,tb)) $ indexFieldRec item tb

checkTime curr = do
    let
      IntervalTB1 time_inter = index curr "time"
      TB1 (STime (STimestamp startLocal)) = justError "cant be null start"$ unFinite $ lowerBound time_inter
      TB1 (STime (STimestamp endLocal)) = justError "cant be null end" $unFinite $ upperBound time_inter
      start = startLocal
      end = endLocal
    current <- getCurrentTime
    return $ (start,end,curr,current)

poller schmRef authmap db plugs is_test = do
  metas <- metaInf schmRef

  let conn = rootconn metas
  ((dbpol,(_,polling)),_)<- runDynamic $ transactionNoLog metas $ selectFrom "polling" Nothing Nothing [] $ mempty
  let
    project tb =  (schema,intervalms,p,pid)
      where
        TB1 (SNumeric schema )= index tb "schema"
        TB1 (SNumeric intervalms) = index tb "poll_period_ms"
        TB1 (SText p) = index2 tb (liftAccess metas "polling" $ Nested [keyRef "plugin"] (Many [One $ keyRef "name"]))
        pid = index tb "plugin"
    enabled = G.toList polling
    poll tb  = do
      let plug = L.find ((==pname ). _name .snd ) plugs
          (schema,intervalms ,pname ,pid) = project tb
          indexRow polling = justError (show $ (tbpred tb )) $ G.lookup (tbpred tb) polling
          tbpred = G.getIndex (tableMeta $ lookTable metas "polling")

      schm <- atomically $ readTVar schmRef
      (inf ,_)<- runDynamic $ keyTables  schmRef (justLook schema (schemaIdMap schm) , T.pack $ user db) authmap plugs
      (startP,_,_,current) <- checkTime (indexRow polling )
      flip traverse plug $ \(idp,p) -> do
          let f = pluginStatic p
              elemp = pluginRun (_plugAction p)
              pname = _name p
              a = _bounds p
          let iter polling = do
                  (start,end,curr,current) <- liftIO$ checkTime polling
                  liftIO$ putStrLn $ "LAST RUN " <> show (schema,pname,current,start,end)
                  let intervalsec = intervalms `div` 10^3
                  when (is_test || diffUTCTime current start  >  fromIntegral intervalsec) $ do
                      liftIO$ putStrLn $ "START " <> T.unpack pname  <> " - " <> show current
                      let fetchSize = 200
                          pred =  WherePredicate $ lookAccess inf a <$> AndColl (catMaybes [ genPredicateU True (fst f) , genPredicateU False (snd f)])
                          predFullIn =  WherePredicate . fmap (lookAccess inf a) <$>  genPredicateFullU True (fst f)
                          predFullOut =  WherePredicate . fmap (lookAccess inf a) <$>  genPredicateFullU True (snd f)
                      (_ ,(l,_ )) <- transactionNoLog inf $ selectFrom a  (Just 0) (Just fetchSize) []  pred
                      liftIO$ threadDelay 10000
                      let sizeL = justLook pred  l
                          lengthPage s pageSize  =   res
                            where
                              res = (s  `div` pageSize) +  if s `mod` pageSize /= 0 then 1 else 0
                      i <- concat <$> mapM (\ix -> do
                          (_,(_,listResAll)) <- transactionNoLog inf $ selectFrom a  (Just ix) (Just fetchSize) [] pred
                          let listRes = L.take fetchSize . G.toList $  listResAll

                          let evb = filter (\i-> maybe False (G.checkPred i) predFullIn && not (maybe False (G.checkPred i) predFullOut) ) listRes
                          i <-  liftIO $ mapM (mapM (\inp -> catchPluginException inf (tableUnique (lookTable inf a)) idp ( getPKM (tableMeta $ lookTable inf a)inp) $ fmap fst $ runDynamic $ transactionLog inf $ do
                              case elemp of
                                Right action  -> do
                                  getP <- getFrom (lookTable inf a) inp
                                  ovm  <- fmap (liftTable' inf a) <$> liftIO (action (mapKey' keyValue (maybe inp (apply inp) getP)))
                                  maybe (return ()) (\ov-> do
                                         p <- fullDiffEdit (tableMeta $ lookTable inf a)inp ov
                                         return ()) ovm
                                Left action -> do
                                    getP <- getFrom (lookTable inf a) inp
                                    ovm  <- fmap (liftPatch inf a) <$> liftIO (action (mapKey' keyValue (maybe inp (apply inp) getP)))
                                    maybe (return ()) (\ov-> do
                                      p <- fullDiffEditInsert (tableMeta $ lookTable inf a)inp (apply inp ov)
                                      return ()) ovm
                              )
                            ) . L.transpose .  chuncksOf 20 $ evb
                          return $ concat i
                          ) [0..(lengthPage (fst sizeL) fetchSize -1)]
                      end <- liftIO $ getCurrentTime
                      liftIO$ putStrLn $ "END " <>T.unpack pname <> " - " <> show end
                      let polling_log = lookTable metas "polling_log"
                      dbplog <-  refTable metas polling_log
                      let table = (\i -> tblist
                              [ attrT ("plugin",pid )
                              , attrT ("schema",TB1 (SNumeric schema))
                              , IT "diffs" (LeftTB1 $ ArrayTB1  . Non.fromList <$> (
                                        nonEmpty  . concat . catMaybes $
                                            fmap (fmap (TB1 . tblist  )) .  either (\r ->Just $ pure $ [attrT ("except", LeftTB1 $ Just $ TB1 (SNumeric r) ),attrT ("modify",LeftTB1 $Nothing)]) (Just . fmap (\r -> [attrT ("modify", LeftTB1 $ Just $ TB1 (SNumeric (justError "no id" $ tableId $  r))   ),attrT ("except",LeftTB1 $Nothing)])) <$> i))
                              , attrT ("duration",srange (time current) (time end))]) <$> nonEmpty i
                          time  = TB1 . STime . STimestamp
                          table2 = tblist
                              [ attrT ("plugin",pid)
                              , attrT ("schema",TB1 (SNumeric schema))
                              , attrT ("time",srange (time current) (time end))
                              ]

                      transactionLog metas  $ do
                          fktable2 <- loadFKS ( lookTable metas "polling") (liftTable' metas "polling"  table2)
                          fullDiffEdit ( lookMeta metas "polling")curr fktable2
                      return ()

          pid <- forkIO (void $ do
              putStrLn ("Start Poller: " <> T.unpack pname )
              -- iter polling
              (tm,_) <- runDynamic $ timer intervalms
              print (intervalms,diffUTCTime current startP,(intervalms - (round $ 10^3 * realToFrac ( diffUTCTime current startP))))
              forkIO (void $  threadDelay (max 0 (10^3*(intervalms - (round $ 10^3 * realToFrac ( diffUTCTime current startP))))) >> putStrLn ("Timer Start" <> T.unpack pname) >> start tm>>  (runDynamic $ iter (indexRow polling)))
              let
                  evIter = indexRow <$> (unionWith const (rumors $ collectionTid dbpol ) (facts ( collectionTid dbpol )<@ tick tm))

              (bhIter ,_) <- runDynamic $ stepper (indexRow  polling) evIter
              let  evDiffIter = diffEvent bhIter evIter
              runDynamic $onEventDyn  evDiffIter (iter) )
          return ()
  mapM poll  enabled

