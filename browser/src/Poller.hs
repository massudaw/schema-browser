{-# LANGUAGE FlexibleContexts,OverloadedStrings , NoMonomorphismRestriction #-}
module Poller
  (poller
  ,plugs
  ) where

import qualified NonEmpty as Non
import Control.Concurrent.Async
import Control.Arrow
import Control.Monad
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
import qualified Data.Set as S
import qualified Data.HashMap.Strict as HM



plugs :: TVar DatabaseSchema -> t1 -> t -> [PrePlugins] -> IO [Plugins]
plugs schm authmap db plugs = do
  inf <- metaInf schm
  fmap fst $ runDynamic $ transactionNoLog inf  $ do
      db <- selectFrom "plugins"  Nothing mempty
      t <- currentState db
      let
        regplugs = catMaybes $ findplug <$> plugs
        findplug :: PrePlugins -> Maybe Plugins
        findplug p = (,p). round . unTB1 . flip index1 (liftRel inf "plugins" $ keyRef "oid") . G.leafValue<$>  listToMaybe (G.getEntries $ G.queryCheck (pred ,rawPK (lookTable inf "plugins")) (primary t))
          where
            pred :: TBPredicate Key Showable
            pred = WherePredicate $ AndColl [PrimColl $ fixrel (liftRel inf "plugins" $ keyRef "name" , Left (txt $ _pluginName p,Equals))]
      return regplugs



index1 tb item = justError ("no item" <> show (item,tb)) $ attrLookup (item) (tableNonRef tb)

index2 tb item = justError ("no item" <> show (item,tb)) $ recLookup item tb

checkTime meta curr = do
    let
      IntervalTB1 time_inter = index1 curr (liftRel meta "polling" $ Inline "time")
      TB1 (STime (STimestamp startLocal)) = justError "cant be null start"$ unFinite $ lowerBound time_inter
      TB1 (STime (STimestamp endLocal)) = justError "cant be null end" $unFinite $ upperBound time_inter
      start = startLocal
      end = endLocal
    current <- getCurrentTime
    return (start,end,curr,current)

poller schmRef authmap user db plugs is_test = do
  metas <- metaInf schmRef

  let conn = rootconn metas
  (dbpol,polling) <- closeDynamic $ do
    v <- transactionNoLog metas $ selectFrom "polling" Nothing mempty
    i <- currentState v
    return (v,i)
  let
    project tb =  (schema,intervalms,p,pid)
      where
        lrel = liftRel metas "polling" .Inline
        TB1 (SNumeric schema) = index1 tb (lrel "schema")
        TB1 (SNumeric intervalms) = index1 tb (lrel "poll_period_ms")
        TB1 (SText p) = index2 tb (liftRel metas "polling" $ RelAccess (keyRef "plugin") (keyRef "name"))
        pid = index1 tb (lrel "plugin")
    enabled = G.toList (primary polling)
    poll tb  = do
      let plug = L.find ((==pname ). _pluginName .snd ) plugs
          (schema,intervalms ,pname ,pid) = project tb
          indexRow polling = justError (show (tbpred tb )) $ G.lookup (tbpred tb) (primary polling)
          tbpred = G.getIndex (tableMeta $ lookTable metas "polling")

      schm <- readTVarIO schmRef
      (inf ,_)<- runDynamic $ keyTables  schmRef (justLook schema (schemaIdMap schm) , user ) authmap
      (startP,_,_,current) <- checkTime metas (indexRow polling )
      forM plug $ \(idp,p) -> do
          let f = pluginStatic p
              elemp = pluginRun (_plugAction p)
              pname = _pluginName p
              a = _pluginTable p
          let iter polling = do
                  (start,end,curr,current) <- liftIO$ checkTime metas polling
                  liftIO$ putStrLn $ "LAST RUN " <> show (schema,pname,current,start,end)
                  let intervalsec = intervalms `div` 10^3
                  when (is_test || diffUTCTime current start  >  fromIntegral intervalsec) $ do
                      liftIO$ putStrLn $ "START " <> T.unpack pname  <> " - " <> show current
                      let
                          pred =  WherePredicate $ fixrel . first(liftRel inf a) <$> AndColl ( catMaybes [ genPredicateU True (fst f) , genPredicateU False (snd f)])
                          predFullIn =  WherePredicate . fmap (fixrel . first (liftRel inf a)) <$>  genPredicateFullU True (fst f)
                          predFullOut =  WherePredicate . fmap (fixrel . first (liftRel inf a)) <$>  genPredicateFullU True (snd f)
                      l <- currentIndex =<< (transactionNoLog inf $ selectFrom a  (Just 0)   pred)
                      liftIO$ threadDelay 10000
                      let sizeL = justLook pred  (unIndexMetadata l)
                          lengthPage s pageSize  =   res
                            where
                              res = (s  `div` pageSize) +  if s `mod` pageSize /= 0 then 1 else 0
                      i <- concat <$> mapM (\ix -> do
                          listResAll <- currentState =<< (transactionNoLog inf $ selectFrom a  (Just ix) pred)
                          let listRes = L.take 400 . G.toList .primary $  listResAll

                          let evb = filter (\i-> maybe False (G.checkPred i) predFullIn && not (maybe False (G.checkPred i) predFullOut) ) listRes
                              table = (lookTable inf a)
                          i <-  liftIO $ mapM (mapM (\inp -> catchPluginException inf (tableUnique (lookTable inf a)) idp ( getPKM (tableMeta $ lookTable inf a)inp) $ fmap fst $ runDynamic $ transaction inf $
                              case elemp of
                                Right action  -> do
                                  getP <-  getFrom  table (allFields inf table)  inp
                                  ovm  <- fmap (liftTable' inf a) <$> liftIO (action (mapKey' keyValue (maybe inp (apply inp) getP)))
                                  maybe (return ()) (\ov-> do
                                         fullEdit (tableMeta $ lookTable inf a)inp ov
                                         return ()) ovm
                                Left action -> do
                                  getP <- getFrom table (allFields inf table)  inp
                                  ovm  <- fmap (liftPatch inf a) <$> liftIO (action (mapKey' keyValue (maybe inp (apply inp) getP)))
                                  maybe (return ()) (\ov-> do
                                      fullEdit (tableMeta $ lookTable inf a) inp (apply inp ov)
                                      return ()) ovm
                              )
                            ) . L.transpose .  chuncksOf 20 $ evb
                          return $ concat i
                          ) [0..(lengthPage (fst sizeL) 400-1)]
                      end <- liftIO getCurrentTime
                      liftIO$ putStrLn $ "END " <>T.unpack pname <> " - " <> show end
                      let
                          time  = TB1 . STime . STimestamp
                          table2 = kvlist
                              [ attrT ("plugin",pid)
                              , attrT ("schema",TB1 (SNumeric schema))
                              , attrT ("time",srange (time current) (time end))
                              ]

                      transactionNoLog metas  $ do
                          fktable2 <- loadFKS ( lookTable metas "polling") (liftTable' metas "polling"  table2)
                          fullEdit ( lookMeta metas "polling") curr fktable2
                      return ()

          pid <- forkIO (void $ do
              putStrLn ("Start Poller: " <> T.unpack pname )
              -- iter polling
              (tm,_) <- runDynamic $ timer intervalms
              print (intervalms,diffUTCTime current startP,intervalms - round (10^3 * realToFrac ( diffUTCTime current startP)))
              forkIO (void $  threadDelay (max 0 (10^3*(intervalms - round (10^3 * realToFrac ( diffUTCTime current startP))))) >> putStrLn ("Timer Start" <> T.unpack pname) >> start tm>>  runDynamic (iter (indexRow polling)))
              let
                  evIter = indexRow <$> unionWith const (rumors $ collectionTid dbpol ) (facts ( collectionTid dbpol )<@ tick tm)

              (bhIter ,_) <- runDynamic $ stepper (indexRow  polling) evIter
              let  evDiffIter = diffEvent bhIter evIter
              runDynamic $onEventDyn  evDiffIter iter )
          return ()
  mapM poll  enabled

