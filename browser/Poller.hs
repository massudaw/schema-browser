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
import Reactive.Threepenny
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
  transactionNoLog inf  $ do
      (db ,(_,t)) <- selectFrom "plugins"  Nothing Nothing [] $ mempty
      let els = L.filter (not . (`L.elem` G.toList t)) $ (\o->  liftTable' inf "plugins" $ tblist (_tb  <$> [Attr "name" (TB1 $ SText $ _name o) ])) <$> plugs
      elsFKS <- mapM loadFKS  els
      liftIO $ transaction inf $ mapM fullDiffInsert  elsFKS



index tb item = snd $ justError ("no item" <> show item) $ indexTable (IProd True [item]) (tableNonRef' tb)

checkTime curr = do
    let
        IntervalTB1 time_inter = index curr "time"
        TB1 (STimestamp startLocal) = justError "cant be null "$ unFinite $ lowerBound time_inter
        TB1 (STimestamp endLocal) = justError "cant be null" $unFinite $ upperBound time_inter
        start = localTimeToUTC utc startLocal
        end = localTimeToUTC utc endLocal
    current <- getCurrentTime
    return $ (start,end,curr,current)

poller schm authmap db plugs is_test = do
  metas <- metaInf schm
  let conn = rootconn metas
  (dbpol,(_,polling))<- transactionNoLog metas $ selectFrom "polling" Nothing Nothing [] $ mempty
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
          indexRow polling = justError (show $ tbpred tb) $ G.lookup (tbpred tb) polling
          tbpred = G.Idex . getPKM

      (inf ,_)<- runDynamic $keyTables  schm conn  (schema, T.pack $ user db) authmap plugs
      (startP,_,_,current) <- checkTime (indexRow polling )
      flip traverse plug $ \p -> do
          let f = pluginStatic p
              elemp = pluginAction p
              pname = _name p
              a = _bounds p
          let iter polling = do
                  (start,end,curr,current) <- checkTime polling
                  putStrLn $ "LAST RUN " <> show (schema,pname,current,start,end)
                  let intervalsec = intervalms `div` 10^3
                  when (is_test || diffUTCTime current start  >  fromIntegral intervalsec) $ do
                      putStrLn $ "START " <> T.unpack pname  <> " - " <> show current
                      let fetchSize = 200
                          pred =  WherePredicate $ lookAccess inf a <$> AndColl (catMaybes [ genPredicate True (fst f) , genPredicate False (snd f)])
                      (_ ,(l,_ )) <- transactionNoLog inf $ selectFrom a  (Just 0) (Just fetchSize) []  pred
                      threadDelay 10000
                      let sizeL = justLook pred  l
                          lengthPage s pageSize  =  traceShow (res,pageSize,s) res
                            where
                              res = (s  `div` pageSize) +  if s `mod` pageSize /= 0 then 1 else 0
                      i <- concat <$> mapM (\ix -> do
                          (_,(_,listResAll)) <- transactionNoLog inf $ selectFrom a  (Just ix) (Just fetchSize) [] pred
                          let listRes = L.take fetchSize . G.toList $  listResAll

                          let evb = filter (\i -> tdInput i  && tdOutput1 i ) listRes
                              tdInput i =  isJust  $ checkTable  (liftAccess inf a $ fst f) i
                              tdOutput1 i =  not $ isJust  $ checkTable  (liftAccess inf a $ snd f) i

                          i <-  mapConcurrently (mapM (\inp -> catchPluginException inf a pname (M.toList $ getPKM inp) $ transactionLog inf $ do
                              ovm  <- fmap (liftTable' inf a) <$> liftIO (elemp (Just $ mapKey' keyValue inp))
                              maybe (return ()) (\ov-> do
                                   p <- fullDiffEdit inp ov
                                   return ()) ovm
                              )
                            ) . L.transpose .  chuncksOf 20 $ evb
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
                                        nonEmpty  . concat . catMaybes $
                                            fmap (fmap (TB1 . tblist  )) .  either (\r ->Just $ pure $ [attrT ("except", LeftTB1 $ Just $ TB1 (SNumeric r) ),attrT ("modify",LeftTB1 $Nothing)]) (Just . fmap (\r -> [attrT ("modify", LeftTB1 $ Just $ TB1 (SNumeric (justError "no id" $ tableId $  r))   ),attrT ("except",LeftTB1 $Nothing)])) <$> i))
                              , attrT ("duration",srange (time current) (time end))]
                          time  = TB1 . STimestamp . utcToLocalTime utc
                          table2 = tblist
                              [ attrT ("poll_name",TB1 (SText pname))
                              , attrT ("schema_name",TB1 (SText schema))
                              , attrT ("time",srange (time current) (time end))
                              ]

                      (p2,p) <- transactionNoLog metas  $ do
                          fktable2 <- loadFKS  (liftTable' metas "polling"  table2)
                          p2 <- fullDiffEdit curr fktable2
                          fktable <- loadFKS  (liftTable' metas  "polling_log"  table)
                          p <-fullDiffInsert  (liftTable' metas  "polling_log"  table)
                          return (fktable2,p)
                      return ()

          pid <- forkIO (void $ do
              putStrLn ("Start Poller: " <> T.unpack pname )
              -- iter polling
              tm <- timer intervalms
              print (intervalms,diffUTCTime current startP,(intervalms - (round $ 10^3 * realToFrac ( diffUTCTime current startP))))
              forkIO (void $  threadDelay (max 0 (10^3*(intervalms - (round $ 10^3 * realToFrac ( diffUTCTime current startP))))) >> putStrLn ("Timer Start" <> T.unpack pname) >> start tm>> iter (indexRow polling))
              let
                  evIter = indexRow <$> (unionWith const (rumors $ collectionTid dbpol ) (facts ( collectionTid dbpol )<@ tick tm))

              bhIter <- stepper (indexRow  polling) evIter
              let  evDiffIter = diffEvent bhIter evIter

              runDynamic $onEventIO  evDiffIter (liftIO . iter) )
          return ()
  mapM poll  enabled

