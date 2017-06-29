{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module TP.Map (mapWidget,mapWidgetMeta) where

import Step.Host
import qualified NonEmpty as Non
import Data.String
import TP.MapSelector
import Utils
import Database.PostgreSQL.Simple
import Control.Monad.Writer as Writer
import Postgresql.Parser
import Control.Arrow (first)
import TP.View
import GHC.Stack
import Control.Monad.Writer
import Control.Concurrent
import Control.Lens ((^.),_1,_2,_3,_5)
import Safe
import Control.Concurrent.Async
import Data.Interval as Interval
import Data.Time.Calendar.WeekDate
import qualified Data.Vector as V
import Data.Char
import qualified Data.Text.Encoding as TE
import Query
import Data.Time
import qualified Data.Aeson as A
import Text
import qualified Types.Index as G
import Debug.Trace
import Types
import SchemaQuery
import TP.Widgets
import Prelude hiding (head)
import TP.QueryWidgets
import Control.Monad.Reader
import Schema
import Data.Maybe
import Reactive.Threepenny hiding(apply)
import qualified Data.List as L
import qualified Data.ByteString.Lazy.Char8 as BSL

import RuntimeTypes
import qualified Graphics.UI.Threepenny as UI
import Graphics.UI.Threepenny.Core hiding (get,delete,apply)
import Data.Monoid hiding (Product(..))

import qualified Data.Foldable as F
import qualified Data.Text as T
import Data.Text (Text)

import qualified Data.Map as M
import qualified Data.HashMap.Strict as HM


instance UI.ToJS (G.Node (TBIndex Showable)) where
  render  = render . A.toJSON

instance A.ToJSON (G.Node (TBIndex Showable)) where
  toJSON (G.TBIndexNode i) = A.toJSON i

instance A.ToJSON (Interval Showable) where
  toJSON i = A.toJSON [G.unFin $ fst $ lowerBound' i , G.unFin $ fst $ upperBound' i]

instance A.ToJSON (G.Node (FTB Showable)) where
  toJSON (G.FTBNode i) = A.toJSON i

mapWidget body (incrementT,resolutionT) (sidebar,prepositionT) sel inf = do
    let
      calendarT = (,) <$> facts incrementT <#> resolutionT
    dashes <- mapWidgetMeta inf
    mapOpen <- liftIO getCurrentTime

    filterInp <- UI.input
    filterInpT <- element filterInp # sourceT "change" UI.valueFFI ""
    let
      parseMany t l =  parseInp t <$> unIntercalate ('&'==) l
      parseInp t i
        | not (L.null j ) && T.pack tnew == tableName t  =    (,tail r ) <$> liftAccessM inf (tableName t) ( nest (unIntercalate ('.'==) (tail j)))
        | not $ L.null r =  (,tail r ) <$> liftAccessM inf (tableName t) ( nest (unIntercalate ('.'==) l))
        | otherwise = Nothing
        where (l,r) = break(=='=') i
              (tnew,j ) = break (=='|') l
              nest (i:[]) = keyRef (T.pack i)
              nest (i:xs) = Nested [keyRef (T.pack i)] (Many [nest xs])
      filteringPred  (k,v) row = maybe True (L.isInfixOf (toLower <$> v)  . fmap toLower . renderShowable )   $ (flip indexFieldRec row  k)
      filtering tb res = (\t -> filter (\row -> all (\i -> filteringPred i row) (catMaybes  t  )) )<$> (fmap (parseMany tb ) (triding filterInpT )) <*> fmap G.toList res
    calendar <-UI.div

    (eselg,hselg) <- ui$newEvent
    start <- ui$stepper Nothing (fmap snd <$> (filterE (maybe False (not .fst)) eselg))
    startD <- UI.div #  sink text (maybe "" (show . G.getIndex) <$> start)
    end <- ui$stepper Nothing (fmap snd <$> filterE (maybe False fst ) eselg)
    endD <- UI.div #  sink text (maybe "" (show . G.getIndex) <$> end)
    route <- UI.button # set text "route"
    let inirouteT = "ways"
    routeT <- UI.input # set value inirouteT
    erouteT <- UI.valueChange routeT
    brouteT <- ui$stepper inirouteT erouteT
    routeE <- UI.click route
    routeD <- UI.div
    element routeD # set children [routeT,startD,endD,route]

    (positionLocal,h) <- ui $ newEvent
    let positionE = (unionWith const (rumors prepositionT) positionLocal)
    pb <- currentValue (facts prepositionT)
    positionB <- ui $stepper  pb positionE
    let positionT = tidings positionB positionE


    element body # set children [filterInp,routeD,calendar]
    let
      calFun selected = do
        innerCalendar <-UI.div # set UI.id_ "map" # set UI.style [("heigth","450px")]
        let
          evc = eventClick innerCalendar

        onEvent (filterJust $ liftA3 (,,) <$> start <*> fmap (lookTableM inf. T.pack) brouteT <*> end <@ routeE) (\(s,t,e) -> do
              l :: [Only Int]<- liftIO$ query (rootconn inf) (fromString $ "select node from pgr_dijkstra('select gid as id ,source,target,cost from " <> T.unpack (schemaName inf <> "." <> tableName t) <> "'::text,  ? , ? ,true)")( fmap ( unTB1 . (\(LeftTB1 (Just i)) -> i) . L.head .F.toList. getPKM) [s,e])
              let path = zip lo (tail lo)
                  lo = fmap unOnly l
                  tb = t
                  Just proj = fmap (^._5) $ L.find ((==tb).(^._2) ) dashes
              traverse (\path -> do
                v <- ui $ refTables' inf tb  Nothing (WherePredicate (OrColl $ (\(i,j) -> AndColl $fmap (PrimColl . first (liftAccess inf (tableName t))) [(   keyRef "source",Left (int i,Equals)), (keyRef "target",Left (int j,Equals))])  <$> path ))
                traverseUI (\i -> do
                  createLayers innerCalendar (tableName tb)  (T.unpack $ TE.decodeUtf8 $  BSL.toStrict $ A.encode  $ catMaybes  $ concat $ fmap proj $   G.toList $ i)) (v^._3)
                  ) (nonEmpty path))

        pb <- currentValue (facts positionT)
        editor <- UI.div
        element calendar # set children [innerCalendar,editor]
        calendarCreate  innerCalendar pb ("[]"::String)
        onEvent (moveend innerCalendar) (liftIO . h. Just)
        onEvent (filterJust $ rumors prepositionT) (\(sw,ne) -> runFunction $ ffi "setPosition(%1,%2,%3)" innerCalendar  sw ne)

        fin <- mapM (\(_,tb,fields,efields,proj) -> do
          let pcal =  liftA2 (,) positionT  calendarT
              tname = tableName tb
          traverseUI (\(positionB,calT)-> do
            let pred = WherePredicate $ predicate inf tb (fmap  fieldKey <$>efields ) (fmap fieldKey <$> Just   fields ) (positionB,Just calT)
                fieldKey (TB1 (SText v))=  v
            reftb <- ui $ refTables' inf (lookTable inf tname) (Just 0) pred
            let v = reftb ^. _3
            let evsel = (\j ((tev,pk,_),s) -> fmap (s,) $ join $ if tev == tb then Just ( G.lookup pk j) else Nothing  ) <$> facts v <@> fmap (first (readPK inf . T.pack) ) evc
            onEvent evsel (liftIO . hselg)

            tdib <- ui $ stepper Nothing (fmap snd <$> evsel)
            let tdi = tidings tdib (fmap snd <$> evsel)
            (el,_) <- crudUITable inf  reftb [] [] (allRec' (tableMap inf) $ lookTable inf tname)  tdi

            traverseUI (\i ->
              createLayers innerCalendar tname (T.unpack $ TE.decodeUtf8 $  BSL.toStrict $ A.encode  $ catMaybes  $ concat $ fmap proj $   i)) (filtering tb v)

            stat <- UI.div  # sinkDiff text (show . M.lookup pred <$>   (reftb ^. _1))
            edit <- UI.div # set children [el] # sink UI.style  (noneShow . isJust <$> tdib)
            UI.div # set children [stat,edit]
            ) pcal
          ) selected
        let els = foldr (liftA2 (:)) (pure []) fin
        element editor  # sink children (facts els)
        return ()
    let calInp = (\i -> filter (flip L.elem (concat (F.toList i)) .  (^. _2)) dashes  )<$> sel
    onFFI "$(document).ready((%1))" (evalUI body $   traverseUI calFun calInp)
    return (legendStyle dashes ,dashes)




