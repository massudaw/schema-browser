{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module TP.Map where

import Step.Host
import qualified NonEmpty as Non
import Data.String
import Utils
import Database.PostgreSQL.Simple
import Control.Monad.Writer as Writer
import Postgresql.Parser
import Control.Arrow (first)
import TP.View
import GHC.Stack
import Control.Monad.Writer
import Control.Concurrent
import Control.Lens ((^.),_1,_2,_5)
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

removeLayers el tname = runFunction $ ffi "removeLayer(%1,%2)" el tname

createLayers el tname evs= runFunction $ ffi "createLayer (%1,%3,%2)" el evs tname
calendarCreate el Nothing evs= runFunction $ ffi "createMap (%1,null,null,null,%2)" el evs
calendarCreate el (Just (p,ne,sw)) evs= runFunction $ ffi "createMap (%1,%2,%3,%4,%5)" el (show p) (show ne) (show sw) evs


idx inf c v@(m,k) = indexField ( liftAccess inf (_kvname m) (keyRef c))  v

mapWidgetMeta  inf = do
    let
      schemaPred2 = [(keyRef ["schema"],Left (int (schemaId inf),Equals))]
    (_,(_,evMap )) <-ui $  transactionNoLog  (meta inf) $ selectFromTable "geo" Nothing Nothing [] schemaPred2
    (_,(_,eventMap )) <-ui $  transactionNoLog  (meta inf) $ selectFromTable "event" Nothing Nothing [] schemaPred2
    cliZone <- jsTimeZone
    return $ (\e ->
          let
              Just (TB1 (SText tname)) = unSOptional' $ _tbattr $ lookAttr' (meta inf) "table_name" $ unTB1 $ _fkttable $ lookAttrs' (meta inf) ["schema","table"] e
              table = lookTable inf tname
              evfields = join $ fmap (unArray . _tbattr ) . idx (meta inf) ["event"]   <$> erow
                where
                  erow = G.lookup (idex (meta inf) "event" [("schema" ,int $ schemaId inf),("table",int (_tableUnique table))])  eventMap
              Just (ArrayTB1 efields ) = indexFieldRec (liftAccess (meta inf) "geo" (Nested (keyRef ["features"] ) $keyRef  ["geo" ])) e
              (IT _ (ArrayTB1 features))= lookAttr' (meta inf) "features" e
              (Attr _ color )= lookAttr' (meta inf) "color" e
              projf  :: TBData Key Showable -> (FTB Showable , FTB (TBData Key Showable) ) -> Maybe (HM.HashMap Text A.Value)
              projf  r (efield@(TB1 (SText field)),features)  = fmap (\i ->  HM.fromList [("label",A.toJSON (HM.fromList $ i <> [("id", txt $ writePK r efield   ),("title"::Text , txt $ (T.pack $  L.intercalate "," $ fmap renderShowable $ allKVRec' $  r))])) ,("style",A.toJSON features)]) $ join $ convField  <$> indexFieldRec (liftAccess inf tname $ indexer field) r
              proj r = projf r <$> zip (F.toList efields) (F.toList features)
              convField (ArrayTB1 v) = Just $ [("position",ArrayTB1 v)]
              convField (LeftTB1 v) = join $ convField  <$> v
              convField (TB1 v ) = Just [("position", TB1 v)]
              convField i  = errorWithStackTrace (show i)
          in ("#" <> renderShowable color ,table,efields,evfields,proj)) <$>  ( G.toList evMap)

legendStyle dashes lookDesc table b
            =  do
              let item = M.lookup table  (M.fromList  $ fmap (\i@((a,b,c,_,_))-> (b,i)) dashes)
              maybe UI.div (\(k@((c,_,_,_,_))) ->
                UI.div # set items [UI.div
                  # set items [element b # set UI.class_ "col-xs-1", UI.div # sink text  (T.unpack . ($table) <$> facts lookDesc) #  set UI.class_ "fixed-label col-xs-11" # set UI.style [("background-color",c)] ]
                  # set UI.style [("background-color",c)]]) item

mapWidget body (incrementT,resolutionT) (sidebar,cposE,h,positionT) sel inf = do
    importUI
      [js "leaflet.js"
      ,js "leaflet-svg-markers.min.js"
      ,css "leaflet.css"]

    let
      calendarT = (\b c -> (b,c)) <$> facts incrementT <#> resolutionT

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
              nest (i:[]) = (IProd Nothing [T.pack i])
              nest (i:xs) = Nested (IProd Nothing [T.pack i]) (Many [nest xs])
      filteringPred  (k,v) row = maybe True (L.isInfixOf (toLower <$> v)  . fmap toLower . renderShowable )   $ (flip indexFieldRec row  k)
      filtering tb res = (\t -> filter (\row -> all (\i -> filteringPred i row) (catMaybes  t  )) )<$> (fmap (parseMany tb ) (triding filterInpT )) <*> fmap G.toList res
    calendar <-UI.div # set UI.class_ "col-xs-10"

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

    element body # set children [filterInp,routeD,calendar]
    let
      calFun selected = do
        innerCalendar <-UI.div # set UI.id_ "map" # set UI.style [("heigth","450px")]
        let
          evc = eventClick innerCalendar

        onEvent (filterJust $ liftA3 (,,) <$> start <*> fmap (lookTableM inf. T.pack) brouteT <*> end <@ routeE) (\(s,t,e) -> do
              l :: [Only Int]<- liftIO$ query (rootconn inf) (fromString $ "select node from pgr_dijkstra('select gid as id ,source,target,cost from " <> T.unpack (schemaName inf <> "." <> tableName t) <> "'::text,  ? , ? ,true)")( fmap ( unTB1 . (\(SerialTB1 (Just i)) -> i) . L.head .F.toList. getPKM) [s,e])
              let path = zip lo (tail lo)
                  lo = fmap unOnly l
                  tb = t
                  Just proj = fmap (^._5) $ L.find ((==tb).(^._2) ) dashes
              traverse (\path -> do
                v <- ui$refTables' inf tb  Nothing (WherePredicate (OrColl $ (\(i,j) -> AndColl $fmap (PrimColl . first (liftAccess inf (tableName t))) [(   IProd Nothing ["source"],Left (int i,Equals)), (IProd Nothing ["target"],Left (int j,Equals))])  <$> path ))
                mapUIFinalizerT innerCalendar (\i -> createLayers innerCalendar (tableName tb)  (T.unpack $ TE.decodeUtf8 $  BSL.toStrict $ A.encode  $ catMaybes  $ concat $ fmap proj $   G.toList $ (snd i))) (v^._1)
                  ) (nonEmpty path))

        onEvent cposE (\(c,sw,ne) -> runFunction $ ffi "setPosition(%1,%2,%3,%4)" innerCalendar c sw ne)
        pb <- currentValue (facts positionT)
        editor <- UI.div
        element calendar # set children [innerCalendar,editor]
        calendarCreate  innerCalendar pb ("[]"::String)
        onEvent (moveend innerCalendar) (liftIO . h)

        fin <- mapM (\(_,tb,fields,efields,proj) -> do
          let pcal =  liftA2 (,) positionT  calendarT
              tname = tableName tb
          mapUIFinalizerT innerCalendar (\(positionB,calT)-> do
            let pred = predicate inf tb (fmap  fieldKey <$>efields ) (fmap fieldKey <$> Just   fields ) (positionB,Just calT)
                fieldKey (TB1 (SText v))=  v
            reftb <- ui $ refTables' inf (lookTable inf tname) (Just 0) (WherePredicate pred)
            let v = fmap snd $ reftb ^. _1
            let evsel = (\j ((tev,pk,_),s) -> fmap (s,) $ join $ if tev == tb then Just ( G.lookup pk j) else Nothing  ) <$> facts v <@> fmap (first (readPK inf . T.pack) ) evc
            onEvent evsel (liftIO . hselg)


            -- shift <- ui$ stepper False holdShift

            tdib <- ui $ stepper Nothing (fmap snd <$> evsel)
            let tdi = tidings tdib (fmap snd <$> evsel)
            (el,_,_) <- crudUITable inf ((\i -> if isJust i then "+" else "-") <$> tdi) reftb [] [] (allRec' (tableMap inf) $ lookTable inf tname)  tdi

            mapUIFinalizerT innerCalendar (\i ->
              createLayers innerCalendar tname (T.unpack $ TE.decodeUtf8 $  BSL.toStrict $ A.encode  $ catMaybes  $ concat $ fmap proj $   i)) (filtering tb v)
            -- stat <- UI.div  # sinkDiff text (show . (\i -> (positionB,length i, i) ).  (fmap snd . G.getEntries .filterfixed tb (WherePredicate pred )) <$> v)
            edit <- UI.div # set children el # sink UI.style  (noneShow . isJust <$> tdib)
            UI.div # set children [edit]
            ) pcal
          ) selected
        let els = foldr (liftA2 (:)) (pure []) fin
        element editor  # sink children (facts els)
        return ()
    let calInp = (\i -> filter (flip L.elem (concat (F.toList i)) .  (^. _2)) dashes  )<$> sel
    _ <- mapUIFinalizerT calendar calFun calInp
    return (legendStyle dashes ,dashes)





readMapPK v = case unsafeFromJSON v of
      [i,j]  -> Just (i,readBool j)
      i -> Nothing
  where
    readBool "false" = False
    readBool "true" = True

eventClick:: Element -> Event (String,Bool)
eventClick el = filterJust $ readMapPK <$> domEvent "mapEventClick" el


moveend :: Element -> Event ([Double],[Double],[Double])
moveend el = filterJust $ readPosition <$>  domEvent "moveend" el

