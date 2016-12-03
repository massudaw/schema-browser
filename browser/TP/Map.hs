{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module TP.Map where

import Step.Host
import qualified NonEmpty as Non
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
mapWidget body (incrementT,resolutionT) (sidebar,cposE,h,positionT) sel inf = do
    importUI
      [js "leaflet.js"
      ,css "leaflet.css"]

    let
      calendarT = (\b c -> (b,c)) <$> facts incrementT <#> resolutionT
      schemaPred2 = [(keyRef ["schema"],Left (int (schemaId inf),Equals))]

    (_,(_,evMap )) <-ui $  transactionNoLog  (meta inf) $ selectFromTable "geo" Nothing Nothing [] schemaPred2
    (_,(_,eventMap )) <-ui $  transactionNoLog  (meta inf) $ selectFromTable "event" Nothing Nothing [] schemaPred2
    cliZone <- jsTimeZone
    let dashes = (\e ->
          let
              Just (TB1 (SText tname)) = unSOptional' $ _tbattr $ lookAttr' (meta inf) "table_name" $ unTB1 $ _fkttable $ lookAttrs' (meta inf) ["schema","table"] e
              table = lookTable inf tname
              evfields = join $ fmap (unArray . _tbattr ) . idx (meta inf) ["event"]   <$> erow
                where
                  erow = G.lookup (idex (meta inf) "event" [("schema" ,int $ schemaId inf),("table",int (_tableUnique table))])  eventMap
              (Attr _ (ArrayTB1 efields ))= lookAttr' (meta inf) "geo" e
              (Attr _ color )= lookAttr' (meta inf) "color" e
              (Attr _ size )= lookAttr' (meta inf) "size" e
              projf  r efield@(TB1 (SText field))  = fmap (\i ->  HM.fromList $ i <> [("id", txt $ writePK r efield   ),("title"::Text , txt $ (T.pack $  L.intercalate "," $ fmap renderShowable $ allKVRec' $  r)),("size", size),("color",   txt $ T.pack $ "#" <> renderShowable color )]) $ join $ convField  <$> indexFieldRec (liftAccess inf tname $ indexer field) r
              proj r = projf r <$> F.toList efields
              convField (ArrayTB1 v) = Just $ [("position",ArrayTB1 v)]
              convField (LeftTB1 v) = join $ convField  <$> v
              convField (TB1 v ) = Just $ to  v
                where to p@(SPosition _ )  =  [("position",TB1 p )]
                      to p@(SLineString (LineString v)) =[("position",ArrayTB1 $ Non.fromList $ fmap (TB1 .SPosition)$ F.toList v)]
                      to p =[("position",TB1 p)]
              convField i  = errorWithStackTrace (show i)
          in ("#" <> renderShowable color ,table,efields,evfields,proj)) <$>  ( G.toList evMap)


    let
      legendStyle lookDesc table b
            =  do
              let item = M.lookup table  (M.fromList  $ fmap (\i@((a,b,c,_,_))-> (b,i)) dashes)
              maybe UI.div (\(k@((c,_,_,_,_))) ->
                UI.div # set items [UI.div
                  # set items [element b # set UI.class_ "col-xs-1", UI.div # sink text  (T.unpack . ($table) <$> facts lookDesc) #  set UI.class_ "fixed-label col-xs-11" # set UI.style [("background-color",c)] ]
                  # set UI.style [("background-color",c)]]) item


    mapOpen <- liftIO getCurrentTime

    calendar <-UI.div # set UI.class_ "col-xs-10"
    element body # set children [calendar]

    let
      calFun selected = do
        innerCalendar <-UI.div # set UI.id_ "map" # set UI.style [("heigth","450px")]
        let
          evc = eventClick innerCalendar
        (eselg,hselg) <- ui$newEvent
        start <- ui$stepper Nothing (fmap snd <$> (filterE (maybe False (not .fst)) eselg))
        startD <- UI.div #  sink text (maybe "" (show . G.getIndex) <$> start)
        end <- ui$stepper Nothing (fmap snd <$> filterE (maybe False fst ) eselg)
        endD <- UI.div #  sink text (maybe "" (show . G.getIndex) <$> end)
        route <- UI.button # set text "route"
        routeE <- UI.click route
        output <- UI.div
        onEvent (filterJust $ liftA2 (,) <$> start <*> end <@ routeE) (\(s,e) -> do
              l :: [Only Int]<- liftIO$ query (rootconn inf) "select node from pgr_dijkstra('select gid as id ,source,target,cost from transito.ways'::text,  ? , ? ,true)"( fmap ( unTB1 . (\(SerialTB1 (Just i)) -> i) . L.head .F.toList. getPKM) [s,e])
              let path = zip lo (tail lo)
                  lo = fmap unOnly l
                  tb = lookTable inf "ways"
                  Just proj = fmap (^._5) $ L.find ((==tb).(^._2) ) dashes

              v <- ui$refTables' inf tb  Nothing (WherePredicate (OrColl $ (\(i,j) -> AndColl $fmap (PrimColl . first (liftAccess inf "ways")) [( IProd Nothing ["source"],Left (int i,Equals)), (IProd Nothing ["target"],Left (int j,Equals))])  <$> path ))
              mapUIFinalizerT innerCalendar (\i -> createLayers innerCalendar (tableName tb)  (T.unpack $ TE.decodeUtf8 $  BSL.toStrict $ A.encode  $ catMaybes  $ concat $ fmap proj $   G.toList $ (snd i))) (v^._1))
              -- element output # sink text (show <$> facts (v ^. _1 )))

        onEvent cposE (\(c,sw,ne) -> runFunction $ ffi "setPosition(%1,%2,%3,%4)" innerCalendar c sw ne)
        pb <- currentValue (facts positionT)
        routeD <- UI.div
        editor <- UI.div
        element calendar # set children [routeD,innerCalendar,editor]
        calendarCreate  innerCalendar pb ("[]"::String)
        onEvent (moveend innerCalendar) (liftIO . h)
        fin <- mapM (\(_,tb,fields,efields,proj) -> do
          let filterInp =  liftA2 (,) positionT  calendarT
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
              createLayers innerCalendar tname (T.unpack $ TE.decodeUtf8 $  BSL.toStrict $ A.encode  $ catMaybes  $ concat $ fmap proj $   G.toList $ i)) v
            -- stat <- UI.div  # sinkDiff text (show . (\i -> (positionB,length i, i) ).  (fmap snd . G.getEntries .filterfixed tb (WherePredicate pred )) <$> v)
            edit <- UI.div # set children el # sink UI.style  (noneShow . isJust <$> tdib)
            UI.div # set children [edit]
            ) filterInp
          ) selected
        element routeD # set children [startD,endD,route,output]
        let els = foldr (liftA2 (:)) (pure []) fin
        element editor  # sink children (facts els)
        return ()
    let calInp = (\i -> filter (flip L.elem (concat (F.toList i)) .  (^. _2)) dashes  )<$> sel
    _ <- mapUIFinalizerT calendar calFun calInp
    return (legendStyle,dashes)





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

