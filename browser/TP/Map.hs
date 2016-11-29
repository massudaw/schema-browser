{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module TP.Map where

import Step.Host
import qualified NonEmpty as Non
import Control.Monad.Writer as Writer
import TP.View
import GHC.Stack
import Control.Monad.Writer
import Control.Concurrent
import Control.Lens ((^.),_1,_2)
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

createLayers el tname Nothing evs= runFunction $ ffi "createLayer (%1,%3,null,null,null,%2)" el evs tname
createLayers el tname (Just (p,ne,sw)) evs= runFunction $ ffi "createLayer (%1,%6,%2,%3,%4,%5)" el (show p) (show ne) (show sw) evs tname
calendarCreate el Nothing evs= runFunction $ ffi "createMap (%1,null,null,null,%2)" el evs
calendarCreate el (Just (p,ne,sw)) evs= runFunction $ ffi "createMap (%1,%2,%3,%4,%5)" el (show p) (show ne) (show sw) evs


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
              evfields = join $fmap (\(Attr _ (ArrayTB1 n))-> n) . indexField  (liftAccess (meta inf) "event" $ keyRef ["event"])   <$> erow
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
        onEvent cposE (\(c,sw,ne) -> runFunction $ ffi "setPosition(%1,%2,%3,%4)" innerCalendar c sw ne)
        pb <- currentValue (facts positionT)
        editor <- UI.div
        element calendar # set children [innerCalendar,editor]
        calendarCreate  innerCalendar pb ("[]"::String)
        onEvent (moveend innerCalendar) (liftIO . h .traceShowId )
        fin <- mapM (\(_,tb,fields,efields,proj) -> do
          let filterInp =  liftA2 (,) positionT  calendarT
              tname = tableName tb
          mapUIFinalizerT innerCalendar (\(positionB,calT)-> do
            let pred = predicate inf tb (fmap  fieldKey <$>efields ) (fmap fieldKey <$> Just   fields ) (positionB,Just calT)
                fieldKey (TB1 (SText v))=  v
            reftb <- ui $ refTables' inf (lookTable inf tname) (Just 0) (WherePredicate pred)
            let v = fmap snd $ reftb ^. _1
            let evsel = (\j (tev,pk,_) -> if tev == tb then Just ( G.lookup pk j) else Nothing  ) <$> facts (v) <@> fmap (readPK inf . T.pack ) evc
            tdib <- ui $ stepper Nothing (join <$> evsel)
            let tdi = tidings tdib (join <$> evsel)
            (el,_,_) <- crudUITable inf ((\i -> if isJust i then "+" else "-") <$> tdi) reftb [] [] (allRec' (tableMap inf) $ lookTable inf tname)  tdi
            mapUIFinalizerT innerCalendar (\i -> do
              createLayers innerCalendar tname positionB (T.unpack $ TE.decodeUtf8 $  BSL.toStrict $ A.encode  $ catMaybes  $ concat $ fmap proj $   G.toList $ i)) v
            stat <- UI.div  # sinkDiff text (show . (\i -> (positionB,length i, i) ).  (fmap snd . G.getEntries .filterfixed tb (WherePredicate pred )) <$> v)
            edit <- UI.div # set children el # sink UI.style  (noneShow . isJust <$> tdib)
            UI.div # set children [stat,edit]
            ) filterInp
          ) selected
        let els = foldr (liftA2 (:)) (pure []) fin
        element editor  # sink children (facts els)
        return ()
    let calInp = (\i -> filter (flip L.elem (concat (F.toList i)) .  (^. _2)) dashes  )<$> sel
    _ <- mapUIFinalizerT calendar calFun calInp
    return (legendStyle,dashes)





readMapPK v = case unsafeFromJSON v of
        [i]  -> Just i

eventClick:: Element -> Event String
eventClick el = filterJust $ readMapPK <$> domEvent "mapEventClick" el


moveend :: Element -> Event ([Double],[Double],[Double])
moveend el = filterJust $ readPosition <$>  domEvent "moveend" el

