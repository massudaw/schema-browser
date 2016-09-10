{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module TP.Map where

import Step.Host
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

createLayers el tname Nothing evs= runFunction $ ffi "createLayer (%1,%3,null,null,null,%2)" el evs tname
createLayers el tname (Just (p,ne,sw)) evs= runFunction $ ffi "createLayer (%1,%6,%2,%3,%4,%5)" el (show p) (show ne) (show sw) evs tname
calendarCreate el Nothing evs= runFunction $ ffi "createMap (%1,null,null,null,%2)" el evs
calendarCreate el (Just (p,ne,sw)) evs= runFunction $ ffi "createMap (%1,%2,%3,%4,%5)" el (show p) (show ne) (show sw) evs


mapWidget body (agendaT,incrementT,resolutionT) (sidebar,cposE,h,positionT) sel inf = do
    let
      calendarT = (\(a,b) c -> (a,b,c)) <$> ((,)<$> facts agendaT <*> facts incrementT )<#> resolutionT
      schemaPred = WherePredicate $ AndColl [PrimColl (IProd True ["schema_name"],"=",TB1 $ SText (schemaName inf))]

    (_,(_,tmap)) <- liftIO $ transactionNoLog (meta inf) $ selectFrom "table_name_translation" Nothing Nothing [] schemaPred
    (_,(_,evMap )) <- liftIO $ transactionNoLog  (meta inf) $ selectFrom "geo" Nothing Nothing [] schemaPred
    (_,(_,eventMap )) <- liftIO$ transactionNoLog  (meta inf) $ selectFrom "event" Nothing Nothing [] schemaPred
    cliZone <- lift $ jsTimeZone
    let dashes = (\e ->
          let
              (Attr _ (TB1 (SText tname))) = lookAttr' (meta inf) "table_name" $ unTB1 $ _fkttable $ lookAttrs' (meta inf) ["schema_name","table_name"] e
              lookDesc = (\i  -> maybe (T.unpack $ tname)  ((\(Attr _ v) -> renderShowable v). lookAttr' (meta inf)  "translation") $ G.lookup (idex (meta inf) "table_name_translation" [("schema_name" ,txt $ schemaName inf),("table_name",txt tname )]) i ) $ tmap
              evfields = (\(Attr _ (ArrayTB1 n))-> n) . lookAttr' (meta inf) "event" <$> erow
                where
                  erow = G.lookup (idex (meta inf) "table_name_translation" [("schema_name" ,txt $ schemaName inf),("table_name",txt tname )])  eventMap
              (Attr _ (ArrayTB1 efields ))= lookAttr' (meta inf) "geo" e
              (Attr _ color )= lookAttr' (meta inf) "color" e
              (Attr _ size )= lookAttr' (meta inf) "size" e
              projf  r efield@(TB1 (SText field))  = fmap (\i ->  HM.fromList $ i <> [("id", TB1 $ SText $ writePK r efield   ),("title"::Text , TB1 $ SText $ (T.pack $  L.intercalate "," $ fmap renderShowable $ allKVRec' $  r)),("size", size),("color",  color)]) $ join $ convField  <$> indexFieldRec (indexer field) r
              proj r = projf r <$> F.toList efields
              convField (ArrayTB1 v) = Just $ [("position",ArrayTB1 v)]
              convField (LeftTB1 v) = join $ convField  <$> v
              convField (TB1 v ) = Just $ to $ v
                where to p@(SPosition (Position (y,x,z) ))  =  [("position",TB1 p )]
              convField i  = errorWithStackTrace (show i)
          in (lookDesc,(color,tname,efields,evfields,proj))) <$>  ( G.toList evMap)


    let
      legendStyle table (b,_)
            =  do
              let item = M.lookup (tableName (fromJust $ M.lookup table (pkMap inf))) (M.fromList  $ fmap (\i@(t,(a,b,c,_,_))-> (b,i)) dashes)
              maybe UI.div (\(k@(t,(c,_,_,_,_))) ->
                UI.div # set items [UI.div
                  # set items [element b # set UI.class_ "col-xs-1", UI.div # set text  t #  set UI.class_ "fixed-label col-xs-11" # set UI.style [("background-color",renderShowable c)] ]
                  # set UI.style [("background-color",renderShowable c)]]) item



    calendar <-lift$ UI.div # set UI.class_ "col-xs-10"
    lift$ element body # set children [calendar]

    let
      calFun selected = do
        innerCalendar <-lift $ UI.div # set UI.id_ "map" # set UI.style [("heigth","450px")]
        let
          evc = eventClick innerCalendar
        liftIO$ onEventIO evc putStrLn
        onEventFT (cposE) (\(c,sw,ne) -> runFunction $ ffi "setPosition(%1,%2,%3,%4)" innerCalendar c sw ne)
        pb <- lift $ currentValue (facts positionT)
        editor <- lift UI.div
        lift $ element calendar # set children [innerCalendar,editor]
        lift $ calendarCreate  innerCalendar pb ("[]"::String)
        onEventFT (moveend innerCalendar) (liftIO . h )
        fin <- mapM (\((_,(_,tname,fields,efields,proj))) -> do
          let filterInp =  liftA2 (,) positionT  calendarT
              t = tname
          mapUIFinalizerT innerCalendar (\(positionB,calT)-> do
            let pred = predicate (fmap (\(TB1 (SText v))->  lookKey inf tname v) <$>efields )(Just $  fields ) (positionB,Just calT)
               --  pred = WherePredicate $ timePred (fieldKey <$> fields ) (agenda,incrementT,resolution)
               -- fieldKey (TB1 (SText v))=  lookKey inf t v
            (v,_) <-  liftIO $  transactionNoLog  inf $ selectFromA tname Nothing Nothing [] pred
            reftb <- refTables inf (lookTable inf t)
            let evsel = (\j (tev,pk,_) -> if tableName tev == t then Just ( G.lookup ( G.Idex  $ notOptionalPK $ M.fromList $pk) j) else Nothing  ) <$> facts (collectionTid v) <@> fmap (readPK inf . T.pack ) evc
            tdib <- stepper Nothing (join <$> evsel)
            let tdi = tidings tdib (join <$> evsel)
            (el,_,_) <- lift $ crudUITable inf (pure "+")  reftb [] [] (allRec' (tableMap inf) $ lookTable inf t)  tdi
            mapUIFinalizerT innerCalendar (\i -> lift $ createLayers innerCalendar tname positionB (T.unpack $ TE.decodeUtf8 $  BSL.toStrict $ A.encode  $ catMaybes  $ concat $ fmap proj $   G.toList $ i)) (collectionTid v)
            lift $ UI.div # set children el # sink UI.style  (noneShow . isJust <$> tdib)
            ) filterInp
          ) selected
        let els = foldr (liftA2 (:)) (pure []) fin
        lift$ element editor  # sink children (facts els)
        return ()
    let calInp = (\i j -> filter (flip L.elem (tableName <$> concat (F.toList i)) .  (^. _2._2)) j )<$> sel <*> pure dashes
    _ <- mapUIFinalizerT calendar calFun calInp
    return (legendStyle,dashes)



txt = TB1. SText


readMapPK v = case unsafeFromJSON v of

        [i]  -> Just i

eventClick:: Element -> Event String
eventClick el = filterJust $ readMapPK <$> domEvent "mapEventClick" el


moveend :: Element -> Event ([Double],[Double],[Double])
moveend el = filterJust $ readPosition <$>  domEvent "moveend" el

