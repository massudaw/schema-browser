{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE Arrows #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module TP.AgendaSelector (Mode(..),eventWidgetMeta,calendarView,agendaDefS,testAgendaDef) where

import GHC.Stack
import Environment
import Data.Functor.Classes
import Step.Host
import TP.View
import qualified Data.Interval as Interval
import qualified Data.Sequence.NonEmpty as NonS
import qualified Data.HashMap.Strict as HM
import NonEmpty (NonEmpty)
import qualified NonEmpty as Non
import Control.Concurrent
import Utils
import Data.Functor.Identity
import Types.Patch
import Control.Arrow
import Control.Lens ((^.), view,_1, mapped,_2, _3,_4,_5)
import Data.Either
import Data.Interval (Interval(..))
import Data.Time.ISO8601
import Control.Monad.Writer
import Data.Time.Calendar.WeekDate
import Data.Char
import qualified Data.Text.Encoding as TE
import Control.Concurrent.Async
import Safe
import Query
import Data.Time hiding(readTime)
import qualified Data.Aeson as A
import Text
import qualified Types.Index as G
import Debug.Trace
import Types
import SchemaQuery
import Schema
import TP.Widgets
import Prelude hiding (head)
import Control.Monad.Reader
import Data.Maybe
import Reactive.Threepenny hiding (apply)
import qualified Data.List as L
import qualified Data.ByteString.Lazy.Char8 as BSL
import RuntimeTypes
import qualified Graphics.UI.Threepenny as UI
import Graphics.UI.Threepenny.Core hiding (get, delete, apply)
import Data.Monoid hiding (Product(..))
import qualified Data.Foldable as F
import qualified Data.Text as T
import Data.Text (Text)
import qualified Data.Map as M
import qualified Data.Set as S

calendarCreate m cal def = runFunctionDelayed cal $ ffi "createAgenda(%1,%2,%3)" cal def m

calendarAddSource cal t evs = do
  runFunctionDelayed cal $ ffi "addSource(%1,%2,%3)" cal (tableName t) (T.unpack . TE.decodeUtf8 .  BSL.toStrict . A.encode  $ evs)
  finalizerUI (calendarRemoveSource cal t)

calendarRemoveSource cal t = runFunctionDelayed cal $ ffi "removeSource(%1,%2)" cal (tableName t)

data Mode
  = Agenda
  | Basic
  | Timeline
  deriving(Eq,Show,Ord)


eventWidgetMeta inf =  do
    importUI =<< mapM js
       ["fullcalendar-3.5.0/lib/jquery-ui.min.js"
       ,"fullcalendar-3.5.0/lib/moment.min.js"
       ,"fullcalendar-3.5.0/fullcalendar.min.js"
       ,"fullcalendar-scheduler-1.7.0/scheduler.min.js"
       ,"fullcalendar-3.5.0/locale-all.js"]
    importUI =<< mapM css
       ["fullcalendar-3.5.0/fullcalendar.min.css"
       ,"fullcalendar-scheduler-1.7.0/scheduler.min.css"
       ]
    fmap F.toList $  join . fmap (currentValue .facts ) . ui $ runMetaArrow inf agendaDefS

agendaDefS inf 
  = projectS 
    (innerJoinS
      (tableDef inf `whereS` schemaPred)
      (fromS "event") [Rel "oid" Equals "table" ])
    (agendaDefProjection inf)
  where schemaPred = [(keyRef "schema",Left (int (schemaId inf),Equals) )]
          
testAgendaDef inf = fmap fst . runDynamic $  do
   v <- runMetaArrow inf agendaDefS
   vi <- currentValue (facts v)
   liftIO $ print (fmap (\(a,b,c,d) -> a ) vi)
   -- ! b <- runMetaArrow inf agendaDef
   -- liftIO $ print (view _1 <$> F.toList b)

agendaDefProjection inf =  fields
  where
      eventjoin = [Rel "oid" Equals "table"]
      fields =  irecord $ proc t -> do
          (tname,desc,_,pks) <- tableProj inf -< ()
          efields <- iforeign eventjoin 
            (ivalue $ irecord 
              (iforeign [Rel "column" Equals "ordinal_position"] 
                (imap . ivalue $ irecord 
                  (ifield "column_name" 
                    (ivalue $ readV PText))))) -< ()
          color <- iforeign eventjoin (ivalue $ irecord (ifield "color" (ivalue $ readV PText))) -< ()
          let
            table = lookTable inf tname
            toLocalTime = fmap to
                where
                  to (STime (STimestamp i ))  = STime . STimestamp $  i
                  to (STime (SDate i )) = STime $ SDate i
            convField (IntervalTB1 i) = catMaybes [fmap (("start",). toLocalTime )$ unFinite $ Interval.lowerBound i,fmap (("end",).toLocalTime) $ unFinite $ Interval.upperBound i]
            convField v = [("start",toLocalTime $v)]
            convField i = errorWithStackTrace (show i)
            scolor =  "#" <> renderPrim color
            projfT ::  Showable  -> PluginM (Union (G.AttributePath T.Text MutationTy))  (Atom (TBData T.Text Showable))  Identity () A.Object 
            projfT efield@(SText field) = irecord $ proc _-> do
              i <- convertRel inf tname field  -< ()
              fields <- mapA buildRel (fromMaybe ((\(SText i) ->  splitRel inf tname i) <$> pks) ( fmap (liftRel inf tname ).  NonS.fromList. explodeTree   <$> desc) ) -< ()
              pkfields <- mapA (\(SText i) -> (Inline (lookKey inf tname i), ) <$> convertRel inf tname i)  pks -<  ()
              returnA -< HM.fromList $ fmap (fmap A.toJSON) $ -- traceShow ("row agenda", desc ,pks,fields)$
                  [("id" :: Text, txt (writePK' tname pkfields (TB1 efield)))
                  ,("title",txt (T.pack $  L.intercalate "," $ renderShowable <$> catMaybes (F.toList fields)))
                  ,("table",txt tname)
                  ,("color" , txt $ T.pack  scolor )
                  ,("field", TB1 efield )] <> (convField i)
            proj =  fmap (fmap Just ) . mapA projfT  $ traceShowId efields
            wherePred predicate  time  =  pred
              where
                pred = WherePredicate . AndColl $ [timePred inf table (fieldKey . TB1 <$> efields ) time] ++ fmap unPred (maybeToList predicate)
            fieldKey (TB1 (SText v))=   v
            unPred (WherePredicate i) = i
          returnA -< ( txt $ T.pack $ scolor ,table,(wherePred,fieldKey . TB1 <$> efields ) ,proj )


calendarView
  :: 
     InformationSchema
     -> Maybe (TBPredicate Key Showable)
     -> TimeZone
     -> [(t, TableK Key,  (Maybe (TBPredicate Key Showable)
                            -> (UTCTime, String) -> WherePredicate , a),
          PluginM (Union (G.AttributePath T.Text MutationTy))  (Atom (TBData T.Text Showable))  Identity () [Maybe A.Object]
         )]
    -> Tidings (S.Set (TableK Key))
     -> Mode
     -> [Char]
     -> Tidings (Maybe (Table,TBData Key Showable))
     -> UTCTime
     -> UI ([Element], Tidings (Maybe (Table,TBData Key Showable)))
calendarView inf predicate cliZone dashes sel  agenda resolution tdi incrementT = do
    (eselg,hselg) <- ui $ newEvent
    ini <- currentValue (facts tdi)
    bhsel <- ui $ stepper ini (unionWith const (rumors tdi ) eselg)
    let
      readPatch  = makePatch cliZone
      readSel = readPK inf . T.pack
    (tds, evc, innerCalendar) <- calendarSelRow readSel (agenda,resolution,incrementT)
    traverseUI (traverse (\tref->  do
      let ref  =  L.find ((== tref) .  (^. _2)) dashes
      traverse (\(_,t,(pred,_),proj)-> do
        let  fields = fst $ staticP proj
             selection = projectFields inf t fields whereClause $ allFields inf t
             whereClause = pred predicate (incrementT,resolution)
        liftIO $ putStrLn "SELECT "
        liftIO $ putStrLn . ident $ Text.render selection
        liftIO $ putStrLn "WHERE "
        liftIO $ putStrLn  $ Text.renderPredicateWhere whereClause
        reftb <- ui $ refTablesProj inf t Nothing whereClause selection
        let output  = reftb ^. _2
            evsel = fmap Just $ filterJust $ (\j (tev,pk,_) -> if tev == t then (t,) <$> G.lookup  pk (primary j) else Nothing  ) <$> facts output <@>  evc
        ui $ onEventIO evsel hselg
        addSource innerCalendar t (evalPlugin proj) output) ref) . F.toList) sel
    onEvent (rumors tds) (ui . transaction inf . mapM (\((t,ix,k),i) ->
      patchFrom (tableMeta t) (ix ,PatchRow $ readPatch (k,i))))
    return ([innerCalendar],tidings bhsel eselg)

calendarSelRow readSel (agenda,resolution,incrementT) = do
    let
      capitalize (i:xs) = toUpper i : xs
      capitalize [] = []
      transMode Agenda i = "agenda" <> capitalize i
      transMode Basic "month" = "month"
      transMode Basic i = "basic" <> capitalize i
      transMode Timeline i = "timeline" <> capitalize i
    innerCalendar  <- UI.div
    calendarCreate (transMode agenda resolution) innerCalendar (show incrementT)
    let
      evc = eventClick innerCalendar
      evd = eventDrop innerCalendar
      evr = eventResize innerCalendar
      evdd = eventDragDrop innerCalendar
      evs =  fmap (first readSel) <$> unions [evr,evdd,evd]
    bhevs <- ui $ stepper [] evs
    return (tidings bhevs evs,readSel <$> evc, innerCalendar)


addSource innerCalendar t proj v = do
    traverseUI
      (\i -> calendarAddSource innerCalendar  t (concatMap catMaybes $ fmap proj $ G.toList (primary i))) v

type DateChange = (String, Either (Interval UTCTime) UTCTime)

readTime :: EventData -> Maybe DateChange
readTime v = case unsafeFromJSON v of
        [i,a,e]  -> (,) <$> Just i <*>
          ((\i j ->
                 Left $
                 Interval.interval
                     (Interval.Finite i, True)
                     (Interval.Finite j, True)) <$>
           parseISO8601 a <*>
           parseISO8601 e)
        [i,a] -> (,) <$> Just i <*> (Right <$> parseISO8601 a)

eventClick:: Element -> Event String
eventClick el = fmap fst $ filterJust $ readTime <$> domEvent "eventClick" el

eventDrop :: Element -> Event DateChange
eventDrop el = filterJust $ readTime <$> domEvent "eventDrop" el

eventDragDrop :: Element -> Event DateChange
eventDragDrop el = filterJust $ readTime <$> domEvent "drop" el

eventResize :: Element -> Event DateChange
eventResize el = filterJust $ readTime <$> domEvent "eventResize" el
