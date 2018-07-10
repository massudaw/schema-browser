{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE Arrows #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module TP.AgendaSelector (Mode(..),eventWidgetMeta,calendarView,agendaDef) where

import GHC.Stack
import Environment
import Control.Arrow
import Step.Host
import Control.Monad.Writer as Writer
import TP.View
import qualified Data.Interval as Interval
import qualified Data.HashMap.Strict as HM
import NonEmpty (NonEmpty)
import Control.Concurrent
import Utils
import Data.Functor.Identity
import Types.Patch
import Control.Arrow
import Control.Lens ((^.), _1, mapped,_2, _3,_4,_5)
import qualified Data.List as L
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
  ui $ registerDynamic (fmap fst $ runDynamic $ evalUI cal $ calendarRemoveSource cal t)

calendarRemoveSource cal t = runFunctionDelayed cal $ ffi "removeSource(%1,%2)" cal (tableName t)

data Mode
  = Agenda
  | Basic
  | Timeline
  deriving(Eq,Show,Ord)


eventWidgetMeta inf =  do
    importUI =<<  mapM js
       ["fullcalendar-3.5.0/lib/jquery-ui.min.js"
       ,"fullcalendar-3.5.0/lib/moment.min.js"
       ,"fullcalendar-3.5.0/fullcalendar.min.js"
       ,"fullcalendar-scheduler-1.7.0/scheduler.min.js"
       ,"fullcalendar-3.5.0/locale-all.js"]
    importUI =<< mapM css
       ["fullcalendar-3.5.0/fullcalendar.min.css"
       ,"fullcalendar-scheduler-1.7.0/scheduler.min.css"
       ]
    fmap F.toList $ ui $ transactionNoLog (meta inf) $ dynPK (agendaDef inf) ()



agendaDef inf
  = projectV
    (innerJoinR
      (fromR "tables" `whereR` schemaPred2)
      (fromR "event" `whereR` schemaPred2) [Rel "schema" Equals "schema", Rel "oid" Equals "table"]  "event") fields
   where
      schemaPred2 =  [(keyRef "schema",Left (int (schemaId inf),Equals) )]
      schemaPredName =  [(keyRef "table_schema",Left (txt (schemaName inf),Equals) )]
      fields =  irecord $ proc t -> do
          SText tname <-
              ifield "table_name" (ivalue (readV PText))  -< ()
          efields <- iinline "event" (ivalue $ irecord (iforeign [Rel "schema" Equals "schema" , Rel "table" Equals "table", Rel "column" Equals "oid"] (imap $ ivalue $ irecord (ifield  "column_name" (ivalue $  readV PText))))) -< ()
          color <- iinline "event" (ivalue $ irecord (ifield "color" (ivalue $ readV PText))) -< ()
          let
            table = lookTable inf tname
            toLocalTime = fmap to
                where
                  to (STime (STimestamp i ))  = STime $ STimestamp $  i
                  to (STime (SDate i )) = STime $ SDate i
            convField (IntervalTB1 i) = catMaybes [fmap (("start",). toLocalTime )$ unFinite $ Interval.lowerBound i,fmap (("end",).toLocalTime) $ unFinite $ Interval.upperBound i]
            convField v = [("start",toLocalTime $v)]
            convField i = errorWithStackTrace (show i)
            scolor =  "#" <> renderPrim color
            projf  r efield@(SText field) = do
                i <- unSOptional =<< recLookupInf inf tname (indexerRel field) r
                return . M.fromList $
                  [("id" :: Text, txt $ writePK (tableMeta table) r (TB1 efield  ) )
                  ,("title",txt (T.pack $  L.intercalate "," $ fmap renderShowable $ allKVRec' inf (tableMeta table)$  r))
                  ,("table",txt tname)
                  ,("color" , txt $ T.pack  scolor )
                  ,("field", TB1 efield )] <> convField i
            proj r = ( projf r <$> (F.toList efields))

          returnA -< (txt $ T.pack $ scolor ,table,fmap TB1 efields,proj )


calendarView
  :: (A.ToJSON a, Foldable t2
      ) =>
     InformationSchema
     -> Maybe (TBPredicate Key Showable)
     -> TimeZone
     -> t2 (t, TableK Key, NonEmpty (FTB Showable),
          TBData Key Showable -> [Maybe a ])
    -> Tidings (S.Set (TableK Key) )
     -> Mode
     -> [Char]
     -> UTCTime
     -> UI ([Element], Tidings (Maybe (Table,TBData Key Showable)))
calendarView inf predicate cliZone dashes sel  agenda resolution incrementT = do
    (eselg,hselg) <- ui $ newEvent
    bhsel <- ui $ stepper Nothing eselg
    let
      readPatch  = makePatch cliZone
      readSel = readPK inf . T.pack
    (tds, evc, innerCalendar) <- calendarSelRow readSel (agenda,resolution,incrementT)
    edits <- traverseUI (traverse (\tref->  do
      let ref  =  L.find ((== tref) .  (^. _2)) dashes
      traverse (\(_,t,fields,proj)-> do
            let pred = WherePredicate $ AndColl $ [timePred inf t (fieldKey <$> fields ) (incrementT,resolution)] ++ fmap unPred (maybeToList predicate)
                fieldKey (TB1 (SText v))=   v
                unPred (WherePredicate i) = i
            reftb <- ui $ refTables' inf t Nothing pred
            let v = reftb ^. _2
            let evsel = fmap Just $ filterJust $ (\j (tev,pk,_) -> if tev == t then (t,) <$> G.lookup  pk j else Nothing  ) <$> facts v <@>  evc
            tdib <- ui $ stepper Nothing evsel
            let tdi = tidings tdib evsel
            ui $ onEventIO evsel hselg
            traverseUI
              (\i ->calendarAddSource innerCalendar  t (concat . fmap (catMaybes) $ fmap proj $ G.toList i)) v
                                  ) ref) . F.toList ) sel

    onEvent (rumors tds) (ui . transaction inf . mapM (\((t,ix,k),i) ->
      patchFrom (tableMeta t) (ix ,PatchRow $ readPatch (k,i)) ))
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
    return $(tidings bhevs evs,readSel <$> evc, innerCalendar)


addSource inf innerCalendar (_,t,fields,proj) (agenda,resolution,incrementT)= do
    let pred = WherePredicate $ timePred inf t (fieldKey <$> fields ) (incrementT,resolution)
        fieldKey (TB1 (SText v))=   v
    reftb <- ui $ refTables' inf t Nothing pred
    let v = reftb ^. _2
    traverseUI
      (\i -> calendarAddSource innerCalendar  t (concat . fmap (catMaybes) $ fmap proj $ G.toList i)) v

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
