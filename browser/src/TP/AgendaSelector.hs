{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE Arrows #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module TP.AgendaSelector (Mode(..),eventWidgetMeta,calendarView,agendaDef) where

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
import Control.Lens ((^.), _1, mapped,_2, _3,_4,_5)
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
    fmap F.toList $ ui $ transactionNoLog (meta inf) $ dynPK (agendaDef inf) ()

data Tree f a 
  = Leaf { unLeaf :: a}
  | Tree a (f (Tree f a))

instance (Foldable f, Show a) => Show (Tree f a ) where
  show (Leaf i )=  show i 
  show (Tree a i ) = show a <> " - " <> L.intercalate "," (show <$> F.toList i)

explodeTree (Tree i f ) = concat $ zipWith (\(SText i) j -> RelAccess (Inline  i) <$> j ) (F.toList i) (fmap explodeTree (F.toList f))
explodeTree (Leaf i ) = ((\(SText t) -> Inline t ) <$> F.toList i) 



agendaDef inf
  = projectV
    (innerJoinR 
      (fixLeftJoinR
        (innerJoinR
          (fromR "tables" `whereR` schemaPred2)
          (fromR "event") [Rel "schema" Equals "schema", Rel "oid" Equals "table"]  "event")
        (fromR "table_description") [Rel "schema_name" Equals "table_schema", Rel "table_name" Equals "table_name"]  (Just indexDescription ) "description")
      (fromR "pks") [Rel "schema_name" Equals "schema_name", Rel "table_name" Equals "table_name"]  "pks") fields
   where
      indexDescription = fmap keyValue $ liftRel (meta inf ) "table_description" $ RelAccess (Rel "description" Equals "column_name")
                            (RelAccess (Inline "col_type")
                                (RelAccess (Inline "composite")
                                    (RelComposite [Rel "schema_name" Equals "schema_name", Rel "data_name" Equals "table_name"])))  
      schemaPred2 =  [(keyRef "schema",Left (int (schemaId inf),Equals) )]
      eitherDescription = isum [nestedDescription , directDescription] 
      directDescription = fmap (fmap Leaf) $ iinline "description" (iopt . ivalue $ irecord (ifield "description" (imap . ivalue $  readV PText)))
      nestedDescription = fmap (join .fmap (\(i,j) -> Tree i <$> NonS.pruneSequence j)) . iinline "description" . iopt . ivalue $ irecord 
              (liftA2 (,) 
                (ifield "description" (imap . ivalue $  readV PText))
                (iforeign (relUnComp $ fmap keyValue $ liftRel (meta inf ) "table_description" $ relComp $ [Rel "description" Equals "column_name"] )
                (imap . ivalue . irecord $ (iinline "col_type" 
                  (ivalue . irecord . iinline "composite" . fmap join . iopt . ivalue $ irecord 
                    (iforeign [Rel "schema_name" Equals "schema_name", Rel "data_name" Equals "table_name"]
                       . ivalue . irecord $ eitherDescription 
                        ))))))
      fields =  irecord $ proc t -> do
          SText tname <-
              ifield "table_name" (ivalue (readV PText))  -< ()
          efields <- iinline "event" 
            (ivalue $ irecord 
              (iforeign [Rel "schema" Equals "schema" , Rel "table" Equals "table", Rel "column" Equals "oid"] 
                (imap . ivalue $ irecord 
                  (ifield "column_name" 
                    (ivalue $ readV PText))))) -< ()
          desc <-  eitherDescription -< ()
          pks <- iinline "pks" (ivalue $ irecord (iforeign [Rel "schema_name" Equals "schema_name" , Rel "table_name" Equals "table_name", Rel "pks" Equals "column_name"] (imap $ ivalue $ irecord (ifield  "column_name" (ivalue $  readV PText))))) -< ()
          color <- iinline "event" (ivalue $ irecord (ifield "color" (ivalue $ readV PText))) -< ()
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
              fields <- mapA buildRel (fromMaybe ((\(SText i) ->  splitRel inf tname i) <$> pks) ( fmap (liftRel inf tname ) . NonS.fromList. explodeTree <$> desc) ) -< ()
              pkfields <- mapA (\(SText i) -> (Inline (lookKey inf tname i), ) <$> convertRel inf tname i)  pks -<  ()
              returnA -< HM.fromList $ fmap (fmap A.toJSON) $
                  [("id" :: Text, txt (writePK' tname pkfields (TB1 efield)))
                  ,("title",txt (T.pack $  L.intercalate "," $ renderShowable <$> catMaybes (F.toList fields)))
                  ,("table",txt tname)
                  ,("color" , txt $ T.pack  scolor )
                  ,("field", TB1 efield )] <> (convField i)
            proj =  fmap (fmap Just ) . mapA projfT  $ efields
            wherePred predicate  time  =  pred
              where
                pred = WherePredicate . AndColl $ [timePred inf table (fieldKey . TB1 <$> efields ) time] ++ fmap unPred (maybeToList predicate)
                fieldKey (TB1 (SText v))=   v
                unPred (WherePredicate i) = i
          returnA -< (txt $ T.pack $ scolor ,table,wherePred ,proj )


calendarView
  :: 
     InformationSchema
     -> Maybe (TBPredicate Key Showable)
     -> TimeZone
     -> [(t, TableK Key,  Maybe (TBPredicate Key Showable)
                            -> (UTCTime, String) -> WherePredicate ,
          PluginM (Union (G.AttributePath T.Text MutationTy))  (Atom (TBData T.Text Showable))  Identity () [Maybe A.Object]
         )]
    -> Tidings (S.Set (TableK Key))
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
    traverseUI (traverse (\tref->  do
      let ref  =  L.find ((== tref) .  (^. _2)) dashes
      traverse (\(_,t,pred ,proj)-> do
        let  selection = projectFields inf t (fst $ staticP proj) $ allFields inf t
        reftb <- ui $ refTablesProj inf t Nothing (pred predicate (incrementT,resolution)) selection
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
