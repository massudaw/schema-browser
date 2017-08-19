{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module TP.Agenda (eventWidget,eventWidgetMeta) where

import GHC.Stack
import Step.Host
import Control.Monad.Writer as Writer
import TP.View
import TP.Selector
import qualified Data.Interval as Interval
import Control.Concurrent
import Utils
import Types.Patch
import Control.Arrow
import TP.Browser
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
import TP.QueryWidgets
import Control.Monad.Reader
import Schema
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

eventWidgetMeta inf cliZone= do
    importUI $ fmap js
       ["fullcalendar-3.0.1/lib/jquery-ui.min.js"
       ,"fullcalendar-3.0.1/lib/moment.min.js"
       ,"fullcalendar-3.0.1/fullcalendar.min.js"
       ,"fullcalendar-scheduler-1.4.0/scheduler.min.js"
       ,"fullcalendar-3.0.1/locale-all.js"]
              <>  fmap css
       ["fullcalendar-3.0.1/fullcalendar.min.css"
       ,"fullcalendar-scheduler-1.4.0/scheduler.min.css"
       ]
    let
      schemaPred2 =  [(keyRef "schema",Left (int (schemaId inf),Equals) )]
    ui$ do
      (_,(_,evMap )) <- transactionNoLog (meta inf) $ selectFromTable "event" Nothing Nothing [] schemaPred2
      return $ fmap (\e ->
        let
            Just (TB1 (SText tname)) = unSOptional' $  _tbattr $ lookAttr' (meta inf) "table_name" $ unTB1 $ _fkttable $ lookAttrs' (meta inf) ["schema","table"] e
            table = lookTable inf tname
            Just (Attr _ (ArrayTB1 efields ))= indexField (liftAccess (meta inf )"event" $ keyRef "event") e
            (Attr _ color )= lookAttr' (meta inf) "color" e
            toLocalTime = fmap to
              where to (STime (STimestamp i ))  = STime $ STimestamp $  utcToLocalTime cliZone $ localTimeToUTC utc i
                    to (STime (SDate i )) = STime $ SDate i
            convField ((IntervalTB1 i )) = catMaybes [fmap (("start",). toLocalTime )$ unFinite $ Interval.lowerBound i,fmap (("end",).toLocalTime) $ unFinite $ Interval.upperBound i]
            convField (LeftTB1 i) = concat $   convField <$> maybeToList i
            convField (v) = [("start",toLocalTime $v)]
            convField i = errorWithStackTrace (show i)
            projf  r efield@(TB1 (SText field))  = (if (isJust $ join $  unSOptional <$> attr) then Left else Right) (M.fromList $ concat (convField <$> maybeToList attr  ) <> [("id", txt $ writePK r efield   ),("title",txt (T.pack $  L.intercalate "," $ fmap renderShowable $ allKVRec' $  r)) , ("table",txt tname),("color" , txt $ T.pack $ "#" <> renderShowable color ),("field", efield )] :: M.Map Text (FTB Showable))
                  where attr  = attrValue <$> lookAttrM inf field r
            proj r = (txt (T.pack $  L.intercalate "," $ fmap renderShowable $ allKVRec' $  r),)$  projf r <$> (F.toList efields)
            attrValue (Attr k v) = v
         in (txt $ T.pack $ "#" <> renderShowable color ,lookTable inf tname,efields,proj)) ( G.toList evMap)


eventWidget body (incrementT,resolutionT) sel inf cliZone = do
    dashes <- eventWidgetMeta inf cliZone
    let
      schemaPred2 =   WherePredicate $ PrimColl (liftAccess (meta inf) "event" $ keyRef "schema",Left (int (schemaId inf),Equals) )
      legendStyle  lookDesc table b
            =  do
              let item = M.lookup table (M.fromList  $ fmap (\i@(a,b,c,_)-> (b,i)) dashes)
              maybe UI.div (\(k@((c,tname,_,_))) -> mdo
                expand <- UI.input # set UI.type_ "checkbox" # sink UI.checked evb # set UI.class_ "col-xs-1"
                evc <- UI.checkedChange expand
                evb <- ui $ stepper False evc
                missing <- UI.div  # set UI.style [("width","100%"),("height","150px") ,("overflow-y","auto")] # sink UI.style (noneShow <$> evb)
                header <- UI.div
                  # set items [element b # set UI.class_"col-xs-1", UI.div # sink text  (T.unpack .($table) <$> facts lookDesc ) # set UI.class_ "fixed-label col-xs-10", element expand ]
                  # set UI.style [("background-color",renderShowable c)]
                UI.div # set children [header,missing]
                  ) item

    choose <- buttonDivSet ["Main","Config"] (pure $ Just "Main") (\i ->  UI.button # set text i # set UI.class_ "buttonSet btn-xs btn-default pull-right")
    let
      chooser "Config" = do
        let
            minf = meta inf
            table = lookTable minf "event"
        reftb@(vptmeta,vp,vpt,_,var) <- ui $ refTables' minf table Nothing schemaPred2
        config <- selector minf table reftb  (pure $ Just schemaPred2 ) (pure Nothing)
        let tds = triding config
        (cru,pretdi) <- crudUITable minf reftb [] [] (allRec' (tableMap minf) table) (triding config)
        return [getElement config,cru]

      chooser "Main" = do
        agenda <- buttonDivSet [Basic,Agenda,Timeline] (pure $ Just Basic) (\i ->  UI.button # set text (show i) # set UI.class_ "buttonSet btn-xs btn-default pull-left")
        out <- traverseUI id $ calendarView inf cliZone dashes sel <$>  triding agenda <*> resolutionT <*> incrementT
        calendar <- UI.div # sink UI.children (facts out)
        return [getElement agenda,calendar]
    els <- traverseUI chooser (triding choose)

    content <- UI.div # sink children (facts els) # set UI.class_ "row"
    element choose  # set UI.class_ "row"

    element body # set children [getElement choose,content] # set UI.style [("overflow","auto")]

    return  (legendStyle , dashes )


calendarView inf cliZone dashes sel  agenda resolution incrementT = do
    let
      readPatch  = makePatch cliZone
      readSel = readPK inf . T.pack
    (tds, evc, innerCalendar) <- calendarSelRow readSel (agenda,resolution,incrementT)
    edits <- ui$ accumDiff (\(tref,_)->  evalUI innerCalendar $ do
      let ref  =  L.find ((== tref) .  (^. _2)) dashes
      traverse (\(_,t,fields,proj)-> do
            let pred = WherePredicate $ timePred inf t (fieldKey <$> fields ) (incrementT,resolution)
                fieldKey (TB1 (SText v))=   v
            reftb <- ui $ refTables' inf t Nothing pred
            let v = reftb ^. _3
            let evsel = fmap join $ (\j (tev,pk,_) -> if tev == t then Just (G.lookup  pk j) else Nothing  ) <$> facts v <@>  evc
            tdib <- ui $ stepper Nothing evsel
            let tdi = tidings tdib evsel
            (el,_) <- crudUITable inf   reftb [] [] (allRec' (tableMap inf) $ t)  tdi
            traverseUI
              (\i ->calendarAddSource innerCalendar  t (concat . fmap (lefts.snd) $ fmap proj $ G.toList i)) v
            UI.div # set children [el] # sink UI.style  (noneShow . isJust <$> tdib)
                           ) ref) sel

    onEvent (rumors tds) (ui . transaction inf . mapM (\i ->
      patchFrom (readPatch i) >>= traverse (tell . pure )))
    selection <- UI.div # sink children ( catMaybes .F.toList <$> facts edits)
    return [innerCalendar,selection]

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
    let v = reftb ^. _3
    traverseUI
      (\i -> calendarAddSource innerCalendar  t (concat . fmap (lefts.snd) $ fmap proj $ G.toList i)) v

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
