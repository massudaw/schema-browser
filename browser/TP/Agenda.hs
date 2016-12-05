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
import qualified Data.Interval as Interval
import Control.Concurrent
import Utils
import Types.Patch
import Control.Arrow
import Control.Lens ((^.), _1, mapped,_2, _3,_4)
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

calendarCreate m cal def = runFunction $ ffi "createAgenda(%1,%2,%3)" cal def m

calendarAddSource cal t evs = runFunction $ ffi "addSource(%1,%2,%3)" cal (tableName t) evs
calendarRemoveSource cal t = runFunction $ ffi "removeSource(%1,%2)" cal (tableName t)

data Mode
  = Agenda
  | Basic
  | Timeline
  deriving(Eq,Show,Ord)

eventWidgetMeta inf cliZone= do
    let
      schemaPred =  [(keyRef ["schema_name"],Left (txt (schemaName inf),Equals) )]
      schemaPred2 =  [(keyRef ["schema"],Left (int (schemaId inf),Equals) )]

    ui$ do
      evMap <- transactionNoLog (meta inf) $ do
        (_,(_,evMap )) <- selectFromTable "event" Nothing Nothing [] schemaPred2
        return evMap
      return $ fmap (\e ->
        let
            Just (TB1 (SText tname)) = unSOptional' $  _tbattr $ lookAttr' (meta inf) "table_name" $ unTB1 $ _fkttable $ lookAttrs' (meta inf) ["schema","table"] e
            table = lookTable inf tname
            Just (Attr _ (ArrayTB1 efields ))= indexField (liftAccess (meta inf )"event" $ keyRef ["event"]) e
            (Attr _ color )= lookAttr' (meta inf) "color" e
            toLocalTime = fmap to
              where to (STimestamp i )  = STimestamp $  utcToLocalTime cliZone $ localTimeToUTC utc i
                    to (SDate i ) = SDate i
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
    w <-  askWindow
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

    dashes<- eventWidgetMeta inf cliZone
    iday <- liftIO getCurrentTime
    let
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

    agenda <- buttonDivSet [Basic,Agenda,Timeline] (pure $ Just Basic) (\i ->  UI.button # set text (show i){- # set UI.class_ "buttonSet btn-xs btn-default pull-right")-})

    calendar <- UI.div # set UI.class_ "col-xs-10"
    element body # set children [getElement agenda,calendar]
    let inpCal = sel
    let calFun (agenda,resolution,incrementT) = mdo
            let
              capitalize (i:xs) = toUpper i : xs
              capitalize [] = []
              transMode Agenda i = "agenda" <> capitalize i
              transMode Basic "month" = "month"
              transMode Basic i = "basic" <> capitalize i
              transMode Timeline i = "timeline" <> capitalize i
            innerCalendar  <- UI.div
            sel <- UI.div
            calendarFrame <- UI.div # set children [innerCalendar]
            element calendar # set children [calendarFrame,sel]
            calendarCreate (transMode agenda resolution) innerCalendar (show incrementT)
            ho <- UI.hover innerCalendar
            ui $ onEventDyn ho (const $ evalUI innerCalendar $ do
                    runFunction $ ffi "$(%1).fullCalendar('render')" innerCalendar )
            let
              evc = eventClick innerCalendar
              evd = eventDrop innerCalendar
              evr = eventResize innerCalendar
              evdd = eventDragDrop innerCalendar
              evs =  fmap (makePatch cliZone . first (readPK inf . T.pack))<$> unions [evr,evdd,evd]
            ui $ onEventDyn evs (transaction inf . mapM
                  (\i -> do
                     patchFrom i >>= traverse (tell . pure )))
            edits <- ui$ accumDiff (\(tref,_)->  evalUI calendar $ do
              let ref  =  (\i j ->  L.find ((== i) .  (^. _2)) j ) tref dashes
              traverse (\((_,t,fields,proj))-> do
                    let pred = WherePredicate $ timePred inf t (fieldKey <$> fields ) (incrementT,resolution)
                        fieldKey (TB1 (SText v))=   v
                    reftb <- ui $ refTables' inf t Nothing pred
                    let v = fmap snd $ reftb ^. _1
                    let evsel = (\j (tev,pk,_) -> if tev == t then Just ( G.lookup  pk j) else Nothing  ) <$> facts (v) <@> fmap (readPK inf . T.pack ) evc
                    tdib <- ui $ stepper Nothing (join <$> evsel)
                    let tdi = tidings tdib (join <$> evsel)
                    (el,ediff,_) <- crudUITable inf ((\i -> if isJust i then "+" else "-") <$> tdi)  reftb [] [] (allRec' (tableMap inf) $ t)  tdi
                    ui $ onEventDyn (pure <$> ediff) (liftIO .  putPatch (reftb ^. _4 ))
                    mapUIFinalizerT innerCalendar
                      (\i -> do
                        calendarAddSource innerCalendar  t ((T.unpack . TE.decodeUtf8 .  BSL.toStrict . A.encode  .  concat . fmap (lefts.snd) $ fmap proj $ G.toList i))
                        ui $ registerDynamic (fmap fst $ runDynamic $ evalUI innerCalendar $ calendarRemoveSource innerCalendar t))
                       (v)
                    UI.div # set children el # sink UI.style  (noneShow . isJust <$> tdib)
                                   ) ref) inpCal

            element sel # sink children ( catMaybes .F.toList <$> facts edits)

            {-fins <- mapM (\((_,(_,t,_)),s)->  fmap snd $ mapUIFinalizerT innerCalendar (
                      lift  $ transactionNoLog  inf $ selectFromA (tname) Nothing Nothing []  (WherePredicate $ timePred ((\(TB1 (SText v))->  lookKey inf tname v) <$> fields ) cal)) calendarSelT
                      (\i -> do
                      calendarAddSource innerCalendar  (T.unpack t) ((T.unpack . TE.decodeUtf8 .  BSL.toStrict . A.encode  . filter (inRange res (utctDay day ) . unTB1 . fromJust .  M.lookup "start"  ) . concat . fmap (lefts.snd) $ i)))
                      )  calendarSelT ) selectedData
            liftIO $ addFin innerCalendar (fin:fins)-}
              {-mapM (\(k,el) -> do
              traverse (\t -> do
                element  el
                  # sink items (fmap (\(t,i) -> do
                         h<- UI.div # set text (renderShowable t)
                         b <- UI.div # set items (fmap (\i->do
                           dv <-  UI.div # set text ((maybe "" renderShowable  $M.lookup "field" i )) # set UI.style ([("border","solid black 1px"),("padding-left","10px")]<> (maybeToList $ ("background-color",) . renderShowable<$>  M.lookup "color" i))
                           runFunction $ ffi "$(%1).data('event', {title: %2 ,id:%3, color :%4 ,stick: false })" dv  (maybe ""  renderShowable $ M.lookup "title" i) (maybe ""  renderShowable $ M.lookup "id" i) (maybe ""  renderShowable $ M.lookup "color" i)
                           runFunction $ ffi "$(%1).draggable({ helper: 'clone',scroll:false,appendTo: 'body' ,'z-index' : 999,revert:true,revertDuration:0})" dv
                           return dv) i)
                         UI.div # set children [h,b] # set UI.style [("border","dotted 1px black")]
                          ) . filter (not .L.null .snd) . fmap (fmap rights) <$> facts t) # set UI.style [("border","solid 1px black")])  $ join $ flip M.lookup  (M.fromList selectedData) <$> Just k) itemListEl2
            return innerCalendar
-}


    mapUIFinalizerT calendar calFun ((,,) <$> triding agenda <*> resolutionT <*> incrementT )

    return  (legendStyle , dashes )



type DateChange = (String, Either (Interval UTCTime) UTCTime)

-- readPosition:: EventData -> Maybe DateChange
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
eventDragDrop el = filterJust $ readTime <$> domEvent "externalDrop" el

eventResize :: Element -> Event DateChange
eventResize el = filterJust $ readTime <$> domEvent "eventResize" el
