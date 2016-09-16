{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module TP.Agenda where

import GHC.Stack
import Step.Host
import TP.View
import qualified Data.Interval as Interval
import Control.Concurrent
import Utils
import Types.Patch
import Control.Arrow
import Control.Lens ((^.), _1, mapped,_2, _3)
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

calendarCreate m cal def = runFunction $ ffi "createAgenda(%1,%2,%3)" cal def m

calendarAddSource cal t evs = runFunction $ ffi "addSource(%1,%2,%3)" cal t evs

eventWidget body (agendaT,incrementT,resolutionT) sel inf cliZone = do
    let
      calendarSelT = liftA3 (,,) agendaT incrementT resolutionT
      schemaPred =  [(IProd True ["schema_name"],"=",TB1 $ SText (schemaName inf))]

    dashes <- liftIO $ do
      (_,(_,tmap)) <- transactionNoLog (meta inf) $ selectFromTable "table_name_translation" Nothing Nothing [] schemaPred
      (evdb,(_,evMap )) <- transactionNoLog  (meta inf) $ selectFromTable "event" Nothing Nothing [] schemaPred
      return $ fmap (\e ->
        let
            (Attr _ (TB1 (SText tname))) = lookAttr' (meta inf) "table_name" $ unTB1 $ _fkttable $ lookAttrs' (meta inf) ["schema_name","table_name"] e
            lookDesc = (\i  -> maybe (T.unpack $ tname)  ((\(Attr _ v) -> renderShowable v). lookAttr' (meta inf)  "translation") $ G.lookup (idex (meta inf) "table_name_translation" [("schema_name" ,txt $ schemaName inf),("table_name",txt tname )]) i ) $ tmap
            (Attr _ (ArrayTB1 efields ))= lookAttr' (meta inf) "event" e
            (Attr _ color )= lookAttr' (meta inf) "color" e
            toLocalTime = fmap to
              where to (STimestamp i )  = STimestamp $  utcToLocalTime cliZone $ localTimeToUTC utc i
                    to (SDate i ) = SDate i
            convField ((IntervalTB1 i )) = [("start", toLocalTime $ unFinite $ Interval.lowerBound i),("end",toLocalTime $ unFinite $ Interval.upperBound i)]
            convField (LeftTB1 i) = concat $   convField <$> maybeToList i
            convField (v) = [("start",toLocalTime $v)]
            convField i = errorWithStackTrace (show i)
            projf  r efield@(TB1 (SText field))  = (if (isJust $ join $  unSOptional <$> attr) then Left else Right) (M.fromList $ concat (convField <$> maybeToList attr  ) <> [("id", TB1 $ SText $ writePK r efield   ),("title",TB1 $ SText (T.pack $  L.intercalate "," $ fmap renderShowable $ allKVRec' $  r)) , ("table",TB1 (SText tname)),("color" , color),("field", efield )] :: M.Map Text (FTB Showable))
                  where attr  = attrValue <$> lookAttrM inf field r
            proj r = (TB1 $ SText (T.pack $  L.intercalate "," $ fmap renderShowable $ allKVRec' $  r),)$  projf r <$> F.toList efields
            attrValue (Attr k v) = v
        in (lookDesc,(color,tname,efields,proj))) ( G.toList evMap)

    iday <- liftIO getCurrentTime
    let allTags =  dashes
    itemListEl2 <- mapM (\i ->
      (i ^. _2._2 ,) <$> UI.div  # set UI.style [("width","100%"),("height","150px") ,("overflow-y","auto")]) allTags
    let
        legendStyle  table (b,_)
            =  do
              let item = M.lookup (tableName (justError ("no table" <> show table)$ M.lookup table (pkMap inf))) (M.fromList  $ fmap (\i@(t,(a,b,c,_))-> (b,i)) allTags)
              maybe (UI.div) (\(k@(t,(c,tname,_,_))) -> mdo
                expand <- UI.input # set UI.type_ "checkbox" # sink UI.checked evb # set UI.class_ "col-xs-1"
                let evc = UI.checkedChange expand
                evb <- stepper False evc
                missing <- (element $ justError ("no table" <> show tname)$ M.lookup tname  (M.fromList $  itemListEl2)) # sink UI.style (noneShow <$> evb)
                header <- UI.div
                  # set items [element b # set UI.class_"col-xs-1", UI.div # set text  t # set UI.class_ "col-xs-10", element expand ]
                  # set UI.style [("background-color",renderShowable c)]
                UI.div # set children [header,missing]
                  ) item
    calendar <- UI.div # set UI.class_ "col-xs-10"
    element body # set children [calendar]
    let calFun (agenda,resolution,incrementT,selected) = mdo
            let
              capitalize (i:xs) = toUpper i : xs
              capitalize [] = []
              transMode _ "month" = "month"
              transMode True i = "agenda" <> capitalize i
              transMode False i = "basic" <> capitalize i
            innerCalendar  <- UI.div
            sel <- UI.div
            calendarFrame <- UI.div # set children [innerCalendar] # set UI.style [("height","450px"),("overflow","auto")]
            element calendar # set children [calendarFrame,sel]
            calendarCreate (transMode agenda resolution) innerCalendar (show incrementT)
            onEventFT (UI.hover innerCalendar) (const $ do
                    runFunction $ ffi "$(%1).fullCalendar('render')" innerCalendar )
            let
              evc = eventClick innerCalendar
              evd = eventDrop innerCalendar
              evr = eventResize innerCalendar
              evdd = eventDragDrop innerCalendar
              evs =  fmap (makePatch cliZone . first (readPK inf . T.pack))<$> unions [evr,evdd,evd]
            onEventFT evs (liftIO . transaction inf . mapM
                  (\i -> do
                     patchFrom i >>= traverse (tell . pure )))
            edits <- mapM (\(cap,(_,t,fields,proj))->  do
                let pred = WherePredicate $ lookAccess inf t<$> timePred (fieldKey <$> fields ) (agenda,incrementT,resolution)
                    fieldKey (TB1 (SText v))=  lookKey inf t v
                -- (v,_) <-  liftIO $  transactionNoLog  inf $ selectFromA t Nothing Nothing [] pred
                reftb <- refTables' inf (lookTable inf t) Nothing pred
                let v = fmap snd $ reftb ^. _1
                let evsel = (\j (tev,pk,_) -> if tableName tev == t then Just ( G.lookup ( G.Idex  $ notOptionalPK $ M.fromList $pk) j) else Nothing  ) <$> facts (v) <@> fmap (readPK inf . T.pack ) evc
                tdib <- stepper Nothing (join <$> evsel)
                let tdi = tidings tdib (join <$> evsel)
                (el,_,_) <- crudUITable inf ((\i -> if isJust i then "+" else "-") <$> tdi)  reftb [] [] (allRec' (tableMap inf) $ lookTable inf t)  tdi
                mapUIFinalizerT innerCalendar
                  ((\i -> do
                    calendarAddSource innerCalendar  (T.unpack t) ((T.unpack . TE.decodeUtf8 .  BSL.toStrict . A.encode  .  concat . fmap (lefts.snd) $ fmap proj $ G.toList i)))
                  ) (v)
                UI.div # set children el # sink UI.style  (noneShow . isJust <$> tdib)
                ) selected
            element sel # set children (edits)

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

    let inpCal =
          ((\i j -> filter (flip L.elem (tableName <$> concat (F.toList i)) .  (^. _2._2)) j )<$> sel <*> pure allTags)

    mapUIFinalizerT calendar calFun ((,,,) <$> agendaT <*> resolutionT <*> incrementT <*> inpCal)

    return  (legendStyle , dashes )

txt = TB1. SText


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
