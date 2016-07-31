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
import Control.Lens ((^.),_1,_2)
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
calendarCreate m cal def = runFunction $ ffi "createAgenda(%1,%2,%3)"  cal def m
calendarAddSource cal t evs= runFunction $ ffi "addSource(%1,%2,%3)"  cal t evs

eventWidget body calendarSelT sel inf cliZone = do
    dashes <- liftIO $ do
      (_,(_,tmap)) <- transactionNoLog (meta inf) $ selectFrom "table_name_translation" Nothing Nothing [] (LegacyPredicate[("=",liftField (meta inf) "table_name_translation" $ uncurry Attr $("schema_name",TB1 $ SText (schemaName inf) ))])
      (evdb,(_,evMap )) <- transactionNoLog  (meta inf) $ selectFrom "event" Nothing Nothing [] (LegacyPredicate[("=",liftField (meta inf) "event" $ uncurry Attr $("schema_name",TB1 $ SText (schemaName inf) ))])
      mapConcurrently (\e -> do
        let (Attr _ (TB1 (SText tname))) = lookAttr' (meta inf) "table_name" e
            lookDesc = (\i  -> maybe (T.unpack $ tname)  ((\(Attr _ v) -> renderShowable v). lookAttr' (meta inf)  "translation") $ G.lookup (idex (meta inf) "table_name_translation" [("schema_name" ,txt $ schemaName inf),("table_name",txt tname )]) i ) $ tmap
            (Attr _ (ArrayTB1 efields ))= lookAttr' (meta inf) "event" e
            (Attr _ color )= lookAttr' (meta inf) "color" e
        evdb <- refTable inf  (lookTable inf tname )
        let toLocalTime = fmap to
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
        return ((lookDesc,(color,tname,efields)), fmap proj  . G.toList <$> collectionTid evdb  )) ( G.toList evMap)

    iday <- liftIO getCurrentTime
    filterInp <- UI.input # set UI.style [("width","100%")]
    filterInpBh <- stepper "" (UI.valueChange filterInp)
    let allTags =  (fst <$> dashes)
    itemListEl2 <- mapM (\i ->
      (i,) <$> UI.div  # set UI.style [("width","100%"),("height","150px") ,("overflow-y","auto")]) allTags
    let
        filterLabel d = (\j ->  L.isInfixOf (toLower <$> j) (toLower <$> d)) <$> filterInpBh
        legendStyle  table (b,_)
            =  do
              let item = M.lookup (tableName (fromJust $ M.lookup table (pkMap inf))) (M.fromList  $ fmap (\i@(t,(a,b,c))-> (b,i)) allTags)
              maybe (UI.div) (\(k@(t,(c,_,_))) -> mdo
                expand <- UI.input # set UI.type_ "checkbox" # sink UI.checked evb # set UI.class_ "col-xs-1"
                let evc = UI.checkedChange expand
                evb <- stepper False evc
                missing <- (element $ fromJust $ M.lookup k (M.fromList $  itemListEl2)) # sink UI.style (noneShow <$> evb)
                header <- UI.div
                  # set items [element b # set UI.class_"col-xs-1", UI.div # set text  t # set UI.class_ "col-xs-10", element expand ]
                  # set UI.style [("background-color",renderShowable c)]
                UI.div # set children [header,missing]
                  ) item
    calendar <- UI.div # set UI.class_ "col-xs-10"
    element body # set children [calendar]
    let calFun ((agenda,day,res),selected) = mdo
            let
              capitalize (i:xs) = toUpper i : xs
              capitalize [] = []
              transMode _ "month" = "month"
              transMode True i = "agenda" <> capitalize i
              transMode False i = "basic" <> capitalize i
              mode = transMode agenda res
              inRange "day" d (SDate c)=   d == c
              inRange "week" d (SDate c)=    oy == cy && ow == cw
                where
                  (oy,ow,_) = toWeekDate d
                  (cy,cw,_) = toWeekDate c
              inRange "month" d (SDate c)=   oy == cy && od == cd
                where
                  (oy,od,_) = toGregorian d
                  (cy,cd,_) = toGregorian c
              inRange m d (STimestamp c)=   inRange m d (SDate (localDay (utcToLocalTime utc $ localTimeToUTC cliZone c)))
              selectedData = filter ((flip L.elem selected) . fst) dashes
            innerCalendar  <- UI.div # set UI.style [("min-height","400px")]
            element calendar # set children [innerCalendar]
            calendarCreate mode innerCalendar (show day)
            onEvent (UI.hover innerCalendar) (const $ do
                    runFunction $ ffi "$(%1).fullCalendar('render')" innerCalendar )
            let
              evd = eventDrop innerCalendar
              evr = eventResize innerCalendar
              evdd = eventDragDrop innerCalendar
              evs =  fmap (makePatch cliZone . first (readPK inf . T.pack))<$> unions [evr,evdd,evd]
            fin <- onEvent evs (liftIO . transaction inf . mapM (\i -> do
                        patchFrom i >>= traverse (tell . pure )))
            fins <- mapM (\((_,(_,t,_)),s)->  fmap snd $ mapUITEventFin innerCalendar (
                      (\i -> do
                      calendarAddSource innerCalendar  (T.unpack t) ((T.unpack . TE.decodeUtf8 .  BSL.toStrict . A.encode  . filter (inRange res (utctDay day ) . unTB1 . fromJust .  M.lookup "start"  ) . concat . fmap (lefts.snd) $ i)))
                      ) s ) selectedData
            liftIO $ addFin innerCalendar (fin:fins)
            mapM (\(k,el) -> do
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

    let inpCal = ((,)
          <$>  calendarSelT
          <*> ((\i j -> filter (flip L.elem (tableName <$> concat (F.toList i)) .  (^. _2._2)) j )<$> sel <*> pure allTags)
          )
    (bh,fin) <- mapUITEventFin calendar calFun inpCal

    liftIO $ do
      mapConcurrently (\(tdesc ,(_,tname,fields))-> do
          mapTEvent  (\cal@(_,incrementT,resolution) ->  do

                   forkIO $ void $ transactionNoLog  inf $ selectFromA (tname) Nothing Nothing []  (WherePredicate $ timePred ((\(TB1 (SText v))->  lookKey inf tname v) <$> fields ) cal)) calendarSelT
        ) allTags
    return  (legendStyle , dashes )

txt = TB1. SText


type DateChange  =  (String,Either (Interval UTCTime ) UTCTime)

-- readPosition:: EventData -> Maybe DateChange
readPosition  v =
 ( let [i,a,e]  = unsafeFromJSON v
   in (,) <$> Just i <*> ((\i j ->  Left $ Interval.interval (Interval.Finite i,True) (Interval.Finite j,True))<$> parseISO8601 a <*> parseISO8601 e)) <|>  (let [i,a] = unsafeFromJSON v in (,) <$> Just i <*> (Right <$> parseISO8601 a ))


eventDrop :: Element -> Event DateChange
eventDrop el = filterJust $ readPosition <$>  domEvent "eventDrop" el

eventDragDrop :: Element -> Event DateChange
eventDragDrop el = filterJust $ readPosition <$>  domEvent "externalDrop" el

eventResize :: Element -> Event DateChange
eventResize el = filterJust $ readPosition <$>  domEvent "eventResize" el

