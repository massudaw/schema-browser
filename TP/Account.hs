{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module TP.Account where

import GHC.Stack
import TP.View
import Data.Ord
import Utils
import Step.Host
import Control.Lens (_1,_2,(^.))
import qualified Data.Interval as Interval
import Control.Concurrent
import Types.Patch
import Control.Arrow
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


accountWidget body calendarSelT sel inf = do
    (_,(_,tmap)) <- liftIO $ transactionNoLog (meta inf) $ selectFrom "table_name_translation" Nothing Nothing [] (LegacyPredicate[("=",liftField (meta inf) "table_name_translation" $ uncurry Attr $("schema_name",TB1 $ SText (schemaName inf) ))])
    (evdb,(_,emap )) <- liftIO $ transactionNoLog  (meta inf) $ selectFrom "event" Nothing Nothing [] (LegacyPredicate[("=",liftField (meta inf) "event" $ uncurry Attr $("schema_name",TB1 $ SText (schemaName inf) ))])
    (evdb,(_,aMap )) <- liftIO $ transactionNoLog  (meta inf) $ selectFrom "accounts" Nothing Nothing [] (LegacyPredicate[("=",liftField (meta inf) "accounts" $ uncurry Attr $("schema_name",TB1 $ SText (schemaName inf) ))])
    cliZone <- jsTimeZone
    dashes <- liftIO $ mapConcurrently (\e -> do
        let (Attr _ (TB1 (SText tname))) = lookAttr' (meta inf) "table_name" e
            lookDesc = (\i  -> maybe (T.unpack $ tname)  ((\(Attr _ v) -> renderShowable v). lookAttr' (meta inf)  "translation") $ G.lookup (idex (meta inf) "table_name_translation" [("schema_name" ,txt $ schemaName inf),("table_name",txt tname )]) i ) $ tmap
            (Attr _ (ArrayTB1 efields )) =lookAttr' (meta inf)  "event" $ fromJust $ G.lookup (idex (meta inf) "event" [("schema_name" ,txt $ schemaName inf),("table_name",txt tname )])  emap
            (Attr _ (ArrayTB1 afields ))= lookAttr' (meta inf) "account" e
            (Attr _ color )= lookAttr' (meta inf) "color" e
        evdb <- refTable inf  (lookTable inf tname )
        let toLocalTime = fmap to
              where to (STimestamp i )  = STimestamp $  utcToLocalTime cliZone $ localTimeToUTC utc i
                    to (SDate i ) = SDate i
            convField ((IntervalTB1 i )) = [("start", toLocalTime $ unFinite $ Interval.lowerBound i),("end",toLocalTime $ unFinite $ Interval.upperBound i)]
            convField (LeftTB1 i) = concat $   convField <$> maybeToList i
            convField (v) = [("start",toLocalTime $v)]
            convField i = errorWithStackTrace (show i)
            projf  r efield@(TB1 (SText field)) afield@(TB1 (SText aafield))  = (if (isJust . unSOptional $ attr) then Left else Right) (M.fromList $ convField attr  <> [("id", TB1 $ SText $ writePK r efield   ),("title",TB1 $ SText (T.pack $  L.intercalate "," $ fmap renderShowable $ allKVRec' $  r)) , ("table",TB1 (SText tname)),("color" , color),("field", efield ), ("commodity", accattr )] :: M.Map Text (FTB Showable))
                  where attr  = attrValue $ lookAttr' inf field r
                        accattr  = attrValue $ lookAttr' inf aafield r
            proj r = (TB1 $ SText (T.pack $  L.intercalate "," $ fmap renderShowable $ allKVRec' $  r),)$  zipWith (projf r) ( F.toList efields) (F.toList afields)
            attrValue (Attr k v) = v
        return ((lookDesc,(color,tname,efields,afields)), fmap proj  . G.toList <$> collectionTid evdb  )) ( G.toList aMap)

    let allTags =  (fst <$> dashes)
    itemListEl2 <- mapM (\i ->
      (i,) <$> UI.div  # set UI.style [("width","100%"),("height","150px") ,("overflow-y","auto")]) allTags
    let
        legendStyle table (b,_)
            =  do
              let item = M.lookup (tableName (fromJust $ M.lookup table (pkMap inf))) (M.fromList  $ fmap (\i@(t,(a,b,_,c))-> (b,i)) allTags)
              maybe UI.div (\k@(t,(c,_,_,_)) ->   mdo
                expand <- UI.input # set UI.type_ "checkbox" # sink UI.checked evb # set UI.class_ "col-xs-1"
                let evc = UI.checkedChange expand
                evb <- stepper False evc
                missing <- (element $ fromJust $ M.lookup k (M.fromList itemListEl2)) # sink UI.style (noneShow <$> evb)
                header <- UI.div
                  # set items [element b # set UI.class_"col-xs-1", UI.div # set text  t # set UI.class_ "col-xs-10", element expand ]
                  # set UI.style [("background-color",renderShowable c)]
                UI.div # set children [header,missing]) item

    calendar <- UI.div # set UI.class_ "col-xs-10"
    element body # set children [calendar]

    let calFun ((agenda,iday,res ),selected) = do
            let

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
            let
                visible =  mergeData selectedData
                mergeData selectedData = fmap  concat $ foldr (liftA2 (:)) (pure []) $ snd <$> selectedData
                selectedData = filter (flip L.elem (selected) . fst) dashes
                calHand innerCalendar  visible = do
                  return ()
            innerCalendarSet <- M.fromList <$> mapM (\((_,(_,i,_,_)),s) -> (i,) <$> UI.table)  selectedData
            innerCalendar  <- UI.div # set children (F.toList innerCalendarSet)
            element calendar # set children [innerCalendar]
            calHand innerCalendar  =<< currentValue   (facts visible)
            fins <- mapM (\((cap,(_,t,_,_)),s)->  fmap snd $ mapUITEventFin (fromJust $ M.lookup t innerCalendarSet) (
                      (\i -> do
                      let caption =  UI.caption # set text cap
                          header = UI.tr # set items [UI.th # set text "Date" , UI.th # set text "Title" ,UI.th # set text "Commodity"]
                          row i = UI.tr # set items [UI.td # set text (maybe "" renderShowable $ M.lookup "start" i), UI.td # set text (maybe "" renderShowable $ M.lookup "title" i), UI.td # set text (maybe "" renderShowable $ M.lookup "commodity" i)]
                          body = fmap row dat
                          dat = L.sortBy (comparing (M.lookup "start")) $filter (inRange res (utctDay iday ) . unTB1 . fromJust . M.lookup "start") . concat .fmap (lefts  .snd)  $ i
                      element (fromJust $ M.lookup t innerCalendarSet) # set items (caption:header:body))
                      ) s ) selectedData
            liftIO $ addFin innerCalendar (fins)
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
                        ) . filter (not .L.null .snd) . fmap (fmap rights) <$> facts t) # set UI.style [("border","solid 1px black")])  $ M.lookup k (M.fromList selectedData) ) itemListEl2
            return ()
    (_,fin) <- mapUITEventFin calendar calFun ((,)
        <$> calendarSelT
        <*> ((\i j -> filter (flip L.elem (tableName <$> concat (F.toList i)) .  (^. _2._2)) j )<$> sel <*> pure allTags)
        )
    liftIO$ addFin calendar [fin]

    liftIO $ mapM (\(tdesc ,(_,tname,efields,afields))-> do
      mapTEvent
        (\cal ->  do
          forkIO $ void $ transactionNoLog  inf $ selectFromA (tname) Nothing Nothing [] (WherePredicate $ timePred efields cal ))
        calendarSelT
      ) allTags
    return (legendStyle,dashes)

txt = TB1. SText


