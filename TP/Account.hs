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
import Control.Lens (_2,(^.))
import qualified Data.Interval as Interval
import Control.Concurrent
import Types.Patch
import Control.Arrow
import Data.Either
import Data.Interval (Interval(..))
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


accountWidget body (agendaT,incrementT,resolutionT)sel inf = do
    let calendarSelT = liftA3 (,,) agendaT incrementT resolutionT

    (_,(_,tmap)) <- liftIO $ transactionNoLog (meta inf) $ selectFrom "table_name_translation" Nothing Nothing [] (LegacyPredicate[("=",liftField (meta inf) "table_name_translation" $ uncurry Attr $("schema_name",TB1 $ SText (schemaName inf) ))])
    (_,(_,emap )) <- liftIO $ transactionNoLog  (meta inf) $ selectFrom "event" Nothing Nothing [] (LegacyPredicate[("=",liftField (meta inf) "event" $ uncurry Attr $("schema_name",TB1 $ SText (schemaName inf) ))])
    (_,(_,aMap )) <- liftIO $ transactionNoLog  (meta inf) $ selectFrom "accounts" Nothing Nothing [] (LegacyPredicate[("=",liftField (meta inf) "accounts" $ uncurry Attr $("schema_name",TB1 $ SText (schemaName inf) ))])
    cliZone <- lift jsTimeZone
    let dashes = fmap (\e ->
          let Attr _ (TB1 (SText tname)) = lookAttr' (meta inf) "table_name" e
              lookDesc = (\i  -> maybe (T.unpack $ tname)  ((\(Attr _ v) -> renderShowable v). lookAttr' (meta inf)  "translation") $ G.lookup (idex (meta inf) "table_name_translation" [("schema_name" ,txt $ schemaName inf),("table_name",txt tname )]) i ) $ tmap
              (Attr _ (ArrayTB1 efields )) =lookAttr' (meta inf)  "event" $ fromJust $ G.lookup (idex (meta inf) "event" [("schema_name" ,txt $ schemaName inf),("table_name",txt tname )])  emap
              (Attr _ (ArrayTB1 afields ))= lookAttr' (meta inf) "account" e
              (Attr _ color )= lookAttr' (meta inf) "color" e
              toLocalTime = fmap to
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
           in (lookDesc,(color,tname,efields,afields,proj))  ) ( G.toList aMap)

    let allTags =  dashes
    itemListEl2 <- lift $ mapM (\i ->
      (i^. _2 ._2,) <$> UI.div  # set UI.style [("width","100%"),("height","150px") ,("overflow-y","auto")]) dashes
    let
        legendStyle table (b,_)
            =  do
              let item = M.lookup (tableName (fromJust $ M.lookup table (pkMap inf))) (M.fromList  $ fmap (\i@(t,(_,b,_,_,_))-> (b,i)) dashes )
              maybe UI.div (\k@(t,(c,tname,_,_,_)) ->   mdo
                expand <- UI.input # set UI.type_ "checkbox" # sink UI.checked evb # set UI.class_ "col-xs-1"
                let evc = UI.checkedChange expand
                evb <- stepper False evc
                missing <- (element $ fromJust $ M.lookup tname  (M.fromList itemListEl2)) # sink UI.style (noneShow <$> evb)
                header <- UI.div
                  # set items [element b # set UI.class_"col-xs-1", UI.div # set text  t # set UI.class_ "col-xs-10", element expand ]
                  # set UI.style [("background-color",renderShowable c)]
                UI.div # set children [header,missing]) item

    calendar <- lift $ UI.div # set UI.class_ "col-xs-10"
    lift $ element body # set children [calendar]

    let
      calFun selected = do
          innerCalendarSet <- lift $ M.fromList <$> mapM (\((_,(_,i,_,_,_))) -> (i,) <$> UI.table)  selected
          innerCalendar  <- lift $ UI.div # set children (F.toList innerCalendarSet)
          lift $ element calendar # set children [innerCalendar]
          _ <- mapM (\(cap,(_,t,fields,efields,proj))->  mapUIFinalizerT (fromJust $ M.lookup t innerCalendarSet)
            (\calT -> do
              let pred = WherePredicate $ timePred (fieldKey <$> fields ) calT
                  fieldKey (TB1 (SText v))=  lookKey inf t v
              (v,_) <-  liftIO $  transactionNoLog  inf $ selectFromA t Nothing Nothing [] pred
              mapUIFinalizerT innerCalendar
                (lift . (\i -> do
                  let caption =  UI.caption # set text cap
                      header = UI.tr # set items [UI.th # set text (L.intercalate "," $ F.toList $ renderShowable<$>  fields) , UI.th # set text "Title" ,UI.th # set text (L.intercalate "," $ F.toList $ renderShowable<$>efields) ]
                      row i = UI.tr # set items [UI.td # set text (L.intercalate "," [maybe "" renderShowable $ M.lookup "start" i , maybe "" renderShowable $ M.lookup "end" i]), UI.td # set text (maybe "" renderShowable $ M.lookup "title" i), UI.td # set text (maybe "" renderShowable $ M.lookup "commodity" i)]
                      body = fmap row dat
                      dat =  concat .fmap (lefts . snd .proj)  $ G.toList i
                  element (fromJust $ M.lookup t innerCalendarSet) # set items (caption:header:body))
                ) (collectionTid v)
                )calendarSelT
              ) selected
          return ()
    _ <- mapUIFinalizerT calendar calFun (((\i j -> filter (flip L.elem (tableName <$> concat (F.toList i)) .  (^. _2._2)) j )<$> sel <*> pure dashes)
        )

    return (legendStyle,dashes)

txt = TB1 . SText

