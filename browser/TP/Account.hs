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


accountWidget body (incrementT,resolutionT) sel inf = do
    let
      calendarSelT = liftA2 (,) incrementT resolutionT
      schId = int (schemaId inf)
      schemaPred = [(keyRef ["schema"],Left (schId,Equals))]

    (_,(_,emap )) <-ui $ transactionNoLog  (meta inf) $ selectFromTable "event" Nothing Nothing [] schemaPred
    (_,(_,aMap )) <-ui $ transactionNoLog  (meta inf) $ selectFromTable "accounts" Nothing Nothing [] schemaPred
    cliZone <- jsTimeZone
    let dashes = fmap (\e ->
          let
              Just (TB1 (SText tname)) = unSOptional' $ _tbattr $ lookAttr' (meta inf) "table_name" $ unTB1 $ _fkttable $ lookAttrs' (meta inf) ["schema","table"] e
              table = lookTable  inf tname
              tablId = int (_tableUnique table)
              Just (Attr _ (ArrayTB1 efields )) =indexField  (liftAccess (meta inf) "event" $ keyRef ["event"]) $ fromJust $ G.lookup (idex (meta inf) "event" [("schema" ,schId ),("table",tablId )])  emap
              (Attr _ (ArrayTB1 afields ))= lookAttr' (meta inf) "account" e
              (Attr _ color )= lookAttr' (meta inf) "color" e
              toLocalTime = fmap to
                where to (STimestamp i )  = STimestamp $  utcToLocalTime cliZone $ localTimeToUTC utc i
                      to (SDate i ) = SDate i
              convField ((IntervalTB1 i )) = catMaybes [fmap (("start",). toLocalTime )$ unFinite $ Interval.lowerBound i,fmap (("end",).toLocalTime )$ unFinite $ Interval.upperBound i]
              convField (LeftTB1 i) = concat $   convField <$> maybeToList i
              convField (v) = [("start",toLocalTime $v)]
              convField i = errorWithStackTrace (show i)
              projf  r efield@(TB1 (SText field)) afield@(TB1 (SText aafield))  = (if (isJust . unSOptional $ attr) then Left else Right) (M.fromList $ convField attr  <> [("id", txt $ writePK r efield   ),("title",txt (T.pack $  L.intercalate "," $ fmap renderShowable $ allKVRec' $  r)) , ("table",TB1 (SText tname)),("color" , color),("field", efield ), ("commodity", accattr )] :: M.Map Text (FTB Showable))
                    where attr  = attrValue $ lookAttr' inf field r
                          accattr  = attrValue $ lookAttr' inf aafield r
              proj r = (txt (T.pack $  L.intercalate "," $ fmap renderShowable $ allKVRec' $  r),)$  zipWith (projf r) ( F.toList efields) (F.toList afields)
              attrValue (Attr k v) = v
           in ((color,table,efields,afields,proj))  ) ( G.toList aMap)

    let allTags =  dashes
    itemListEl2 <- mapM (\i ->
      (i^. _2,) <$> UI.div  # set UI.style [("width","100%"),("height","150px") ,("overflow-y","auto")]) dashes
    let
        legendStyle lookDesc table b
            =  do
              let item = M.lookup table  (M.fromList  $ fmap (\i@((_,b,_,_,_))-> (b,i)) dashes )
              maybe UI.div (\k@((c,tname,_,_,_)) ->   mdo
                expand <- UI.input # set UI.type_ "checkbox" # sink UI.checked evb # set UI.class_ "col-xs-1"
                evc <-  UI.checkedChange expand
                evb <- ui $ stepper False evc
                missing <- (element $ fromJust $ M.lookup tname  (M.fromList itemListEl2)) # sink UI.style (noneShow <$> evb)
                header <- UI.div
                  # set items [element b # set UI.class_"col-xs-1", UI.div # sink text  (T.unpack . ($table) <$> facts lookDesc) # set UI.class_ "col-xs-10", element expand ]
                  # set UI.style [("background-color",renderShowable c)]
                UI.div # set children [header,missing]) item

    calendar <- UI.div # set UI.class_ "col-xs-10"
    element body # set children [calendar]

    let
      calFun selected = do
          innerCalendarSet <- M.fromList <$> mapM (\a -> (a^._2,) <$> UI.table)  selected
          innerCalendar  <- UI.div # set children (F.toList innerCalendarSet)
          element calendar # set children [innerCalendar]
          _ <- mapM (\((_,table,fields,efields,proj))->  mapUIFinalizerT (fromJust $ M.lookup table innerCalendarSet)
            (\calT -> do
              let pred = WherePredicate $ timePred inf table (fieldKey <$> fields ) calT
                  fieldKey (TB1 (SText v))=   v
              (v,_) <-  ui $ transactionNoLog  inf $ selectFromA (tableName table) Nothing Nothing [] pred
              mapUIFinalizerT innerCalendar
                ((\i -> do
                  let caption =  UI.caption -- # set text (T.unpack $ maybe (rawName t) id $ rawDescription t)
                      header = UI.tr # set items [UI.th # set text (L.intercalate "," $ F.toList $ renderShowable<$>  fields) , UI.th # set text "Title" ,UI.th # set text (L.intercalate "," $ F.toList $ renderShowable<$>efields) ]
                      row i = UI.tr # set items [UI.td # set text (L.intercalate "," [maybe "" renderShowable $ M.lookup "start" i , maybe "" renderShowable $ M.lookup "end" i]), UI.td # set text (maybe "" renderShowable $ M.lookup "title" i), UI.td # set text (maybe "" renderShowable $ M.lookup "commodity" i)]
                      body = (fmap row dat ) <> if L.null dat then [] else [totalrow totalval]
                      dat =  concat .fmap (lefts . snd .proj)  $ G.toList i

                      totalval = M.fromList [("start",mindate),("end",maxdate),("title",txt "Total") ,("commodity", totalcom)]
                        where
                          totalcom = sum $ justError "no" .M.lookup "commodity" <$> dat
                          mindate = minimum $ justError "no" . M.lookup "start" <$> dat
                          maxdate = maximum $ justError "no" . M.lookup "start" <$> dat
                      totalrow i = UI.tr # set items  (fmap (\i -> i # set UI.style [("border","solid 2px")] )[UI.td # set text (L.intercalate "," [maybe "" renderShowable $ M.lookup "start" i , maybe "" renderShowable $ M.lookup "end" i]), UI.td # set text (maybe "" renderShowable $ M.lookup "title" i), UI.td # set text (maybe "" renderShowable $ M.lookup "commodity" i)] ) # set UI.style [("border","solid 2px")]
                  element (fromJust $ M.lookup table innerCalendarSet) # set items (caption:header:body))
                ) (collectionTid v)
                )calendarSelT
              ) selected
          return ()
    _ <- mapUIFinalizerT calendar calFun ((\i j -> filter (flip L.elem (concat (F.toList i)) .  (^. _2)) j )<$> sel <*> pure dashes)


    return (legendStyle,dashes)


