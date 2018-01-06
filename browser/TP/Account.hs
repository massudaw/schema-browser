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



accountWidgetMeta inf = do
    let
      schId = int (schemaId inf)
      schemaPred = [(keyRef "schema",Left (schId,Equals))]
    (_,minf,amap) <- ui $ transactionNoLog  (meta inf) $ fromTable "accounts" schemaPred >>= joinTable "event" [Rel "schema" Equals "schema", Rel "table" Equals "table"]  "event" schemaPred
    cliZone <- jsTimeZone
    return $ fmap (\e ->
          let
              (TB1 (SText tname)) =  lookAttr' "table_name" $ unTB1 $ lookRef  ["schema","table"] e
              table = lookTable  inf tname
              Just (ArrayTB1 efields ) = join $ fmap unSOptional $ indexFieldRec (liftAccess minf "accounts" $ Nested [keyRef "event"] $ One $ Nested [keyRef "schema",keyRef "table",keyRef "column"] (One $ keyRef "column_name")) e
              (ArrayTB1 afields )= lookAttr' "account" e
              color =  lookAttr'  "color" e
              toLocalTime = fmap to
                where to (STime (STimestamp i ))  = STime (STimestamp $ localTimeToUTC utc $  utcToLocalTime cliZone   i)
                      to (STime (SDate i )) = STime (SDate i)
              convField ((IntervalTB1 i )) = catMaybes [fmap (("start",). toLocalTime )$ unFinite $ Interval.lowerBound i,fmap (("end",).toLocalTime )$ unFinite $ Interval.upperBound i]
              convField (LeftTB1 i) = concat $   convField <$> maybeToList i
              convField (v) = [("start",toLocalTime $v)]
              convField i = errorWithStackTrace (show i)
              projf  r efield@(TB1 (SText field)) afield@(TB1 (SText aafield))  = (if (isJust . unSOptional $ attr) then Left else Right) (M.fromList $ convField attr  <> [("id", txt $ writePK (tableMeta table) r efield   ),("title",txt (T.pack $  L.intercalate "," $ fmap renderShowable $ allKVRec' inf (tableMeta table)$  r)) , ("table",TB1 (SText tname)),("color" , color),("field", efield ), ("commodity", accattr )] :: M.Map Text (FTB Showable))
                    where attr = lookAttr' field r
                          accattr  = lookAttr' aafield r
              proj r = (txt (T.pack $  L.intercalate "," $ fmap renderShowable $ allKVRec' inf (tableMeta table)$  r),)$  zipWith (projf r) ( F.toList efields) (F.toList afields)
           in ((color,table,efields,afields,proj))  ) ( G.toList amap)



accountWidget body (incrementT,resolutionT) sel inf = do
    let
      calendarSelT = liftA2 (,) incrementT resolutionT

    dashes <- accountWidgetMeta inf
    let allTags =  dashes
    itemListEl2 <- mapM (\i ->
      (i^. _2,) <$> UI.div  # set UI.style [("width","100%"),("height","150px") ,("overflow-y","auto")]) dashes
    let
        legendStyle lookDesc table b
            =  do
              let item = M.lookup table  (M.fromList  $ fmap (\i@((_,b,_,_,_))-> (b,i)) dashes )
              traverse (\k@((c,tname,_,_,_)) ->   mdo
                header <-  UI.div # sink text  (T.unpack . ($table) <$> facts lookDesc) # set UI.class_ "col-xs-11"
                element b # set UI.class_ "col-xs-1"
                UI.label # set children [b,header]
                         # set UI.style [("background-color",renderShowable c)] # set UI.class_ "table-list-item" # set UI.style [("display","-webkit-box")]
                ) item
    calendar <- UI.div # set UI.class_ "col-xs-10"
    element body # set children [calendar]

    let
      calFun selected = do
          innerCalendarSet <- M.fromList <$> mapM (\a -> (a^._2,) <$> UI.table)  selected
          innerCalendar  <- UI.div # set children (F.toList innerCalendarSet)
          element calendar # set children [innerCalendar]
          _ <- mapM (\((_,table,fields,efields,proj))->  traverseUI
            (\calT -> do
              let pred = WherePredicate $ timePred inf table (fieldKey <$> fields ) calT
                  fieldKey (TB1 (SText v))=   v
              (v,_) <-  ui $ transactionNoLog  inf $ selectFromA (tableName table) Nothing Nothing [] pred
              traverseUI
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
    _ <- traverseUI calFun ((\i j -> filter (flip L.elem ((F.toList i)) .  (^. _2)) j )<$> sel <*> pure dashes)


    return (legendStyle,dashes)


