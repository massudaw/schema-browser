{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module TP.Chart (chartWidget,chartWidgetMetadata) where

import GHC.Stack
import Data.Ord
import qualified NonEmpty as Non
import Step.Host
import Control.Monad.Writer as Writer
import TP.View
import qualified Data.Interval as Interval
import Control.Concurrent
import Utils
import Types.Patch
import Control.Arrow
import Control.Lens ((^.), _1, mapped,_2, _3,_4,_5)
import qualified Data.List as L
import Data.Either
import Data.Interval (Interval(..))
import Data.Time.ISO8601
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


instance ToJS (FTB Showable ) where
  render  = return .JSCode . BSL.unpack . A.encode

calendarCreate cal def = runFunction $ ffi "createChart(%1,%2)" cal def
calendarAddSource cal chart t fields evs = runFunction $ ffi "addChartColumns(%1,%2,%3,%4,%5)" cal (tableName t) fields evs chart
calendarRemoveSource cal t = runFunction $ ffi "removeChartColumns(%1,%2)" cal (tableName t)

chartWidgetMetadata inf = do
  let
      schId = int (schemaId inf)
      schemaPred = [(keyRef "schema",Left (schId,Equals))]
      rel = [Rel "schema" Equals "schema", Rel "table" Equals "table"]
  ui$ transactionNoLog  (meta inf) $ do
      (_,minf,evMap) <-fromTable "metrics" schemaPred
          >>= joinTable "event" rel "event" schemaPred
          >>= joinTable "geo" rel "geo" schemaPred
      return $ fmap (\e ->
        let
          TB1 (SText tname) = lookAttr' "table_name" $ unTB1 $  lookRef ["schema","table"] e
          table = lookTable inf tname
          Just (Attr _ (ArrayTB1 efields )) = indexField (liftAccess (meta inf )"metrics" $ keyRef "metrics") e
          Just (Attr _ chart) = indexField (liftAccess (meta inf )"metrics" $ keyRef "chart_type") e
          timeFields = fmap unArray . join . fmap unSOptional $ indexFieldRec (liftAccess (meta inf )"event" $ Nested [keyRef "event"] $ One $ Nested [keyRef "schema",keyRef "table",keyRef "column"] (One $ keyRef "column_name")) e
          geoFields = fmap unArray . join . fmap unSOptional $ indexFieldRec (liftAccess (meta inf )"geo" $ Nested [keyRef "geo"] $ One $ Nested [keyRef "schema",keyRef "table",keyRef "column"] (One $ keyRef "column_name")) e
          color = lookAttr'  "color" e
          projf  r efield  = M.fromList [("value" ,ArrayTB1 $  attr <$> efield), ("title",txt (T.pack $  L.intercalate "," $ fmap renderShowable $ allKVRec' inf (tableMeta table) r)) , ("table",txt tname),("color" , txt $ T.pack $ "#" <> renderShowable color )] :: M.Map Text (FTB Showable)
            where attr  (TB1 (SText field)) = _tbattr $ justError ("no attr " <> show field) (findAttr (lookKey inf tname field) r)
          proj r = (txt (T.pack $  L.intercalate "," $ fmap renderShowable $ allKVRec' inf (tableMeta table)$  r),)$  projf r efields
          attrValue (Attr k v) = v
       in (txt $ T.pack $ "#" <> renderShowable color ,table ,F.toList efields,(timeFields,geoFields,chart),proj) ) ( G.toList evMap)

chartWidget body (incrementT,resolutionT) (_,positionB) sel inf cliZone = do
    dashes <- chartWidgetMetadata inf
    iday <- liftIO getCurrentTime
    let
      legendStyle  lookDesc table b =
        let item = M.lookup table (M.fromList  $ fmap (\i@(a,b,c,t,_)-> (b,i)) dashes)
        in traverse (\(k@(c,tname,_,_,_)) -> do
          element b # set UI.class_"col-xs-1"
          header <- UI.div # sink text  (T.unpack .($table) <$> facts lookDesc ) # set UI.class_ "fixed-label col-xs-11"
          UI.label # set children [b,header]# set UI.style [("background-color",renderShowable c),("display","-webkit-box")]
            ) item
    calendar <- UI.div # set UI.class_ "col-xs-10"
    element body # set children [calendar]
    let calFun (resolution,incrementT,positionB) = mdo
            let
              evc = eventClick calendar
            edits <- ui$ accumDiff (\tref->  evalUI calendar $ do
              charts <- UI.div  # set UI.style [("height", "300px"),("width", "900px")]
              calendarCreate  charts (show incrementT)
              let ref  =  (\i j ->  L.find ((== i) .  (^. _2)) j ) tref dashes
              traverse (\(_,t,fields,(timeFields,geoFields,chart),proj)-> do
                    let pred = fromMaybe mempty (fmap (\fields -> WherePredicate $  timePred inf t (fieldKey <$> fields) (incrementT,resolution)) timeFields  <> liftA2 (\field pos-> WherePredicate $ geoPred inf t(fieldKey <$>  field) pos ) geoFields positionB )
                        fieldKey (TB1 (SText v))=   v
                    reftb <- ui $ refTables' inf t Nothing pred
                    let v = reftb ^. _3
                    let evsel = (\j (tev,pk,_) -> if tev == t then Just ( G.lookup pk j) else Nothing  ) <$> facts v <@> fmap (readPK inf . T.pack ) evc
                    tdib <- ui $ stepper Nothing (join <$> evsel)
                    let tdi = tidings tdib (join <$> evsel)
                    (el,_) <- crudUITable inf  t reftb mempty [] (allRec' (tableMap inf) t)  tdi
                    traverseUI
                      (\i -> do
                        calendarAddSource charts chart t (renderShowable <$> fields ) (T.unpack . TE.decodeUtf8 .  BSL.toStrict . A.encode  .   fmap (snd.proj) $ L.sortBy (comparing (G.getIndex (tableMeta t)))$ G.toList i)
                        ui $ registerDynamic (fmap fst $ runDynamic $ evalUI charts $ calendarRemoveSource charts t))
                       v
                    element el # sink UI.style  (noneShow . isJust <$> tdib)
                    UI.div # set children [charts,el] # set UI.class_ "row"
                                   ) ref) sel

            element calendar # sink children ( catMaybes .F.toList <$> facts edits)
    onFFI "google.charts.setOnLoadCallback(%1)" (evalUI body $  traverseUI calFun ((,,) <$> resolutionT <*> incrementT <*> positionB))
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
