{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE Arrows #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module TP.Chart (chartDef,chartWidget,chartWidgetMetadata) where

import GHC.Stack
import Data.Ord
import Environment
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
import qualified Data.HashMap.Strict as HM
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

chartDef inf
  = projectV
     (innerJoinR
        (leftJoinR
          (leftJoinR
            (leftJoinR
              (innerJoinR
                (fromR "tables" schemaPred)
                (fromR "metrics" schemaPred) schemaI "metric")
              (fromR "geo" schemaPred ) schemaI "geo")
            (fromR "event" schemaPred) schemaI "event")
          (fromR "table_description" schemaNamePred ) [Rel "schema_name" Equals "table_schema", Rel "table_name" Equals "table_name"] "description")
        (fromR "pks" schemaNamePred2 ) [Rel "schema_name" Equals "schema_name", Rel "table_name" Equals "table_name"]  "pks") fields
  where
    schemaNamePred2 = [(keyRef "schema_name",Left (txt $schemaName inf ,Equals))]
    schemaPred = [(keyRef "schema",Left (int (schemaId inf),Equals))]
    schemaNamePred = [(keyRef "table_schema",Left (txt (schemaName inf),Equals))]
    schemaI = [Rel "schema" Equals "schema", Rel "oid" Equals "table"]
    schemaN = [Rel "schema_name" Equals "table_schema", Rel "table_name" Equals "table_name"]
    fields =  proc t -> do
      SText tname <-
          ifield "table_name" (ivalue (readV PText))  -< ()
      mfields <- iinline "metric" (irecord $ ifield "metrics" (imap $ ivalue $  readV PText)) -< ()
      gfields <- iinline "geo" (iopt $ irecord (iinline "features" (imap $ irecord (ifield  "geo" ( ivalue $  readV PText))))) -< ()
      evfields <- iinline "event" (iopt $ irecord (iforeign [Rel "schema" Equals "schema" , Rel "table" Equals "table", Rel "column" Equals "oid"] (imap $ irecord (ifield  "column_name" (ivalue $  readV PText))))) -< ()
      desc <- iinline "description" (iopt $  irecord (ifield "description" (imap $ ivalue $  readV PText))) -< ()
      pksM <- iinline "pks" (irecord (ifield "pks" (iopt $ imap $ ivalue $  readV PText))) -< ()
      color <- iinline "metric" (irecord (ifield "color" (ivalue $ readV PText))) -< ()
      chart <- iinline "metric" (irecord (ifield "chart_type" (ivalue $ readV PText))) -< ()
      let
        proj r = do
          pks <- pksM
          values <- mapM (\(SText i)->  unSOptional =<< recLookupInf inf tname (indexerRel i) r) mfields
          let fields = fmap fromJust $ Non.filter isJust $ fmap (\(SText i) -> unSOptional =<< recLookupInf inf tname (indexerRel i) r) (fromMaybe pks desc)
          return $ fmap A.toJSON $ HM.fromList
                    [("value" :: Text,ArrayTB1  $ values )
                    ,("title",txt (T.pack $  L.intercalate "," $ renderShowable <$> F.toList fields))
                    ,("color" , TB1 color)
                    ]
      returnA -< ("#" <> renderPrim color ,lookTable inf tname,F.toList $ fmap TB1 mfields,((fmap TB1 . F.toList <$> evfields),(fmap TB1 . F.toList <$> gfields),TB1 chart),proj )


chartWidgetMetadata inf =  do
    importUI
      =<< sequence
        [js "leaflet.js"
        ,css "leaflet.css"
        ,js "leaflet-svg-markers.min.js"
        ]
    fmap F.toList $ ui $ transactionNoLog (meta inf) $ dynPK (chartDef inf)()


chartWidget (incrementT,resolutionT) (_,positionB) sel inf cliZone = do
    dashes <- chartWidgetMetadata inf
    iday <- liftIO getCurrentTime
    let
      legendStyle  lookDesc table b =
        let item = M.lookup table (M.fromList  $ fmap (\i@(a,b,c,t,_)-> (b,i)) dashes)
        in traverse (\(k@(c,tname,_,_,_)) -> do
          element b # set UI.class_"col-xs-1"
          header <- UI.div # sink text  (T.unpack .($table) <$> facts lookDesc ) # set UI.class_ "fixed-label col-xs-11"
          UI.label # set children [b,header]# set UI.style [("background-color",c),("display","-webkit-box")]
            ) item
    calendar <- UI.div # set UI.class_ "col-xs-10"
    -- element body # set children [calendar]
    let calFun (resolution,incrementT,positionB) = mdo
            edits <- ui$ accumDiff (\tref->  evalUI calendar $ do
              let
                evc = eventClick calendar
              charts <- UI.div  # set UI.style [("height", "300px"),("width", "900px")]
              calendarCreate  charts (show incrementT)
              let ref  =  (\i j ->  L.find ((== i) .  (^. _2)) j ) tref dashes
              traverse (\(_,t,fields,(timeFields,geoFields,chart),proj)-> do
                    let pred = fromMaybe mempty (fmap (\fields -> WherePredicate $  timePred inf t (fieldKey <$> fields) (incrementT,resolution)) timeFields  <> liftA2 (\field pos-> WherePredicate $ geoPred inf t(fieldKey <$>  field) pos ) geoFields positionB )
                        fieldKey (TB1 (SText v))=   v
                    reftb <- ui $ refTables' inf t Nothing pred
                    let v = reftb ^. _2
                    let evsel = (\j (tev,pk,_) -> if tev == t then Just ( G.lookup pk j) else Nothing  ) <$> facts v <@> fmap (readPK inf . T.pack ) evc
                    tdib <- ui $ stepper Nothing (join <$> evsel)
                    let tdi = tidings tdib (join <$> evsel)
                    TrivialWidget _ el <- crudUITable inf  t reftb mempty [] (allRec' (tableMap inf) t)  tdi
                    traverseUI
                      (\i -> do
                        calendarAddSource charts chart t (renderShowable <$> fields ) (T.unpack . TE.decodeUtf8 .  BSL.toStrict . A.encode  .   fmap proj $ L.sortBy (comparing (G.getIndex (tableMeta t)))$ G.toList i)
                        ui $ registerDynamic (fmap fst $ runDynamic $ evalUI charts $ calendarRemoveSource charts t))
                       v
                    element el # sink UI.style  (noneShow . isJust <$> tdib)
                    UI.div # set children [charts,el] # set UI.class_ "row"
                                   ) ref) sel

            element calendar # sink children ( catMaybes .F.toList <$> facts edits)
        exec = do
          onFFI "google.charts.setOnLoadCallback(%1)" (evalUI calendar $ traverseUI calFun ((,,) <$> resolutionT <*> incrementT <*> positionB))
          return [calendar]

    return  (legendStyle , dashes ,exec)



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
