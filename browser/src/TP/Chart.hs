{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE Arrows #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module TP.Chart (chartDef,chartWidget,chartWidgetMetadata) where

import Environment
import qualified NonEmpty as Non
import Step.Host
import Control.Monad.Writer as Writer
import TP.View
import qualified Data.Interval as Interval
import Control.Arrow
import Control.Lens ((^.), _2)
import qualified Data.List as L
import Data.Interval (Interval(..))
import Data.Time.ISO8601
import qualified Data.Text.Encoding as TE
import Data.Time
import qualified Data.Aeson as A
import Text
import qualified Types.Index as G
import Types
import SchemaQuery
import TP.Widgets
import qualified Data.HashMap.Strict as HM
import Data.Maybe
import Reactive.Threepenny
import qualified Data.ByteString.Lazy.Char8 as BSL
import RuntimeTypes
import qualified Graphics.UI.Threepenny as UI
import Graphics.UI.Threepenny.Core
import qualified Data.Foldable as F
import qualified Data.Text as T
import Data.Text (Text)
import qualified Data.Map as M


instance ToJS (FTB Showable) where
  render  = return .JSCode . BSL.unpack . A.encode

chartCreate = runFunction . ffi "createChart(%1)"
chartAddSource cal chart t fields evs = runFunction $ ffi "addChartColumns(%1,%2,%3,%4,%5)" cal (tableName t) fields evs chart
chartRemoveSource cal t = runFunction $ ffi "removeChartColumns(%1,%2)" cal (tableName t)


chartDef inf
  = projectV
     (innerJoinR
        (leftJoinR
          (leftJoinR
            (leftJoinR
              (innerJoinR
                (fromR "tables" `whereR` schemaPred)
                (fromR "metrics" `whereR` schemaPred) schemaI "metric")
              (fromR "geo" `whereR` schemaPred ) schemaI "geo")
            (fromR "event" `whereR` schemaPred) schemaI "event")
          (fromR "table_description" `whereR` schemaNamePred ) [Rel "schema_name" Equals "table_schema", Rel "table_name" Equals "table_name"] "description")
        (fromR "pks" `whereR` schemaNamePred2 ) [Rel "schema_name" Equals "schema_name", Rel "table_name" Equals "table_name"]  "pks") fields
  where
    schemaNamePred2 = [(keyRef "schema_name",Left (txt $schemaName inf ,Equals))]
    schemaPred = [(keyRef "schema",Left (int (schemaId inf),Equals))]
    schemaNamePred = [(keyRef "table_schema",Left (txt (schemaName inf),Equals))]
    schemaI = [Rel "schema" Equals "schema", Rel "oid" Equals "table"]
    schemaN = [Rel "schema_name" Equals "table_schema", Rel "table_name" Equals "table_name"]
    fields =  irecord $ proc t -> do
      SText tname <-
          ifield "table_name" (ivalue (readV PText))  -< ()
      mfields <- iinline "metric" (ivalue $ irecord $ ifield "metrics" (imap $ ivalue $  readV PText)) -< ()
      gfields <- iinline "geo" (iopt $ ivalue $ irecord (iinline "features" (imap $ ivalue $ irecord (ifield  "geo" ( ivalue $  readV PText))))) -< ()
      evfields <- iinline "event" (iopt $ ivalue $ irecord (iforeign [Rel "schema" Equals "schema" , Rel "table" Equals "table", Rel "column" Equals "oid"] (imap $ ivalue $ irecord (ifield  "column_name" (ivalue $  readV PText))))) -< ()
      desc <- iinline "description" (iopt $  ivalue $ irecord (ifield "description" (imap $ ivalue $  readV PText))) -< ()
      pks <- iinline "pks" (ivalue $ irecord (iforeign [Rel "schema_name" Equals "schema_name" , Rel "table_name" Equals "table_name", Rel "pks" Equals "column_name"] (imap $ ivalue $ irecord (ifield  "column_name" (ivalue $  readV PText))))) -< ()
      color <- iinline "metric" (ivalue $ irecord (ifield "color" (ivalue $ readV PText))) -< ()
      chart <- iinline "metric" (ivalue $ irecord (ifield "chart_type" (ivalue $ readV PText))) -< ()
      let
        proj r = do
          values <- mapM (\(SText i)->  unSOptional =<< recLookupInf inf tname (indexerRel i) r) mfields
          let fields = fmap fromJust $ filter isJust $ F.toList $ fmap (\(SText i) -> unSOptional =<< recLookupInf inf tname (indexerRel i) r) (fromMaybe pks desc)
          return $ A.toJSON <$> HM.fromList
                    [("value" :: Text,ArrayTB1 values)
                    ,("title",txt (T.pack $  L.intercalate "," $ renderShowable <$> fields))
                    ,("color" , TB1 color)
                    ]
      returnA -< ("#" <> renderPrim color ,lookTable inf tname,F.toList $ fmap TB1 mfields,(fmap TB1 . F.toList <$> evfields,fmap TB1 . F.toList <$> gfields,TB1 chart),proj )


chartWidgetMetadata inf =  do
    importUI
      =<< sequence
        [js "leaflet.js"
        ,css "leaflet.css"
        ,js "leaflet-svg-markers.min.js"
        ]
    fmap F.toList $ ui $ transactionNoLog (meta inf) $ dynPK (chartDef inf) ()

chartWidget (incrementT,resolutionT) (_,positionB) sel inf cliZone = do
    dashes <- chartWidgetMetadata inf
    iday <- liftIO getCurrentTime
    let
      legendStyle  lookDesc table b =
        let item = M.lookup table (M.fromList  $ fmap (\i@(a,b,c,t,_)-> (b,i)) dashes)
        in traverse (\k@(c,tname,_,_,_)-> do
          element b # set UI.class_"col-xs-1"
          header <- UI.div # set text  (T.unpack  lookDesc ) # set UI.class_ "fixed-label col-xs-11"
          UI.label # set children [b,header]# set UI.style [("background-color",c),("display","-webkit-box")]
            ) item
    chart <- UI.div # set UI.class_ "col-xs-10"
    let
      calFun (resolution,incrementT,positionB) = do
        edits <- ui$ accumDiff (\tref->  evalUI chart $ do
          charts <- UI.div # set UI.class_ "row" # set UI.style [("height", "300px"),("width", "900px")]
          chartCreate  charts
          let ref  =  (\i j ->  L.find ((== i) .  (^. _2)) j ) tref dashes
          F.traverse_ (\(_,t,fields,(timeFields,geoFields,chart),proj)-> do
                let pred = fromMaybe mempty (fmap (\fields -> WherePredicate $  timePred inf t (fieldKey <$> fields) (incrementT,resolution)) timeFields  <> liftA2 (\field pos-> WherePredicate $ geoPred inf t(fieldKey <$>  field) pos ) geoFields positionB )
                    fieldKey (TB1 (SText v))=   v
                reftb <- ui $ refTables' inf t Nothing pred
                let v = primary <$> reftb ^. _2
                traverseUI
                  (\i -> do
                    chartAddSource charts chart t (renderShowable <$> fields ) (T.unpack . TE.decodeUtf8 .  BSL.toStrict . A.encode  .   fmap proj $ L.sortOn (G.getIndex (tableMeta t)) $ G.toList i)
                    ui $ registerDynamic (fmap fst $ runDynamic $ evalUI charts $ chartRemoveSource charts t)) v
                               ) ref
          return charts) sel

        element chart # sink children (F.toList <$> facts edits)
      exec =   do
        v <- traverseUI calFun ((,,) <$> resolutionT <*> incrementT <*> positionB)
        pure <$> UI.div # sink children (pure <$> facts v)

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


