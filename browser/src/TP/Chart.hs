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
  = projectS
      (leftJoinS
        (leftJoinS
          (innerJoinS
            (tableDef inf `whereS` schemaPred)
            (fromS "metrics" ) (schemaI "metrics"))
          (fromS "geo" ) (schemaI "geo"))
        (fromS "event" ) (schemaI "event")) fields
  where
    schemaPred = [(keyRef "schema",Left (int (schemaId inf),Equals))]
    schemaI t = [Rel "oid" Equals (NInline t "table")]
    fields =  irecord $ proc t -> do
      (tname,desc,_,pks) <- tableProj inf -< ()
      mfields <- iforeign (schemaI "metrics")  (ivalue $ irecord $ ifield "metrics" (imap $ ivalue $  readV PText)) -< ()
      gfields <- iforeign (schemaI "geo") (iopt $ ivalue $ irecord (iinline "features" (imap $ ivalue $ irecord (ifield  "geo" ( ivalue $  readV PText))))) -< ()
      evfields <- iforeign (schemaI "event") (iopt $ ivalue $ irecord (iforeign [Rel "column" (AnyOp Equals) "ordinal_position"] (imap $ ivalue $ irecord (ifield  "column_name" (ivalue $  readV PText))))) -< ()
      color <- iforeign (schemaI "metrics") (ivalue $ irecord (ifield "color" (ivalue $ readV PText))) -< ()
      chart <- iforeign (schemaI "metrics") (ivalue $ irecord (ifield "chart_type" (ivalue $ readV PText))) -< ()
      let
        proj r = do
          values <- mapM (\(SText i)->  unSOptional =<< recLookupInf inf tname (indexerRel i) r) mfields
          let fields = fmap fromJust $ filter isJust $ F.toList $ fmap (\(SText i) -> unSOptional =<< recLookupInf inf tname (indexerRel i) r) (fromMaybe pks (toListTree<$> desc))
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
    fmap F.toList  . currentValue . facts  =<< ui ( transactionNoLog (meta inf) $ dynPK (chartDef inf) ())

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
          chartCreate charts
          let ref  =  (\i j ->  L.find ((== i) .  (^. _2)) j ) tref dashes
          F.traverse_ (\(_,t,fields,(timeFields,geoFields,chart),proj)-> do
                let pred = fromMaybe mempty (fmap (\fields -> WherePredicate $  timePred inf t (fieldKey <$> fields) (incrementT,resolution)) timeFields  <> liftA2 (\field pos-> WherePredicate $ geoPred inf t(fieldKey <$>  field) pos ) geoFields positionB )
                    fieldKey (TB1 (SText v))=   v
                reftb <- ui $ refTables' inf t Nothing pred
                let v = primary <$> reftb ^. _2
                traverseUI
                  (\i -> do
                    chartAddSource charts chart t (renderShowable <$> fields ) (T.unpack . TE.decodeUtf8 .  BSL.toStrict . A.encode  .   fmap proj $ L.sortOn (G.getIndex (tableMeta t)) $ G.toList i)
                    finalizerUI (chartRemoveSource charts t)) v
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


