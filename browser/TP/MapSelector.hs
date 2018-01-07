{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module TP.MapSelector (mapWidgetMeta,mapSelector,mapCreate,moveend,eventClick,createLayers,legendStyle) where

import Step.Host
import qualified NonEmpty as Non
import Data.String
import Foreign.JavaScript (toCode,JSFunction)
import Utils
import qualified Data.Sequence as S
import Database.PostgreSQL.Simple
import qualified Data.Interval as I
import Control.Monad.Writer as Writer
import Postgresql.Parser
import Control.Arrow (first)
import TP.View
import GHC.Stack
import Control.Concurrent
import Control.Lens ((^.),_1,_2,_3,_5)
import Safe
import Control.Concurrent.Async
import Data.Interval as Interval
import Data.Time.Calendar.WeekDate
import qualified Data.Vector as V
import Data.Char
import qualified Data.Text.Encoding as TE
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
import qualified Data.HashMap.Strict as HM

removeLayers el tname = runFunction $ ffi "removeLayer(%1,%2)" el tname
createBounds el tname evs= runFunction $ ffi "createBounds(%1,%3,%2)" el evs tname
createLayers el tname evs= runFunction $ ffi "createLayer(%1,%3,%2)" el evs tname
mapCreate el Nothing = runFunction $ ffi "createMap(%1,null,null,null)" el
mapCreate el (Just (ne,sw)) = runFunction $ ffi "createMap(%1,%2,%3,null)" el  (show ne) (show sw)

idx inf m c k = indexField ( liftAccess inf (_kvname m) (keyRef c))  k

mapWidgetMeta  inf =  do
    importUI
      =<< sequence
        [js "leaflet.js"
        ,css "leaflet.css"
        ,js "leaflet-svg-markers.min.js"
        ]
    let
      schemaPred = [(keyRef "schema",Left (int (schemaId inf),Equals))]
    (_,minf,amap) <- ui . transactionNoLog (meta inf) $ fromTable "geo" schemaPred >>= joinTable "event" [Rel "schema" Equals "schema", Rel "table" Equals "table"]  "event" schemaPred
    return $ (\e ->
          let
              TB1 (SText tname) =  lookAttr' "table_name" $ unTB1 $ lookRef ["schema","table"] e
              table = lookTable inf tname
              evfields = fmap unArray $ join $ unSOptional <$> indexFieldRec (liftAccess minf "geo" $ Nested [keyRef "event"] $ One $ Nested [keyRef "schema",keyRef "table",keyRef "column"] (One $ keyRef "column_name")) e
              Just (ArrayTB1 efields ) = indexFieldRec (liftAccess (meta inf) "geo" (Nested [keyRef "features"] $ Many [One $ keyRef  "geo"] )) e
              ArrayTB1 features = lookRef ["features"] e
              color = lookAttr'  "color" e
              projf  :: TBData Key Showable -> (FTB Showable , FTB (TBData Key Showable) ) -> Maybe (HM.HashMap Text A.Value)
              projf  r (efield@(TB1 (SText field)),features)  = fmap (\i ->  HM.fromList [("label",A.toJSON (HM.fromList $ i <> [("id", txt $ writePK (tableMeta table) r efield   ),("title"::Text , txt (T.pack $  L.intercalate "," $ fmap renderShowable $ allKVRec' inf (tableMeta table) r))])) ,("style",A.toJSON (Row <$> features))]) $ join $ convField  <$> indexFieldRec (head $ liftAccess inf tname <$> indexer field) r
              proj r = projf r <$> zip (F.toList efields) (F.toList features)
              convField (ArrayTB1 v) = Just [("position",ArrayTB1 v)]
              convField (LeftTB1 v) = join $ convField  <$> v
              convField (TB1 v ) = Just [("position", TB1 v)]
              convField i  = errorWithStackTrace (show i)
          in ("#" <> renderShowable color ,table,efields,evfields,proj)) <$>  G.toList amap

legendStyle dashes lookDesc table b = traverse render item
  where
    render (c, _, _, _, _) = do
      element b # set UI.class_ "col-xs-1"
      label <-
        UI.div # sink text (T.unpack . ($table) <$> facts lookDesc) #
        set UI.class_ "fixed-label col-xs-11"
      UI.label # set children [b, label] #
        set UI.style [("background-color", c)] #
        set UI.class_ "table-list-item" #
        set UI.style [("display", "-webkit-box")]
    item =
      M.lookup table (M.fromList $ fmap (\i@(a, b, c, _, _) -> (b, i)) dashes)

mapSelector
  :: A.ToJSON a =>
     InformationSchema
     -> Tidings (Maybe (TBPredicate Key Showable))
     -> (String,
         TableK Key,
         Non.NonEmpty (FTB Showable),
         Maybe (Non.NonEmpty (FTB Showable)),
         TBData Key Showable -> [Maybe a])
     -> Tidings (UTCTime, String)
     -> Tidings (Maybe (TBData Key Showable))
     -> (Event ([Double], [Double]),
         Tidings (Maybe ([Double], [Double])))
     -> UI (TrivialWidget (Maybe (TBData Key Showable)))
mapSelector inf pred selected mapT sel (cposE,positionT) = do
        innermap <- UI.div # set UI.style [("height","250px"),("width","100%")]

        (eselg,hselg) <- ui newEvent
        (egselg,hgselg) <- ui newEvent

        let
          fields = selected ^. _3
          evc = eventClick innermap
          boundSel :: FTB Showable ->  TBData Key Showable -> Maybe (Interval Showable)
          boundSel (TB1 (SText field)) sel = (\(G.FTBNode i) -> i) . G.bound <$> indexFieldRec (liftAccess inf (tableName (selected ^._2 )) $ head $ indexer field)   sel
          boundsSel :: Tidings (Maybe (Interval Showable ))
          boundsSel = join . fmap (\j -> fmap (((\(G.FTBNode i) -> i).G.union) . S.fromList) . nonEmpty . fmap leftEntry .  catMaybes .  fmap (flip boundSel  j) . F.toList  $  fields) <$> sel
          leftEntry :: Interval Showable -> G.Node (FTB Showable)
          leftEntry i  = G.FTBNode i
        onEvent cposE (liftIO . hgselg)
        p <- currentValue (facts boundsSel)
        pt <- currentValue (facts positionT)
        let
            pb = join (convertInter <$> p) <|> pt
            positionE = unionWith const (Just <$> egselg ) ( join . fmap convertInter <$> rumors boundsSel)
            setPosition = (\v@(sw,ne) -> runFunctionDelayed innermap $ ffi "setPosition(%1,%2,%3)" innermap  sw ne)

        positionB <- ui $stepper  pb  positionE

        let
          positionT = tidings positionB positionE
          pcal = liftA2 (,)   positionT mapT

        mapCreate  innermap (Nothing :: Maybe ([Double],[Double]))
        onEvent (moveend innermap) (liftIO . hgselg)
        traverseUI (traverse setPosition ) =<< ui (calmT positionT)

        fin <- (\(_,tb,fields,efields,proj) -> do
          let
            tname = tableName tb
          traverseUI (\(predi,(positionB,calT))-> do
            let pred = WherePredicate $ AndColl $ predicate inf tb (fmap  fieldKey <$>efields ) (fmap fieldKey <$> Just   fields ) (positionB,Just calT) : maybeToList (unPred <$> predi)
                unPred (WherePredicate e)  =e
                fieldKey (TB1 (SText v))=  v
            reftb <- ui $ refTables' inf (lookTable inf tname) (Just 0) pred
            let v = reftb ^. _3
            let evsel = (\j ((tev,pk,_),s) -> fmap (s,) $ join $ if tev == tb then Just ( G.lookup pk j) else Nothing  ) <$> facts v <@> fmap (first (readPK inf . T.pack) ) evc
            onEvent evsel (liftIO . hselg)
            traverseUI (\i ->
              createLayers innermap tname (T.unpack $ TE.decodeUtf8 $  BSL.toStrict $ A.encode  $ catMaybes  $ concatMap proj i)) v
            ) $ liftA2 (,) pred pcal
          ) selected
        bselg <- ui $ stepper Nothing (fmap snd <$> eselg )
        cal <- UI.div  # set children [ innermap]
        return (TrivialWidget (tidings bselg (fmap snd <$> eselg)) cal)

readMapPK v = case unsafeFromJSON v of
      [i,j]  -> Just (i,readBool j)
      i -> Nothing
  where
    readBool "false" = False
    readBool "true" = True

eventClick:: Element -> Event (String,Bool)
eventClick el = filterJust $ readMapPK <$> domEvent "mapEventClick" el


moveend :: Element -> Event ([Double],[Double])
moveend el = filterJust $ readPosition <$>  domEvent "moveend" el

