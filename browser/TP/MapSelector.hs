{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module TP.MapSelector where

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
import Control.Monad.Writer
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
calendarCreate el Nothing evs= runFunction $ ffi "createMap(%1,null,null,%2)" el evs
calendarCreate el (Just (ne,sw)) evs= runFunction $ ffi "createMap(%1,%2,%3,%4)" el  (show ne) (show sw) evs


idx inf c v@(m,k) = indexField ( liftAccess inf (_kvname m) (keyRef c))  v

mapWidgetMeta  inf = do
  {-importUI
      [js "leaflet.js"
      ,css "leaflet.css"
      ,js "leaflet-svg-markers.min.js"
      ]-}
    let
      schemaPred2 = [(keyRef ["schema"],Left (int (schemaId inf),Equals))]
    (_,(_,evMap )) <-ui $  transactionNoLog  (meta inf) $ selectFromTable "geo" Nothing Nothing [] schemaPred2
    (_,(_,eventMap )) <-ui $  transactionNoLog  (meta inf) $ selectFromTable "event" Nothing Nothing [] schemaPred2
    cliZone <- jsTimeZone
    return $ (\e ->
          let
              Just (TB1 (SText tname)) = unSOptional' $ _tbattr $ lookAttr' (meta inf) "table_name" $ unTB1 $ _fkttable $ lookAttrs' (meta inf) ["schema","table"] e
              table = lookTable inf tname
              evfields = join $ fmap (unArray . _tbattr ) . idx (meta inf) ["event"]   <$> erow
                where
                  erow = G.lookup (idex (meta inf) "event" [("schema" ,int $ schemaId inf),("table",int (_tableUnique table))])  eventMap
              Just (ArrayTB1 efields ) = indexFieldRec (liftAccess (meta inf) "geo" (Nested (keyRef ["features"] ) $keyRef  ["geo" ])) e
              (IT _ (ArrayTB1 features))= lookAttr' (meta inf) "features" e
              (Attr _ color )= lookAttr' (meta inf) "color" e
              projf  :: TBData Key Showable -> (FTB Showable , FTB (TBData Key Showable) ) -> Maybe (HM.HashMap Text A.Value)
              projf  r (efield@(TB1 (SText field)),features)  = fmap (\i ->  HM.fromList [("label",A.toJSON (HM.fromList $ i <> [("id", txt $ writePK r efield   ),("title"::Text , txt $ (T.pack $  L.intercalate "," $ fmap renderShowable $ allKVRec' $  r))])) ,("style",A.toJSON features)]) $ join $ convField  <$> indexFieldRec (liftAccess inf tname $ indexer field) r
              proj r = projf r <$> zip (F.toList efields) (F.toList features)
              convField (ArrayTB1 v) = Just $ [("position",ArrayTB1 v)]
              convField (LeftTB1 v) = join $ convField  <$> v
              convField (TB1 v ) = Just [("position", TB1 v)]
              convField i  = errorWithStackTrace (show i)
          in ("#" <> renderShowable color ,table,efields,evfields,proj)) <$>  ( G.toList evMap)

legendStyle dashes lookDesc table b
            =  do
              let item = M.lookup table  (M.fromList  $ fmap (\i@((a,b,c,_,_))-> (b,i)) dashes)
              maybe UI.div (\(k@((c,_,_,_,_))) ->
                UI.div # set items [UI.div
                  # set items [element b # set UI.class_ "col-xs-1", UI.div # sink text  (T.unpack . ($table) <$> facts lookDesc) #  set UI.class_ "fixed-label col-xs-11" # set UI.style [("background-color",c)] ]
                  # set UI.style [("background-color",c)]]) item
mapSelector
  :: (A.ToJSON a) =>
     InformationSchema
     -> (String,
         TableK Key,
         Non.NonEmpty (FTB Showable),
         Maybe (Non.NonEmpty (FTB Showable)),
         TBData Key Showable -> [Maybe a])
     -> Tidings (UTCTime, String)
     -> Tidings (Maybe (TBData Key Showable))
     -> (Event ( [Double], [Double]),
         Tidings (Maybe ([Double], [Double])))
     -> UI (TrivialWidget (Maybe (TBData Key Showable)))
mapSelector inf selected calendarT sel (cposE,positionT) = do
        innerCalendar <- UI.div # set UI.style [("height","250px"),("width","100%")]

        (eselg,hselg) <- ui$newEvent
        (egselg,hgselg) <- ui$newEvent

        let
          fields = selected ^. _3
          evc = eventClick innerCalendar
          boundSel :: FTB Showable ->  TBData Key Showable -> Maybe (Interval Showable)
          boundSel (TB1 (SText field)) sel = (\(G.FTBNode i) -> i) . G.bound <$> indexFieldRec (liftAccess inf (tableName (selected ^._2 )) $ indexer field)   sel
          boundsSel :: Tidings (Maybe (Interval Showable ))
          boundsSel = join . traceShowId . fmap (\j -> fmap ((\(G.FTBNode i) -> i).G.union) . fmap S.fromList  . traceShowId . nonEmpty . fmap leftEntry .  catMaybes .  fmap (flip boundSel  j) . F.toList  $  fields) <$> sel
          leftEntry :: Interval Showable -> Either (G.Node (FTB Showable)) (FTB Showable)
          leftEntry i  = Left (G.FTBNode i)
        onEvent cposE (liftIO . hgselg)
        p <- currentValue (facts boundsSel)
        liftIO $print p
        let
            pb = (join $ convertInter <$> p)
            positionE = (unionWith const (Just <$> egselg ) ( join . fmap convertInter <$> rumors boundsSel) )
            setPosition = (\v@(sw,ne) -> runFunction $ ffi "setPosition(%1,%2,%3)" innerCalendar  sw ne)

        positionB <- ui $stepper  pb  positionE



        let
          positionT = (tidings positionB positionE)
          pcal = liftA2 (,)   positionT calendarT

        calendarCreate  innerCalendar (Nothing :: Maybe ([Double],[Double])) ("[]"::String)
        onEvent (moveend innerCalendar) (liftIO . hgselg)
        onEvent ( filterJust $ join . fmap convertInter <$> rumors boundsSel)  setPosition
        codep <- mapUIFinalizerT innerCalendar (liftIO . traverse (\(sw,ne) ->toCode $ (ffi "setPosition(%1,%2,%3)" innerCalendar sw ne :: JSFunction ()))) positionT
        pscript <- mkElement "script" # sink text (maybe "" id .traceShowId <$> facts codep)

        fin <- (\(_,tb,fields,efields,proj) -> do
          let
            tname = tableName tb
          mapUIFinalizerT innerCalendar (\(positionB,calT)-> do
            let pred = WherePredicate $ predicate inf tb (fmap  fieldKey <$>efields ) (fmap fieldKey <$> Just   fields ) (positionB,Just calT)
                fieldKey (TB1 (SText v))=  v
            reftb <- ui $ refTables' inf (lookTable inf tname) (Just 0) pred
            let v = reftb ^. _3
            let evsel = (\j ((tev,pk,_),s) -> fmap (s,) $ join $ if tev == tb then Just ( G.lookup pk j) else Nothing  ) <$> facts v <@> fmap (first (readPK inf . T.pack) ) evc
            onEvent evsel (liftIO . hselg)
            mapUIFinalizerT innerCalendar (\i ->
              createLayers innerCalendar tname (T.unpack $ TE.decodeUtf8 $  BSL.toStrict $ A.encode  $ catMaybes  $ concat $ fmap proj $   i)) v
            ) pcal
          ) selected
        bselg <- ui $ stepper Nothing (fmap snd <$> eselg )
        cal <- UI.div  # set children [ innerCalendar, pscript]
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
moveend el = filterJust $ traceShowId . readPosition <$>  domEvent "moveend" el

