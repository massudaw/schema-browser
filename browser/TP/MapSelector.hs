{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE Arrows #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module TP.MapSelector (mapWidgetMeta,mapSelector,mapCreate,moveend,eventClick,createLayers,legendStyle,mapDef) where

import Step.Host
import qualified NonEmpty as Non
import Environment
import Data.String
import Control.Arrow
import Data.Functor.Identity
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



mapDef inf
  = projectV
     (innerJoinR
        (leftJoinR
          (leftJoinR
            (innerJoinR
              (fromR "tables" schemaPred)
              (fromR "geo" schemaPred) schemaI "geo")
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
      evfields <- iinline "event" (iopt $ irecord (iforeign [Rel "schema" Equals "schema" , Rel "table" Equals "table", Rel "column" Equals "oid"] (imap $ irecord (ifield  "column_name" (ivalue $  readV PText))))) -< ()
      efields <- iinline "geo" (irecord (iinline "features" (imap $ irecord (ifield  "geo" ( ivalue $  readV PText))))) -< ()
      desc <- iinline "description" (iopt $  irecord (ifield "description" (imap $ ivalue $  readV PText))) -< ()
      pksM <- iinline "pks" (irecord (ifield "pks" (iopt $ imap $ ivalue $  readV PText))) -< ()
      features <- iinline "geo" (irecord (iinlineR "features" (imap $ ivalue (readR ("metadata","style_options"))))) -< ()
      color <- iinline "geo" (irecord (ifield "color" (ivalue $ readV PText))) -< ()
      let
        table = lookTable inf tname
        projf ::  (Showable , (TBData Text Showable)) -> TBData Key Showable -> Maybe A.Object
        projf (efield@(SText field),features)  r = do
          i <- unSOptional =<< recLookupInf inf tname (indexerRel field) r
          pks <- pksM
          fields <- mapM (\(SText i) -> unSOptional =<< recLookupInf inf tname (indexerRel i) r) (fromMaybe pks desc)
          pkfields <- mapM (\(SText i) -> fmap (i,). unSOptional =<< recLookupInf inf tname (indexerRel i) r) pks
          return $ HM.fromList [("label", A.toJSON (HM.fromList
                               [("position" :: Text,i)
                               ,("id" :: Text, txt $ writePK' tname (F.toList pkfields) (TB1 efield))
                                ,("title",txt (T.pack $  L.intercalate "," $ renderShowable <$> F.toList fields))
                               ]))
                          ,("style",A.toJSON (TRow (liftTable' (meta inf) "style_options" features)))]
        proj r = flip projf  r <$> zip (F.toList efields) (F.toList features)
      returnA -< ("#" <> renderPrim color ,table,fmap TB1 efields,fmap TB1 <$> evfields,proj )


mapWidgetMeta  inf =  do
    importUI
      =<< sequence
        [js "leaflet.js"
        ,css "leaflet.css"
        ,js "leaflet-svg-markers.min.js"
        ]
    fmap F.toList $ ui $ transactionNoLog (meta inf) $ dynPK (mapDef inf)()


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
  :: (Show a ,A.ToJSON a ) =>
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
        evc <- eventClick innermap
        let
          fields = selected ^. _3
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
        move <- moveend innermap
        onEvent move (liftIO . hgselg)
        traverseUI (traverse setPosition ) =<< ui (calmT positionT)

        fin <- (\(_,tb,fields,efields,proj) -> do
          let
            tname = tableName tb
          traverseUI (\(predi,(positionB,calT))-> do
            let pred = WherePredicate $ AndColl $ predicate inf tb (fmap  fieldKey <$>efields ) (fmap fieldKey <$> Just   fields ) (positionB,Just calT) : maybeToList (unPred <$> predi)
                unPred (WherePredicate e)  =e
                fieldKey (TB1 (SText v))=  v
            reftb <- ui $ refTables' inf (lookTable inf tname) (Just 0) pred
            let v =  reftb ^. _2
            traverseUI (\i -> do
              createLayers innermap tname (T.unpack $ TE.decodeUtf8 $  BSL.toStrict $ A.encode  $ catMaybes  $ concatMap proj i)) v
            let evsel = (\j ((tev,pk,_),s) -> fmap (s,) $ join $ if tev == tb then Just (G.lookup pk j) else Nothing) <$> facts v <@> fmap (first (readPK inf . T.pack) ) evc
            onEvent evsel (liftIO . hselg)
            ) $ liftA2 (,) pred pcal
          ) selected
        mapSel <- ui $ stepperT Nothing (fmap snd <$> eselg )
        return (TrivialWidget mapSel innermap)

readMapPK v = case unsafeFromJSON v of
      [i,j]  -> Just (i,readBool j)
      i -> Nothing
  where
    readBool "false" = False
    readBool "true" = True

eventClick:: Element -> UI (Event (String,Bool))
eventClick el = (filterJust . fmap readMapPK) <$> domEventClient "mapEventClick" el (ffi "")


moveend :: Element -> UI (Event ([Double],[Double]))
moveend el = (filterJust . fmap readPosition) <$>  domEventClient "moveend" el (ffi "")

