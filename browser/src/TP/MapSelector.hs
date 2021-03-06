{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE Arrows #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module TP.MapSelector (mapWidgetMeta,mapSelector,setPosition,mapCreate,moveend,eventClick,createLayers,legendStyle,mapDef) where

import Step.Host
import qualified NonEmpty as Non
import qualified Data.Sequence.NonEmpty as NonS
import Environment
import Types.Patch
import qualified Control.Lens  as Le 
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

removeLayers el tname = runFunctionDelayed el $ ffi "removeLayer(%1,%2)" el tname

createLayers el tname evs = do
  runFunctionDelayed el  $ ffi "createLayer(%1,%3,%2)" el evs tname
  finalizerUI (removeLayers el tname)

mapCreate el = runFunctionDelayed el $ ffi "createMap(%1)" el
mapCreate el  = runFunctionDelayed el $ ffi "createMap(%1)" el
setPosition el (i,j) = runFunctionDelayed el $ ffi "setPosition(%1,%2,%3)"  el i j 


mapDef inf
  = projectS
      (leftJoinS
        (innerJoinS
          (tableDef inf `whereS` schemaPred)
          (fromS "geo") (schemaI "geo"))
        (fromS "event") (schemaI "event")) fields
  where
    schemaPred = [(keyRef "schema",Left (int (schemaId inf),Equals))]
    schemaI t = [Rel "oid" Equals (NInline t "table")]
    fields =  irecord $ proc t -> do
      (tname,desc,dir,pks) <- tableProj inf -< ()
      evfields  <- iforeign (schemaI "event") 
            (iopt $ ivalue $ irecord (iforeign [Rel "column" (AnyOp Equals) "oid"] 
              (imap $ ivalue $ irecord (ifield  "column_name" (ivalue $  readV PText))))) -< ()
      (efields , features, color) <- iforeign (schemaI "geo") ((,,) 
                 <$> (ivalue $ irecord (iinline "features" (imap $ ivalue $ irecord (ifield  "geo" ( ivalue $  readV PText)))))
                 <*> (ivalue $ irecord (iinlineR "features" (imap $ ivalue (readR ("metadata","style_options"))))) 
                 <*> (ivalue $ irecord (ifield "color" (ivalue $ readV PText)))) -<  ()
      let
        table = lookTable inf tname
        projfT ::  (Showable , TBData Text Showable) -> PluginM (Union (G.AttributePath T.Text MutationTy))  (Atom (TBData T.Text Showable))  Identity () (Maybe A.Object )
        projfT (efield@(SText field),features) = irecord $ proc _ -> do
          i <- convertRelM inf tname field  -< ()
          pkfields <- mapA (\(SText i) -> (Inline (lookKey inf tname i), ) <$> convertRel inf tname i)  pks -<  ()
          fields <- mapA buildRel (fromMaybe ((\(SText i) ->  splitRel inf tname i) <$> pks) ( fmap (liftRel inf tname ).  NonS.fromList. explodeTree   <$> desc) ) -< ()
          returnA -< (\i -> HM.fromList [("label", A.toJSON (HM.fromList
                                     [("position" :: Text,i)
                                     ,("id" :: Text, txt $ writePK' tname pkfields (TB1 efield))
                                     ,("title",txt (T.pack $  L.intercalate "," $ renderShowable <$> catMaybes (F.toList fields)))
                                     ]))
                                 ,("style",A.toJSON (TRow (liftTable' (meta inf) "style_options" features)))]) <$> i
        proj =   mapA projfT  $ zip (F.toList efields) (F.toList features)
        pred predi positionB calT = WherePredicate $ AndColl $ predicate inf table (fmap  fieldKey <$>efields' ) (fmap fieldKey <$> Just   gfields' ) (positionB,Just calT) : maybeToList (unPred <$> predi)
          where
            gfields' = fmap TB1 ( Non.fromList . F.toList $ efields)
            efields' = fmap TB1 . Non.fromList . F.toList <$> evfields
            unPred (WherePredicate e)  =e
            fieldKey (TB1 (SText v))=  v
      returnA -< ("#" <> renderPrim color, table, (pred,efields), proj)



mapWidgetMeta  inf =  do
    fmap F.toList . currentValue . facts  =<<  ui ( transactionNoLog (meta inf) $ dynPK (mapDef inf) ())


legendStyle dashes lookDesc table b = traverse render item
  where
    render c = do
      element b # set UI.class_ "col-xs-1"
      label <-
        UI.div # set text (T.unpack  lookDesc) #
        set UI.class_ "fixed-label col-xs-11"
      UI.label # set children [b, label] #
        set UI.style [("background-color", Le.view Le._1 c )] #
        set UI.class_ "table-list-item" #
        set UI.style [("display", "-webkit-box")]
    item =
      M.lookup table (M.fromList $ fmap (\i -> (Le.view Le._2 i, i)) dashes)

mapSelector
  :: 
     InformationSchema
     -> Tidings (Maybe (TBPredicate Key Showable))
     -> (String,
         TableK Key,
          (Maybe (TBPredicate Key Showable)
                     -> Maybe ([Double], [Double])
                     -> (UTCTime, String)
                     -> WherePredicate, NonS.NonEmptySeq Showable),
         PluginM (Union (G.AttributePath T.Text MutationTy))  (Atom (TBData T.Text Showable))  Identity () [Maybe A.Object]
         )
     -> Tidings (UTCTime, String)
     -> Tidings (Maybe (TBData Key Showable))
     -> (Event ([Double], [Double]),
         Tidings (Maybe ([Double], [Double])))
     -> UI (TrivialWidget (Maybe (TBData Key Showable)))
mapSelector inf pred (_,tb,(wherePred,_),proj) mapT sel (cposE,positionT) = do
        innermap <- UI.div # set UI.style [("height","250px"),("width","100%")]
        (eselg,hselg) <- ui newEvent
        (egselg,hgselg) <- ui newEvent
        evc <- eventClick innermap
        onEvent cposE (liftIO . hgselg)
        -- p <- currentValue (facts boundsSel)
        pt <- currentValue (facts positionT)
        let
            -- boundsSel :: Tidings (Maybe (Interval Showable ))
            -- boundsSel = join . fmap (\j -> fmap (((\(G.FTBNode i) -> i).G.union) . S.fromList) . nonEmpty . fmap leftEntry .  catMaybes .  fmap (flip boundSel  j) . F.toList  $  fields) <$> sel
            pb = {-join (convertInter <$> p) <|>-} pt
            positionE = (Just <$> egselg) -- unionWith const (Just <$> egselg ) ( join . fmap convertInter <$> rumors boundsSel)
            setP = setPosition innermap  

        position <- ui $ stepperT  pb  positionE

        let
          pcal = liftA3 wherePred pred position mapT
          tname = tableName tb

        mapCreate  innermap 
        move <- moveend innermap
        onEvent move (liftIO . hgselg)
        traverseUI (traverse setP) =<< ui (calmT positionT)

        fin <- traverseUIInt (\pred-> do
          let 
            selection = projectFields inf tb (fst $ staticP proj) mempty $ allFields inf tb
          reftb <- ui $ refTablesProj inf tb Nothing (liftPredicateF lookupKeyName  inf (tableName tb ) $ mapPredicate (fmap keyValue)  pred )selection
          let v = primary <$> reftb ^. _2
          traverseUI (createLayers innermap tname . A.toJSON . catMaybes  . concatMap (evalPlugin  proj)) v
          let evsel = (\j ((tev,pk,_),s) -> fmap (s,) $ join $ if tev == tb then Just (G.lookup pk j) else Nothing) <$> facts v <@> fmap (first (readPK inf . T.pack) ) evc
          onEvent evsel (liftIO . hselg)) pcal
        inisel <- currentValue (facts sel)
        mapSel <- ui $ stepperT inisel (unionWith const (rumors sel ) (fmap snd <$> eselg ))
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

