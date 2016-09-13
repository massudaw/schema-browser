{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module TP.Selector (calendarSelector,positionSel,tableChooser,selectFromTable) where

import TP.View
import Control.Monad.Writer (runWriterT, WriterT(..))
import Control.Lens (_1, _2, (^.), over)
import Safe
import qualified NonEmpty as Non
import Data.Char
import Step.Common
import Query
import Data.Time
import Text
import qualified Types.Index as G
import Data.Bifunctor (first)
import Debug.Trace
import Types
import SchemaQuery
import TP.Widgets
import Prelude hiding (head)
import TP.QueryWidgets
import Control.Monad.Reader
import Data.Ord
import Utils
import Schema
import Types.Patch
import Data.Maybe
import Reactive.Threepenny hiding (apply)
import qualified Data.List as L
import qualified Data.ByteString.Char8 as BS
import RuntimeTypes
import OAuthClient
import qualified Graphics.UI.Threepenny as UI
import Graphics.UI.Threepenny.Core hiding (get, delete, apply)
import Data.Monoid hiding (Product(..))
import qualified Data.Foldable as F
import qualified Data.Text as T
import Data.Text (Text)
import qualified Data.Set as S
import qualified Data.Map as M
import GHC.Stack

calendarSelector = do
    let buttonStyle k e = e # set UI.text (fromJust $ M.lookup k transRes)# set UI.class_ "btn-xs btn-default buttonSet"
          where transRes = M.fromList [("month","Mês"),("week","Semana"),("day","Dia")]
        defView = "week"
        viewList = ["month","day","week"] :: [String]
        transMode _ "month" = "month"
        transMode True i = "agenda" <> capitalize i
        transMode False i = "basic" <> capitalize i
        capitalize (i:xs) = toUpper i : xs
        capitalize [] = []

    iday <- liftIO getCurrentTime
    resolution <- fmap (fromMaybe defView) <$> buttonDivSetT  viewList (pure id) (pure $ Just defView ) (const UI.button)  buttonStyle

    next <- UI.button  # set text ">"
    today <- UI.button # set text "Hoje"
    prev <- UI.button  # set text "<"
    agenda <- mdo
      agenda <- UI.button # sink text ((\b -> if b then "Agenda" else "Basic") <$> agB)
      let agE = pure not <@ UI.click agenda
      agB <- accumB False agE
      return $ TrivialWidget (tidings agB (flip ($) <$> agB <@> agE)) agenda

    current <- UI.div # set children [prev,today,next]
    let
      currentE = concatenate <$> unions  [resRange False  <$> facts (triding resolution) <@ UI.click next
                                       ,resRange True   <$> facts (triding resolution) <@ UI.click prev , const (const iday) <$> UI.click today ]
    increment <- accumB iday  currentE
    let incrementT =  tidings increment (flip ($) <$> increment <@> currentE)

    currentOutput <- UI.div # sink text (fmap show $ (\i j -> (resRange False i j ,resRange True i j))<$>  facts (triding resolution) <*> facts incrementT )
    sidebar <- UI.div # set children [getElement agenda,current,getElement resolution,currentOutput ]
    return (sidebar,(triding agenda ,incrementT,triding resolution))

positionSel = do
    cpos <-UI.div
    bcpos <-UI.button # set text "Localização Atual"
    sidebar <-UI.div # set children [bcpos,cpos]
    (e,h) <- liftIO$ newEvent
    positionB <- stepper Nothing (Just <$>e)
    onEventFT (UI.click bcpos) (\_ -> runFunction $ ffi "fireCurrentPosition(%1)" bcpos)
    onEventFT (currentPosition bcpos ) (liftIO. h )
    element cpos # sink text (show <$> positionB)
    return (sidebar,currentPosition bcpos, h,tidings positionB (diffEvent positionB  (Just <$> e)))

tableChooser  inf tables legendStyle tableFilter iniSchemas iniUsers iniTables = do
  let
      pred =  [(IProd True ["schema_name"],"IN",ArrayTB1 $ TB1 . SText <$> iniSchemas )]
      authPred =  [(IProd True ["grantee"],"IN",  ArrayTB1 $ TB1 . SText <$> iniUsers ), (IProd True ["table_schema"],"IN",ArrayTB1 $ TB1 . SText <$> iniSchemas  )]
  (orddb ,authorization,translation) <- liftIO $ transactionNoLog  (meta inf) $
      (,,) <$> (fst <$> (selectFromTable "ordering"  Nothing Nothing []  pred ))
           <*> (fst <$> (selectFromTable "authorization" Nothing Nothing [] authPred   ))
           <*> (fst <$> (selectFromTable "table_name_translation" Nothing Nothing []  pred ))
  filterInp <- UI.input # set UI.style [("width","100%")]
  filterInpBh <- stepper "" (UI.valueChange filterInp)
  let filterInpT = tidings filterInpBh (UI.valueChange filterInp)

  let
      selTable = flip M.lookup (pkMap inf)
      -- Table Description
      lookDesc = (\i j -> maybe (T.unpack $ maybe "" rawName j)  ((\(Attr _ v) -> renderShowable v). lookAttr' (meta inf)  "translation") $ G.lookup (idex (meta inf) "table_name_translation" [("schema_name" ,TB1 $ SText $ schemaName inf),("table_name",TB1 $ SText (maybe ""  tableName j))]) i) <$> collectionTid translation
      -- Authorization
      authorize =  (\autho t -> isJust $ G.lookup (idex  (meta inf) "authorization"  [("table_schema", TB1 $ SText (schemaName inf) ),("table_name",TB1 $ SText $ tableName t),("grantee",TB1 $ SText $ username inf)]) autho)  <$> collectionTid authorization
      -- Text Filter
      filterLabel = (\j d -> (\i -> L.isInfixOf (toLower <$> j) (toLower <$> d (Just i))))<$> filterInpT <*> lookDesc
      -- Usage Count
      tableUsage orderMap table selection = maybe (Right 0) (Left .(L.elem table (lookPK inf <$> M.keys selection),)) . fmap (lookAttr' (meta inf)  "usage" ) $  G.lookup  (G.Idex ( M.fromList pk )) orderMap
          where  pk = L.sortBy (comparing fst ) $ first (lookKey (meta inf ) "ordering") <$> [("table_name",TB1 . SText . rawName $ table ), ("schema_name",TB1 $ SText (schemaName inf))]
  bset <- mdo
    let

        buttonString k = do
          b <- UI.input# set UI.type_ "checkbox"
          let un = rawUnion tableK
              tableK = fromJust $ selTable k
          unions <- mapM (\i -> (i,) <$> UI.input# set UI.type_ "checkbox") un
          let ev = (k,) . (\b -> if b then (if L.null un then [tableK ] else un,[]) else ([],if L.null un then [tableK] else un))<$>UI.checkedChange b
          let evs = foldr (unionWith const) ev $ fmap (k,) .  (\(ki,e) -> (\i-> (if i then ([ki],[]) else ([],[ki]))) <$> UI.checkedChange e  )<$> unions
          return (k,((b,(snd <$> unions)),evs))

    let
      visible  k = (\i j k-> i tb && j tb && k tb ) <$> filterLabel <*> authorize <*> tableFilter
        where
          tb =  justLook   k (pkMap inf)

    bset <- checkDivSetTGen tables ((\i k j -> tableUsage i (justLook j (pkMap inf)) k ) <$> collectionTid orddb <*> triding bset) (M.fromList . fmap  (\e -> (e,). (\i ->  if L.null (rawUnion i) then [i] else rawUnion  i) . fromJust . selTable $ e ) <$> iniTables) buttonString ((\lg i j -> lg i j # set UI.class_ "table-list-item" # sink UI.style (noneDisplay "-webkit-box" <$> facts (visible i))) <$> legendStyle)
    return bset
  let
      bBset = M.keys <$> triding bset
      ordRow orderMap pkset =  field
          where
            field =  G.lookup (G.Idex $ M.fromList pk) orderMap
            pk = L.sortBy (comparing fst) $ first (lookKey (meta inf ) "ordering") <$>[("table_name",TB1 . SText . rawName $ justLook   pkset (pkMap inf) ), ("schema_name",TB1 $ SText (schemaName inf))]
      incClick field =  (fst field , G.getIndex field ,[patch $ fmap (+SNumeric 1) usage])
          where
            usage = lookAttr' (meta inf ) "usage"   field

  ui $ onEventIO ((\i j -> fmap incClick <$> (ordRow i <$> j)) <$> facts (collectionTid orddb) <@> rumors bBset)
    (traverse (traverse (\p -> do
      _ <- transactionNoLog (meta inf ) $ patchFrom  p
      putPatch (patchVar orddb) [p] )))

  element bset # set UI.style [("overflow","auto"),("height","99%")]
  tableHeader <- UI.h4 # set text "Table"
  tbChooserI <- UI.div # set children [tableHeader,filterInp,getElement bset]  # set UI.style [("height","50vh")]
  return $ (lookDesc,TrivialWidget ((\f -> M.mapKeys (fmap (f. selTable) ))<$> facts lookDesc <#> (M.mapKeys (\i-> (i,i))  <$>triding bset)) tbChooserI)


