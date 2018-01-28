{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}

module TP.Browser where

import Control.Monad.Writer (runWriterT,tell)
import Control.Lens (_1,_2,(^.),over)
import GHC.Generics
import ClientAccess
import Safe
import qualified Data.Dynamic as Dyn
import qualified NonEmpty as Non
import Graphics.UI.Threepenny.Internal (wId)
import Data.Char
import Serializer
import Step.Common
import qualified Data.Vector as V
import Step.Host
import Query
import Data.Time
import Text
import qualified Types.Index as G
import Data.Bifunctor (first)
import Debug.Trace
import TP.Selector
import TP.Widgets
import TP.QueryWidgets
import Types
import SchemaQuery
import Database.PostgreSQL.Simple
import Postgresql.Backend (postgresOps)
import Control.Monad.Reader
import System.Environment
import Data.Ord
import Utils
import Schema
import Types.Patch
import Data.Maybe
import Reactive.Threepenny hiding(apply)
import qualified Data.List as L
import qualified Data.ByteString.Char8 as BS

import RuntimeTypes
import qualified Graphics.UI.Threepenny as UI
import Graphics.UI.Threepenny.Core hiding (get,delete,apply)
import qualified Data.ExtendedReal as ER
import qualified Data.Interval as Interval
import Data.Interval  (Interval)
import Data.Monoid hiding (Product(..))

import qualified Data.Foldable as F
import qualified Data.Text as T
import Data.Text (Text)
import qualified Data.Set as S
import qualified Data.Map as M
import GHC.Stack


layFactsDiv i j =  case i of
   Vertical -> "col-xs-" <> show (12 `div` fromIntegral (max 1 j))
   Horizontal -> "col-xs-12"
   Tabbed -> "col-xs-12"

data Layout
  = Vertical
  | Horizontal
  | Tabbed
  deriving(Eq,Ord,Show)


layoutSel' keyword list = do
  let styles = [Vertical,Horizontal]
  body <- UI.div
  alt <- keyword 76 body
  next <- mdo
    let initial = Vertical
    let
      next c = styles !! ((current c + 1) `mod` length styles)
        where current = fromJust . flip L.elemIndex styles
      ev = const next <$> alt
    bh <- ui $ accumB initial ev
    return (tidings bh (flip ($) <$> bh<@> ev))
  sel <- buttonDivSet
    styles
    (Just <$> next)
    (\i ->UI.button
        # set UI.class_ "buttonSet label"
        # set text (show i)
        # set UI.style [("font-size","smaller"),("font-weight","bolder")])

  traverseUI (\(sel,list) ->
      mapM (\i -> element i # set UI.class_ (layFactsDiv sel (L.length list))) list)
      ((,) <$> triding sel <*> (F.toList <$> list))
  w <- askWindow
  ui $ accumDiffMapCounter (\ix (k,v) -> runUI w $ do
    element body # set UI.addChild v
      ) list
  return (getElement sel,body)

layoutSel k l = do
  (i,j) <- layoutSel'  k l
  UI.div # set children [i,j]



viewerMode True =  viewerKey
viewerMode False = viewerKeyBatch

chooserTable mode six inf bset cliTid cli = do
  let
    pred2 =  [(keyRef "schema",Left (int $ schemaId inf  ,Equals))]
  translationDb <- ui $ transactionNoLog  (meta inf)
        (fst <$> selectFromTable "table_name_translation" Nothing Nothing []  pred2 )
  w <- askWindow
  iniTable <- currentValue (facts cliTid)
  liftIO $ print (maybe 0 (length .table_selection) iniTable,iniTable)
  el <- ui $ accumDiffCounterIni  (maybe 0 (length .table_selection)  iniTable) (\ix -> runUI w . (\table-> do
    header <- UI.h4
        # set UI.class_ "header"
        # sink0 text (facts $ T.unpack . lookDesc inf table <$> collectionTid translationDb)
    let viewer t = viewerMode mode six inf t ix cli (indexTable inf (ix,table) <$> cliTid)
    ui $ trackTable (meta inf) (wId w) table six ix
    body <-
      if L.null (rawUnion table)
         then
          viewer table
         else do
           unions <- buttonDivSet
              (rawUnion table)
              (pure Nothing)
              (\i ->UI.button
                  # set UI.class_ "buttonSel btn"
                  # set text (T.unpack $ tableName i))
           els <- traverseUI ((\t -> do
             b <- viewer t
             element b # set UI.class_ "col-xs-12"
             return b))(triding  unions)
           body <- UI.div # sink root (facts els)
           UI.div # set children [getElement unions ,body]
    UI.div
      # set children [header,body]
      # set UI.style [("border","2px dotted "),("border-color",maybe "gray" (('#':).T.unpack) (schemaColor inf))]))
        (triding bset)
  layoutSel onAlt  el

viewerKeyBatch
  ::
      Int -> InformationSchema -> Table -> Int ->  Int -> Tidings  (Maybe ClientTableSelection) -> UI Element
viewerKeyBatch six inf table tix cli cliTid = do
  let
  reftb@(_,_,vpt,_,_) <- ui $ refTables' inf table Nothing mempty
  let
    tdip = listRows inf table <$> cliTid
    tdi = (\i -> fromMaybe [] . traverse (\v -> G.lookup  (G.Idex (justError "no key" $ traverse unSOptional $ v)) i) . fmap (F.toList . fmap pk_value . data_index) . filter (isNothing . unFin . fst . Interval.upperBound' .  row_up_time) ) <$> vpt <*> tdip
  itemList <- multiSelector inf table reftb (pure Nothing) tdi
  v <- ui $ currentValue (facts tdi)
  tds <- do
    let
      updatedValue = (\i j -> const . catMaybes  $ flip G.lookup j  . G.getIndex  (tableMeta table)<$> i )<$> facts (triding itemList) <@> rumors vpt
      selection = const <$> rumors (triding itemList)
    ui $ accumT  v (unionWith (.) selection  updatedValue)
  TrivialWidget _ cru <- batchUITable inf table reftb M.empty [] (allRec' (tableMap inf) table) tds
  w  <- askWindow
  ui $ accumDiffCounterIni (L.length v)
    (logRowAccess w (six,inf) (tix,table))
    (S.fromList <$> tds)

  title <- UI.h5
    # sink text (facts $ L.intercalate "," . fmap (attrLine inf  (tableMeta table)) <$> tds)
    # set UI.class_ "header col-xs-12"
  insertDivBody <- UI.div # set children [title,cru]
  element cru
    # set UI.class_ "col-xs-12"
  UI.div # set children [getElement itemList,insertDivBody]


viewerKey
  ::
      Int -> InformationSchema -> Table -> Int ->  Int -> Tidings  (Maybe ClientTableSelection) -> UI Element
viewerKey six inf table tix cli cliTid = do
  let
  reftb@(_,_,vpt,_,_) <- ui $ refTables' inf table Nothing mempty
  let
    tdip = listRows inf table <$> cliTid
    tdi = (\i -> fromMaybe [] . traverse (\v -> G.lookup  (G.Idex (justError "no key" $ traverse unSOptional $ v)) i). fmap (F.toList . fmap pk_value . data_index). filter (isNothing . unFin . fst . Interval.upperBound' .  row_up_time)) <$> vpt <*> tdip
  itemList <- selector inf table reftb (pure Nothing) (safeHead <$> tdi)
  v <- ui $ currentValue (facts tdi)
  tds <- do
    let
      updatedValue = (\i j -> const . join $ flip G.lookup j  . G.getIndex  (tableMeta table)<$> i )<$> facts (triding itemList) <@> rumors vpt
      selection = const <$> rumors (triding itemList)
    ui $ accumT  (safeHead v) (unionWith (.) selection  updatedValue)
  TrivialWidget _ cru <- crudUITable inf table reftb M.empty [] (allRec' (tableMap inf) table) tds
  dbmeta  <- ui $ prerefTable (meta inf) (lookTable (meta inf ) "clients")
  w  <- askWindow
  ui $ accumDiffCounterIni (L.length v)
    (logRowAccess w (six,inf) (tix,table))
    (S.fromList .maybeToList <$> tds)
  title <- UI.h5
    # sink text (facts $ L.intercalate "," . fmap (attrLine inf  (tableMeta table)). maybeToList <$> tds)
    # set UI.class_ "header col-xs-12"
  element cru
    # set UI.class_ "col-xs-12"
  insertDivBody <- UI.div # set children [title,cru]
  UI.div # set children [getElement itemList,insertDivBody]


logRowAccess w (six,inf) (tix,table) ix row = do
  let sel =  Non.fromList . M.toList $ getPKM (tableMeta table) row
  let lift =  liftPatch minf "clients"
      cli = lookTable minf "clients"
      minf = meta inf
  now <- liftIO getCurrentTime
  let p = lift <$> addRow  (wId w) now  sel  six tix ix
  transactionNoLog minf $ do
    patchFrom (tableMeta cli) (PatchRow <$>p)
  registerDynamic (void $ do
    now <- liftIO getCurrentTime
    let d = lift <$> removeRow (wId w) now  six  tix ix
    runDynamic $ transactionNoLog minf $ do
      patchFrom (tableMeta cli) (PatchRow<$>d))
