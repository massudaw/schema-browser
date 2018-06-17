{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}

module TP.Browser where

import ClientAccess
import Control.Monad.Reader
import qualified Data.List as L
import qualified Data.Map as M
import Data.Maybe
import Data.Monoid hiding (Product(..))
import qualified Data.Set as S
import qualified Data.Text as T
import qualified Graphics.UI.Threepenny as UI
import Graphics.UI.Threepenny.Core hiding (apply, delete, get)
import Query
import RuntimeTypes
import Schema
import SchemaQuery
import TP.QueryWidgets
import TP.Selector
import TP.Widgets
import Types
import qualified Types.Index as G
import Utils

layFactsDiv i j =
  case i of
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
    let
      initial = Vertical
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

  w <- askWindow
  ui $ accumDiffMapCounter (\ix (k,v) -> runUI w $ do
    element body # set UI.addChild v
    element v # sink UI.class_ (facts $ (\sel list -> layFactsDiv sel (M.size list) )<$> triding sel <*> list)
      ) list
  return (getElement sel,body)

layoutSel k l = do
  (i, j) <- layoutSel' k l
  UI.div # set children [i, j]

chooserTable six inf bset cliTid cli = do
  let
    pred2 =  [(keyRef "schema",Left (int $ schemaId inf  ,Equals))]
  translationDb <- ui $ transactionNoLog  (meta inf)
        (selectFromTable "table_name_translation" Nothing Nothing []  pred2 )
  w <- askWindow
  iniTable <- currentValue (facts cliTid)
  el <- ui $ accumDiffCounterIni  (maybe 0 (length .table_selection)  iniTable) (\ix -> runUI w . (\table-> do
    header <- UI.h4
        # set UI.class_ "header"
        # sink0 text (facts $ T.unpack . lookDesc inf table <$> collectionTid translationDb)
    let viewer t = viewerMode six inf t ix cli (indexTable inf (ix,table) <$> cliTid)
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
           els <- traverseUI (\t -> do
             b <- viewer t
             element b # set UI.class_ "col-xs-12") (triding unions)
           body <- UI.div # sink root (facts els)
           UI.div # set children [getElement unions, body]
    UI.div
      # set children [header,body]
      # set UI.style [("border","2px dotted "),("border-color",maybe "gray" (('#':).T.unpack) (schemaColor inf))]))
        (triding bset)
  layoutSel onAlt  el

viewerMode
  ::
      Int -> InformationSchema -> Table -> Int ->  Int -> Tidings  (Maybe ClientTableSelection) -> UI Element
viewerMode six inf table tix cli cliTid = do
  reftb@(_,vpt,_,_) <- ui $ refTablesPorj inf table Nothing mempty (recPKDesc inf (tableMeta table) (allRec' (tableMap inf) table))
  let
    tdip = listRows inf table <$> cliTid
    tdi = (\i -> fromMaybe [] . traverse (\v -> G.lookup  (G.Idex v) i)) <$> facts vpt <#> fmap activeRows tdip

  nav  <- buttonDivSet  ["Edit","Table"] (pure Nothing)
      (\i -> UI.button # set UI.text i # set UI.class_ "buttonSet btn-sm btn-default pull-right" )

  v <- ui $ currentValue (facts tdi)

  cru <- switchManyUI tdi (triding nav) $
    M.fromList [
    ("Edit",do
      itemList <- selector inf table reftb (pure Nothing) (safeHead <$> tdi)
      let
        updatedValue = (\i j -> const . join $ flip G.lookup j  . G.getIndex  (tableMeta table)<$> i )<$> facts (triding itemList)<@> rumors vpt
        selection = const <$> rumors (triding itemList)
        tds = triding itemList
        tds2 = (\i j -> join $ flip G.lookup j . G.getIndex (tableMeta table) <$> i) <$> triding itemList  <*> vpt
      title <- UI.h5
        # sink text (facts $ maybe "" (attrLine inf  (tableMeta table)) <$> tds)
        # set UI.class_ "header col-xs-12"
      TrivialWidget tdf ev <- crudUITable inf table reftb M.empty [] (allRec' (tableMap inf) table) tds2
      element ev # set UI.class_ "col-xs-12"
      TrivialWidget (maybeToList <$> tds) <$> UI.div # set children [ getElement itemList,title,ev]
    ),
    ("Table",do
      itemList <- multiSelector inf table reftb (pure Nothing) tdi
      let
          tds = triding itemList
          tds2 = (\i j -> catMaybes  $ flip G.lookup j . G.getIndex (tableMeta table) <$> i) <$> triding itemList  <*> vpt
      title <- UI.h5
        # sink text (facts $ L.intercalate "," . fmap (attrLine inf  (tableMeta table)) <$> tds)
        # set UI.class_ "header col-xs-12"
      TrivialWidget tdf ev <- batchUITable inf table reftb M.empty [] (allRec' (tableMap inf) table) tds2
      element ev # set UI.class_ "col-xs-12"
      TrivialWidget tds <$> UI.div # set children [getElement itemList,title,ev]
    )]

  w  <- askWindow
  ui $ do
    calmPK <-  calmT (S.fromList . fmap (G.getIndex (tableMeta table))<$> triding cru)
    accumDiffCounterIni (L.length v)
      (logRowAccess w (six,inf) (tix,table))
        calmPK
  UI.div # set children [getElement nav , getElement cru]

