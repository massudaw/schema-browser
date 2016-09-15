{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module TP.Browser where

import Control.Monad.Writer (runWriterT)
import Control.Lens (_1,_2,(^.),over)
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
import Postgresql.Backend (postgresOps)
import SortList
import Prelude hiding (head)
import TP.QueryWidgets
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
import OAuthClient
import qualified Graphics.UI.Threepenny as UI
import Graphics.UI.Threepenny.Core hiding (get,delete,apply)
import Data.Monoid hiding (Product(..))

import qualified Data.Foldable as F
import qualified Data.Text as T
import Data.Text (Text)
import qualified Data.Set as S

import qualified Data.Map as M

import GHC.Stack

updateClient metainf inf table tdi clientId now =
    let
      row = tblist . fmap _tb
            $ [ Attr "clientid" (TB1 (SNumeric (fromInteger clientId )))
              , Attr "creation_time" (TB1 (STimestamp (utcToLocalTime utc now)))
              , Attr "schema" (LeftTB1 $ TB1 . SText .  schemaName <$> inf )
              , Attr "table" (LeftTB1 $ TB1 . SText .  tableName <$>table)
              , IT "data_index"   (LeftTB1 $ ArrayTB1 . Non.fromList .   fmap (\(i,j) -> TB1 $ tblist $ fmap _tb [Attr "key" (TB1 . SText  $ keyValue i) ,Attr "val" (TB1 . SDynamic $  j) ]) <$>tdi )
              ]
      lrow = liftTable' metainf "clients" row
    in lrow

getClient metainf clientId ccli = G.lookup (G.Idex $ M.fromList [(lookKey metainf "clients" "clientid",TB1 (SNumeric (fromInteger clientId)))]) ccli :: Maybe (TBData Key Showable)

deleteClient metainf clientId = do
  (dbmeta ,(_,ccli)) <- transactionNoLog metainf $ selectFrom "clients"  Nothing Nothing [] $ mempty
  putPatch (patchVar dbmeta) [(tableMeta (lookTable metainf "clients") , G.Idex $ M.fromList [(lookKey metainf "clients" "clientid",TB1 (SNumeric (fromInteger clientId)))],[])]

editClient metainf inf dbmeta ccli  table tdi clientId now = do
  let cli :: Maybe (TBData Key Showable)
      cli = getClient metainf clientId ccli
      new :: TBData Key Showable
      new = updateClient metainf inf table tdi clientId now
      lrow :: Maybe (Index (TBData Key Showable))
      lrow = maybe (Just $ patch new ) (flip diff new )  cli
  traverse (putPatch (patchVar dbmeta ) . pure ) lrow

addClient clientId metainf inf table dbdata =  do
    now <- getCurrentTime
    let
      tdi = fmap (M.toList .getPKM) $ join $ (\inf table -> fmap (tblist' table ) .  traverse (fmap _tb . (\(k,v) -> fmap (Attr k) . readType (keyType $ k) . T.unpack  $ v).  first (lookKey inf (tableName table))  ). F.toList) <$>  inf  <*> table <*> rowpk dbdata
    (dbmeta ,(_,ccli)) <- transactionNoLog metainf $ selectFrom "clients"  Nothing Nothing []  mempty
    editClient metainf inf dbmeta ccli table tdi clientId now
    return (clientId, getClient metainf clientId <$> collectionTid dbmeta)

txt = TB1 . SText


chooserTable inf bset cliTid cli = do
  let
    bBset = triding bset

  nav  <- buttonDivSet ["Browser"] (pure $ Just "Browser")(\i -> UI.button # set UI.text i # set UI.style [("font-size","smaller")]. set UI.class_ "buttonSet btn-xs btn-default pull-right")
  element nav # set UI.class_ "col-xs-11"
  layout <- checkedWidget (pure False)
  body <- UI.div
  el <- mapUIFinalizerT body (\l -> mapM (\(nav,((table,desc),sub))-> do
    header <- UI.h3
        # set UI.class_ "header"
        # set text desc
    let layFacts i =  if i then ("col-xs-" <> (show $  (12`div`length l))) else "row"
        layFacts2 i =  if i then ("col-xs-" <> (show $  6)) else "row"

    body <- case nav of
        "Browser" -> do
            let selTable = flip M.lookup (pkMap inf)
            if L.length sub == 1
               then do
              viewerKey inf (fromJust $ selTable table) cli (layFacts2 . not <$> triding layout) cliTid
               else do
              els <- mapM (\t -> do
                  l <- UI.h4 #  set text (T.unpack $fromMaybe (rawName t)  $ rawTranslation t) # set UI.class_ "col-xs-12 header"
                  b <- viewerKey inf t cli (layFacts2 . not <$> triding layout) cliTid
                  element b # set UI.class_ "col-xs-12"
                  UI.div # set children [l,b]
                  ) sub
              UI.div # set children els
    UI.div # set children [header,body] # sink0 UI.class_ (facts $ layFacts <$> triding layout)# set UI.style [("border","2px dotted gray")]
        ) l) $ liftA2 (\i j -> (i,) <$> j)  (triding nav) (M.toList <$> bBset)
  element body # sink0 UI.children (facts el) # set UI.class_ "col-xs-12"
  element layout  # set UI.class_ "col-xs-1"
  return [getElement layout ,getElement nav ,body]

viewerKey
  ::
      InformationSchema -> Table -> Integer -> Tidings String -> Tidings  (Maybe (TBData Key Showable)) -> UI Element
viewerKey inf table cli layout cliTid = mdo
  iv   <- currentValue (facts cliTid)
  let lookT iv = let  i = unLeftItens $ lookAttr' (meta inf)  "table" iv
                in fmap (\(Attr _ (TB1 (SText t))) -> t) i
      lookPK iv = let  i = unLeftItens $ lookAttr' (meta inf)  "data_index" iv
                       unKey t = liftA2 (,) ((\(Attr _ (TB1 (SText i)))-> flip (lookKey inf ) i <$> lookT iv ) $ lookAttr' (meta inf)  "key" t  )( pure $ (\(Attr _ (TB1 (SDynamic i)))-> i) $ lookAttr'  (meta inf)  "val" t )
                in fmap (\(IT _ (ArrayTB1 t)) -> catMaybes $ F.toList $ fmap (unKey.unTB1) t) i
  let
  reftb@(vpt,vp,_ ,var ) <- refTables inf table

  let
      tdip = (\i -> join $ traverse (\v -> G.lookup  (G.Idex (M.fromList $ justError "" $ traverse (traverse unSOptional' ) $v)) (snd i) ) (join $ lookPK <$> iv) ) <$> vpt
      tdi = if Just (tableName table) == join (lookT <$> iv) then tdip else pure Nothing
  cv <- currentValue (facts tdi)
  -- Final Query ListBox
  filterInp <- UI.input
  filterInpBh <- stepper "" (UI.valueChange filterInp)
  let filterInpT = tidings filterInpBh (diffEvent filterInpBh (UI.valueChange filterInp))
      sortSet = rawPK table <>  L.filter (not .(`L.elem` rawPK table)) (F.toList . tableKeys . TB1 . tableNonRef' . allRec' (tableMap inf ) $ table)
  sortList <- selectUI sortSet ((,True) <$> rawPK table ) UI.div UI.div conv
  element sortList # set UI.style [("overflow-y","scroll"),("height","200px")]
  let
     filteringPred i = T.isInfixOf (T.pack $ toLower <$> i) . T.toLower . T.intercalate "," . fmap (T.pack . renderPrim ) . F.toList  .snd
     tsort = sorting' . filterOrd <$> triding sortList
     filtering res = (\t -> fmap (filter (filteringPred t )) )<$> filterInpT  <*> res
     pageSize = 20
     lengthPage (fixmap,i) = (s  `div` pageSize) +  if s `mod` pageSize /= 0 then 1 else 0
        where (s,_)  = fromMaybe (sum $ fmap fst $ F.toList fixmap ,M.empty ) $ M.lookup mempty fixmap
  inisort <- currentValue (facts tsort)
  itemListEl <- UI.select # set UI.class_ "col-xs-6" # set UI.style [("width","100%")] # set UI.size "21"
  let wheel = negate <$> mousewheel itemListEl
  (offset,res3)<- mdo
    offset <- offsetField (pure 0) wheel  (lengthPage <$> facts res3)
    res3 <- ui $ mapT0EventDyn (fmap inisort (fmap G.toList vp)) return ( (\f i -> fmap f i)<$> tsort <*> (filtering $ fmap (fmap G.toList) $ tidings ( res2) ( rumors vpt) ) )
    return (offset, res3)
  onEvent (rumors $ triding offset) $ (\i ->  liftIO $ do
    transactionNoLog inf $ eventTable  table  (Just $ i `div` ((opsPageSize $ schemaOps inf) `div` pageSize)) Nothing  [] $ mempty)
  let
    paging  = (\o -> fmap (L.take pageSize . L.drop (o*pageSize)) ) <$> triding offset
  page <- currentValue (facts paging)
  res4 <- ui $ mapT0EventDyn (page $ fmap inisort (fmap G.toList vp)) return (paging <*> res3)
  itemList <- listBoxEl itemListEl ((Nothing:) . fmap Just <$> fmap snd res4) (fmap Just <$> tidings st sel ) (pure id) (pure (maybe id attrLine))
  let evsel =  rumors (fmap join  $ triding itemList)
  (dbmeta ,(_,_)) <- liftIO$ transactionNoLog (meta inf) $ selectFromTable "clients"  Nothing Nothing [] ([(IProd True ["schema"],"=",  LeftTB1 $ Just $TB1 $ SText (schemaName inf) ), (IProd True ["table"],"=",LeftTB1 $ Just $ TB1 $ SText (tableName table))])
  ui $onEventIO ((,) <$> facts (collectionTid dbmeta ) <@> evsel ) (\(ccli ,i) -> void . editClient (meta inf) (Just inf) dbmeta  ccli (Just table ) (M.toList . getPKM <$> i) cli =<< getCurrentTime )
  prop <- stepper cv evsel
  let tds = tidings prop evsel

  (cru,ediff,pretdi) <- crudUITable inf (pure "+")  reftb [] [] (allRec' (tableMap inf) table) tds
  diffUp <-  ui $ mapEvent (fmap pure)  $ (\i j -> traverse (return . flip apply j ) i) <$> facts pretdi <@> ediff
  let
     sel = filterJust $ safeHead . concat <$> unions [ diffUp,unions [rumors  $ fmap join (triding itemList) ]]
  st <- stepper cv sel
  res2 <- stepper (vp) (rumors vpt)
  onEvent (pure <$> ediff) (liftIO .  putPatch var )
  title <- UI.div #  sink items (pure . maybe UI.h4 (\i -> UI.h4 # attrLine i  )  <$> st) # set UI.class_ "col-xs-8"
  expand <- UI.input # set UI.type_ "checkbox" # sink UI.checked filterEnabled# set UI.class_ "col-xs-1"
  let evc = UI.checkedChange expand
  filterEnabled <- stepper False evc
  insertDiv <- UI.div # set children [title,head cru] # set UI.class_ "container-fluid"
  insertDivBody <- UI.div # set children [insertDiv,last cru]
  element sortList # sink UI.style  (noneShow <$> filterEnabled) # set UI.class_ "col-xs-4"
  element offset # set UI.class_ "col-xs-4"
  element filterInp # set UI.class_ "col-xs-3"
  element itemList -- # set UI.class_ "row"
  itemSel <- UI.div # set children ( [expand , filterInp, getElement offset ,getElement sortList] ) -- # set UI.class_ "row"
  itemSelec <- UI.div # set children [itemSel,getElement itemList] -- # set UI.class_ "col-xs-6"
  mapM (\i -> element i # sink0 UI.class_ (facts $ layout)) [itemSelec,insertDivBody]
  UI.div # set children ([itemSelec,insertDivBody ] )
