{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}

module TP.Browser where

import Control.Monad.Writer (runWriterT,tell)
import Control.Lens (_1,_2,(^.),over)
import Safe
import qualified NonEmpty as Non
import Data.Char
import Step.Common
import Step.Host
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
import qualified Data.ExtendedReal as ER
import qualified Data.Interval as Interval
import Data.Monoid hiding (Product(..))

import qualified Data.Foldable as F
import qualified Data.Text as T
import Data.Text (Text)
import qualified Data.Set as S

import qualified Data.Map as M

import GHC.Stack

clientCreate metainf now = liftTable' metainf "client_login" row
  where
    row = tblist . fmap _tb
            $ [ Attr "id" (SerialTB1 Nothing)
              , Attr "up_time" (IntervalTB1 $ Interval.interval (ER.Finite (TB1 (STimestamp (utcToLocalTime utc now))),True) (ER.PosInf,True))
              ]

serverCreate metainf now = liftTable' metainf "server" row
  where
    row = tblist . fmap _tb
            $ [ Attr "serverid" (SerialTB1 Nothing)
              , Attr "up_time" (IntervalTB1 $ Interval.interval (ER.Finite (TB1 (STimestamp (utcToLocalTime utc now))),True) (ER.PosInf,True))
              ]

addClientLogin inf =  transactionNoLog inf $ do
    now <- liftIO$ getCurrentTime
    let
      obj = clientCreate inf now
    i@(Just (TableModification _ _ tb))  <-  insertFrom obj
    tell (maybeToList i)
    return i

attrIdex l =  G.Idex $ M.fromList $ fmap (\(Attr i k) -> (i,k)) l

deleteClientLogin inf i= do
  now <- liftIO $ getCurrentTime

  (_,(_,tb)) <- transactionNoLog inf $ selectFrom "client_login"  Nothing Nothing [] (WherePredicate (AndColl [PrimColl (IProd True [ (lookKey inf "client_login" "id")] , Left ((TB1 (SNumeric i)),Equals))]))
  let
    pk = Attr (lookKey inf "client_login" "id") (TB1 (SNumeric i))
    old = justError ("no row " <> show (attrIdex [pk]) ) $ G.lookup (attrIdex [pk]) tb
    pt = (tableMeta (lookTable inf "client_login") , G.getIndex old,[PAttr (lookKey inf "client_login" "up_time") ( PInter False ((ER.Finite $ PAtom (STimestamp (utcToLocalTime utc now)) , False)))])

  transactionNoLog inf $ do
    v <- updateFrom  (apply old pt) old
    tell (maybeToList v)
    return v

addServer inf =  do
    now <- liftIO$ getCurrentTime
    let
      obj = serverCreate inf now
    transactionNoLog inf $ insertFrom obj

idexToPred (G.Idex  i) = head $ (\(k,a)-> (IProd True [k],Left (a,Contains))) <$>  M.toList  i

deleteServer inf (TableModification _ _ o@(a,ref,c)) = do
  now <- liftIO $ getCurrentTime
  (_,(_,tb)) <- transactionNoLog inf $ selectFrom "client_login"  Nothing Nothing [] (WherePredicate (AndColl [PrimColl (IProd True [(lookKey inf "client_login" "up_time") ],Left ((TB1 (STimestamp (utcToLocalTime utc now))),Flip Contains))]))
  let
    pk = Attr (lookKey inf "client_login" "up_time")(TB1 (STimestamp (utcToLocalTime utc now)))
    oldClis =  L.filter (G.indexPred (idexToPred $ attrIdex [pk])) (G.toList tb)
    pt old = (tableMeta (lookTable inf "client_login") , G.getIndex old,[PAttr (lookKey inf "client_login" "up_time") ( PInter False ((ER.Finite $ PAtom (STimestamp (utcToLocalTime utc now)) , False)))])

  mapM (\(old) -> transactionNoLog inf $ do
    v <- updateFrom   (apply old (pt old)) old
    tell (maybeToList v)
    return v) oldClis
  let pt = (tableMeta (lookTable inf "server") , ref ,[PAttr (lookKey inf "server" "up_time") (PInter False ((ER.Finite $ PAtom (STimestamp (utcToLocalTime utc now)) , False)))])
  transactionNoLog inf $ updateFrom (apply (create o) pt) (create o)


opt f = LeftTB1 . fmap f

updateClient metainf inf table tdi clientId now = do
    (_,(_,tb)) <- transactionNoLog metainf $ selectFrom "client_login"  Nothing Nothing [] (WherePredicate $ AndColl [PrimColl(IProd True [(lookKey metainf "client_login" "id")] ,Left (int clientId,Equals))]  )
    let
      pk = Attr (lookKey metainf "client_login" "id") (SerialTB1 $ Just $ TB1 (SNumeric clientId))
      old = justError ("no row " <> show (attrIdex [pk],tb) ) $ G.lookup (attrIdex [pk]) tb
    let
      time = TB1  . STimestamp . utcToLocalTime utc
      inter i j  = IntervalTB1 $ Interval.interval (i,True) (j,True)
      row = tblist . fmap _tb
            $ [ FKT (kvlist [_tb $ Attr "clientid" (TB1 (SNumeric (clientId )))]) [Rel "clientid" Equals "id"] (TB1 $ mapKey' keyValue $ old)
              , Attr "up_time" (inter (Interval.Finite $ time now) Interval.PosInf)
              , Attr "schema" (int .  schemaId $ inf )
              , IT "selection"
                  (LeftTB1 $ (\table -> ArrayTB1 $ Non.fromList [
                    TB1 $ tblist $ fmap _tb[ Attr "table" (txt .  tableName $ table)
                                       , Attr "up_time" ( inter (Interval.Finite (time now)) (Interval.PosInf))
                                       , IT "selection"   (LeftTB1  $ (\tdi -> ArrayTB1 $ Non.fromList [
                                              TB1 $ tblist $ fmap _tb [
                                               Attr "up_time" (inter (Interval.Finite $ time now) Interval.PosInf)
                                              ,IT "data_index"
                                                  ( ArrayTB1 . Non.fromList .   fmap (\(i,j) -> TB1 $ tblist $ fmap _tb [Attr "key" (txt  $ keyValue i) ,Attr "val" (TB1 . SDynamic $  j) ]) $tdi)]
                                              ]) <$> tdi)
                                       ]
                    ]) <$> table )
              ]
      lrow = liftTable' metainf "clients" row
    return lrow

num = TB1 . SNumeric
getClient metainf clientId inf ccli = G.lookup (idex metainf "clients"  [("clientid",num clientId),("schema",int $ schemaId inf)]) ccli :: Maybe (TBData Key Showable)

deleteClient metainf clientId = do
  dbmeta  <-  prerefTable metainf (lookTable metainf "clients")
  putPatch (patchVar dbmeta) [(tableMeta (lookTable metainf "clients") , G.Idex $ M.fromList [(lookKey metainf "clients" "clientid",TB1 (SNumeric (clientId)))],[])]

editClient metainf inf dbmeta ccli  table tdi clientId now
  | fmap tableName table == Just "client" && schemaName inf == "metadata" = return ()
  | otherwise = do
    let cli :: Maybe (TBData Key Showable)
        cli = getClient metainf clientId inf ccli
    new <- updateClient metainf inf table tdi clientId now
    let
        lrow :: Maybe (Index (TBData Key Showable))
        lrow = maybe (Just $ patch new ) (flip diff new )  cli
    traverse (putPatch (patchVar $ iniRef $ dbmeta ) . pure ) lrow
    return ()

addClient clientId metainf inf table row =  do
    now <- liftIO getCurrentTime
    let
      tdi = fmap (M.toList .getPKM) $ join $ (\ t -> fmap (tblist' t ) .  traverse (fmap _tb . (\(k,v) -> fmap (Attr k) . readType (keyType $ k) . T.unpack  $ v).  first (lookKey inf (tableName t))  ). F.toList) <$>  table <*> row
    dbmeta  <- refTable metainf (lookTable metainf "clients")
    new <- updateClient metainf inf table tdi clientId now
    putPatch (patchVar $iniRef dbmeta ) [patch new]
    return (clientId, getClient metainf clientId inf <$> collectionTid dbmeta)



layFactsDiv i j =  if i then ("col-xs-" <> (show $  12 `div` fromIntegral (max 1 $ j))) else "col-xs-12"

chooserTable inf bset cliTid cli = do

  let
    pred2 =  [(IProd True ["schema"],Left (int $ schemaId inf  ,Equals))]
  orddb <- ui $ transactionNoLog  (meta inf) $
      (fst <$> (selectFromTable "ordering"  Nothing Nothing []  pred2))
  layout <- checkedWidget (pure False)
  body <- UI.div
  el <- ui $ accumDiff (evalUI body  . (\((table,sub))-> do
    header <- UI.h3
        # set UI.class_ "header"
        # set text (T.unpack (rawName table))
    let
    body <-  do
            if L.length sub == 1
               then do
                 viewerKey inf table cli  (triding layout ) cliTid
               else do
              els <- mapM (\t -> do
                  l <- UI.h4 #  set text (T.unpack $fromMaybe (rawName t)  $ rawTranslation t) # set UI.class_ "col-xs-12 header"
                  b <- viewerKey inf t cli  (triding layout )cliTid
                  element b # set UI.class_ "col-xs-12"
                  UI.div # set children [l,b]
                  ) sub
              UI.div # set children els
    UI.div # set children [header,body] # sink0 UI.class_ (facts $ layFactsDiv <$> triding layout <*> fmap M.size (triding bset))# set UI.style [("border","2px dotted gray")]
                       ).fst)  (M.fromList . fmap (\i -> (i,())) . M.toList <$> triding bset)

  element body # sink0 UI.children (facts $ (\els ord-> fmap snd $ L.sortBy (flip $ comparing fst) $ fmap (first (tableOrder inf ord .fst)) els ) <$> fmap M.toList el <*> collectionTid orddb) # set UI.class_ "col-xs-12"
  element layout  # set UI.class_ "col-xs-1"
  return [getElement layout ,body]

viewerKey
  ::
      InformationSchema -> Table -> Int -> Tidings Bool -> Tidings  (Maybe (TBData Key Showable)) -> UI Element
viewerKey inf table cli layoutS cliTid = mdo
  let layout = layFactsDiv <$> layoutS <*> pure 2
  iv   <- currentValue (facts cliTid)
  let
      lookT,lookPK :: TBData Key Showable -> Maybe (Int,TBData Key Showable)
      lookT iv = join $ fmap ((\t -> L.find (\(ix,i)->  G.indexPred (liftAccess (meta inf) "clients_table" $ IProd True ["table"],Left (txt (tableName table), Equals)) i) $ zip [0..] (fmap unTB1 $ F.toList t) ).unArray) (join $ unSOptional <$> i)
        where
          i = _fkttable <$> indexField (liftAccess (meta inf) "clients" $ (IProd False ["selection"]) ) iv

      lookPK iv = join $ fmap ((\t -> safeHead  $ zip [0..] (fmap unTB1 $ F.toList t) ). unArray) (join $ unSOptional <$> i)
        where
          i = _fkttable <$> indexField (liftAccess (meta inf) "clients_table" $ (IProd False ["selection"]) ) iv
      lookKV iv = let i = lookAttr' (meta inf)  "data_index" iv
                      unKey t = liftA2 (,) ((\(Attr _ (TB1 (SText i)))-> Just $ lookKey inf  (tableName table) i ) $ lookAttr' (meta inf)  "key" t  )( pure $ (\(Attr _ (TB1 (SDynamic i)))-> i) $ lookAttr'  (meta inf)  "val" t )
                in (\(IT _ (ArrayTB1 t)) -> catMaybes $ F.toList $ fmap (unKey.unTB1) t) i

  reftb@(vpt,vp,_,var) <- ui $ refTables inf table

  let
      tdi = (\i iv-> join $ traverse (\v -> G.lookup  (G.Idex (M.fromList $ justError "" $ traverse (traverse unSOptional' ) $v)) (snd i) ) iv ) <$> vpt <*> tdip
      tdip = join . fmap (join . fmap ( fmap (lookKV . snd ). lookPK .snd). lookT ) <$> cliTid
  cv <- currentValue (facts tdi)
  -- Final Query ListBox
  filterInp <- UI.input # set UI.class_ "col-xs-3"
  filterInpT <- element filterInp # sourceT "keydown" UI.valueFFI ""
  let
      sortSet = rawPK table <>  L.filter (not .(`L.elem` rawPK table)) (F.toList . tableKeys . TB1 . tableNonRef' . allRec' (tableMap inf ) $ table)
  sortList <- selectUI sortSet ((,True) <$> rawPK table ) UI.div UI.div conv
  element sortList # set UI.style [("overflow-y","scroll"),("height","200px")]
  let
     filteringPred i = T.isInfixOf (T.pack $ toLower <$> i) . T.toLower . T.intercalate "," . fmap (T.pack . renderPrim ) . F.toList  .snd
     tsort = sorting' . filterOrd <$> triding sortList
     filtering res = (\t -> fmap (filter (filteringPred t )) )<$> triding filterInpT  <*> res
     pageSize = 20
     divPage s = (s  `div` pageSize) +  if s `mod` pageSize /= 0 then 1 else 0
     lengthPage (fixmap,_) = s
        where (s,_)  = fromMaybe (sum $ fmap fst $ F.toList fixmap ,M.empty ) $ M.lookup mempty fixmap
  inisort <- currentValue (facts tsort)
  itemListEl <- UI.select # set UI.class_ "col-xs-6" # set UI.style [("width","100%")] # set UI.size "21"
  runFunction $ ffi "$(%1).selectpicker('mobile')" itemListEl
  wheel <- fmap negate <$> UI.mousewheel itemListEl
  (offset,res3)<- mdo
    offset <- offsetFieldFiltered (pure 0) wheel   [(L.length . snd <$> res3) ,L.length . snd <$> vpt,(lengthPage <$> res3)]
    res3 <- ui $ mapT0EventDyn (fmap inisort (fmap G.toList vp)) return ( (\f i -> fmap f i)<$> tsort <*> (filtering $ fmap (fmap G.toList) $ vpt) )
    return (offset, res3)
  ui $ onEventDyn (rumors $ triding offset) $ (\i ->  do
    transactionNoLog inf $ selectFrom (tableName table ) (Just $ divPage (i + pageSize) `div` ((opsPageSize $ schemaOps inf) `div` pageSize)) Nothing  [] $ mempty)
  let
    paging  = (\o -> fmap (L.take pageSize . L.drop o) ) <$> triding offset
  page <- currentValue (facts paging)
  res4 <- ui $ mapT0EventDyn (page $ fmap inisort (fmap G.toList vp)) return (paging <*> res3)
  itemList <- listBoxElEq (\l m -> maybe False id $ liftA2 (\i j ->G.getIndex i == G.getIndex j) l m) itemListEl ((Nothing:) . fmap Just <$> fmap snd res4) (Just <$> tds) (pure id) (pure (maybe id attrLine))
  -- (dbmeta ,(_,_)) <- ui $ transactionNoLog (meta inf) $ selectFromTable "clients"  Nothing Nothing [] [(IProd True ["schema"],Left (int (schemaId inf),Equals ))]
  -- ui $onEventDyn ((,) <$> facts (collectionTid dbmeta ) <@> evsel ) (\(ccli ,i) -> void . editClient (meta inf) inf dbmeta  ccli (Just table ) (M.toList . getPKM <$> i) cli =<< liftIO getCurrentTime )
  let tds = (fmap join  $ triding itemList)

  (cru,ediff,pretdi) <- crudUITable inf (pure "+")  reftb [] [] (allRec' (tableMap inf) table) tds
  title <- UI.div #  sink items (pure . maybe UI.h4 (\i -> UI.h4 # attrLine i  )  <$> facts tds ) # set UI.class_ "col-xs-8"
  expand <- UI.input # set UI.type_ "checkbox" # sink UI.checked filterEnabled# set UI.class_ "col-xs-1"
  evc <- UI.checkedChange expand
  filterEnabled <- ui $ stepper False evc
  insertDiv <- UI.div # set children [title,head cru] # set UI.class_ "container-fluid"
  insertDivBody <- UI.div # set children [insertDiv,last cru]
  element sortList # sink UI.style  (noneShow <$> filterEnabled) # set UI.class_ "col-xs-4"
  element offset # set UI.class_ "col-xs-2"
  itemSel <- UI.div # set children ( [expand , filterInp, getElement offset ,getElement sortList] )
  itemSelec <- UI.div # set children [itemSel,getElement itemList]
  mapM (\i -> element i # sink0 UI.class_ (facts $ layout)) [itemSelec,insertDivBody]
  UI.div # set children ([itemSelec,insertDivBody ] )
