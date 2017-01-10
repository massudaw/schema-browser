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
import Graphics.UI.Threepenny.Internal (wId)
import Data.Char
import Step.Common
import qualified Data.Vector as V
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
            $ [
               Attr "up_time" (IntervalTB1 $ Interval.interval (ER.Finite (TB1 (STimestamp (utcToLocalTime utc now))),True) (ER.PosInf,True))
              ]

serverCreate metainf now = liftTable' metainf "server" row
  where
    row = tblist . fmap _tb
            $ [
               Attr "up_time" (IntervalTB1 $ Interval.interval (ER.Finite (TB1 (STimestamp (utcToLocalTime utc now))),True) (ER.PosInf,True))
              ]

addClientLogin inf =  transactionNoLog inf $ do
    now <- liftIO$ getCurrentTime
    let
      obj = clientCreate inf now
    i@(Just (TableModification _ _ tb))  <-  insertFrom obj
    tell (maybeToList i)
    return i

attrIdex l =  G.Idex $  fmap (\(Attr i k) -> k) l

deleteClientLogin inf i= do
  now <- liftIO $ getCurrentTime

  (_,(_,tb)) <- transactionNoLog inf $ selectFrom "client_login"  Nothing Nothing [] (WherePredicate (AndColl [PrimColl (keyRef [ (lookKey inf "client_login" "id")] , Left ((TB1 (SNumeric i)),Equals))]))
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

idexToPred t (G.Idex  i) = head $ (\(k,a)-> (keyRef [k],Left (a,Contains))) <$>  zip (rawPK t) (F.toList i)

deleteServer inf (TableModification _ _ (PatchRow o@(a,ref,c))) = do
  now <- liftIO $ getCurrentTime
  (_,(_,tb)) <- transactionNoLog inf $ selectFrom "client_login"  Nothing Nothing [] (WherePredicate (AndColl [PrimColl (keyRef [(lookKey inf "client_login" "up_time") ],Left ((TB1 (STimestamp (utcToLocalTime utc now))),Contains))]))
  let
    t= (lookTable inf "client_login")
    pk = Attr (lookKey inf "client_login" "up_time")(TB1 (STimestamp (utcToLocalTime utc now)))
    oldClis =  L.filter (G.indexPred (idexToPred t $ attrIdex [pk])) (G.toList tb)
    pt old = (tableMeta (lookTable inf "client_login") , G.getIndex old,[PAttr (lookKey inf "client_login" "up_time") ( PInter False ((ER.Finite $ PAtom (STimestamp (utcToLocalTime utc now)) , False)))])

  mapM (\(old) -> transactionNoLog inf $ do
    v <- updateFrom   (apply old (pt old)) old
    tell (maybeToList v)
    return v) oldClis
  let pt = (tableMeta (lookTable inf "server") , ref ,[PAttr (lookKey inf "server" "up_time") (PInter False ((ER.Finite $ PAtom (STimestamp (utcToLocalTime utc now)) , False)))])
  transactionNoLog inf $ updateFrom (apply (create o) pt) (create o)


opt f = LeftTB1 . fmap f

removeTable :: Int -> UTCTime -> Table -> Int ->  TBIdx Text Showable
removeTable idClient now table  tix = (mempty,G.Idex [num idClient],[PInline "selection" (POpt $ Just $ PIdx tix (Just $ PAtom $
                        (mempty,mempty, [ PAttr "up_time" ( PInter False (Interval.Finite $ patch(time now),True ))])))
                                       ])


addTable :: Int -> UTCTime -> Table -> Int ->  TBIdx Text Showable
addTable idClient now table  tix = (mempty,G.Idex [num idClient],[PInline "selection" (POpt $ Just $ PIdx tix (Just $ patch$
                    TB1 $ tblist $ fmap _tb[ Attr "table" (txt .  tableName $ table)
                                       , Attr "up_time" ( inter (Interval.Finite (time now)) (Interval.PosInf))
                                       , IT "selection" (LeftTB1 $ Nothing)
                                           ]))
                                       ])
removeRow idClient now tix rix =  (mempty,G.Idex [num idClient],[PInline "selection" (POpt$Just $ PIdx tix $ Just$ PAtom
                          (mempty,mempty,[PInline "selection" $ POpt $ Just $ PIdx rix $ Just $ PAtom(
                          (mempty,mempty,[ PAttr "up_time" ( PInter False (Interval.Finite $ patch(time now),True ))]))]))])


addRow idClient now tdi tix rix =  (mempty,G.Idex [num idClient],[PInline "selection" (POpt$Just $ PIdx tix $ Just$ PAtom
                          (mempty,mempty,[PInline "selection" $ POpt $ Just $ PIdx rix $ Just $ patch(
                                              TB1 $ tblist $ fmap _tb [
                                               Attr "up_time" (inter (Interval.Finite $ time now) Interval.PosInf)
                                              ,IT "data_index"
                                                  ( ArrayTB1 . Non.fromList .   fmap (\(i,j) -> TB1 $ tblist $ fmap _tb [Attr "key" (txt  $ keyValue i) ,Attr "val" (TB1 . SDynamic $  j) ]) $tdi)])
                                              ]))])

time = TB1  . STimestamp . utcToLocalTime utc
inter i j  = IntervalTB1 $ Interval.interval (i,True) (j,True)

updateClient metainf inf table tdi clientId now = do
    (_,(_,tb)) <- transactionNoLog metainf $ selectFrom "client_login"  Nothing Nothing [] (WherePredicate $ AndColl [PrimColl(keyRef [(lookKey metainf "client_login" "id")] ,Left (int clientId,Equals))]  )
    let
      pk = Attr (lookKey metainf "client_login" "id") (SerialTB1 $ Just $ TB1 (SNumeric clientId))
      old = justError ("no row " <> show (attrIdex [pk]) ) $ G.lookup (attrIdex [pk]) tb
    let
      row = tblist . fmap _tb
            $ [ FKT (kvlist [_tb $ Attr "clientid" (TB1 (SNumeric (clientId )))]) [Rel "clientid" Equals "id"] (TB1 $ mapKey' keyValue $ old)
              , Attr "up_time" (inter (Interval.Finite $ time now) Interval.PosInf)
              , Attr "schema" (int .  schemaId $ inf )
              , IT "selection" (LeftTB1 Nothing)]

      lrow = liftTable' metainf "clients" row
    return lrow

num = TB1 . SNumeric
getClient metainf clientId inf ccli = G.lookup (idex metainf "clients"  [("clientid",num clientId)]) ccli :: Maybe (TBData Key Showable)

deleteClient metainf clientId = do
  dbmeta  <-  prerefTable metainf (lookTable metainf "clients")
  putPatch (patchVar dbmeta) [PatchRow (tableMeta (lookTable metainf "clients") , idex metainf "clients" [("clientid",num clientId)],[])]

editClient metainf inf dbmeta ccli  table tdi clientId now ix
  | fmap tableName table == Just "client" && schemaName inf == "metadata" = return ()
  | otherwise = do
    let cli :: Maybe (TBData Key Showable)
        cli = getClient metainf clientId inf ccli
    new <- updateClient metainf inf table tdi clientId now
    let
        lrow :: Maybe (Index (TBData Key Showable))
        lrow = maybe (Just $ patch new ) (flip diff new )  cli
    traverse (putPatch (patchVar $ iniRef $ dbmeta ) . pure .PatchRow) lrow
    return ()

addClient clientId metainf inf table row =  do
    now <- liftIO getCurrentTime
    let
      tdi = fmap (M.toList .getPKM) $ join $ (\ t -> fmap (tblist' t ) .  traverse (fmap _tb . (\(k,v) -> fmap (Attr k) . readType (keyType $ k) . T.unpack  $ v).  first (lookKey inf (tableName t))  ). F.toList) <$>  table <*> row
    newi <- updateClient metainf inf table tdi clientId now
    let new = maybe newi (\table -> apply newi (liftPatch metainf "clients" $addTable (clientId) now table  0)) table
    dbmeta  <- prerefTable metainf (lookTable metainf "clients")
    putPatch (patchVar $dbmeta ) [PatchRow $patch new]
    (_,_,clientState,_)  <- refTables' metainf (lookTable metainf "clients") Nothing (WherePredicate (AndColl [PrimColl (keyRef [ (lookKey (meta inf) "clients" "clientid")] , Left (num clientId,Equals))]))
    return (clientId, getClient metainf clientId inf <$> clientState)



layFactsDiv i j =  if i then ("col-xs-" <> (show $  12 `div` fromIntegral (max 1 $ j))) else "col-xs-12"

chooserTable inf bset cliTid cli = do
  let
    pred2 =  [(keyRef ["schema"],Left (int $ schemaId inf  ,Equals))]
  orddb <- ui $ transactionNoLog  (meta inf) $
      (fst <$> (selectFromTable "ordering"  Nothing Nothing []  pred2))
  translationDb <- ui $ transactionNoLog  (meta inf) $
      (fst <$> (selectFromTable "table_name_translation" Nothing Nothing []  pred2 ))
  layout <- checkedWidget (pure False)
  body <- UI.div
  el <- ui $ accumDiffCounter (\ix -> evalUI body  . (\((table,sub))-> do
    header <- UI.h3
        # set UI.class_ "header"
        # sink0 text (facts $ T.unpack . lookDesc inf table <$> collectionTid translationDb)
    let
    ui$do
      i <-liftIO$ getWindow body
      ref <- prerefTable (meta inf ) (lookTable (meta inf ) "clients")
      now <- liftIO$ getCurrentTime
      let cpatch = liftPatch (meta inf) "clients" $ addTable  (wId i) now table ix
          dpatch now = liftPatch (meta inf) "clients" $ removeTable (wId i) now table ix
      putPatch (patchVar ref) [PatchRow cpatch]
      registerDynamic(do
        now <- getCurrentTime
        putPatch (patchVar ref) [PatchRow $ dpatch now])


    body <-  do
            if L.length sub == 1
               then do
                 viewerKey inf table ix cli  (triding layout ) cliTid
               else do
              els <- mapM (\t -> do
                  l <- UI.h4 #  set text (T.unpack $fromMaybe (rawName t)  $ rawTranslation t) # set UI.class_ "col-xs-12 header"
                  b <- viewerKey inf t ix cli  (triding layout )cliTid
                  element b # set UI.class_ "col-xs-12"
                  UI.div # set children [l,b]
                  ) sub
              UI.div # set children els
    UI.div # set children [header,body] # sink0 UI.class_ (facts $ layFactsDiv <$> triding layout <*> fmap M.size (triding bset))# set UI.style [("border","2px dotted gray")]
                              ).fst)                                  ( M.fromList . fmap (\i -> (i,())) . M.toList <$> triding bset)

  let sortTable els ord = fmap snd $ L.sortBy (flip $ comparing fst) $ fmap (first (\i -> tableOrder inf (fst i) ord )) els
  element body # sink0 UI.children (facts $ sortTable <$> fmap M.toList el <*> collectionTid orddb) # set UI.class_ "col-xs-12"
  element layout  # set UI.class_ "col-xs-1"
  return [getElement layout ,body]

viewerKey
  ::
      InformationSchema -> Table -> Int ->  Int -> Tidings Bool -> Tidings  (Maybe (TBData Key Showable)) -> UI Element
viewerKey inf table tix cli layoutS cliTid = mdo
  let layout = layFactsDiv <$> layoutS <*> pure 2
  iv   <- currentValue (facts cliTid)
  let
      lookT,lookPK :: TBData Key Showable -> Maybe (Int,TBData Key Showable)
      lookT iv = join $ fmap ((\t -> L.find (\(ix,i)->  G.indexPred (liftAccess (meta inf) "clients_table" $ keyRef ["table"],Left (txt (tableName table), Equals)) i) $ zip [0..] (fmap unTB1 $ F.toList t) ).unArray) (join $ unSOptional <$> i)
        where
          i = _fkttable <$> indexField (liftAccess (meta inf) "clients" $ (IProd Nothing ["selection"]) ) iv

      lookPK iv = join $ fmap ((\t -> safeHead  $ zip [0..] (fmap unTB1 $ F.toList t) ). unArray) (join $ unSOptional <$> i)
        where
          i = _fkttable <$> indexField (liftAccess (meta inf) "clients_table" $ (IProd Nothing ["selection"]) ) iv
      lookKV iv = let i = lookAttr' (meta inf)  "data_index" iv
                      unKey t = liftA2 (,) ((\(Attr _ (TB1 (SText i)))-> Just $ lookKey inf  (tableName table) i ) $ lookAttr' (meta inf)  "key" t  )( pure $ (\(Attr _ (TB1 (SDynamic i)))-> i) $ lookAttr'  (meta inf)  "val" t )
                in (\(IT _ (ArrayTB1 t)) -> catMaybes $ F.toList $ fmap (unKey.unTB1) t) i

  reftb@(vptmeta,vp,vpt,var) <- ui $ refTables inf table

  let
      tdi = (\i iv-> join $ traverse (\v -> G.lookup  (G.Idex (fmap snd $ justError "" $ traverse (traverse unSOptional' ) $v)) i ) iv ) <$> vpt <*> tdip
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
     tsort = sorting' . filterOrd <$> triding sortList
     filteringPred i = T.isInfixOf (T.pack $ toLower <$> i) . T.toLower . T.intercalate "," . fmap (T.pack . renderPrim ) . F.toList  .snd
     filtering res = (\t -> (filter (filteringPred t )) )<$> triding filterInpT  <*> res
     pageSize = 20
     divPage s = (s  `div` pageSize) +  if s `mod` pageSize /= 0 then 1 else 0
     lengthPage (fixmap) = s
        where (s,_)  = fromMaybe (sum $ fmap fst $ F.toList fixmap ,M.empty ) $ M.lookup mempty fixmap
  inisort <- currentValue (facts tsort)
  itemListEl <- UI.select # set UI.class_ "col-xs-6" # set UI.style [("width","100%")] # set UI.size "21"
  runFunction $ ffi "$(%1).selectpicker('mobile')" itemListEl
  wheel <- fmap negate <$> UI.mousewheel itemListEl
  let inivp = inisort .G.toList $ snd vp
  (offset,res3)<- mdo
    offset <- offsetFieldFiltered (pure 0) wheel   [(L.length <$> res3) ,L.length <$> vpt,(lengthPage <$> vptmeta)]
    res3 <- ui $ mapT0EventDyn inivp return ( tsort <*> (filtering $ fmap G.toList $ vpt) )
    return (offset, res3)
  ui $ onEventDyn (rumors $ triding offset) $ (\i ->  do
    transactionNoLog inf $ selectFrom (tableName table ) (Just $ divPage (i + pageSize) `div` ((opsPageSize $ schemaOps inf) `div` pageSize)) Nothing  [] $ mempty)
  let
    paging  = (\o -> (L.take pageSize . L.drop o) ) <$> triding offset
  page <- currentValue (facts paging)
  res4 <- ui $ mapT0EventDyn (page inivp) return (paging <*> res3)
  itemList <- listBoxElEq (\l m -> maybe False id $ liftA2 (\i j ->G.getIndex i == G.getIndex j) l m) itemListEl ((Nothing:) . fmap Just <$> res4) (Just <$> tds) (pure id) (pure (maybe id attrLine))
  let tds = (fmap join  $ triding itemList)

  (cru,ediff,pretdi) <- crudUITable inf (pure "+")  reftb [] [] (allRec' (tableMap inf) table) tds
  let pktds = fmap getPKM <$> tds
  dbmeta  <- liftIO$ prerefTable (meta inf)(lookTable (meta inf ) "clients")
  w  <- askWindow
  let diffpk = diffEvent (facts pktds ) (rumors pktds)
  ixpk<-ui$accumB 0 (pure (+1) <@diffpk)
  onEvent ((,)<$> ixpk <@>diffpk) (\(ix,v)->traverse (\sel -> do
    now <- liftIO$ getCurrentTime
    let p =liftPatch (meta inf) "clients" $ addRow  (wId w) now  (M.toList sel ) tix ix
    putPatch (patchVar dbmeta) [PatchRow p]
    ui$registerDynamic (do
      now <- liftIO$ getCurrentTime
      let d =liftPatch (meta inf) "clients" $ removeRow (wId w) now  tix ix
      putPatch (patchVar dbmeta) [PatchRow d]
          )
        )v)

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
