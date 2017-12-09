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
import Postgresql.Backend (postgresOps)
import Prelude hiding (head)
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

clientCreate metainf now = liftTable' metainf "clients" row
  where
    row = tblist
             [
               Attr "up_time" (IntervalTB1 $ Interval.interval (ER.Finite (time now),True) (ER.PosInf,True)),
               IT "selection"  (LeftTB1 Nothing)
              ]

serverCreate metainf now = liftTable' metainf "server" row
  where row = tblist
             [
               Attr "up_time" (IntervalTB1 $ Interval.interval (ER.Finite (time now),True) (ER.PosInf,True))
              ]

addClientLogin inf =  transactionNoLog inf $ do
    now <- liftIO$ getCurrentTime
    let
      obj = clientCreate inf now
    i <-  insertFrom (lookMeta inf  "clients" ) obj
    tell (maybeToList i)
    return i

attrIdex l =  G.Idex $  fmap (\(Attr i k) -> k) l

deleteClientLogin inf i= do
  now <- liftIO $ getCurrentTime

  (_,(_,tb)) <- transactionNoLog inf $ selectFrom "clients"  Nothing Nothing [] (WherePredicate (AndColl [PrimColl (keyRef (lookKey inf "clients" "id") , Left ((TB1 (SNumeric i)),Equals))]))
  let
    pk = Attr (lookKey inf "clients" "id") (TB1 (SNumeric i))
    old = justError ("no row " <> show (attrIdex [pk]) ) $ G.lookup (attrIdex [pk]) tb
    pt = ( G.getIndex (lookMeta inf "clients")old,[PAttr (lookKey inf "clients" "up_time") ( PInter False ((ER.Finite $ PAtom (STime $ STimestamp (now)) , False)))])

  transactionNoLog inf $ do
    v <- updateFrom (lookMeta inf "clients") old (fst pt) (snd pt)
    tell (maybeToList v)
    return v

addServer inf =  do
    now <- liftIO$ getCurrentTime
    let
      obj = serverCreate inf now
    transactionNoLog inf $ insertFrom (lookMeta inf "server") obj

idexToPred t (G.Idex  i) = head $ (\(k,a)-> (keyRef k,Left (a,Contains))) <$>  zip (rawPK t) (F.toList i)

deleteServer inf (TableModification _ _ _ _ (CreateRow o)) = do
  now <- liftIO $ getCurrentTime
  (_,(_,tb)) <- transactionNoLog inf $ selectFrom "clients"  Nothing Nothing [] (WherePredicate (AndColl [PrimColl (keyRef (lookKey inf "clients" "up_time") ,Left ((TB1 (STime $ STimestamp (now))),Contains))]))
  let
    t= lookTable inf "clients"
    pk = Attr (lookKey inf "clients" "up_time")(TB1 (STime $ STimestamp (now)))
    oldClis =  L.filter (G.indexPred (idexToPred t $ attrIdex [pk])) (G.toList tb)
    pt old = (G.getIndex (lookMeta inf "clients")old,[PAttr (lookKey inf "clients" "up_time") ( PInter False ((ER.Finite $ PAtom (STime $ STimestamp (now)) , False)))])

  mapM (\(old) -> transactionNoLog inf $ do
    v <- uncurry (updateFrom (lookMeta inf "clients") old) (pt old)
    tell (maybeToList v)
    return v) oldClis
  let pt = (G.getIndex (tableMeta $lookTable inf "server")o,[PAttr (lookKey inf "server" "up_time") (PInter False ((ER.Finite $ PAtom (STime $ STimestamp (now)) , False)))])
  transactionNoLog inf $ uncurry (updateFrom (lookMeta inf "server")o )pt

removeTable :: Int -> UTCTime -> Table -> Int -> Int ->  (TBIndex Showable,TBIdx Text Showable)
removeTable idClient now table  six tix = atClient idClient ([PInline "selection" (POpt $ Just $ PIdx six (Just $ PAtom $
        ([PInline "selection" (POpt $ Just $ PIdx tix (Just $ PAtom
                        ([ PAttr "up_time" ( PInter False (Interval.Finite $ patch(time now),True ))])))
        ])))])

addTable :: Int -> UTCTime -> Table -> Int -> Int ->  (TBIndex Showable,TBIdx Text Showable)
addTable idClient now table  six tix
  = atClient idClient [PInline "selection" (POpt$Just $ PIdx six $ Just$ PAtom
     ([PInline "selection" (POpt $ Just $ PIdx tix (Just $ patch$
      TB1 $ encodeT ( ClientTableSelection (tableName table) (startTime now) [])))]))]

atClient idClient =  (G.Idex [num idClient],)

removeRow idClient now six tix rix
  =  atClient idClient [PInline "selection" (POpt$Just $ PIdx six $ Just$ PAtom
        ([PInline "selection" (POpt$Just $ PIdx tix $ Just$ PAtom
          ([PInline "selection" $ POpt $ Just $ PIdx rix $ Just $ PAtom(
            ([ PAttr "up_time" ( PInter False (Interval.Finite $ patch(time now),True ))]))]))]))]


addRow idClient now tdi six tix rix
  =  atClient idClient ([PInline "selection" (POpt$Just $ PIdx six $ Just$ PAtom
       ([PInline "selection" (POpt$Just $ PIdx tix $ Just$ PAtom
          ([PInline "selection" $ POpt $ Just $ PIdx rix $ Just $ PAtom $ patch(
              encodeT $ createRow now tdi)]))]))])



startTime now = Interval.interval (Interval.Finite now,True) (Interval.PosInf,True)
createRow now tdi = ClientRowSelection ( startTime now) (first keyValue <$>  tdi)

instance DecodeTable (Text, FTB Showable) where
  encodeT (i, j) = tblist [Attr "key" (txt i), Attr "val" (TB1 . SDynamic $ j)]

instance DecodeTable ClientRowSelection where
  encodeT (ClientRowSelection now tdi) =
    tblist
      [ Attr "up_time" (encFTB $ encodeS <$> now)
      , IT "data_index" (array (TB1 . encodeT) tdi)
      ]

instance DecodeTable ClientTableSelection where
  encodeT (ClientTableSelection table now sel) =
    tblist
      [ Attr "table" (txt table)
      , Attr "up_time" (encFTB$ encodeS <$> now)
      , IT "selection" (encFTB $ encodeT <$> sel)
      ]
instance DecodeTable ClientSchemaSelection where
  encodeT (ClientSchemaSelection sch now sel) =
    tblist
      [ Attr "schema" (TB1 (SNumeric sch))
      , Attr "up_time" (encFTB$ encodeS <$> now)
      , IT "selection" (encFTB $ encodeT <$> sel)
      ]
instance DecodeTable ClientState where
  encodeT (ClientState cli time sel) =
    tblist
      [ Attr "id" (TB1 (SNumeric cli))
      , Attr "up_time" (encFTB $ encodeS <$> time)
      , IT "selection" (encFTB $ encodeT <$> sel)]

time = TB1  . STime . STimestamp

inter i j  = IntervalTB1 $ Interval.interval (i,True) (j,True)

data ClientState
  = ClientState
    { client_id ::  Int
    , client_up_time :: Interval UTCTime
    , schema_selection :: [ClientSchemaSelection]
    }

data ClientSchemaSelection
  = ClientSchemaSelection
    { schema_sel :: Int
    , schema_up_time :: Interval UTCTime
    , table_selection :: [ClientTableSelection]
    }

data ClientTableSelection
  = ClientTableSelection
    { client_table :: Text
    , table_up_time :: Interval UTCTime
    , row_selection :: [ClientRowSelection]
    }

data ClientRowSelection
  = ClientRowSelection
    { row_up_time :: Interval UTCTime
    , data_index :: Non.NonEmpty (Text ,FTB Showable)
    }

addSchema :: Int -> UTCTime -> InformationSchema -> Int ->  (TBIndex Showable,TBIdx Text Showable)
addSchema idClient now inf tix
  =atClient idClient  ([PInline "selection" (POpt $ Just $ PIdx tix (Just $ patch$
      TB1 $ encodeT ( ClientSchemaSelection (schemaId inf ) (startTime now) [])))])


num = TB1 . SNumeric

getClient metainf clientId inf ccli = G.lookup (idex metainf "clients"  [("id",num clientId)]) ccli :: Maybe (TBData Key Showable)

deleteClient metainf clientId = do
  dbmeta  <-  prerefTable metainf (lookTable metainf "clients")
  putPatch (patchVar dbmeta) [PatchRow ( idex metainf "clients" [("id",num clientId)],[])]

editClient metainf inf dbmeta ccli  table tdi clientId now ix
  | fmap tableName table == Just "clients" && schemaName inf == "metadata" = return ()
  | otherwise = maybe (return ()) (\table -> do
    let
      lrow = PatchRow $ liftPatch metainf (tableName table) <$> addSchema  clientId now inf 0
    putPatch (patchVar $ iniRef $ dbmeta ) [lrow]) table


addClient clientId metainf inf table row =  do
    now <- liftIO getCurrentTime
    let
      tdi = fmap (M.toList ) $ join $ (\t -> fmap (getPKM (tableMeta t) . tblist'  ) .  traverse ((\(k,v) -> fmap (Attr k) . readType (keyType $ k) . T.unpack  $ v).  first (lookKey inf (tableName t))  ). F.toList) <$>  table <*> row
    traverse (\table -> do
      let new = liftPatch metainf "clients" <$> addTable clientId now table  0 0
      dbmeta  <- prerefTable metainf (lookTable metainf "clients")
      putPatch (patchVar $dbmeta ) [PatchRow $new] ) table
    (_,_,clientState,_,_)  <- refTables' metainf (lookTable metainf "clients") Nothing (WherePredicate (AndColl [PrimColl (keyRef (lookKey (meta inf) "clients" "id") , Left (num clientId,Equals))]))
    return (clientId, getClient metainf clientId inf <$> clientState)

layFactsDiv i j =  case i of
   Vertical -> "col-xs-" <> (show $  12 `div` fromIntegral (max 1 $ j))
   Horizontal -> "col-xs-12"
   Tabbed -> "col-xs-12"

data Layout
  = Vertical
  | Horizontal
  | Tabbed
  deriving(Eq,Ord,Show)


layoutSel keyword list = do
  let styles = [Vertical,Horizontal,Tabbed]
  body <- UI.div
  alt <- keyword 32 body
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
      ((,) <$> triding sel <*> list)
  element body # sink children (facts list)
  UI.div # set children [getElement sel,body]


chooserTable inf bset cliTid cli = do
  let
    pred2 =  [(keyRef "schema",Left (int $ schemaId inf  ,Equals))]
  (orddb ,translationDb) <- ui $ transactionNoLog  (meta inf) $
    (,) <$> (fst <$> selectFromTable "ordering"  Nothing Nothing []  pred2)
        <*> (fst <$> selectFromTable "table_name_translation" Nothing Nothing []  pred2 )
  w <- askWindow
  el <- ui $ accumDiffCounter (\ix -> runUI w . (\((table,sub))-> do
    header <- UI.h4
        # set UI.class_ "header"
        # sink0 text (facts $ T.unpack . lookDesc inf table <$> collectionTid translationDb)
    let
    ui$do
      now <- liftIO$ getCurrentTime
      let cpatch = liftPatch (meta inf) "clients" <$> addTable   (wId w) now table 0 ix
          dpatch now = liftPatch (meta inf) "clients" <$> removeTable  (wId w) now table 0 ix
      ref <- prerefTable (meta inf ) (lookTable (meta inf ) "clients")
      putPatch (patchVar ref) [PatchRow cpatch]
      registerDynamic(do
        now <- getCurrentTime
        putPatch (patchVar ref) [PatchRow $ dpatch now])
    body <-  do
      if L.length sub == 1
         then
           viewerKey inf table ix cli cliTid
         else do
        els <- mapM (\t -> do
          l <- UI.h4 #  set text (T.unpack $fromMaybe (rawName t)  $ rawTranslation t) # set UI.class_ "col-xs-12 header"
          b <- viewerKey inf t ix cli  cliTid
          element b # set UI.class_ "col-xs-12"
          a <- UI.a # set (UI.strAttr "data-toggle") "tab" # set UI.href ("#" ++( T.unpack $ rawName t))
              # set text (T.unpack $fromMaybe (rawName t)  $ rawTranslation t)
          h <- UI.li
              # set  UI.children [a]
          c <- UI.div
              # set children [l,b]
              # set UI.id_ (T.unpack $ rawName t)
              # set UI.class_ "tab-pane"
          return (h,c)) sub
        h <- UI.div # set children (fst <$> els) # set UI.class_ "nav nav-tabs"
        runFunctionDelayed h $ ffi  "$(%1).find('li').click(function (e) { $('.active').removeClass('active');})" h
        b <- UI.div # set children (snd <$> els) # set UI.class_ "tab-content"
        UI.div # set children [h,b]
    UI.div
      # set children [header,body]
      # set UI.style [("border","2px dotted "),("border-color",maybe "gray" (('#':).T.unpack) (schemaColor inf))]).fst)
        (M.fromList . fmap (\i -> (i,())) . M.toList <$> triding bset)
  layoutSel onAlt (F.toList <$> el)

viewerKey
  ::
      InformationSchema -> Table -> Int ->  Int -> Tidings  (Maybe (TBData Key Showable)) -> UI Element
viewerKey inf table tix cli cliTid = do
  iv   <- currentValue (facts cliTid)
  let
      lookT,lookPK :: TBData Key Showable -> Maybe (TBData Key Showable)
      lookT iv = do
        schemas <-  indexField (liftAccess (meta inf) "clients" $ (keyRef "selection") ) iv >>= unSOptional ._fkttable
        s <- L.find (G.indexPred (liftAccess (meta inf) "clients_schema" $ keyRef "schema",Left (int (schemaId inf), Equals))) $  (fmap unTB1 (F.toList $ unArray schemas))
        tables <-  indexField (liftAccess (meta inf) "clients_schema" $ (keyRef "selection") ) iv >>= unSOptional . _fkttable
        L.find (G.indexPred (liftAccess (meta inf) "clients_table" $ keyRef "table",Left (txt (tableName table), Equals))) $  (fmap unTB1 (F.toList $ unArray tables))

      lookPK iv = fmap (unTB1 . Non.head . unArray) (unSOptional =<< i)
        where
          i = _fkttable <$> indexField (liftAccess (meta inf) "clients_table" $ (keyRef "selection") ) iv
      lookKV iv = let i = lookAttr' (meta inf)  "data_index" iv
                      unKey t = (,) ((\(Attr _ (TB1 (SText i)))-> lookKey inf  (tableName table) i ) $ lookAttr' (meta inf)  "key" t  )( (\(Attr _ (TB1 (SDynamic i)))-> i) $ lookAttr'  (meta inf)  "val" t )
                in (\(IT _ (ArrayTB1 t)) -> F.toList $ fmap (unKey.unTB1) t) i

  reftb@(vptmeta,vp,vpt,_,var) <- ui $ refTables' inf table Nothing mempty
  let
    tdi = (\i -> join . traverse (\v -> G.lookup  (G.Idex (justError "no key" $ traverse (unSOptional' ) $ fmap snd v)) i ) ) <$> vpt <*> tdip
    tdip = join . fmap (join . fmap ( fmap (lookKV ). lookPK ). lookT ) <$> cliTid
  itemList <- selector inf table reftb (pure Nothing) tdi
  v <- ui $ currentValue (facts tdi)
  tds <-  mdo
    let
      updatedValue = (\i j -> const . join $ flip G.lookup j  . G.getIndex  (tableMeta table)<$> i )<$> facts tds <@> rumors vpt
      selection = const <$> rumors (triding itemList)
    tds <- ui $ accumT  v (unionWith (.) selection  updatedValue)
    ui $ cacheTidings tds

  (cru,pretdi) <- crudUITable inf table reftb [] [] (allRec' (tableMap inf) table) tds
  let pktds = fmap (getPKM (tableMeta table))<$> tds
  dbmeta  <- ui $ prerefTable (meta inf)(lookTable (meta inf ) "clients")
  w  <- askWindow
  let diffpk = diffEvent (facts pktds ) (rumors pktds)
  ixpk <- ui $ accumB 0 (pure (+1) <@diffpk)
  onEvent ((,)<$> ixpk <@>diffpk) (\(ix,v)->
    traverse (traverse (\sel -> do
      now <- liftIO$ getCurrentTime
      let p =liftPatch (meta inf) "clients" <$> addRow  (wId w) now  sel  0 tix ix
      putPatch (patchVar dbmeta) [PatchRow p]
      ui $ registerDynamic (do
        now <- liftIO$ getCurrentTime
        let d =liftPatch (meta inf) "clients" <$> removeRow (wId w) now  0 tix ix
        putPatch (patchVar dbmeta) [PatchRow d]
            ))) (Non.nonEmpty . M.toList <$> v))

  title <- UI.div #  sink items (pure . maybe UI.h4 (\i -> UI.h4 # attrLine inf (tableMeta table) i  )  <$> facts tds) # set UI.class_ "col-xs-8"
  insertDiv <- UI.div # set children [title] # set UI.class_ "container-fluid"
  insertDivBody <- UI.div # set children [insertDiv,cru]
  UI.div # set children ([getElement itemList,insertDivBody ] )
