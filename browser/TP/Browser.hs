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
    now <- liftIO getCurrentTime
    let obj = clientCreate inf now
    Just i@(TableModification _ _ _ _ (CreateRow (ix,_))) <-  insertFrom (lookMeta inf  "clients" ) obj
    tell [i]
    lift . registerDynamic . closeDynamic $ do
      now <- liftIO getCurrentTime
      let
        pt = [PAttr (lookKey inf "clients" "up_time") (PInter False (ER.Finite $ PAtom (STime $ STimestamp now) , False))]
      transactionNoLog inf $ do
        v <- patchFrom (lookMeta inf "clients") ix  pt
        tell (maybeToList v)
      return ()
    return i

attrIdex l =  G.Idex $  fmap (\(Attr i k) -> k) l


addServer inf =  do
    now <- liftIO getCurrentTime
    let
      obj = serverCreate inf now
    transactionNoLog inf $ insertFrom (lookMeta inf "server") obj

idexToPred t (G.Idex  i) = head $ (\(k,a)-> (keyRef k,Left (a,Contains))) <$>  zip (rawPK t) (F.toList i)

deleteServer inf (TableModification _ _ _ _ (CreateRow (ix,o))) = do
  now <- liftIO getCurrentTime
  (_,(_,tb)) <- transactionNoLog inf $ selectFrom "clients"  Nothing Nothing [] (WherePredicate (AndColl [PrimColl (keyRef (lookKey inf "clients" "up_time") ,Left (TB1 (STime $ STimestamp now),Contains))]))
  let
    t= lookTable inf "clients"
    pk = Attr (lookKey inf "clients" "up_time")(TB1 (STime $ STimestamp now))
    oldClis =  L.filter (G.indexPred (idexToPred t $ attrIdex [pk])) (G.toList tb)
    pt old = (G.getIndex (lookMeta inf "clients")old,[PAttr (lookKey inf "clients" "up_time") ( PInter False (ER.Finite $ PAtom (STime $ STimestamp now) , False))])

  mapM_ (\old -> transactionNoLog inf $ do
    v <- uncurry (updateFrom (lookMeta inf "clients") old) (pt old)
    tell (maybeToList v)
    return v) oldClis
  let pt = (G.getIndex (tableMeta $lookTable inf "server")o,[PAttr (lookKey inf "server" "up_time") (PInter False (ER.Finite $ PAtom (STime $ STimestamp now) , False))])
  transactionNoLog inf $ uncurry (updateFrom (lookMeta inf "server")o )pt

trackTable
  :: InformationSchemaKV Key Showable
  -> Int
  -> Table
  -> Int
  -> Int
  -> Dynamic ()
trackTable inf cid table six ix = do
  now <- lift getCurrentTime
  let cpatch = liftPatch (meta inf) "clients" <$> addTable  cid now table six ix
      dpatch now = liftPatch (meta inf) "clients" <$> removeTable  cid now table six ix
  ref <- prerefTable (meta inf ) (lookTable (meta inf ) "clients")
  putPatch (patchVar ref) [PatchRow cpatch]
  registerDynamic(do
    now <- getCurrentTime
    putPatch (patchVar ref) [PatchRow $ dpatch now])

removeTable :: Int -> UTCTime -> Table -> Int -> Int ->  (TBIndex Showable,TBIdx Text Showable)
removeTable idClient now table  six tix = atClient idClient [PInline "selection" (POpt $ Just $ PIdx six (Just $ PAtom
        [PInline "selection" (POpt $ Just $ PIdx tix (Just $ PAtom
                        ([ PAttr "up_time" ( PInter False (Interval.Finite $ patch(time now),True ))])))
        ]))]

addTable :: Int -> UTCTime -> Table -> Int -> Int ->  (TBIndex Showable,TBIdx Text Showable)
addTable idClient now table  six tix
  = atClient idClient [PInline "selection" (POpt$Just $ PIdx six $ Just$ PAtom
     [PInline "selection" (POpt $ Just $ PIdx tix (Just $ patch$
      TB1 $ encodeT ( ClientTableSelection (tableName table) (startTime now) [])))])]

atClient idClient =  (G.Idex [num idClient],) . (PAttr "id" (POpt $ Just $ patch $num idClient):)

removeRow idClient now six tix rix
  =  atClient idClient [PInline "selection" (POpt$Just $ PIdx six $ Just$ PAtom
        [PInline "selection" (POpt$Just $ PIdx tix $ Just$ PAtom
          [PInline "selection" $ POpt $ Just $ PIdx rix $ Just $ PAtom
            ([ PAttr "up_time" ( PInter False (Interval.Finite $ patch(time now),True ))])])])]


addRow idClient now tdi six tix rix
  =  atClient idClient [PInline "selection" (POpt$Just $ PIdx six $ Just$ PAtom
       [PInline "selection" (POpt$Just $ PIdx tix $ Just$ PAtom
          [PInline "selection" $ POpt $ Just $ PIdx rix $ Just $ PAtom $ patch(
              encodeT $ createRow now tdi)])])]



startTime now = Interval.interval (Interval.Finite now,True) (Interval.PosInf,True)
createRow now tdi = ClientRowSelection ( startTime now) (uncurry ClientPK . first keyValue <$>  tdi)

instance DecodeTable ClientPK where
  encodeT (ClientPK i j) = tblist [Attr "key" (txt i), Attr "val" (TB1 . SDynamic $ j)]
  decodeT = ClientPK <$>   (unOnly . primS  "key") <*> (primS "val")


instance DecodeTable ClientRowSelection where
  encodeT (ClientRowSelection now tdi) =
    tblist
      [ Attr "up_time" (encFTB $ encodeS <$> now)
      , IT "data_index" (array (TB1 . encodeT) tdi)
      ]
  decodeT = ClientRowSelection <$>  (primS  "up_time") <*> (nestS "data_index")

instance DecodeTable ClientTableSelection where
  encodeT (ClientTableSelection table now sel) =
    tblist
      [ Attr "table" (txt table)
      , Attr "up_time" (encFTB$ encodeS <$> now)
      , IT "selection" (encFTB $ encodeT <$> sel)
      ]
  decodeT = ClientTableSelection <$> ( unOnly . primS "table") <*> (primS  "up_time") <*> (nestS "selection")

instance DecodeTable ClientSchemaSelection where
  encodeT (ClientSchemaSelection sch now sel) =
    tblist
      [ Attr "schema" (TB1 (SNumeric sch))
      , Attr "up_time" (encFTB$ encodeS <$> now)
      , IT "selection" (encFTB $ encodeT <$> sel)
      ]
  decodeT = ClientSchemaSelection <$> ( unOnly . primS "schema") <*> (primS  "up_time") <*> (nestS "selection")

instance DecodeTable ClientState where
  encodeT (ClientState cli time sel) =
    tblist
      [ Attr "id" (TB1 (SNumeric cli))
      , Attr "username" (TB1 (SNumeric cli))
      , Attr "up_time" (encFTB $ encodeS <$> time)
      , IT "selection" (encFTB $ encodeT <$> sel)]
  decodeT = ClientState <$> ( unOnly . primS "id") <*> (primS  "up_time") <*> (nestS "selection")

unOnly (Only i) = i
primS s d = att . ix s $ d
nestS s d = itt . ix s $ d

time = TB1  . STime . STimestamp

inter i j  = IntervalTB1 $ Interval.interval (i,True) (j,True)

data ClientState
  = ClientState
    { client_id ::  Int
    , client_up_time :: Interval UTCTime
    , schema_selection :: [ClientSchemaSelection]
    }deriving(Eq,Show)

data ClientSchemaSelection
  = ClientSchemaSelection
    { schema_sel :: Int
    , schema_up_time :: Interval UTCTime
    , table_selection :: [ClientTableSelection]
    }deriving(Eq,Show)

data ClientTableSelection
  = ClientTableSelection
    { table_sel :: Text
    , table_up_time :: Interval UTCTime
    , row_selection :: [ClientRowSelection]
    }deriving(Eq,Show)

data ClientRowSelection
  = ClientRowSelection
    { row_up_time :: Interval UTCTime
    , data_index :: Non.NonEmpty  ClientPK
    }deriving(Eq,Show)

data ClientPK
  = ClientPK
    { key :: Text
    , value :: FTB Showable
    }deriving(Eq,Show)

addSchema :: Int -> UTCTime -> InformationSchema -> Int ->  (TBIndex Showable,TBIdx Text Showable)
addSchema idClient now inf tix
  =atClient idClient  [PInline "selection" (POpt $ Just $ PIdx tix (Just $ patch$
      TB1 $ encodeT ( ClientSchemaSelection (schemaId inf ) (startTime now) [])))]


removeSchema :: Int -> UTCTime -> InformationSchema -> Int ->  (TBIndex Showable,TBIdx Text Showable)
removeSchema idClient now inf tix
  =atClient idClient  [PInline "selection" (POpt $ Just $ PIdx tix (
      (Just $ PAtom
                        ([ PAttr "up_time" ( PInter False (Interval.Finite $ patch(time now),True ))]))))]


num = TB1 . SNumeric

getClient metainf clientId ccli = G.lookup (idex metainf "clients"  [("id",num clientId)]) ccli :: Maybe (TBData Key Showable)


editClient six metainf inf dbmeta ccli  table tdi clientId now ix
  | fmap tableName table == Just "clients" && schemaName inf == "metadata" = return ()
  | otherwise = maybe (return ()) (\table -> do
    let
      lrow = PatchRow $ liftPatch metainf (tableName table) <$> addSchema  clientId now inf six
    putPatch (patchVar $ iniRef dbmeta ) [lrow]) table

lookClient clientId metainf = do
    (_,_,clientState,_,_)  <- refTables' metainf (lookTable metainf "clients") Nothing (WherePredicate (AndColl [PrimColl (keyRef (lookKey metainf "clients" "id") , Left (num clientId,Equals))]))
    return (getClient metainf clientId <$> clientState)



addSchemaIO clientId metainf inf six = do
  dbmeta  <- prerefTable metainf (lookTable metainf "clients")
  now <- liftIO getCurrentTime
  let new = addSchema clientId  now inf six
  putPatch (patchVar dbmeta) [PatchRow $ liftPatch metainf "clients"  <$>new]
  registerDynamic (do
    now <- liftIO getCurrentTime
    let new = removeSchema clientId  now inf six
    putPatch (patchVar dbmeta) [PatchRow $ liftPatch metainf "clients"  <$>new])



layFactsDiv i j =  case i of
   Vertical -> "col-xs-" <> show (12 `div` fromIntegral (max 1 j))
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


chooserTable six inf bset cliTid cli = do
  let
    pred2 =  [(keyRef "schema",Left (int $ schemaId inf  ,Equals))]
  (orddb ,translationDb) <- ui $ transactionNoLog  (meta inf) $
    (,) <$> (fst <$> selectFromTable "ordering"  Nothing Nothing []  pred2)
        <*> (fst <$> selectFromTable "table_name_translation" Nothing Nothing []  pred2 )
  w <- askWindow
  el <- ui $ accumDiffCounter (\ix -> runUI w . (\table-> do
    header <- UI.h4
        # set UI.class_ "header"
        # sink0 text (facts $ T.unpack . lookDesc inf table <$> collectionTid translationDb)
    ui $ trackTable inf (wId w) table six ix
    body <-
      if L.null (rawUnion table)
         then
           viewerKey six inf table ix cli cliTid
         else do
        els <- mapM (\t -> do
          l <- UI.h4 #  set text (T.unpack $fromMaybe (rawName t)  $ rawTranslation t) # set UI.class_ "col-xs-12 header"
          b <- viewerKey six inf t ix cli  cliTid
          element b # set UI.class_ "col-xs-12"
          a <- UI.a # set (UI.strAttr "data-toggle") "tab" # set UI.href ("#" ++T.unpack (rawName t))
              # set text (T.unpack $fromMaybe (rawName t)  $ rawTranslation t)
          h <- UI.li
              # set  UI.children [a]
          c <- UI.div
              # set children [l,b]
              # set UI.id_ (T.unpack $ rawName t)
              # set UI.class_ "tab-pane"
          return (h,c)) (rawUnion table)
        h <- UI.div # set children (fst <$> els) # set UI.class_ "nav nav-tabs"
        runFunctionDelayed h $ ffi  "$(%1).find('li').click(function (e) { $('.active').removeClass('active');})" h
        b <- UI.div # set children (snd <$> els) # set UI.class_ "tab-content"
        UI.div # set children [h,b]
    UI.div
      # set children [header,body]
      # set UI.style [("border","2px dotted "),("border-color",maybe "gray" (('#':).T.unpack) (schemaColor inf))]))
        (triding bset)
  layoutSel onAlt (F.toList <$> el)

viewerKey
  ::
      Int -> InformationSchema -> Table -> Int ->  Int -> Tidings  (Maybe (TBData Key Showable)) -> UI Element
viewerKey six inf table tix cli cliTid = do
  iv   <- currentValue (facts cliTid)
  let
      lookT,lookPK :: TBData Key Showable -> Maybe (TBData Key Showable)
      lookT iv = do
        schemas <-  indexField (liftAccess (meta inf) "clients" (keyRef "selection") ) iv >>= unSOptional ._fkttable
        s <- L.find (G.indexPred (liftAccess (meta inf) "clients_schema" $ keyRef "schema",Left (int (schemaId inf), Equals))) (fmap unTB1 (F.toList $ unArray schemas))
        tables <-  indexField (liftAccess (meta inf) "clients_schema" (keyRef "selection") ) iv >>= unSOptional . _fkttable
        L.find (G.indexPred (liftAccess (meta inf) "clients_table" $ keyRef "table",Left (txt (tableName table), Equals))) (fmap unTB1 (F.toList $ unArray tables))

      lookPK iv = fmap (unTB1 . Non.head . unArray) (unSOptional =<< i)
        where
          i = _fkttable <$> indexField (liftAccess (meta inf) "clients_table" (keyRef "selection") ) iv
      lookKV iv = let i = lookRef ["data_index"] iv
                      unKey t = (,) ((\(TB1 (SText i))-> lookKey inf  (tableName table) i ) $ lookAttr' "key" t  )( (\(TB1 (SDynamic i))-> i) $ lookAttr' "val" t )
                in (\(ArrayTB1 t) -> F.toList $ fmap (unKey.unTB1) t) i

  reftb@(_,_,vpt,_,_) <- ui $ refTables' inf table Nothing mempty
  let
    tdi = (\i -> join . traverse (\v -> G.lookup  (G.Idex (justError "no key" $ traverse unSOptional' $ fmap snd v)) i ) ) <$> vpt <*> tdip
    tdip = join . fmap (join . fmap ( fmap lookKV. lookPK ). lookT ) <$> cliTid
  itemList <- selector inf table reftb (pure Nothing) tdi
  v <- ui $ currentValue (facts tdi)
  tds <- do
    let
      updatedValue = (\i j -> const . join $ flip G.lookup j  . G.getIndex  (tableMeta table)<$> i )<$> facts (triding itemList)<@> rumors vpt
      selection = const <$> rumors (triding itemList)
    ui $ accumT  v (unionWith (.) selection  updatedValue)

  (cru,pretdi) <- crudUITable inf table reftb M.empty [] (allRec' (tableMap inf) table) tds
  let pktds = fmap (getPKM (tableMeta table))<$> tds
  dbmeta  <- ui $ prerefTable (meta inf)(lookTable (meta inf ) "clients")
  w  <- askWindow
  let diffpk = diffEvent (facts pktds ) (rumors pktds)
  ixpk <- ui $ accumB 0 (pure (+1) <@diffpk)
  onEvent ((,)<$> ixpk <@>diffpk) (\(ix,v)->
    traverse (traverse (\sel -> do
      now <- liftIO getCurrentTime
      let p =liftPatch (meta inf) "clients" <$> addRow  (wId w) now  sel  six tix ix
      putPatch (patchVar dbmeta) [PatchRow p]
      ui $ registerDynamic (do
        now <- liftIO getCurrentTime
        let d =liftPatch (meta inf) "clients" <$> removeRow (wId w) now  six  tix ix
        putPatch (patchVar dbmeta) [PatchRow d]
            ))) (Non.nonEmpty . M.toList <$> v))

  title <- UI.div #  sink items (pure . maybe UI.h4 (\i -> UI.h4 # attrLine inf (tableMeta table) i  )  <$> facts tds) # set UI.class_ "col-xs-8"
  insertDiv <- UI.div # set children [title] # set UI.class_ "container-fluid"
  insertDivBody <- UI.div # set children [insertDiv,cru]
  UI.div # set children [getElement itemList,insertDivBody ]
