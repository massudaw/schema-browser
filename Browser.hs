{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE Arrows #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE NoMonomorphismRestriction,UndecidableInstances,FlexibleContexts,OverloadedStrings ,TupleSections, ExistentialQuantification #-}

import Query
import Step
import PrefeituraSNFSE
import Pdf
import Safe hiding (at)
import Siapi3
import CnpjReceita
import GHC.Generics
import qualified Network.HTTP as HTTP
import Network.Browser
import Widgets
import QueryWidgets
import Control.Concurrent
import Data.Functor.Apply
import System.Environment
import Debug.Trace
import Data.Ord
import Data.Tuple
import Data.Time.Format
import System.Locale
import Data.Aeson
import Utils
import Schema
import Data.Char (toLower)
import Gpx
import GHC.Int
import Data.Functor.Compose (Compose(..))
import PandocRenderer
import Data.Unique
import Control.Monad.Trans.Class as C
import Control.Monad.Trans.Maybe
import Control.Monad
import Postgresql
import Data.Aeson as A
import Data.Maybe
import Data.Distributive
import Data.Functor.Identity
import Text.Read
import qualified Data.HashMap.Strict as HM
import System.Directory
import Data.Typeable
import Data.Time.Parse
import Reactive.Threepenny
import           Database.PostgreSQL.Simple.Arrays as Arrays
import Data.Graph(stronglyConnComp,flattenSCCs)
import Control.Exception
import           Data.Attoparsec.Char8 hiding (Result)
import Data.Traversable (mapAccumL,Traversable,traverse)
import qualified Data.Traversable as Tra
import Warshal
import Data.Time.LocalTime
import Data.IORef
import Control.Monad((>=>),void,mapM,replicateM,liftM,join)
import Data.Functor.Compose
import qualified Database.PostgreSQL.Simple.TypeInfo.Static as TI
import qualified Data.List as L
import Data.Vector(Vector)
import qualified Data.Vector as V
import qualified Data.Interval as Interval
import qualified Data.ExtendedReal as ER
import qualified Data.ByteString.Char8 as BS
import qualified Data.ByteString.Lazy.Char8 as BSL
import Data.Time

import Reactive.Threepenny
import qualified Graphics.UI.Threepenny as UI
import Graphics.UI.Threepenny.Core hiding (get,delete)
import Data.Monoid hiding (Product(..))
import Data.Time.Parse

import System.IO.Unsafe
import Debug.Trace
import qualified Data.Foldable as F
import qualified Data.Text.Lazy as T
import qualified Data.Text.Lazy.IO as T
import Data.ByteString.Lazy(toStrict)
import Data.Text.Lazy.Encoding
import qualified Data.Text.Encoding as TE
import qualified Data.Text as TE
import Data.Text.Lazy (Text)
import qualified Data.Set as S
import Data.Set (Set)


import Database.PostgreSQL.Simple
import Database.PostgreSQL.Simple.Time
import Database.PostgreSQL.Simple.Ok
import Database.PostgreSQL.Simple.FromField as F
import qualified Database.PostgreSQL.Simple.ToField as TF
import qualified Database.PostgreSQL.Simple.FromRow as FR
import qualified Data.Map as M
import Blaze.ByteString.Builder(fromByteString)
import Blaze.ByteString.Builder.Char8(fromChar)
import Data.Map (Map)
import Data.String

import GHC.Show
import Data.Functor.Classes

import Control.Arrow
import Data.ByteString.Search (replace)
import Crea

setup
     :: Show a =>   Event [a] -> [String] -> Window -> UI ()
setup e args w = void $ do
  return w # set title "Data Browser"
  (evDB,chooserDiv) <- databaseChooser args
  body <- UI.div
  be <- stepper [] e
  pollRes <- UI.div # sink UI.text (show <$> be)
  getBody w #+ [element chooserDiv , element body]
  mapUITEvent body (traverse (\(conn,inf)-> do
    let k = M.keys (pkMap inf )
    span <- chooserKey  conn inf k (atMay args 2)
    element body # set UI.children [span,pollRes] )) evDB

listDBS :: IO (Map Text [Text])
listDBS = do
  connMeta <- connectPostgreSQL ("user=postgres dbname=postgres")
  dbs :: [Only Text]<- query_  connMeta "SELECT datname FROM pg_database  WHERE datistemplate = false"
  M.fromList <$> mapM (\db -> do
        connDb <- connectPostgreSQL ("user=postgres dbname=" <> toStrict (encodeUtf8 db))
        schemas :: [Only Text] <- query_  connDb "SELECT schema_name from information_schema.schemata"
        return (db,filter (not . (`elem` ["information_schema","pg_catalog","pg_temp_1","pg_toast_temp_1","pg_toast","public"])) $ fmap unOnly schemas)) (fmap unOnly dbs)


databaseChooser sargs = do
  let args = fmap T.pack sargs
      dbsInit = liftA2 (,) (safeHead args) (safeHead $ tail args)
  dbs  <- liftIO$ listDBS
  dbsW <- UI.listBox (pure $ concat $ fmap (\(i,j) -> (i,) <$> j) $ M.toList dbs ) (pure dbsInit  ) (pure (\i -> UI.div # set text (show i)))
  load <- UI.button # set UI.text "Connect" # sink UI.enabled (facts (isJust <$> UI.userSelection dbsW) )
  let genSchema (dbN,schemaN) = do
        conn <- connectPostgreSQL ("user=postgres dbname=" <> toStrict ( encodeUtf8 dbN ))
        inf <- keyTables conn  schemaN
        return (conn,inf)
  chooserT <-  mapTEvent (traverse genSchema) (UI.userSelection dbsW )
  let chooserEv = facts chooserT <@ UI.click load
  chooserDiv <- UI.div # set children [getElement dbsW,load]
  return $ (tidings (facts chooserT) chooserEv,chooserDiv)



unSOptional' (SOptional i ) = i
unSOptional' (SSerial i )  = i
unSOptional' i   = Just i

applyUI el f = (\a-> getWindow el >>= \w -> runUI w (f a))


tableNonRec (TB1 k ) = concat $ F.toList $  fmap (attrNonRec. unTB ) k


pollingUI' conn inf listRes p@(BoundedPollingPlugins n deftime (table,f) a) = do
    let plug = a conn inf
    headerP <- UI.div # set text n
    b <- UI.button # set UI.text "Submit"
    let  convert = 60000
    inp <- UI.input # set UI.value  (show deftime)
    inter <- stepper (deftime*convert) (filterJust  $ fmap (fmap (*convert).readMaybe) (UI.valueChange inp) )
    tmr <- UI.timer # sink UI.interval  inter
    staT <- UI.button # set text "Start" # set UI.enabled True
    stoT <- UI.button # set text "Stop" # set UI.enabled False
    onEvent (UI.click staT) (const (do
            UI.start tmr
            v <- tmr # UI.get UI.interval
            element stoT # set UI.enabled True
            element staT # set UI.enabled False ))
    onEvent (UI.click stoT) (const (do
            UI.stop tmr
            element stoT # set UI.enabled False
            element staT # set UI.enabled True ))
    let
      evpoll =(unionWith const (UI.click b) (UI.tick tmr))
    bht <- stepper Nothing (unsafeMapIO (fmap Just . const getCurrentTime) evpoll)
    output <- UI.div  # sink text ((\v  t -> "Timer Interval: " <> show (fromIntegral v/60000) <> " minutes" <> " -  Last Poll: " <> maybe "-" show t ) <$> inter <*> bht)
    let evb = ( (facts (filter (\i -> tdInput i && tdOutput1 i ) <$>listRes) <@ UI.click b))
        tdInput i =  maybe False (const True) $ allMaybes $ fmap (\t -> (if fst t then join . fmap unRSOptional' else id ) $ fmap snd $ (indexTable  $ snd t) i) (fst f)
        tdOutput1 i =  maybe True (const False) $ allMaybes $ fmap (\f -> (if not(fst f ) then join . fmap unRSOptional' else id ) $ fmap snd $ (indexTable  $ snd f) i) (snd f)

    bh <- stepper []  evb
    ev <- plug  (tidings bh evb)
    body <- UI.div  # set children [headerP,b,inp,staT,stoT,output,ev]
    return body


-- Split composite PKs in list of atomic pks
invertPK :: PK a -> [PK a]
invertPK  (PK k [] ) = fmap (\i -> PK [i] []) k
invertPK  (PK k d ) = zipWith (\i j -> PK [i] [j]) k d

projectFk schema k = case M.keys <$> M.lookup k schema of
                Just l ->   l
                Nothing -> []




doQueryTable :: Traversable t => Connection -> InformationSchema -> QueryT Identity (t KAttribute)  ->
                    (Map Key [Filter]) -> [PathQuery] -> (S.Set Key) -> IO (t Key,[t Showable])
doQueryTable conn inf q f p arg  = projectTable  conn inf (do
              predicate (concat $ filterToPred <$> (M.toList f))
              addPath p
              q
               ) arg
  where
    filterToPred (k,f) = fmap (k,) f


doQueryAttr :: Traversable t => Connection -> InformationSchema -> QueryT Identity (t KAttribute)  ->
                    (Map Key [Filter]) -> (S.Set Key) -> IO [t (Key,Showable)]
doQueryAttr conn inf q f arg  = fmap (fmap (fmap (\(Metric k , t)-> (k,t)))) $ projectKey' conn inf (do
              predicate (concat $ filterToPred <$> (M.toList f))
              q ) arg
  where
    filterToPred (k,f) = fmap (k,) f


doQuery :: Traversable t => Connection -> InformationSchema -> QueryT Identity (t KAttribute)  ->
                    (Map Key [Filter]) -> (S.Set Key) -> IO [t Showable]
doQuery conn inf q f arg  = fmap (fmap (fmap snd )) $ projectKey' conn inf (do
              predicate (concat $ filterToPred <$> (M.toList f))
              q
               ) arg
  where
    filterToPred (k,f) = fmap (k,) f




line n = UI.li # set  text n



chooserKey conn inf kitems i = do
  let initKey = pure . join $ fmap rawPK . flip M.lookup (tableMap inf) . T.pack <$> i
  filterInp <- UI.input
  filterInpBh <- stepper "" (onEnter filterInp)
  bset <- buttonFSet  (L.sortBy (comparing (fmap keyValue . S.toList )) kitems)  initKey ((\j -> (\i -> L.isInfixOf (toLower <$> j) (toLower <$> i) ))<$> filterInpBh) (\i -> case M.lookup i (pkMap inf) of
                                       Just (Raw _ i  _ _ _ _ )-> T.unpack i
                                       Nothing -> showVertex i )
  let bBset = triding bset
  body <- UI.div # sink items (facts (pure . chooseKey conn inf <$> bBset ))
  UI.div # set children [filterInp,getElement bset, body]

tableNonrec (TB1 k ) = concat $ F.toList $ _kvAttr $ fmap (attrNonRec .unTB) k

chooseKey
  :: Connection
     -> InformationSchema -> S.Set Key -> UI Element
chooseKey conn  inf key = mdo
  -- Filter Box (Saved Filter)
  let bBset = pure key :: Tidings (S.Set Key)
  let
    bFk = projectFk (hashedGraph inf) key

  vp <- joinTEvent $ (\j -> do
                    let rp = rootPaths'  (tableMap inf) (fromJust  $ M.lookup j $ pkMap inf )
                    queryWith_ (fromAttr (fst rp) ) conn  (traceShowId $ fromString $ T.unpack $ snd rp)
                    ) <$>   bBset
  -- Final Query ListBox
  filterInp <- UI.input
  filterInpBh <- stepper "" (onEnter filterInp)

  let filterInpT = tidings filterInpBh (onEnter  filterInp)

  let sortSet = filter (filterIntervalSort . keyType ) . F.toList . tableNonRec  . allRec' (tableMap inf). (\(Just i)-> i) . flip M.lookup (pkMap inf) <$> bBset
      filterIntervalSort (KInterval i) = False
      filterIntervalSort (KOptional i) = filterIntervalSort i
      filterIntervalSort i = True
  sortList  <- UI.listBox sortSet ((safeHead . F.toList) <$> sortSet) (pure (line . show))
  asc <- checkedWidget (pure False)
  let listManip :: (Show (f Showable), Traversable f) => String ->[f (Key,Showable)] -> Maybe Key -> Bool -> [f (Key,Showable)]
      listManip i j Nothing  _ =  filtering  i j
      listManip i j (Just s) b  =   L.sortBy ( ifApply (const b) flip (comparing (fmap snd .F.find ((== s).fst) )) ) $ filtering i j
      filtering :: (Show (f Showable), Functor f) => String -> [f (Key,Showable)] -> [f (Key,Showable)]
      filtering i = filter (L.isInfixOf (toLower <$> i) . fmap toLower . show  . fmap snd)
      listRes = listManip  <$> filterInpT <*> res2 <*> UI.userSelection sortList <*> triding asc

  itemList <- UI.listBox listRes  (pure Nothing ) (pure (\i -> line $   L.intercalate "," (F.toList $ fmap (renderShowable . snd ) $  _kvKey $ allKVRec i) <> "," <>  (L.intercalate "," $ fmap (renderShowable.snd) $  tableNonrec i)))
  element (getElement itemList) # set UI.multiple True
  element itemList # set UI.style [("width","100%"),("height","300px")]
  let
    foldr1Safe f [] = []
    foldr1Safe f xs = foldr1 f xs

  let

  pollingChk <- checkedWidget (pure True)
  pres  <- mapM (\i -> (_pollingName i ,) <$> pollingUI' conn inf ((\i j ->if i then j else [] ) <$> triding pollingChk <*>listRes ) i)  (filter (\(BoundedPollingPlugins n _  (tb,_)  _ )-> tb  == (tableName $ (\(Just i)-> i) $ M.lookup key (pkMap inf)  ))  [queryPollAndamentoB ,queryPollArtAndamento])
  pollingsDiv <- tabbed ((\(l,d)-> (l,d) )<$> pres)
  let
     pollings = ("POLLINGS" ,(pollingChk ,pollingsDiv ))
     filterOptions = case M.keys <$> M.lookup key (hashedGraph inf) of
               Just l -> key :  l
               Nothing -> [key]
     convertPK i = case fmap F.toList i of
        Nothing -> Just []
        i -> i
     table = (\(Just i)-> i) $ M.lookup key (pkMap inf)

  let whenWriteable = do
            (crud,_,evs) <- crudUITable conn inf  [queryTimeline,lplugOrcamento ,notaPrefeitura,queryArtCrea , queryArtBoletoCrea , queryShowMap ,queryCEPBoundary ,queryGeocodeBoundary,queryCNPJStatefull,queryCPFStatefull{-,queryCNPJBoundary -},queryTimeline, queryAndamentoB,queryArtAndamento ] (allRec' (tableMap inf) table) (UI.userSelection itemList)
            let eres = fmap (addToList  (allRec' (tableMap inf ) table )  <$> ) evs
            res2 <- accumTds vp eres
            insertDiv <- UI.div # set children [crud]
            chk <- checkedWidget (pure True)
            return (res2 , Just ("CRUD",(chk,insertDiv)) )
  (res2,crud) <- whenWriteable
  codeChk <- checkedWidget (pure False)
  createcode <- UI.textarea # set UI.text (T.unpack$ createTable table)
              # set style [("width","100%"),("height","300px")]
  dropcode <- UI.textarea # set UI.text (T.unpack$ dropTable table)
              # set style [("width","100%"),("height","300px")]
  code <- tabbed [("CREATE",createcode),("DROP",dropcode)]
  v <- liftIO  $ doQueryAttr conn inf (projectAllRec' (tableMap inf)) (M.singleton (lookKey inf "modification_table" "table_name") [Category $S.fromList $ [PK [SText .tableName $ table ] []]]) (S.singleton $lookKey inf "modification_table" "modification_id" )
  modBox <- checkedWidget (pure True)
  box <- UI.multiListBox (pure v) (pure []) (pure (\i -> line $   L.intercalate "," (F.toList $ fmap (show . fmap (renderShowable . snd )) $   _unTB1$ i) <> "," <>  (L.intercalate "," $ fmap (renderShowable.snd) $  tableNonrec i)))
  tab <- tabbedChk  (maybeToList crud <> [pollings,("CODE",(codeChk,code)),("MODS",(modBox,getElement box))])
  itemSel <- UI.div # set children [filterInp,getElement sortList,getElement asc]
  UI.div # set children ([itemSel,getElement itemList,tab] )




lplugOrcamento = BoundedPlugin "Orçamento" "pricing" (fst renderProjectPricingA )  (\i j k -> snd renderProjectPricingA $   k)

{-
pluginContactDiv conn inf inp = do
  b <- UI.button # set UI.text "query"
  st <- stepper "" (unsafeMapIO (fmap show) (pure (pluginContact inf )<@ UI.click b))
  e <- UI.div # sink UI.text st
  (,pure Nothing ) <$> UI.div # set UI.children [b,e]
-}

simpleGetRequest =  fmap BSL.pack . join . fmap HTTP.getResponseBody . HTTP.simpleHTTP . HTTP.getRequest

shortCutClick  t i = tidings (facts t) (facts t <@ i)

renderUrlM args url = fmap address . kv
  where
    kv i = allMaybes $ (\k -> join . fmap (\inp ->  fmap (snd k,) . M.lookup (fst k) . M.fromList $ fmap (\(k,v)-> (keyValue k,v)) inp ) $  i ) <$> args
    renderKv = HTTP.urlEncodeVars . fmap (\(k,v)-> (k , renderShowable v))
    address i =  url <> "?"  <> renderKv i

renderUrl args url = address
  where
    kv i = catMaybes $ (\k -> join . fmap (\inp ->  fmap (snd k,) . M.lookup (fst k) . M.fromList $ fmap (\(k,v)-> (keyValue k,v)) inp ) $  i ) <$> args
    renderKv = HTTP.urlEncodeVars . fmap (\(k,v)-> (k , renderShowable v))
    address i =  url <> "?"  <> renderKv (kv i)

testPlugin db pg input = startGUI defaultConfig $ \w -> do
    let e = withConnInf db (\conn inf -> fst <$> pg conn inf (pure (fmap (\((t,k),v) -> (lookKey inf t k ,v)) <$> input)))
    getBody w #+ [e]
    return ()

getRequest ::  String -> MaybeT IO BSL.ByteString
getRequest = join . C.lift . (`catch` (\e ->  traceShow (e :: IOException) $ return mzero ) ).  fmap return . simpleGetRequest


hasInput k v inp = case snd <$> lookInput  k inp of
                        Just i  -> testShowable v i
                        Nothing -> False

testShowable  v s = case s of
          (SOptional Nothing ) -> False
          (SOptional (Just i)) -> testShowable v i
          i -> v i

lookInput k = L.find ((== k ) . keyValue . fst )
lookInputV k = L.find ((== k ) . keyValue . fst )

queryAndamentoB =  BoundedPlugin "Andamento Bombeiro" "fire_project"( staticP arrow ) elem
  where
    arrow :: FunArrowPlug (Maybe Showable)
    arrow = proc t -> do
      idp <- varT "id_project" -< t
      ano <- varT "ano" -< t
      protocolo <- varT "protocolo" -< t
      cpf <- varT "id_owner,id_contact:id_owner:cgc_cpf" -< t
      odx "aproval_date" -<t
      returnA -< idp
    elem conn inf inputs = fst <$> queryAndamento2  conn inf inputs

queryPollAndamentoB :: PollingPlugins (Tidings [TB1 (Key,Showable)]) (UI Element)
queryPollAndamentoB =  BoundedPollingPlugins "Andamento Bombeiro" 60  ("fire_project", staticP arrow ) elem
  where
    arrow :: FunArrowPlug (Maybe Showable)
    arrow = proc t -> do
      idp <- varT "id_project" -< t
      ano <- varT "ano" -< t
      protocolo <- varT "protocolo" -< t
      cpf <- varT "id_owner,id_contact:id_owner:cgc_cpf" -< t
      odx "aproval_date" -< t
      returnA -< idp
    elem conn inf inputs = fst <$> queryAndamento3  conn inf inputs

queryPollAndamentoIO ,queryPollArtAndamentoIO  :: PollingPlugins [TB1 (Key,Showable)] (IO [([TableModification Showable])])

queryPollAndamentoIO =  BoundedPollingPlugins "Andamento Bombeiro" 60  ("fire_project", staticP arrow ) elem
  where
    arrow :: FunArrowPlug (Maybe Showable)
    arrow = proc t -> do
      idp <- varT "id_project" -< t
      ano <- varT "ano" -< t
      protocolo <- varT "protocolo" -< t
      cpf <- varT "id_owner,id_contact:id_owner:cgc_cpf" -< t
      odx "aproval_date" -< t
      returnA -< idp
    elem conn inf inputs = fmap snd . catMaybes <$> mapM (queryAndamento4  conn inf ) inputs

queryPollArtAndamentoIO = BoundedPollingPlugins "Andamento Art Crea"  60  ("art",staticP url) elem
  where
    varTB = fmap ( fmap (BS.pack . renderShowable ))<$>  varT
    url :: ArrowPlug (Kleisli IO) [(Text,Showable)]
    url = proc t -> do
      i <- varTB "art_number" -< t
      odx "verified_date" -< t
      odx "payment_date" -< t
      r <- at "crea_register" (proc t -> do
                               n <- varTB "crea_number" -< t
                               u <- varTB "crea_user"-< t
                               p <- varTB "crea_password"-< t
                               returnA -< liftA3 (, , ) n u p  ) -< t
      o <- act (fmap (join .maybeToList) . traverse (\(i, (j, k,a)) -> creaConsultaArt  j k a i ) ) -< liftA2 (,) i r
      let
          artVeri d = Attr ("verified_date" ,SOptional $ Just $ STimestamp $ Finite $ (\(Just i)-> fst i) $ strptime "%d/%m/%Y %H:%M" ( d !!1) )
          artPayd d = Attr ("payment_date" ,SOptional $Just $ STimestamp $ Finite $ (\(Just i)-> fst i) $ strptime "%d/%m/%Y %H:%M" (d !!1) )
          artInp :: [[String]] -> TB1 (Text,Showable)
          artInp inp = TB1 $ KV (PK [] []) $ fmap _tb $ [maybe (Attr ("verified_date",SOptional Nothing)) artVeri $  L.find (\[h,d,o] -> L.isInfixOf "Cadastrada" h )  inp ,maybe (Attr ("payment_date",SOptional Nothing)) artPayd $ L.find (\[h,d,o] -> L.isInfixOf "Registrada" h ) (inp) ]
      i <- checkOutput "verified_date" -< (t,Just$ artInp o)
      j <- checkOutput "payment_date" -< (t,Just $artInp o)
      returnA -< (catMaybes [i, j] )


    elem conn inf inputs = do
       let ev = mapM (\im -> do
                              h <- dynPK url (Just im)
                              updateArtStatus (Just im)  h) inputs
           updateArtStatus  im it = do
              let i = fmap (first (lookKey inf "art")) it
              if null (i)
                 then return []
                 else do
                   v <- updateMod conn inf (i)  (fromJust $ im) (lookTable inf "art")
                   return $ maybeToList v
       ev


queryAndamento4 conn inf  tbinputs = fmap (snd $ (\(Just i)-> i) .L.find ((== "project_description") . keyValue . fst )$ F.toList $ tbinputs,) <$> (runMaybeT $  do
              let
                  inputs = F.toList tbinputs
                  fire_project = lookTable inf "fire_project"
                  andamento = lookTable inf "andamento"
              ano <- MaybeT $ return $ lookInput "ano" $ filter (not . isEmptyShowable. snd )  $ inputs
              liftIO$ print (getInput "project_description" inputs)
              if testShowable (<=14) (snd ano )
                then do
                let
                    addrs ="http://siapi.bombeiros.go.gov.br/consulta/consulta_protocolo.php"
                    translate = [("protocolo" , "protocolo"),("ano","ano")]
                (lkeys,modB) <- if not $ elem "id_bombeiro" ((keyValue . fst)<$>  filter (not . isEmptyShowable. snd ) inputs )
                   then do
                    url <- MaybeT $ return $ renderUrlM translate addrs  $ filter (not . isEmptyShowable. snd )  <$> Just inputs
                    lq <-  getRequest . traceShowId $ url
                    let
                      lq2 =  Just . maybe M.empty (uncurry M.singleton . ("id_bombeiro",)) . fmap SNumeric . readMaybe.  fst .  break (=='&') . concat . tail .  splitL ("php?id=")  .T.unpack . decodeLatin1  $  lq
                      lkeys = fmap ( M.toList . M.mapKeys ((\(Just i)-> i) . flip M.lookup (keyMap inf) . ("fire_project",)  ))  $ lq2
                    mod <- C.lift $ updateMod conn inf ((\(Just i)-> i) lkeys) tbinputs  fire_project
                    return $  (lkeys,mod)
                   else do return $ (fmap (\i-> [i])   $ L.find ((== "id_bombeiro") .  keyValue . fst) inputs,Nothing)
                let
                  tkeys t v =  M.mapKeys (lookKey inf t )  v
                  insertAndamento :: MaybeT IO [Maybe (TableModification Showable)]
                  insertAndamento   = do
                    let
                        addrs_a ="http://siapi.bombeiros.go.gov.br/consulta/consulta_andamento.php"
                        translate_a = [("id_bombeiro" , "id")]
                    MaybeT $ return $ if elem "aproval_date" ((keyValue . fst)<$>  filter (not . isEmptyShowable. snd ) inputs )  then Nothing else Just undefined
                    tq <-  getRequest . traceShowId . (renderUrl translate_a addrs_a)  $  lkeys
                    let
                      i =  T.unpack $  decodeLatin1 tq
                      convertAndamento [da,desc] = [("andamento_date",STimestamp . Finite . fst . justError "wrong date parse" $  strptime "%d/%m/%y" da  ),("andamento_description",SText (T.filter (not . (`elem` "\n\r\t")) $ T.pack  desc))]
                      convertAndamento i = error $ "convertAndamentoLegacy:  " <> show i
                      prepareArgs  = fmap ( tkeys "andamento". M.fromList . convertAndamento ) .  tailEmpty . concat
                      lookInput = justError "could not find id_project" . fmap (\(k,v) -> let k1 = (\(Just i)-> i) $ M.lookup ("andamento","id_project") (keyMap inf) in (k1, transformKey (textToPrim <$> keyType k)  (textToPrim <$> keyType k1) v) ) . L.find ((== "id_project") . keyValue . fst)

                    C.lift $ do
                      html <- readHtml $ i
                      let
                          args :: S.Set (Map Key Showable)
                          args = S.fromList $ fmap (uncurry M.insert  (lookInput inputs )) $ prepareArgs html
                      mod <- case filter ( maybe False (\(SText t) -> T.isInfixOf "Aprovado" t ) .  M.lookup "andamento_description" . M.mapKeys keyValue )  $ S.toList args of
                          -- [i] -> updateMod  conn inf [(justError "could not lookup aproval_date " . flip M.lookup (keyMap inf) $ ("fire_project","aproval_date") , justError "could not lookup andamento_date" $ M.lookup "andamento_date"  $ M.mapKeys keyValue i)] tbinputs fire_project
                          i -> return Nothing
                      vp <- doQueryAttr conn inf (projectAllRec' (tableMap inf)) (uncurry M.singleton $  fmap ( (\i->[i]) . Category . S.singleton . flip PK [].(\i->[i]) ) (lookInput inputs ) ) ( (\(Raw _ _ pk _ _ _ ) -> pk ) andamento )

                      let kk = S.fromList (fmap (M.fromList . filter ((`elem` ["id_project","andamento_description","andamento_date"] ) . keyValue . fst ) . concat . F.toList . fmap (attrNonRec .unTB). _unTB1) vp) :: S.Set (Map Key Showable)
                      adds <-  mapM (\kv -> (`catch` (\e -> return $ trace ( show (e :: SqlError)) Nothing )) $ insertMod conn  inf (M.toList kv) (andamento )) (S.toList $ args  `S.difference`  kk)
                      return $ mod : adds

                  updateSolicitacao :: MaybeT IO (Maybe (TableModification Showable))
                  updateSolicitacao = do
                    MaybeT $ return $ if maybe False (\(_,SOptional  mb)-> maybe False (\(SBoolean b) -> b) mb)$ L.find ((=="taxa_paga"). keyValue . fst) $ (filter (not . isEmptyShowable. snd ) inputs )  then Nothing else Just undefined
                    let  addrs_b ="http://siapi.bombeiros.go.gov.br/consulta/consulta_solicitacao.php"
                         translate_b = [("id_bombeiro" ,"id")]
                    tq3 <-  getRequest . traceShowId . (renderUrl translate_b addrs_b)  $  lkeys
                    htmlSoli <- C.lift $ testSolicitation tq3
                    let tq4 = catMaybes .fmap Tra.sequence . M.toList . tkeys "fire_project" . M.fromList $ htmlSoli
                    MaybeT $ return $ if not $ maybe False (\(_,SBoolean mb)-> mb) $ L.find ((=="taxa_paga"). keyValue . fst)  tq4 then Nothing else Just undefined
                    C.lift $ updateMod  conn inf tq4 tbinputs fire_project
                  getPdf = do
                    MaybeT $ return $ if (\i->elem "analista" i || elem "aproval_date" i ) $ (keyValue . fst <$> filter (not . isEmptyShowable. snd ) inputs ) then Nothing else Just undefined
                    C.lift $ testPdfGet conn inf tbinputs
                and <- C.lift $ concat . maybeToList <$> runMaybeT insertAndamento
                sol <- C.lift $ maybeToList <$> runMaybeT updateSolicitacao
                gets <-C.lift $ maybeToList <$> runMaybeT getPdf
                let mods =  catMaybes (   modB :  gets <> and  <> sol)
                MaybeT $ return  $ (\case {[] -> Nothing ; i -> Just i }) mods
              else do
                    -- MaybeT $ return $ if elem "aproval_date" ((keyValue . fst)<$>  filter (not . isEmptyShowable. snd ) inputs )  then Nothing else Just undefined
                    html <- MaybeT $   fmap join $ Tra.sequence $  liftA3 siapi3 (getInput "protocolo" inputs) (getInput "ano" inputs) (getInput "cgc_cpf" inputs)
                    MaybeT $ return $ case (L.null $ join $ join $  fst html) of
                                  True -> Nothing
                                  False -> Just undefined
                    let
                      tkeys t v =  M.mapKeys (lookKey inf t)  v
                      convertAndamento [_,da,desc,s,sta] = [("andamento_date",STimestamp . Finite .  fst . justError "wrong date parse" $  strptime "%d/%m/%Y %H:%M:%S" da  ),("andamento_description",SText $ T.pack  desc)]
                      convertAndamento i = error $ "convertAndamento2015 :  " <> show i
                      prepareArgs  = fmap (tkeys "andamento" . M.fromList . convertAndamento)
                      lookInput = justError "could not find id_project" . fmap (\(k,v) -> let k1 = (\(Just i)-> i) $ M.lookup ("andamento","id_project") (keyMap inf) in (k1, transformKey (textToPrim <$> keyType k)  (textToPrim <$> keyType k1) v) ) . L.find ((== "id_project") . keyValue . fst)

                    firemods <- C.lift $ do
                      let taxa_paga = maybe False (\(SBoolean mb)-> mb) $ join $ fmap (unRSOptional' .snd)$  lookInputV "taxa_paga"  inputs
                      if not taxa_paga
                         then (if taxa_paga /= (not .snd $html) then updateMod  conn inf [(lookKey inf "fire_project" "taxa_paga" , SBoolean . not .snd $html)] tbinputs fire_project else return Nothing)
                         else return  Nothing

                    mods <- C.lift $  do
                      let
                          args :: S.Set (Map Key Showable)
                          args = S.fromList $ fmap (uncurry M.insert  (lookInput inputs )) $  prepareArgs  $ fst html
                      --mod <- case filter ( maybe False (\(SText t) -> T.isInfixOf "APROVADO" t ) .  M.lookup "andamento_description" . M.mapKeys keyValue )  $ S.toList args of
                       --   [] -> return Nothing
                          -- i:xs -> updateMod  conn inf [(lookKey inf "fire_project" "aproval_date"  , justError "could not lookup andamento_date" $ M.lookup "andamento_date"  $ M.mapKeys keyValue i)] tbinputs fire_project
                      vp <- doQueryAttr conn inf (projectAllRec' (tableMap inf)) (uncurry M.singleton $  fmap ( (\i->[i]) . Category . S.singleton . flip PK [].(\i->[i]) ) (lookInput inputs ) ) ( (\(Raw _ _ pk _ _ _ ) -> pk ) andamento )

                      let kk = S.fromList (fmap (M.fromList . filter ((`elem` ["id_project","andamento_description","andamento_date"] ) . keyValue . fst ) . concat . F.toList . fmap (attrNonRec . unTB) . _unTB1) vp) :: S.Set (Map Key Showable)
                      adds <- mapM (\kv -> (`catch` (\e -> return $ trace ( show (e :: SqlError)) Nothing )) $ insertMod conn  inf (M.toList kv) (andamento )) (S.toList $ args  `S.difference`  kk)
                      return $  adds
                    MaybeT $ return  $ (\case {[] -> Nothing ; i -> Just i }) (catMaybes (firemods:mods) ))

getInput k = fmap (BSL.toStrict. BSL.pack .renderShowable . snd) . lookInput k

allNonEmpty [] = Nothing
allNonEmpty l = Just  l

eitherToMaybeT (Left i) =  Nothing
eitherToMaybeT (Right r) =  Just r

queryAndamento3 conn inf  input = do
        tq <-  mapT (mapM (queryAndamento4 conn inf  ) ) input
        e <- UI.div # sink appendItems ( fmap (\i -> UI.div # set text (show $ (fmap (fmap renderShowable)) <$> i) ) . catMaybes  <$> facts tq  )
        return (e , pure Nothing :: Tidings (Maybe (Map Key Showable)))

deleteMod conn inf kv table = do
  delete conn kv table
  Just <$> logTableModification inf conn (TableModification Nothing table (Delete $ Just kv))

updateMod conn inf kv old table = do
  (i,j) <- update conn  kv old table
  Just <$> logTableModification inf conn j

insertPKMod conn inf kv table = do
  s <- insertPK fromShowableList conn kv table
  let mod =  TableModification Nothing table (Insert $ Just $ kv <> s)
  Just <$> logTableModification inf conn mod

insertMod conn inf kv table = do
  insert conn  kv table
  let mod =  TableModification Nothing table (Insert $ Just kv)
  Just <$> logTableModification inf conn mod

logTableModification inf conn (TableModification Nothing table i) = do
  let look k = lookKey inf "modification_table" k
  time <- getCurrentTime
  let ltime = STimestamp . Finite . utcToLocalTime utc $ time
  [s] <- insertPK fromShowableList conn [(look "modification_time", ltime ) ,(look "table_name" ,SText $ tableName  table) , (look "modification_data", SText $ T.pack $ show i)] ((\(Just i)-> i) $ M.lookup ("modification_table") (tableMap inf))
  return (TableModification ((\(SSerial (Just (SNumeric i)))-> Just i ) $ snd s) table i )

bradescoRead file = do
  file <- TE.decodeLatin1 <$> BS.readFile file
  let result =  fmap (fmap TE.unpack . L.take 5) $ filter (\(i:xs) -> isJust $ strptime "%d/%m/%y" (TE.unpack i)) $ filter ((>5) . length) $  TE.split (';'==) <$> TE.split (=='\r') file
  return result

testIAG = do
  f <- BSL.readFile "testiag.html"
  testSolicitation f
testFranklin = do
  f <- BSL.readFile "solicitacao.html"
  testSolicitation f
testHimalaia= do
  f <- BSL.readFile "himalaia.html"
  testSolicitation f

testSolicitation f = do
  -- f <- BSL.readFile "solicitacao.html"
  let dec =  decodeLatin1 f
  html <-  (head <$> readHtml ( T.unpack $ dec ))
  let packed = fmap (fmap T.pack) html
      log = fmap (splitAt 2) $ safeHead $ filter ((==4).length) packed
      tx = fmap (splitAt 2) $ safeHead $ filter (T.isInfixOf "TAXA" . head ) $ filter ((==3).length) packed
      translateSolicitation :: [(Text,(Text,Text-> Maybe Showable))]
      translateSolicitation  =
        [("ÁREA CONSTRUÍDA",("area",(\i-> SDouble <$> readMaybe (T.unpack $ fst $ T.break (' '==) i))))
        ,("VALOR  DA TAXA",("taxa_aprovacao",(\i -> SDouble <$> readMaybe (T.unpack $ fst $ T.breakOn ("\160") i))))
        ,("LOCAL DE ATENDIMENTO",("local_atendimento",fmap SText . nonEmpty ))
        ,("REGIÃO DE ATENDIMENTO",("regiao_atendimento",fmap SText . nonEmpty ))
        ,("TAXA PAGA",("taxa_paga",fmap SBoolean . readMaybe . T.unpack))
        ]
      nonEmpty "" = Nothing
      nonEmpty i = Just i
      keyvalue = fmap (\[i,j]-> (T.strip $ fst (T.breakOn "..:" i) ,j)) $ (filter ((==2). length) $   packed <> maybe [] (\(logr,num) -> [logr,num]) log  <> maybe [["TAXA PAGA..:","True"]] (\(taxa,apagar) -> [taxa,["TAXA PAGA..:", T.pack $ show $ not $ T.isInfixOf "TAXA A RECOLHER" dec ]] ) tx)
      result =  catMaybes .fmap (\(k,v) -> fmap ($v) <$> M.lookup k (M.fromList translateSolicitation))
  return $ (result keyvalue)

sdate = SDate . Finite . localDay
stimestamp = STimestamp . Finite

bradescoExtractTxt  conn  inf   inputs = do
    pathInput <- UI.input -- # set UI.type_ "file"
    b <- UI.button # set UI.text "Import"
    bhInp <- stepper "" (UI.valueChange pathInput)
    let process (Just inp) path = do
          content <- bradescoRead  path
          let parse  = uncurry M.insert (lookInput inp )  . tkeys . parseField  <$> content
              lookInput = (\(Just i)-> i) .L.find ((== "id_account") . keyValue . fst)
              tkeys v =  M.mapKeys (lookKey inf "transaction")  v
              parseField [d,desc,_,v,""] = M.fromList [("transaction_date",sdate $ fst $ (\(Just i)-> i) $ strptime "%d/%m/%y" d),("transaction_description",SText $ T.pack desc),("transaction_price", SDouble $ read $ fmap (\i -> if i == ',' then '.' else i) $ filter (not . (`elem` ".\"")) v)]
              parseField [d,desc,_,"",v] = M.fromList [("transaction_date",sdate $ fst $ (\(Just i)-> i) $ strptime "%d/%m/%y" d),("transaction_description",SText $ T.pack desc),("transaction_price", SDouble $ read $ fmap (\i -> if i == ',' then '.' else i) $ filter (not . (`elem` ".\"")) v)]
          vp <- doQueryAttr conn inf (projectAllRec' (tableMap inf)) (uncurry M.singleton $  fmap ( (\i->[i]) . Category . S.singleton . flip PK [].(\i->[i]) ) (lookInput inp ) ) ( (\(Raw _ _ pk _ _ _ ) -> pk ) $(\(Just i)-> i) $  M.lookup  "transaction" (tableMap inf ))
          let kk = S.fromList (fmap (M.fromList . filter ((`elem` ["id_account","transaction_description","transaction_date","transaction_price"] ) . keyValue . fst ) . F.toList ) vp) :: S.Set (Map Key Showable)
          adds <- mapM (\kv -> (`catch` (\e -> return $ trace ( show (e :: SqlError)) Nothing )) $ fmap Just $ insertPK fromShowableList  conn  (M.toList kv) ((\(Just i)-> i) $ M.lookup  "transaction" (tableMap inf) )) (S.toList $ ( S.fromList parse ) `S.difference` kk)
          return parse
        process Nothing _ = do return []
        j = unsafeMapIO id $ process  <$> facts inputs <*> bhInp <@ UI.click b
    outStp <- stepper "" (fmap show $ j)
    out <- UI.div # sink UI.text outStp
    (,pure Nothing) <$> UI.div # set children [pathInput,b,out]

itauExtractTxt  conn  inf   inputs = do
    pathInput <- UI.input -- # set UI.type_ "file"
    b <- UI.button # set UI.text "Import"
    bhInp <- stepper "" (UI.valueChange pathInput)
    let process (Just inp) path = do
          file <-  readFile (traceShowId path)
          let parse  = uncurry M.insert (lookInput inp )  . tkeys . parseField . unIntercalate (';'==) <$> lines (filter (/='\r') file)
              lookInput = (\(Just i)-> i) .L.find ((== "id_account") . keyValue . fst)
              tkeys v =  M.mapKeys (lookKey  inf "transaction")  v
              parseField [d,desc,v] = M.fromList [("transaction_date", SDate $ Finite $ localDay $ fst $ (\(Just i)-> i) $ strptime "%d/%m/%Y" d),("transaction_description",SText $ T.pack desc),("transaction_price", SDouble $ read $ fmap (\i -> if i == ',' then '.' else i) v)]
          vp <- doQueryAttr conn inf (projectAllRec' (tableMap inf)) (uncurry M.singleton $  fmap ( (\i->[i]) . Category . S.singleton . flip PK [].(\i->[i]) ) (lookInput inp ) ) ( (\(Raw _ _ pk _ _ _ ) -> pk ) $(\(Just i)-> i) $  M.lookup  "transaction" (tableMap inf ))
          let kk = S.fromList (fmap (M.fromList . filter ((`elem` ["id_account","transaction_description","transaction_date","transaction_price"] ) . keyValue . fst ) . F.toList ) vp) :: S.Set (Map Key Showable)
          adds <- mapM (\kv -> (`catch` (\e -> return $ trace ( show (e :: SqlError)) Nothing )) $ fmap Just $ insertPK fromShowableList  conn  (M.toList kv) ((\(Just i)-> i) $ M.lookup  "transaction" (tableMap inf) )) (S.toList $ ( S.fromList parse ) `S.difference` kk)
          return parse
        process Nothing _ = do return []
        j = unsafeMapIO id $ process  <$> facts inputs <*> bhInp <@ UI.click b
    outStp <- stepper "" (fmap show $ j)
    out <- UI.div # sink UI.text outStp
    (,pure Nothing) <$> UI.div # set children [pathInput,b,out]

fkattrsB inputs fks = foldr (liftA2 (:))   inputs fks

lookAttr inp attr = justError ("Error looking Attr: " <> show attr <> " " <> show inp) $ M.lookup attr  inp

lookKeyMap inp attr = justError ("Error looking KeyMap: " <> show attr <> " " <> show inp) $ M.lookup attr  inp

queryAndamento2 conn inf   input = do
        b <- UI.button # set UI.text "Submit"
        tq <-  mapT (\case {Just input -> queryAndamento4 conn inf (input) ; Nothing -> return Nothing}) (shortCutClick input (UI.click b))
        e <- UI.div # sink UI.text (fmap (maybe "" show ) $ facts $ tq)
        body <-UI.div # set children [b,e]
        return (body , pure Nothing :: Tidings (Maybe (Map Key Showable)))

tailEmpty [] = []
tailEmpty i  = tail i




queryShowMap = BoundedPlugin "Google Map" "address"( fst showMap') (\i j k -> snd showMap'$ k)

showMap' = (staticP req , element)
  where
      varT t =   join . fmap (unRSOptional'.snd)  <$> idxT t
      req :: FunArrowPlug  (Maybe String)
      req = proc t -> do
            p<- varT "geocode" -< t
            returnA -< (\(SPosition (Position (lon,lat,_)))-> "http://maps.google.com/?output=embed&q=" <> (HTTP.urlEncode $ show lat  <> "," <>  show lon )) <$>  p
      element inputs = do
        iframe  # sink UI.src (maybe "" id . dynP req  <$> facts inputs) # set style [("width","99%"),("height","300px")]

data Timeline
  = Timeline
  { header :: String
  , dates :: [(Day,String)]
  }

queryTimeline = BoundedPlugin "Timeline" "pricing"(staticP arrow)  elem
  where
    convDateArr i = swap . fmap (\(SDate (Finite f))-> f) <$> (catMaybes $ fmap (traverse unRSOptional') $ catMaybes $ i)
    arrow :: FunArrowPlug [(Day,String)]
    arrow = proc t -> do
      prd <- varT "pricing_date" -< t
      papr <- varN "pricing_approval" -< t
      apd <- varN "id_project:aproval_date" -< t
      arr <- varN "pagamentos:payment_date" -< t
      arrD <- varN "pagamentos:payment_description" -< t
      let vv =  concat $ maybeToList $ (\(SComposite i) (SComposite j)-> fmap Just $ zip (renderShowable <$> F.toList j ) (F.toList i)) <$>  arr <*> arrD

      returnA -<  convDateArr ([("Proposta de Enviada",)<$> prd,("Projeto Aprovado",) <$> apd ,("Proposta Aprovada",) <$> papr] <>  vv )
    elem con inf inputs = do
        e <- UI.div # set UI.id_ "timeline-embed"
        let  timeline i = Timeline "hello" (dynP arrow $ i)
        i <- UI.div # sink UI.html  (fmap (\i->  "<script>    var container = document.getElementById('timeline-embed');var items = new vis.DataSet("  <>  BSL.unpack ( encode (timeline i)) <> ") ;  var options = {} ; if (container.vis != null ) { container.vis.destroy(); } ; container.vis = new vis.Timeline(container,items,options); </script>") $ facts inputs)
        UI.div # set children [e,i]


instance ToJSON Timeline where
  toJSON (Timeline h v) = toJSON (dates <$> zip [0..] v)

    where dates (id,(i,j)) = object ["id" .= (id :: Int) ,"start" .=  ti i, "content" .= j, "type" .= ("point" :: String)]
          ti  = formatTime defaultTimeLocale "%Y/%m/%d"

notaPrefeitura = BoundedPlugin2 "Nota Prefeitura" "nota"(staticP url) elem
  where
    varTB = fmap ( fmap (BS.pack . renderShowable ))<$>  varT
    url :: ArrowPlug (Kleisli IO) (Maybe (TB1 (Text,Showable)))
    url = proc t -> do
      i <- varTB "id_nota" -< t
      odx "nota" -<  t
      r <- at "inscricao" (proc t -> do
                               n <- varTB "inscricao_municipal" -< t
                               u <- varTB "goiania_user"-< t
                               p <- varTB "goiania_password"-< t
                               returnA -< liftA3 (, , ) n u p  ) -< t
      b <- act (fmap join  . traverse (\(i, (j, k,a)) -> prefeituraNota j k a i ) ) -< liftA2 (,) i r
      let ao =  Just $ TB1 $ KV (PK [] []) [_tb $ Attr  ("nota",    SOptional b)]
      returnA -< ao

    elem conn inf = maybe (return Nothing) (\inp -> do
                              b <- dynPK url (Just inp)
                              return $ fmap (first (lookKey inf "nota")) <$> b
                            )

queryArtCrea = BoundedPlugin2 "Documento Final Art Crea" "art"(staticP url) elem
  where
    varTB = fmap ( fmap (BS.pack . renderShowable ))<$>  varT
    url :: ArrowPlug (Kleisli IO) (Maybe (TB1 (Text,Showable)))
    url = proc t -> do
      i <- varTB "art_number" -< t
      idxT "payment_date" -<  t
      odx "art" -<  t
      r <- at "crea_register" (proc t -> do
                               n <- varTB "crea_number" -< t
                               u <- varTB "crea_user"-< t
                               p <- varTB "crea_password"-< t
                               returnA -< liftA3 (, , ) n u p  ) -< t
      b <- act (fmap join  . traverse (\(i, (j, k,a)) -> creaLoginArt  j k a i ) ) -< liftA2 (,) i r
      let ao =  Just $ TB1 $ KV (PK [] []) [_tb $ Attr  ("art",    SOptional b)]
      returnA -< ao
    elem conn inf = maybe (return Nothing) (\inp -> do
                              b <- dynPK url (Just inp)
                              return $ fmap (first (lookKey inf "art")) <$> b
                            )


queryArtBoletoCrea :: Plugins
queryArtBoletoCrea = BoundedPlugin2 "Boleto Art Crea" "art"(staticP url) elem
  where
    varTB = fmap ( fmap (BS.pack . renderShowable ))<$>  varT
    url :: ArrowPlug (Kleisli IO) (Maybe (TB1 (Text,Showable)))
    url = proc t -> do
      i <- varTB "art_number" -< t
      idxT "verified_date" -< t
      odx "boleto" -< t
      r <- at "crea_register" (proc t -> do
                               n <- varTB "crea_number" -< t
                               u <- varTB "crea_user"-< t
                               p <- varTB "crea_password"-< t
                               returnA -< liftA3 (, , ) n u p  ) -< t
      b <- act ( traverse (\(i, (j, k,a)) -> creaBoletoArt  j k a i ) ) -< liftA2 (,) i r
      let ao =  Just $ TB1 $ KV (PK [] []) [_tb $ Attr  ("boleto",   SOptional $ (SBinary. BSL.toStrict) <$> b)]
      returnA -< ao
    elem conn inf
       = maybe (return Nothing) (\inp -> do
                            b <- dynPK url (Just inp)
                            return $ fmap (first (lookKey inf "art")) <$> b
                            )



checkOutput i = proc t -> do
      o <- odx i -< fst t
      v <- odx i -< snd t
      returnA -< if isJust o  && fmap snd o == fmap snd v
         then Nothing
         else v


queryPollArtAndamento = BoundedPollingPlugins "Andamento Art Crea"  60  ("art",staticP url) elem
  where
    varTB = fmap ( fmap (BS.pack . renderShowable ))<$>  varT
    url :: ArrowPlug (Kleisli IO) [(Text,Showable)]
    url = proc t -> do
      i <- varTB "art_number" -< t
      odx "verified_date" -< t
      odx "payment_date" -< t
      r <- at "crea_register" (proc t -> do
                               n <- varTB "crea_number" -< t
                               u <- varTB "crea_user"-< t
                               p <- varTB "crea_password"-< t
                               returnA -< liftA3 (, , ) n u p  ) -< t
      o <- act (fmap (join .maybeToList) . traverse (\(i, (j, k,a)) -> creaConsultaArt  j k a i ) ) -< liftA2 (,) i r
      let
          artVeri d = Attr ("verified_date" ,SOptional $ Just $ STimestamp $ Finite $ (\(Just i)-> fst i) $ strptime "%d/%m/%Y %H:%M" ( d !!1) )
          artPayd d = Attr ("payment_date" ,SOptional $Just $ STimestamp $ Finite $ (\(Just i)-> fst i) $ strptime "%d/%m/%Y %H:%M" (d !!1) )
          artInp :: [[String]] -> TB1 (Text,Showable)
          artInp inp = TB1 $ KV (PK [] []) $ fmap _tb $ [maybe (Attr ("verified_date",SOptional Nothing)) artVeri $  L.find (\[h,d,o] -> L.isInfixOf "Cadastrada" h )  inp ,maybe (Attr ("payment_date",SOptional Nothing)) artPayd $ L.find (\[h,d,o] -> L.isInfixOf "Registrada" h ) (inp) ]
      i <- checkOutput "verified_date" -< (t,Just$ artInp o)
      j <- checkOutput "payment_date" -< (t,Just $artInp o)
      returnA -< catMaybes [i, j]


    elem conn inf inputs = do
       let ev = unsafeMapIO (mapM (\im -> do
                              h <- dynPK url (Just im)
                              updateArtStatus (Just im)  h)) (rumors inputs)
           updateArtStatus  im it = do
              let i = fmap (first (lookKey inf "art")) it
              if null (i)
                 then return []
                 else do
                   v <- updateMod conn inf (i)  (fromJust im) (lookTable inf "art")
                   return $ maybeToList v
       bh <- stepper [] ev
       UI.div # sink UI.text (show <$> bh )





queryArtAndamento = BoundedPlugin "Andamento Art Crea" "art"(staticP url) elem
  where
    varTB = fmap ( fmap (BS.pack . renderShowable ))<$>  varT
    url :: ArrowPlug (Kleisli IO) [[String]]
    url = proc t -> do
      i <- varTB "art_number" -< t
      r <- at "crea_register" (proc t -> do
                               n <- varTB "crea_number" -< t
                               u <- varTB "crea_user"-< t
                               p <- varTB "crea_password"-< t
                               returnA -< liftA3 (, , ) n u p  ) -< t
      act (fmap (join .maybeToList) . traverse (\(i, (j, k,a)) -> creaConsultaArt  j k a i ) ) -< liftA2 (,) i r
    elem conn inf inputs = do
       consulta <- UI.button # set UI.text "Consultar"
       let ev = unsafeMapIO (\im -> do
                              h <- dynPK url im
                              updateArtStatus im  h ) (facts inputs <@ UI.click consulta)
           updateArtStatus  im i = do
              let artVeri d = (lookKey inf "art" "verified_date" ,STimestamp $ Finite $ (\(Just i)-> fst i) $ strptime "%d/%m/%Y %H:%M" ( d !!1) )
                  artPayd d = (lookKey inf "art" "payment_date" ,STimestamp $ Finite $ (\(Just i)-> fst i) $ strptime "%d/%m/%Y %H:%M" (d !!1) )
                  artInp inp = catMaybes [artVeri <$>  L.find (\[h,d,o] -> L.isInfixOf "Cadastrada" h )  inp ,artPayd <$> L.find (\[h,d,o] -> L.isInfixOf "Registrada" h ) (inp) ]
              if null (artInp i)
                 then return []
                 else maybeToList <$> updateMod conn inf (artInp i)  (fromJust $ im) (lookTable inf "art")
       i <- stepper [] ev
       out <- UI.div # sink UI.text (show <$> i )
       UI.div # set children [consulta ,out]

testParse = strptime "%d/%m/%Y %H:%M""24/03/2015 08:30"

strAttr :: String -> WriteAttr Element String
strAttr name = mkWriteAttr (set' (attr name))

queryGeocodeBoundary = BoundedPlugin "Google Geocode" "address"(staticP url) elem
  where
    elem conn inf inputs = do
      b <- UI.button # set UI.text "Import"
      let
          req im = runMaybeT $ do
            r <- getRequest  .  dynP url $im
            let dec = decode r :: Maybe Value
                loc = dec !> "results" !!> 0 !> "geometry" !> "location"
                bounds = dec !> "results" !!> 0 !> "geometry" !> "bounds"
                viewport = dec !> "results" !!> 0 !> "geometry" !> "viewport"
                lkey  = lookKey inf "address"
                getPos l = Position <$> liftA2 (\(A.Number i) (A.Number j)-> (realToFrac i ,realToFrac j ,0)) (l !> "lng" )( l  !> "lat" )
            p <- MaybeT $ return $ getPos loc
            b <- MaybeT $ return $ case (fmap Bounding $  (\i j -> Interval.interval (ER.Finite i ,True) (ER.Finite j ,True))<$> getPos (bounds !> "southwest") <*> getPos (bounds !> "northeast"), fmap Bounding $ (\i j -> Interval.interval (ER.Finite i ,True) (ER.Finite j ,True))<$> getPos (viewport !> "southwest") <*> getPos (viewport !> "northeast")) of
                                        (i@(Just _), _ ) -> i
                                        (Nothing , j) -> j
            mod <- C.lift $ updateMod conn inf [(lkey "geocode" ,SPosition p),( lkey "bounding", SBounding b)] (fromJust $ im) (lookTable inf "address")
            return [(lkey "geocode" ,SPosition p),( lkey "bounding", SBounding b)]
      let et =  unsafeMapIO req (facts inputs <@ UI.click b)
      t <- stepper "" (show <$> et)
      out <- UI.div # UI.sink text t
      UI.div # set children [b,out]

    url :: FunArrowPlug String
    url = proc t -> do
      id <- varT "id" -< t
      log <- varT "logradouro"-< t
      num <- varN "number"-< t
      bai <- varN "bairro"-< t
      mun <- varT "municipio"-< t
      uf <- varT "uf"-< t
      returnA -<  "http://maps.googleapis.com/maps/api/geocode/json?address=" <> (HTTP.urlEncode $ vr log <> " , " <> vr num <> " - " <>  vr bai<> " , " <> vr mun <> " - " <> vr uf)
      where vr =  maybe "" renderShowable


varT t = join . fmap (unRSOptional'.snd)  <$> idxT t
varN t = fmap snd  <$> idx t

type FunArrowPlug o = Step.Parser (->) (Bool,[[Text]]) (Maybe (TB1 (Key,Showable))) o
type ArrowPlug a o = Step.Parser a (Bool,[[Text]]) (Maybe (TB1 (Key,Showable))) o

dynPK =  runKleisli . dynP

queryCEPBoundary = BoundedPlugin2  "Correios CEP" "address"(staticP open  )  element
  where
      translate :: Text -> Text
      translate "localidade" =  "municipio"
      translate i = i
      open :: ArrowPlug  (Kleisli IO ) (Maybe (TB1 (Text ,Showable)))
      open = proc t -> do
          i <- varT "cep" -< t
          odx "bairro" -< t
          odx "municipio" -< t
          odx "uf" -< t
          odx "logradouro" -< t
          r <- (act (  traverse (\input -> do
                       v <- ( (`catch` (\e ->  return $ trace (show (e :: IOException )) "{}" ) ). simpleGetRequest  . traceShowId .  (\i-> addrs <> i <> ".json") ) . T.unpack $ input
                       return $ ( \i -> fmap (filter ((/="").snd) . M.toList ) $ decode i ) v ))) -< (\(SText t)-> t) <$> i
          let tb = TB1 . KV (PK [] []) . fmap (Compose . Identity. Attr . first translate. second (SOptional. Just . SText)) <$> join r
          returnA -< tb

      addrs ="http://cep.correiocontrol.com.br/"
      element conn inf
          = maybe (return Nothing) (\inp -> do
                   b <- dynPK open (Just inp)
                   return $ fmap (first (lookKey inf "address")) <$> b)

executeStep
  :: Connection
  -> InformationSchema
  -> TB1 (Key,Showable)
  -> StepPlan (Maybe Showable)
  -> IO (Maybe [(Key,Showable)])
executeStep  conn inf inputs (TBPlan t  ta steps) =  do
          k <- mapM (executeStep conn inf inputs ) steps
          case t of
            TInsert -> do
               traverse (\i -> do
                        mod <- insertMod conn inf (concat i) ta
                        return mod
                        ) (allMaybes k)
               return $ Just []
            TUpdate -> do
               traverse (\i -> do
                        mod <- updateMod conn inf (concat i) inputs ta
                        return mod
                        ) (onlyJust k)

               return $ Just []
executeStep  _ inf _ (SPAttr t k v) = return $ fmap (\i -> [(k,i)]) v
executeStep  conn inf inputs (SPFK t (Path  i (FKJoinTable ti s tj ) j) steps) = do
  k <-  mapM (executeStep conn inf inputs) steps
  joinTable (M.fromList $ swap <$> s) <$> case t of
       FKEInsertGenerated -> do
         traverse (\i -> insertPK fromShowableList conn (concat i) tj) (allMaybes k)
       FKEUpdateFK -> do
         traverse (\i -> do
                    mod <- updateMod conn inf ( concat  i) inputs tj
                    let upPKs = filter ((`S.member` j) .fst) (concat i)
                    return  upPKs
                  ) (onlyJust k)

joinTable  m  i= join $ allMaybes . fmap (fmap swap . Tra.sequence . fmap (flip M.lookup  m) . swap ) <$> i

onlyJust = allNonEmpty . catMaybes

testPlan conn inf input ndata = executeStep  conn inf input   .  generateValues ndata .   generateStepPlan inf input

generateValues
  :: (Ord k, Functor f) => Map k a -> f (k, Maybe a -> b) -> f b
generateValues m plan = fmap (\(l,f)->  f  $ M.lookup l m ) plan

generateStepPlan
  :: InformationSchema
     -> TB1 (Key, b)
     -> (Text, [Step a])
     -> StepPlan (String, Maybe a -> Maybe Showable)
generateStepPlan inf input (tname , i) = TBPlan TUpdate table (fmap (attrPlan table) i)
  where
    attrPlan table (SAttr i) =  (if k `S.member` inputSet  then SPAttr AEUpdate  else SPAttr AEInsert) k $ transformAttr table i
        where k = (lookKey inf  (tableName  table) . fst . snd $ i)
    attrPlan table (SFK fk steps)
      | all (`S.member` inputSet) (fmap (lookKey inf (tableName table)) $ F.toList fk ) = SPFK FKEUpdateFK (fmap (lookTable inf) <$> path)  (attrPlan tfk <$> steps)
      | all (isSerial . keyType ) . filter (not . (`S.member` inputSet)  ) $ (F.toList fkt) = SPFK FKEInsertGenerated (fmap (lookTable inf) <$> path)  (attrPlan tfk <$> steps)
      | otherwise  = SPFK FKEInsertFind (fmap (lookTable inf) <$> path)  (attrPlan tfk <$> steps)
        where path@(Path _ (FKJoinTable _ _ j) fkt )  = justError ("table  " <> T.unpack (tableName table ) <>  " has no path for keyset " <> show fk  ) $ L.find (\(Path i _ _) -> S.map keyValue i == fk) (F.toList (rawFKS table) )
              tfk = lookTable inf j
    inputSet = S.fromList $ F.toList $ fmap fst input
    transformAttr table (i,(k,f)) = (i,(readTypeOpt (textToPrim <$> keyType nk ) .  fmap f))
        where nk = lookKey inf (tableName table) k
    table = lookTable inf tname

--testPlan1 conn inf = testPlan conn inf (testInput inf ) testData ("owner",testStep)

-- testInput inf = [(lookKey inf "owner" "id_owner",SSerial $  Just $ SNumeric 4) {-,(lookKey inf "owner" "address" , SOptional $Just $SNumeric 41 ), (lookKey inf "address" "id" , SSerial$ Just $SNumeric 41 )-}]


testData :: (IsString a, IsString k, Ord k) => Map k a
testData = M.fromList [("NOME EMPRESARIAL","Massuda Engenharia"),("CEP","74140140"),("UF","GO"),("LOGRADOURO","Rua Rui Brasil Cavalcante"),("NÚMERO","436"),("COMPLEMENTO","APT 502"),("BAIRRO/DISTRITO","Setor Oeste"),("MUNICÍPIO","Goiânia")]

testStep = translate_o
  where
    translate_o =
      [SAttr ("NOME EMPRESARIAL",("owner_name",id))
      ,SFK (S.singleton "address") translate]
    translate = fmap SAttr
      [("CEP",("cep" , filter (not . (`elem` "-."))))
      ,("UF",("uf",id ))
      ,("LOGRADOURO",("logradouro", id))
      ,("NÚMERO",("number",id))
      ,("COMPLEMENTO",("complemento",id))
      ,("BAIRRO/DISTRITO",("bairro",id))
      ,("MUNICÍPIO",("municipio",id))]

-- testPlanner = withConnInf "incendio" testPlan1

testPdfGet conn inf inp =  runMaybeT$ do
  let addrs = "http://siapi.bombeiros.go.gov.br/relatorios/relatorio_exigencia_projeto_web.php"
      translate = [("protocolo" , "protocolo"),("ano","ano")]
      tempName = "temp" <> renderShowable (snd $ justError "no id project testPdfGet"  $L.find ((=="id_project").keyValue .fst) $ F.toList inp) <> ".pdf"
      fire_project = lookTable inf "fire_project"
      translate_q =
            [("Name",("analista",id))
            ,("tipo",("id_tipo",id))
            ,("subtipo",("id_subtipo",id))
            ,("Carga de incêndio",("carga_incendio", fst . L.break (' '==) ))]
      transK = nonUpdateTranslator (F.toList inp) $ translateK inf "fire_project" translate_q
  if (not . null $  transK )
     then do
        url <- MaybeT $ return $ renderUrlM translate addrs  $ filter (not . isEmptyShowable. snd )  <$> Just (F.toList inp)
        pdf <- getRequest $ traceShowId url
        C.lift $ BS.writeFile (tempName) (BSL.toStrict pdf)
        v <- C.lift $ parseBombeiroPdf tempName
        C.lift $ removeFile tempName
        v <- MaybeT $ return $ eitherToMaybeT $ v
        let vp  =  catMaybes . applyTranslator (M.fromList transK) . fmap (fmap (T.unpack . T.fromStrict ) )  $  v
        MaybeT $   updateMod  conn inf vp inp fire_project
      else MaybeT $ return Nothing

queryCPFStatefull =
  let arrow :: FunArrowPlug  (Maybe Text)
      arrow = proc t -> do
        i <- varT "cpf_number" -< t
        returnA -< (\(SText s)->  s)  <$> i
      elem conn inf inputs = do
          out <- UI.div
          ev <- cnpjquery out ( fmap (BS.pack.T.unpack) . dynP arrow <$> inputs)
          s <- stepper [] (unsafeMapIO (\(inp,res) -> do
                      testPlan conn inf ( inp) ( M.fromList  res) ("owner",testStep)
                      return []
                            ) (filterJust $ liftA2 (,) <$> facts inputs <@> ev ))
          element out #+ [UI.div # sink UI.text s]
          return out
  in (StatefullPlugin "CPF Receita" "owner" [([(True,[["cpf_number"]])],[(False ,[["captchaViewer"]])]),([(True,[["captchaInput"]])],[(True,[["owner_name"]])])]   [[("captchaViewer",Primitive "jpg") ],[("captchaInput",Primitive "character varying")]] cpfCall )



queryCNPJStatefull =
  let arrow :: FunArrowPlug  (Maybe Text)
      arrow = proc t -> do
        i <- varT "cnpj_number" -< t
        returnA -< (\(SText s)->  s)  <$> i
      elem conn inf inputs = do
          out <- UI.div
          ev <- cnpjquery out ( fmap (BS.pack.T.unpack) . dynP arrow <$> inputs)
          s <- stepper [] (unsafeMapIO (\(inp,res) -> do
                      testPlan conn inf ( inp) ( M.fromList  res) ("owner",testStep)
                      return []
                            ) (filterJust $ liftA2 (,) <$> facts inputs <@> ev ))
          element out #+ [UI.div # sink UI.text s]
          return out
  in (StatefullPlugin "CNPJ Receita" "owner" [([(True,[["cnpj_number"]])],[(False ,[["captchaViewer"]])]),([(True,[["captchaInput"]])],[(True,[["owner_name"]])])]   [[("captchaViewer",Primitive "jpg") ],[("captchaInput",Primitive "character varying")]] wrapplug )



queryCNPJBoundary =
  let arrow :: FunArrowPlug  (Maybe Text)
      arrow = proc t -> do
        i <- varT "cnpj_number" -< t
        returnA -< (\(SText s)->  s)  <$> i
      elem conn inf inputs = do
          out <- UI.div
          ev <- cnpjquery out ( fmap (BS.pack.T.unpack) . dynP arrow <$> inputs)
          s <- stepper [] (unsafeMapIO (\(inp,res) -> do
                      testPlan conn inf ( inp) ( M.fromList  res) ("owner",testStep)
                      return []
                            ) (filterJust $ liftA2 (,) <$> facts inputs <@> ev ))
          element out #+ [UI.div # sink UI.text s]
          return out
  in (BoundedPlugin "CNPJ Receita" "owner" (staticP arrow )   elem)

translateK inf t =  fmap  (\(i,(kv,f))->  (i,) $  (\kkv ->  (kkv,) $ readType (textToPrim <$> keyType kkv) . f ) (lkeys kv))
  where
            lkeys = lookKey inf t

nonUpdateTranslator  input =  filter (not . flip S.member (inpSet input) . fst . snd )
  where inpSet = S.fromList . fmap fst .  filter (not . isEmptyShowable . snd )

applyTranslator t i = fmap (\(k,v) ->  join $ (\(kv,f) -> fmap (kv,) (f$v))   <$> (M.lookup k t )) i

iframe = mkElement "iframe"


projectTable
  :: Connection
     -> InformationSchema ->
     (forall t . Traversable t => QueryT Identity (t KAttribute)
         -> S.Set Key -> IO (t Key ,[t Showable]))
projectTable conn inf q  = (\(j,(h,i)) -> fmap (fmap (\(Metric k) -> k) j,)  . queryWith_ (fromShowableList j) conn . buildQuery $ i ) . projectAllKeys (pkMap inf ) (hashedGraph inf) q

projectKey'
  :: Connection
     -> InformationSchema ->
     (forall t . Traversable t => QueryT Identity (t KAttribute)
         -> S.Set Key -> IO [t (KAttribute ,Showable)])
projectKey' conn inf q  = (\(j,(h,i)) -> fmap (fmap (zipWithTF (,) j)) . queryWith_ (fromShowableList j) conn . buildQuery $ i ) . projectAllKeys (pkMap inf ) (hashedGraph inf) q


topSortTables tables = flattenSCCs $ stronglyConnComp item
  where item = fmap (\n@(Raw _ t k _ fk _ ) -> (n,k,fmap (\(Path _ _ end)-> end) (S.toList fk) )) tables



main :: IO ()
main = do
  args <- getArgs
  --let schema = "public"
  --conn <- connectPostgreSQL "user=postgres password=queijo dbname=usda"
  {-
  let sorted = topSortTables (M.elems baseTables)

  print "DROPPING TABLES"
  traverse (\t -> do
    execute_ connTest . fromString . T.unpack . dropTable $ t
    print $ tableName t
    )  $ reverse  sorted

  print "CREATING TABLES"
  traverse (\t -> do
    execute_  connTest . fromString . T.unpack . createTable $ t
    print $ tableName t
    )  sorted
  -}
  (e,h) <- newEvent
  forkIO $ poller  h queryPollAndamentoIO
  forkIO $ poller  h queryPollArtAndamentoIO
  startGUI (defaultConfig { tpStatic = Just "static", tpCustomHTML = Just "index.html"})  (setup e args)
  print "Finish"

poller handler (BoundedPollingPlugins n d (a,f) elem ) = do
  conn <- connectPostgreSQL ("user=postgres dbname=incendio")
  inf <- keyTables conn  "incendio"
  let loop =  do
        print =<<  getCurrentTime
        print "START"
        let rp = rootPaths'  (tableMap inf) (fromJust  $ M.lookup  a  $ tableMap inf )
        listRes <- queryWith_ (fromAttr (fst rp) ) conn  (traceShowId $ fromString $ T.unpack $ snd rp)
        let evb = filter (\i -> tdInput i && tdOutput1 i ) listRes
            tdInput i =  maybe False (const True) $ allMaybes $ fmap (\t -> (if fst t then join . fmap unRSOptional' else id ) $ fmap snd $ (indexTable  $ snd t) i) (fst f)
            tdOutput1 i =  maybe True (const False) $ allMaybes $ fmap (\f -> (if not(fst f ) then join . fmap unRSOptional' else id ) $ fmap snd $ (indexTable  $ snd f) i) (snd f)

        i <- elem conn inf evb
        handler i
        print =<<  getCurrentTime
        print "END"
        threadDelay (d*1000*1000*60)
        loop
  loop




layout  infT = do
  vis <- UI.div # set UI.id_ "visualization"
  let draw inf  =
        let
            g = graphP inf
            v :: [(Int,Set Key)]
            v = zip [0..] (L.nub $ hvertices g <> tvertices g)
            e = filter  (\case {(Path _ _ _)-> True ; i -> False}) $ concat $ fmap snd $ M.toList $ edges g
            vmap = M.fromList $ swap <$>  v
            genVertices (i,t ) = object [ "id" .= i, "label" .= T.intercalate "," (F.toList (S.map keyValue t)) ]
            genEdges (Path i (FKJoinTable m _ l)  j ) = object [ "from" .= lid i , "to" .= lid j  , "label" .= (tableName m <> " join " <> tableName l ) ]
            genEdges (Path i (FetchTable  l)  j ) = object [ "from" .= lid i , "to" .= lid j  , "label" .= tableName l ]
            lid t = justError ("no key " <> show t) (M.lookup t vmap)
            nodesJSON = "var nodes = " <> encode (genVertices <$> v) <> ";"
            edgesJSON = "var edges = " <> encode (genEdges <$> e) <> ";"
            graphJSON = "<script> " <> BSL.unpack (nodesJSON <> edgesJSON) <> "var container = document.getElementById('visualization');  var data = { nodes: nodes,edges: edges}; var options = { hierarchicalLayout : { layout : 'direction' } , edges : { style : 'arrow'}} ;  var network = new vis.Network(container, data, options ); </script> "
        in graphJSON
  script <- UI.div # sink UI.html (maybe "" draw <$> infT)
  UI.div # set children [vis,script]


testFireQuery q = withConnInf "incendio" (\conn inf -> do
                                       let (rp,rpq) = rootPaths' (tableMap inf) (fromJust $ M.lookup q (tableMap inf))
                                       putStrLn (  show rpq)
                                       putStrLn (  show rp)
                                       q <- queryWith_ (fromAttr (rp) ) conn  (fromString $ T.unpack $ rpq)
                                       putStrLn$  unlines $ fmap show q
                                           )

