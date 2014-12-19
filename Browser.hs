{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances,RankNTypes,NoMonomorphismRestriction,UndecidableInstances,FlexibleContexts,OverloadedStrings ,TupleSections, ExistentialQuantification #-}

import Query
import GHC.Generics
import qualified Network.HTTP as HTTP
import Widgets
import Data.Functor.Apply
import Debug.Trace
import Data.Ord
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
import Data.Aeson
import Data.Maybe
import Data.Distributive
import Data.Functor.Identity
import Text.Read
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
import qualified Numeric.Interval as Interval
import qualified Numeric.Interval.Internal as NI
import qualified Data.ByteString.Char8 as BS
import qualified Data.ByteString.Lazy.Char8 as BSL
import Data.Time

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
import Data.GraphViz (preview)
import qualified Data.Map as M
import Blaze.ByteString.Builder(fromByteString)
import Blaze.ByteString.Builder.Char8(fromChar)
import Data.Map (Map)
import Data.String

import GHC.Show
import Data.Functor.Classes

type QueryCursor t =(t KAttribute, (HashSchema Key Table, Table))


setup
     ::  Window -> UI ()
setup w = void $ do
  return w # set title "Data Browser"
  (evDB,chooserDiv) <- databaseChooser
  getBody w #+ [element chooserDiv]
  onEvent evDB $ (\(conn,inf@(_,baseTables,_,schema,invSchema,graphP))-> do
    let k = M.keys baseTables
    let pg = catMaybes [pluginWapp inf ,pluginBradescoCsv inf,pluginItauTxt inf ,pluginAndamentoId inf , pluginBombeiro inf ,pluginCnpjReceita inf ,pluginCEP inf,{-solicitationPlugin inf,-} pluginOrcamento inf]
        poll = catMaybes [pollingAndamento inf ]
    span <- chooserKey  conn pg inf k
    poll <- poller conn poll inf
    header <- tabbed [("Query",span) ,("Process",poll)]
    getBody w #+ [element header])

listDBS = do
  connMeta <- connectPostgreSQL ("user=postgres dbname=postgres")
  dbs :: [Only Text]<- query_  connMeta "SELECT datname FROM pg_database  WHERE datistemplate = false"
  M.fromList <$> mapM (\db -> do
        connDb <- connectPostgreSQL ("user=postgres dbname=" <> toStrict (encodeUtf8 db))
        schemas :: [Only Text] <- query_  connDb "SELECT schema_name from information_schema.schemata"
        return (db,fmap unOnly schemas)) (fmap unOnly dbs)

databaseChooser = do
  dbs  <- liftIO$ listDBS
  dbsW <- UI.listBox (pure $ M.keys dbs ) (pure Nothing ) (pure (\i -> UI.div # set text (T.unpack i)))
  schW <- UI.listBox (concat . maybeToList .join .fmap  (flip M.lookup dbs) <$> UI.userSelection dbsW ) (pure Nothing ) (pure (\i -> UI.div # set text (T.unpack i)))
  load <- UI.button # set UI.text "Connect" # sink UI.enabled (facts $ liftA2 (&&) (isJust <$> UI.userSelection dbsW) (isJust <$> UI.userSelection schW))
  chooserDiv <- UI.div # set children [getElement dbsW,getElement schW,load]
  let genSchema (Just dbN) (Just schemaN) = do
        conn <- connectPostgreSQL ("user=postgres dbname=" <> toStrict ( encodeUtf8 dbN ))
        inf@(k,baseTables,_,schema,invSchema,graphP) <- keyTables conn  schemaN
        return (conn,inf)
  return $ (unsafeMapIO id $ genSchema <$> (facts $ UI.userSelection dbsW ) <*> (facts $ UI.userSelection schW) <@ UI.click load,chooserDiv)

-- TODO: Remove Normalization to avoid inconsistencies
unSSerial (SSerial i ) = i
unSSerial i = traceShow ("No Pattern Match SSerial " <> show i) Nothing

unSOptional (SOptional i ) = i
unSOptional i = traceShow ("No Pattern Match SOptional" <> show i) Nothing

buildUI i  tdi = case i of
         (KOptional ti) -> fmap (Just . SOptional) <$> buildUI ti (join . fmap unSOptional <$> tdi)
         (KSerial ti) -> fmap (Just . SSerial) <$> buildUI ti ( join . fmap unSSerial <$> tdi)
         (KArray ti)  -> do
          let
              justCase i j@(Just _) = j
              justCase i Nothing = i
          inputUI <- UI.textarea # sink UI.value (facts (forceDefaultType  <$> tdi)) # set UI.style [("width","300px"),("height","60px"),("vertical-align","middle")]
          let pke = foldl1 (unionWith justCase ) [readType (textToPrim <$> i) <$> UI.valueChange inputUI,rumors  tdi]
          pk <- stepper (defaultType i)  pke
          let pkt = tidings pk pke
          return $ TrivialWidget pkt inputUI
         z -> do
          let
              justCase i j@(Just _) = j
              justCase i Nothing = i
          inputUI <- UI.input # sink UI.value (facts (forceDefaultType  <$> tdi))
          let pke = foldl1 (unionWith justCase ) [readType (textToPrim <$> i) <$> UI.valueChange inputUI,rumors  tdi]
          pk <- stepper (defaultType i)  pke
          let pkt = tidings pk pke
          return $ TrivialWidget pkt inputUI



ifApply p f a = if p a then f a else a

crudUITable
  :: Connection
     -> InformationSchema
     -> TB1 Key
     -> Tidings (Maybe (TB1 (Key,Showable)))
     -> UI (Element,Behavior (Maybe (TB1 (Key,Showable))),[Event (Modification Key Showable)])
crudUITable conn inf tb@(TB1 (KV (PK k d) a)) oldItems = do
  let
      tbCase td ix i@(FKT _ _) = fkUITable conn inf (fmap ((!!ix) .td .unTB1) <$> oldItems) i
      tbCase td ix a@(Attr i) = attrUITable (fmap ((!!ix) .td .unTB1) <$> oldItems)  a
      mapMI f = Tra.mapM (uncurry f) . zip [0..]
      Just table = M.lookup (S.fromList $findPK tb) (pkMap inf)
  fks <- liftA3 (\i j k -> KV (PK i j ) k)
      (mapMI (tbCase (pkKey.kvKey)) k)
      (mapMI (tbCase (pkDescription.kvKey)) d)
      (mapMI (tbCase (kvAttr)) a)
  let tb = fmap TB1 . Tra.sequenceA <$> Tra.sequenceA (fmap (snd) fks)
  crudHeader <- UI.div # set text (T.unpack "")
  (panelItems,evsa)<- processPanelTable conn  ( tb ) table ( oldItems)
  listBody <- UI.ul
    # set children (F.toList (fst <$> fks))
    # set style [("border","1px"),("border-color","gray"),("border-style","solid"),("margin","1px")]
  body <- UI.div
    # set children ([crudHeader, listBody ]<> panelItems )
    # set style [("border","2px"),("border-color","gray"),("border-style","solid")]
  return (body, tb ,evsa)

processPanelTable
     :: Connection
     -- -> Behavior (Maybe [(Key, Showable)])
     -> Behavior (Maybe (TB1 (Key, Showable)))
     -> Table
     -> Tidings (Maybe (TB1 (Key, Showable)))
     -> UI ([Element],[Event (Modification Key Showable)])
processPanelTable conn attrsB table oldItemsi = do
  let fkattrsB = fmap (concat . F.toList .fmap attrNonRec .unTB1 ) <$> attrsB
      oldItems = fmap (concat . F.toList .fmap attrNonRec .unTB1 ) <$> oldItemsi
      efkattrsB :: Behavior (Maybe [(Key,Showable)])
      efkattrsB = fmap (catMaybes . concat .F.toList. fmap attrNonRec . unTB1 ) <$> liftA2 (liftA2 (liftF2  (\i j -> if i == j then Nothing else Just i))) attrsB (facts oldItemsi)
  deleteB <- UI.button  # sink UI.enabled (isJust <$> facts oldItems) # set text "DELETE"
  editB <- UI.button # sink UI.enabled (liftA2 (&&) (isJust <$>  efkattrsB) (isJust <$> fkattrsB)) # set text "EDIT"
  insertB <- UI.button  # sink UI.enabled (isJust <$> fkattrsB) # set text "INSERT"
  let
      deleteAction ki =  do
        let k = fmap (concat . F.toList .fmap attrNonRec .unTB1 ) ki
            kf = fmap F.toList ki
        res <- liftIO $ catch (Right <$> delete conn (fromJust k) table) (\e -> return $ Left (show $ traceShowId  (e :: SomeException) ))
        return $ const (Delete kf ) <$> res
      editAction attr old = do
        let i = traceShowId $ fromJust isM
            k = traceShowId $ fromJust kM
            kM = (concat . F.toList .fmap attrNonRec .unTB1 ) <$> old
            isM :: Maybe [(Key,Showable)]
            isM = (catMaybes . concat . F.toList  . fmap attrNonRec .unTB1) <$> (liftA2 (liftF2  (\i j -> if i == j then Nothing else Just i))) attr old
            isM' :: Maybe [(Key,Showable)]
            isM' = (catMaybes . F.toList  ) <$> (liftA2 (liftF2  (\i j -> if i == j then Nothing else Just i))) attr old
            kM' = F.toList <$> old
        res <- liftIO $ catch (Right <$> update conn i k table) (\e -> return $ Left (show $ traceShowId (e :: SomeException) ))
        let updated = fromJust isM'
        return $ fmap (const (Edit (fmap (mappend updated) (filter (\(k,_) -> not $ k `elem` (fmap fst updated)) <$> kM') ) kM')) res

      insertAction ip = do
          let i2 = F.toList  ip
              i = concat . F.toList .fmap attrNonRec .unTB1 $ ip
          res <- catch (Right <$> insertPK fromShowableList conn i table) (\e -> return $ Left (show $ traceShowId (e :: SomeException) ))
          return $ (\v -> Insert $ Just $ (v <> (filter (not . flip elem (fst <$> v) . fst) i2))) <$> res

      evir, ever ,evdr:: Event (Modification Key Showable)
      (evid,evir) = spMap $ filterJust $ (fmap insertAction  <$> attrsB ) <@ (UI.click insertB)
      (evdd,evdr) = spMap $ (deleteAction <$> facts oldItemsi) <@ UI.click deleteB
      (eved,ever) = spMap $ (editAction  <$> attrsB <*> (facts oldItemsi) ) <@ UI.click editB
      spMap = split . unsafeMapIO id

  -- (evid,evir) <- split <$> shortCut (insertAction . catMaybes <$> fkattrsB)  (UI.click insertB)
  -- (evdd,evdr) <- split <$> shortCut (deleteAction <$> facts oldItems) (UI.click deleteB)
  -- (eved,ever) <- split <$> shortCut (editAction  <$> efkattrsB <*> (facts oldItems) ) (UI.click editB)
  -- stp <- stepper [] (unions [evid,evdd])
  -- end <- UI.div # sink text (show <$> stp)
  return ([insertB,editB,deleteB],[evir,ever,evdr])


attrUITable
  :: Tidings (Maybe (TB (Key,Showable)))
     -> TB Key
     -> UI
          (Element, Behavior (Maybe (TB (Key, Showable))))
attrUITable  tAttr' (Attr i) = do
      l<- UI.span # set text (show i)
      let tdi = tAttr -- foldrTds justCase plugItens [tAttr]
          justCase i j@(Just _) = j
          justCase i Nothing = i
      attrUI <- buildUI (keyType i) tdi
      expandEdit <- checkedWidget
      let
          ei (Just a) = Just a
          ei Nothing = defaultType (keyType i)
      e <- buildUI (keyType i) tAttr
      eplug <- buildUI (keyType i) (pure Nothing)
      element e # sink UI.style (noneShowSpan <$> (facts $ triding expandEdit)) # set UI.enabled False
      element eplug # sink UI.style (noneShowSpan <$> (facts $ triding expandEdit)) # set UI.enabled False
      paint l (facts $ triding attrUI )
      sp <- UI.li # set children [l,getElement attrUI ,getElement expandEdit,getElement e,getElement eplug]
      let insertT = fmap (Attr .(i,)) <$> (triding attrUI)
          editT = liftA2 (\n m -> join $ liftA2 (\i j -> if i == j then Nothing else Just j) n m) tAttr' insertT
      return (sp,facts insertT)
  where tAttr = fmap (\(Attr i)-> snd i) <$> tAttr'


findPK = concat . fmap attrNonRec . pkKey  . kvKey . unTB1

attrNonRec (FKT ifk _ ) = ifk
attrNonRec (Attr i ) = [i]

fkUITable
  :: Connection
  -> InformationSchema
  -> Tidings (Maybe (TB (Key,Showable)))
  -> TB Key
  -> UI (Element,Behavior (Maybe (TB (Key, Showable))))
fkUITable conn inf oldItems tb@(FKT ifk tb1) = mdo
      let
          o1 = S.fromList $ findPK tb1
          tdi :: Tidings (Maybe (TB1  (Key,Showable)))
          tdi =  fmap (\(FKT _ t) -> t) <$> oldItems
      res <- liftIO $ projectKey conn inf (projectAllRec' (tableMap inf )) o1
      l <- UI.span # set text (show ifk)
      box <- UI.listBox res2 tdi (pure (\v-> UI.span # set text (show $ kvKey $ unTB1 $  snd <$> v)))
      let
        fksel = fmap (zipWith (\kn (ko,v)-> (kn,transformKey (textToPrim <$> keyType ko ) (textToPrim <$> keyType kn) v) )  ifk  ) <$>  facts (fmap findPK  <$> UI.userSelection box)
        tdsel = fmap (\i -> FKT (zip ifk . fmap snd  . findPK $ i ) i)  <$>  UI.userSelection box
        edited = liftA2 (\i j -> join $ liftA2 (\i j-> if  i == j then Nothing else Just j ) i j) oldItems tdsel
      paint (getElement l) fksel
      chw <- checkedWidget
      (celem,tcrud,evs) <- crudUITable conn inf tb1 (UI.userSelection box)
      let eres = fmap (addToList  (allRec (tableMap inf) (fromJust $ M.lookup o1 (pkMap inf))) <$> ) evs
      res2  <-  accumTds (pure res) eres
      element celem
        # sink UI.style (noneShow <$> (facts $ triding chw))
        # set style [("padding-left","10px")]
      fk <- UI.li # set  children [l, getElement box,getElement chw,celem]
      let bres =  liftA2 (liftA2 FKT) fksel  tcrud
      return (fk,bres)

addToList i  (Insert m) =  (\i-> mappend (fmap ((\(k,v)-> (k, v)))  <$> maybeToList i) ) (editedMod  i m )
addToList i  (Delete m ) =  (\i-> concat . L.delete (fmap ((\(k,v)-> (k, v)))  <$> maybeToList i)  . fmap pure ) (editedMod  i  m )
addToList i  (Edit m n ) =  (map (\e-> if maybe False (e == ) (editedMod i n) then  fmap (\(k,v) -> (k,)  $ fromJust $ M.lookup k (M.fromList $ fromJust m) ) e  else e ) ) --addToList i  (Insert  m) . addToList i  (Delete n)

-- lookup pk from attribute list
editedMod :: (Show (f (a,b)),Show (a,b),Traversable f ,Ord a) => f a ->  Maybe [(a,b)] -> Maybe (f (a,b))
editedMod  i  m=  traceShow m $ traceShowId $ join $ fmap (\mn-> look mn i ) m
  where look mn k = allMaybes $ fmap (\ki -> fmap (ki,) $  M.lookup ki (M.fromList mn) ) k


forceDefaultType  (Just i ) = renderShowable i
forceDefaultType  (Nothing) = ""

paint e b = element e # sink UI.style (greenRed . isJust <$> b)

data Plugins
  = Plugins
  { _name :: String
  ,_inputs :: (Table, S.Set Key)
  , _action :: Connection -> InformationSchema -> Plugins -> Tidings (Maybe [(Key,Showable)]) -> UI (Element,Tidings (Maybe (Map Key Showable)) )
  }
data  PollingPlugins = PollingPlugins
  { _pollingName :: String
  , _pollingTime :: Int
  , _pollingInputs :: (Table, S.Set Key)
  , _pollingAction :: Connection -> InformationSchema -> PollingPlugins -> Tidings ([[(Key,Showable)]]) -> UI (Element,Tidings (Maybe (Map Key Showable)) )
  }

classifyKeys (table@(Raw s t pk desc fk allI),keys) = (S.intersection keys attrSet,S.intersection keys fkSet)
    where fkSet = S.unions $ fmap (\(Path ifk t o) ->  ifk)  (S.toList fk)
          attrSet = S.fromList $ filter (not. (`S.member` fkSet)) $ (S.toList pk <> S.toList allI)

attrSet pkm (Raw s t pk desc fk allI) =  pk <> allI <>  foldr mappend mempty (catMaybes $ pathTable <$> (F.toList fk) )
    where pathTable (Path o t e) = attrSet pkm <$> M.lookup e pkm

pollingUI conn inf p@(PollingPlugins n deftime (table@(Raw s t pk desc fk allI),keys) a) = do
  let plug = a conn inf p
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
    evq = fmap (fmap (F.toList .allKVRec)) $ unsafeMapIO  (\i -> doQueryAttr conn inf (projectAllRec' (tableMap inf) ) M.empty pk)    evpoll
  bht <- stepper Nothing (unsafeMapIO (fmap Just . const getCurrentTime) evpoll)
  bh <- stepper [] evq
  output <- UI.div  # sink text ((\v  t -> "Timer Interval: " <> show (fromIntegral v/60000) <> " minutes" <> " -  Last Poll: " <> maybe "-" show t ) <$> inter <*> bht)
  ev <- plug (tidings bh evq )
  body <- UI.div  # set children (([headerP,b,inp,staT,stoT,output]<>) . pure $  fst ev :: [Element])
  return (body, snd ev)


pluginUI conn inf p@(Plugins n (table@(Raw s t pk desc fk allI),keys) a) oldItems = do
  let plug = a conn inf p
  ev <- plug oldItems
  headerP <- UI.div # set text n
  body <- UI.div  # set children ((headerP:) . pure $  fst ev :: [Element])
  return (body,  snd ev )



-- Split composite PKs in list of atomic pks
invertPK :: PK a -> [PK a]
invertPK  (PK k [] ) = fmap (\i -> PK [i] []) k
invertPK  (PK k d ) = zipWith (\i j -> PK [i] [j]) k d

projectFk schema k = case M.keys <$> M.lookup k schema of
                Just l ->  fmap S.singleton l
                Nothing -> []

type ProjAction = (forall t. Traversable t =>
                    (QueryCursor t  -> IO [t Showable],
                      QueryT Identity (t KAttribute)
                      -> S.Set Key -> QueryCursor t ))


safeHead [] = Nothing
safeHead i = Just $ head i




doQueryTable :: Traversable t => Connection -> InformationSchema -> QueryT Identity (t KAttribute)  ->
                    (Map Key [Filter]) -> (S.Set Key) -> IO (t Key,[t Showable])
doQueryTable conn inf q f arg  = projectTable  conn inf (do
              predicate (concat $ filterToPred <$> (M.toList f))
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

addEvent ne t = do
  c <- currentValue (facts t)
  let ev = unionWith const (rumors t) ne
  nb <- stepper c ev
  return $ tidings nb ev

data RangeBox a
  = RangeBox
  { _rangeSelection ::  Tidings (Maybe (Interval.Interval (Maybe a)))
  , _rangeElement :: Element
  }

rangeBoxes fkbox bp = do
  rangeInit <- UI.listBox bp (const <$> pure Nothing <*> fkbox) (pure (\i-> UI.li # set text (show i)))
  rangeEnd <- UI.listBox bp (const <$> pure Nothing <*> fkbox) (pure (\i-> UI.li # set text (show i)))
  range <- UI.div # set children (getElement <$> [rangeInit,rangeEnd])
  return $ RangeBox (NI.interval <$> (UI.userSelection rangeInit) <*> (UI.userSelection rangeEnd)) range



instance Widget (RangeBox a) where
  getElement = _rangeElement


unionsT :: MonadIO m => Tidings [Tidings a] ->  m (Tidings [a])
unionsT c = do
  vals <- currentValue (facts c)
  vcur <- mapM currentValue (facts <$> vals)
  let ecur = unions $ rumors <$> vals
  b <- stepper vcur ecur
  return $ tidings b ecur

filterMaybe f (Just i ) = f i
filterMaybe _ _  = []


filterWidget
  :: Connection -> InformationSchema
     -> Tidings (S.Set Key)
     -> Tidings (Map Key [Filter])
     -> UI (UI.MultiListBox (PK Showable ),UI.ListBox (S.Set Key ),RangeBox (PK Showable),TrivialWidget (Map Key [Filter]))
filterWidget conn inf bBset filterT = do
  -- Filter Box (Saved Filter)
  ff  <- insdel (facts filterT)

  -- Filterable Keys
  let bFk = fmap (projectFk (hashedGraph inf) ) bBset
  fkbox <- UI.listBox (liftA2 (<>) (fmap S.singleton .S.toList <$> bBset) bFk) (const <$> pure Nothing <*> fmap Just bBset) (pure (\i-> UI.li # set text (showVertex i)))

  -- Filter Query
  bp <- joinT $ (\i j-> maybe (return []) id (fmap (doQuery conn inf projectDesc i) j)) <$> triding ff <*> UI.userSelection fkbox
  rangeWidget <- rangeBoxes (UI.userSelection fkbox)  bp

  -- Filter Selector
  filterItemBox <- UI.multiListBox bp (const <$> pure [] <*> UI.userSelection fkbox) (pure (\i-> UI.li # set text (show i)))
  return  (filterItemBox,fkbox, rangeWidget ,ff)

line n = UI.li # set  text n

tableElem h b =  grid $ header h : body b
	where header = fmap st
	      body = fmap (fmap st)
	      st i = UI.div # set text (show  i) # set UI.style [("padding","5px"),("border-width","1px"),("border-color","gray"),("border-style","solid")]


selectedItems conn inf ff key = do
  let
    invItems :: Tidings [(S.Set Key , Path Key (SqlOperation Table))]
    invItems = ((\k -> case  M.lookup k (hashedGraphInv inf) of
            Just invItems ->  M.toList invItems
            Nothing -> [] )) <$> key
  let
    query i j
      | M.null i = return []
      | otherwise = fmap catMaybes $ mapM (\k-> fmap (fmap (fst k,)) . (`catch` (\e-> flip const (e :: SomeException)  $ return $ traceShow e  Nothing ) ) . fmap Just . doQueryTable conn inf (projectTableAttrs  (fromJust $ M.lookup (fst k) $ pkMap inf )) i.  fst $ k ) j
  bp <- joinT $ (query <$> ff <*> invItems)
  body <- UI.div # sink items (fmap (\(v,i) -> UI.div # set items (UI.div # set text (showVertex  v ) : [tableElem  (F.toList $ fst i) $ fmap F.toList (snd i)]) )  . filter (not . null . snd .snd)  <$> facts bp)
  UI.div # set children [body]

poller conn poll inf = do
  -- Base Button Set
  resPoll  <- mapM ( pollingUI conn inf)   $ poll
  polling <- UI.div # set children (fst <$> resPoll)
  UI.div # set children [polling]


chooserKey conn pg inf kitems  = do
  -- Base Button Set
  bset <- buttonSet kitems (\i -> case M.lookup i (pkMap inf) of
                                       Just (Raw _ i  _ _ _ _ )-> T.unpack i
                                       Nothing -> showVertex i )

  let bBset = triding bset
  body <- UI.div # sink items (facts (pure . chooseKey conn pg inf <$> bBset ))
  UI.div # set children [getElement bset, body]

chooseKey
  :: Connection
     -> [Plugins]
     -> InformationSchema -> S.Set Key -> UI Element
chooseKey conn  pg inf key = mdo
  -- Filter Box (Saved Filter)
  let bBset = pure key :: Tidings (S.Set Key)
  (filterItemBox,fkbox,range,ff) <- filterWidget conn inf bBset filterT

  -- countAll Query
  let
    bFk = projectFk (hashedGraph inf) key
    {- aggQuery i j ka k
      | S.null j = return []
      | otherwise = doQuery conn inf (aggAll  (pkMap inf) (S.toList j) ka)  i k-}

  let pkFields = allAttrs . fromJust . (flip M.lookup (pkMap inf)) <$> bBset
      aggregators = (concat . fmap (\i->  flip availableAggregators i . primType $ i) . S.toList <$> pkFields )
  let aset = flip buttonSet show <$> facts aggregators

  -- Filter Map Selected
  let
    rangeT :: Tidings (Map Key [Filter])
    rangeT = corners <$> _rangeSelection range <*> (fmap S.toList  <$> UI.userSelection fkbox)
      where corners i mk = case i of
              Just i -> case NI.inf i of
                          Just l -> case  NI.sup i of
                            Just u -> case (fmap (\k -> zipWith (\m n-> (n,[RangeFilter m])) [l NI.... u ] k) mk) of
                              Just res -> M.fromList res
                              Nothing -> M.empty
                            Nothing -> M.empty
                          Nothing -> M.empty
              _ ->  M.empty
    categoryT :: Tidings (Map Key [Filter])
    categoryT = M.fromListWith mappend <$> (filterMaybe (fmap (\(fkv,kv)-> (fkv,[Category (S.fromList kv)]))) <$> arg)
      where arg :: Tidings (Maybe [(Key, [PK Showable])])
            arg = (\i j -> fmap (\nj -> zipWith (,) nj (L.transpose j) ) i) <$> (fmap S.toList  <$> UI.userSelection fkbox ) <*> (fmap invertPK <$> UI.multiUserSelection filterItemBox)
    filterT = liftA2 (M.unionWith mappend) categoryT rangeT


  vp <-   joinT $ doQueryAttr conn inf (projectAllRec' (tableMap inf)) <$> (M.unionWith mappend <$> filterT <*> triding ff) <*>  bBset
  -- Final Query ListBox
  filterInp <- UI.input
  filterInpBh <- stepper "" (UI.valueChange filterInp)

  let filterInpT = tidings filterInpBh (UI.valueChange filterInp)

  let sortSet = filter (filterIntervalSort . keyType ) . F.toList . allRec (tableMap inf) . fromJust . flip M.lookup (pkMap inf) <$> bBset
      filterIntervalSort (KInterval i) = False
      filterIntervalSort (KOptional i) = filterIntervalSort i
      filterIntervalSort i = True
  sortList  <- UI.listBox sortSet ((safeHead . F.toList) <$> sortSet) (pure (line . show  ))
  asc <- checkedWidget
  let listManip :: (Show (f (Key,Showable)), F.Foldable f) => String ->[f (Key,Showable)] -> Maybe Key -> Bool -> [f (Key,Showable)]
      listManip i j Nothing  _ =  filtering  i j
      listManip i j (Just s) b  = filtering i .  L.sortBy ( ifApply (const b) flip (comparing (M.lookup s .M.fromList . F.toList )) ) $ (F.toList j)
      filtering i= filter (L.isInfixOf (toLower <$> i) . fmap toLower . show )
      listRes = listManip  <$> filterInpT <*> res2 <*> UI.userSelection sortList <*> triding asc
      reducer (SDouble i) (SDouble j)  =  SDouble $ i + j
      reducer i j = error $ "not reducible : " <> show i <> " - " <> show j
      isReducible (Primitive PDouble)  = True
      isReducible i = False

  itemList <- UI.listBox listRes  (pure Nothing) (pure (\i -> line $ show  $ allKVRec $ fmap snd i))
  element itemList # set UI.style [("width","100%"),("height","300px")]
  total <- UI.div  # sink UI.text (("Total: " <> ) . show . (\k-> foldr (M.unionWith reducer ) M.empty (  M.fromList . filter(isReducible . fmap textToPrim . keyType . fst) . F.toList <$> k )) <$>  facts listRes)
  let
    categoryT1 :: Tidings (Map Key [Filter])
    categoryT1 = M.fromListWith mappend <$> (filterMaybe (fmap (\(fkv,kv)-> (fkv,[Category (S.fromList kv)]))) <$> arg)
      where arg :: Tidings (Maybe [(Key, [PK Showable])])
            arg = (\i j -> fmap (\nj -> zipWith (,) nj (L.transpose j) ) i) <$> (fmap S.toList  . Just <$> bBset ) <*> (fmap invertPK  . maybeToList . fmap (\i -> snd <$> kvKey ( allKVRec i) )  <$> UI.userSelection itemList)

  sel <- UI.multiListBox (pure bFk) (pure bFk) (pure (line . showVertex))
  -- t <- joinT $ aggQuery  <$> (M.unionWith mappend <$> categoryT1 <*> triding ff) <*> (S.unions <$> UI.multiUserSelection sel) <*> aggregators <*> bBset
  -- count <- UI.div # sink text (fmap show $ facts t)

  selected <- selectedItems conn inf categoryT1  bBset
  element (getElement itemList) # set UI.multiple True
  element (getElement filterItemBox) # set UI.multiple True
  res  <- mapM (\i -> pluginUI conn inf i (fmap F.toList <$> UI.userSelection itemList  ) )   (filter (\(Plugins n tb _ )-> S.isSubsetOf  (snd tb) (attrSet (pkMap inf) (fromJust $ M.lookup key (pkMap inf)))  ) pg )
  plugins <- UI.div # set children (fst <$> res)
  let
      tdi2 = case snd <$> res of
        [] -> pure Nothing
        xs -> foldr1 (liftA2 mappend)  xs

  let
     filterOptions = case M.keys <$> M.lookup key (hashedGraph inf) of
               Just l -> key : fmap S.singleton l
               Nothing -> [key]
     convertPK i = case fmap F.toList i of
        Nothing -> Just []
        i -> i
     table = fromJust $ M.lookup key (pkMap inf)
  (crud,_,evs) <- crudUITable conn inf (allRec (tableMap inf) table) (UI.userSelection  itemList) -- UI.userSelection itemList)
  let eres = fmap (addToList  (allRec (tableMap inf ) table )  <$> ) evs
  res2 <- accumTds vp  eres
  insertDiv <- UI.div # set children [crud]
  filterSel <- UI.div # set children [getElement ff,getElement fkbox,getElement range, getElement filterItemBox]
  -- aggr <- UI.div # set children [getElement sel , count]
  tab <- tabbed  [("CRUD",insertDiv),("FILTER",filterSel){-,("AGGREGATE", aggr)-},("PLUGIN",plugins),("SELECTED",selected)]
  itemSel <- UI.div # set children [filterInp,getElement sortList,getElement asc]
  UI.div # set children ([itemSel,getElement itemList,total,tab] )



queryCnpjProject conn inf (Plugins n (table@(Raw s t pk desc fk allI),keys) a) oldItems= fmap (,pure Nothing ) $ do
      let tableName = "fire_project"
          addrs ="http://siapi.bombeiros.go.gov.br/consulta/consulta_protocolo.php"
          translate = [("protocolo","protocolo"),("ano","ano")]
          td =  renderUrl translate addrs  . fmap (filter (not . isEmptyShowable. snd ))  <$> oldItems
      iframe <- mkElement "iframe" #  sink UI.src (facts td)
              # set style [("width","100%"),("height","300px")]
      body <- UI.div  # set children [iframe]
      return body


genPlugin :: (Ord a1, Ord t, Ord a) => t -> [a] -> (Map (t, a) a1, t1, Map t t2, t3, t4, t5) -> Maybe (t2, Set a1)
genPlugin tname attr inf = do
  table2 <- M.lookup tname (tableMap inf)
  keys2 <- allMaybes $ fmap (flip M.lookup (keyMap inf) . (tname,)) attr
  return $ (table2,S.fromList keys2)


plug :: (Ord a, Ord t) => String -> (Connection -> InformationSchema -> Plugins -> Tidings (Maybe [(Key, Showable)]) -> UI (Element, Tidings (Maybe (Map Key Showable)))) -> t -> [a] -> (Map (t, a) Key, t1, Map t Table, t3, t4, t5) -> Maybe Plugins
plug  name fun table attr inf = flip (Plugins name ) fun <$> (genPlugin table attr inf)

poll :: (Ord a, Ord t) => String -> Int -> (Connection -> InformationSchema -> PollingPlugins -> Tidings [[(Key, Showable)]] -> UI (Element, Tidings (Maybe (Map Key Showable)))) -> t -> [a] -> (Map (t, a) Key, t1, Map t Table, t3, t4, t5) -> Maybe PollingPlugins
poll name time fun table attr inf = flip (PollingPlugins name time) fun <$> genPlugin table attr inf

pluginOrcamento = plug "Pricing Document" renderProjectPricing "pricing" ["pricing_price"]

pluginCEP = plug "CEP Correios" queryCEP2 "owner" ["id_owner"]

pluginAndamentoId = plug "Andamento" queryAndamento2 "fire_project" ["id_bombeiro"]

pluginItauTxt = plug  "Extrato Itau" itauExtractTxt "account" ["id_account"]

pluginBradescoCsv = plug  "Extrato Bradesco" bradescoExtractTxt "account" ["id_account"]

pluginWapp = plug  "Import Conversation" wappImport "chat" ["chat_instant"]

pollingAndamento = poll "Andamento Poll" 60 queryAndamento3 "fire_project" ["id_bombeiro"]

solicitationPlugin = plug "Solicitacao Bombeiro" solicitationForm "fire_project" ["id_bombeiro"]

pluginBombeiro = plug "Projeto Bombeiro" queryCnpjProject "fire_project" ["id_owner","ano","protocolo"]

pluginCnpjReceita = plug "Cnpj Receita" queryCnpjReceita "owner" ["id_owner"]

simpleGetRequest =  fmap BSL.pack . join . fmap HTTP.getResponseBody . HTTP.simpleHTTP . HTTP.getRequest


shortCutClick  t i = tidings (facts t) (facts t <@ i)

strAttr :: String -> WriteAttr Element String
strAttr name = mkWriteAttr (set' (attr name))


renderUrlM args url = fmap address . kv
  where
    kv i = allMaybes $ (\k -> join . fmap (\inp ->  fmap (snd k,) . M.lookup (fst k) . M.fromList $ fmap (\(k,v)-> (keyValue k,v)) inp ) $  i ) <$> args
    renderKv = HTTP.urlEncodeVars . fmap (\(k,v)-> (k , show v))
    address i =  url <> "?"  <> renderKv i

renderUrl args url = address
  where
    kv i = catMaybes $ (\k -> join . fmap (\inp ->  fmap (snd k,) . M.lookup (fst k) . M.fromList $ fmap (\(k,v)-> (keyValue k,v)) inp ) $  i ) <$> args
    renderKv = HTTP.urlEncodeVars . fmap (\(k,v)-> (k , show v))
    address i =  url <> "?"  <> renderKv (kv i)
-- This Iframe needs cross reference scripting enabled in the browser , this implies big security concerns
renderUrlWithKeys args url inputs =   element
  where
    element = mkElement "iframe" # sink UI.src (renderUrl args url <$> facts inputs) # set style [("width","100%"),("height","300px")] # set (strAttr "onload") script
    -- script to set query kv to form kv
    script = "var win = this.contentWindow ; var docu = this.contentDocument ; function getUrlVars() {    var vars = [], hash;    var hashes = win.location.href.slice(win.location.href.indexOf('?') + 1).split('&');    for(var i = 0; i < hashes.length; i++)    {        hash = hashes[i].split('=');        vars.push(hash[0]);        vars[hash[0]] = hash[1] != null ? decodeURIComponent(hash[1].replace(/\\+/g, ' ')) : hash[1] ;    }    return vars;} ; var args = getUrlVars(); Object.keys(args).map(function(i){var doc = docu.getElementById(i) ; doc != null ? doc.value = args[i] : args[i] });"


spanList :: ([a] -> Bool) -> [a] -> ([a], [a])

spanList _ [] = ([],[])
spanList func list@(x:xs) =
    if func list
       then (x:ys,zs)
       else ([],list)
    where (ys,zs) = spanList func xs

{- | Similar to Data.List.break, but performs the test on the entire remaining
list instead of just one element.
-}
breakList :: ([a] -> Bool) -> [a] -> ([a], [a])
breakList func = spanList (not . func)

solicitationForm _ _  _ inputs =  (,pure Nothing) <$> element
   where translate  =  [("owner_municipio","localidade"),("cgc_cpf","cgc_cpf"),("owner_name","razao_social"),("logradouro","logradouro"),("owner_number","numero"),("owner_complemento","complemento")]
         address =  "http://siapi.bombeiros.go.gov.br/projeto/cad_solicitacao_projeto.php"
         element = renderUrlWithKeys translate address inputs

splitL :: Eq a => [a] -> [a] -> [[a]]
splitL _ [] = []
splitL delim str =
    let (firstline, remainder) = breakList (L.isPrefixOf delim) str
        in
        firstline : case remainder of
                                   [] -> []
                                   x -> if x == delim
                                        then [] : []
                                        else splitL delim
                                                 (drop (length delim) x)

getRequest ::  String -> MaybeT IO BSL.ByteString
getRequest = join . C.lift . (`catch` (\e ->  traceShow (e :: IOException) $ return mzero ) ).  fmap return . simpleGetRequest

lookTable inf t = justError ("no table: " <> T.unpack t) $ M.lookup t (tableMap inf)


queryAndamento4 conn inf k inputs = fmap (snd $ fromJust .L.find ((== "project_description") . keyValue . fst )$ inputs,) <$> (  runMaybeT $ do
                MaybeT $ return $ if elem "aproval_date" ((keyValue . fst)<$>  filter (not . isEmptyShowable. snd ) inputs ) then Nothing else Just undefined
                let tableName = "fire_project"
                    fire_project = lookTable inf "fire_project"
                    andamento = lookTable inf "andamento"
                    addrs ="http://siapi.bombeiros.go.gov.br/consulta/consulta_protocolo.php"
                    translate = [("protocolo" , "protocolo"),("ano","ano")]
                (lkeys,modB) <- if not $ elem "id_bombeiro" ((keyValue . fst)<$>  filter (not . isEmptyShowable. snd ) inputs )
                   then do
                    url <- MaybeT $ return $ renderUrlM translate addrs  $ filter (not . isEmptyShowable. snd )  <$> Just inputs
                    lq <-  getRequest . traceShowId $ url
                    let
                      lq2 =  Just . maybe M.empty (uncurry M.singleton . ("id_bombeiro",)) . fmap SNumeric . readMaybe.  fst .  break (=='&') . concat . tail .  splitL ("php?id=")  .T.unpack . decodeLatin1  $  lq
                      lkeys = fmap ( M.toList . M.mapKeys (fromJust . flip M.lookup (keyMap inf) . (tableName,)  ))  $ lq2
                    mod <- C.lift $ updateMod conn (fromJust lkeys) inputs (fromJust $ M.lookup  tableName (tableMap inf) )
                    return $  (lkeys,mod)
                   else do return $ (fmap (\i-> [i])   $ L.find ((== "id_bombeiro") .  keyValue . fst) inputs,Nothing)
                let
                    addrs_a ="http://siapi.bombeiros.go.gov.br/consulta/consulta_andamento.php"
                    translate_a = [("id_bombeiro" , "id")]
                tq <-  getRequest . traceShowId . (renderUrl translate_a addrs_a)  $  lkeys
                let
                  tq2 =  T.unpack $  decodeLatin1 tq
                  convertAndamento [da,desc] = [("andamento_date",SDate . Finite . localDay . fst . justError "wrong date parse" $  strptime "%d/%m/%y" da  ),("andamento_description",SText (T.filter (not . (`elem` "\n\r\t")) $ T.pack  desc))]
                  convertAndamento i = error $ "convertAndamento:  " <> show i
                  tkeys v =  M.mapKeys (justError "attr table andamento" . flip M.lookup (keyMap inf) . ("andamento" :: Text,)  )  v
                  prepareArgs  = fmap ( tkeys . M.fromList . convertAndamento ) .  tailEmpty . concat
                  lookInput = justError "could not find id_project" . fmap (\(k,v) -> let k1 = fromJust $ M.lookup ("andamento","id_project") (keyMap inf) in (k1, transformKey (textToPrim <$> keyType k)  (textToPrim <$> keyType k1) v) ) . L.find ((== "id_project") . keyValue . fst)
                  insertAndamento :: String -> MaybeT IO [Maybe (TableModification Showable)]
                  insertAndamento i  =  C.lift $ do
                      html <- readHtml $ i
                      let
                          args :: S.Set (Map Key Showable)
                          args = S.fromList $ fmap (uncurry M.insert  (lookInput inputs )) $ prepareArgs html
                      mod <- case filter ( maybe False (\(SText t) -> T.isInfixOf "Aprovado" t ) .  M.lookup "andamento_description" . M.mapKeys keyValue )  $ S.toList args of
                          [i] -> updateMod  conn [(justError "could not lookup approval_date " . flip M.lookup (keyMap inf) $ (tableName,"aproval_date") , justError "could not lookup andamento_date" $ M.lookup "andamento_date"  $ M.mapKeys keyValue i)] inputs fire_project
                          i -> return Nothing
                      vp <- doQueryAttr conn inf (projectAllRec' (tableMap inf)) (uncurry M.singleton $  fmap ( (\i->[i]) . Category . S.singleton . flip PK [].(\i->[i]) ) (lookInput inputs ) ) ( (\(Raw _ _ pk _ _ _ ) -> pk ) andamento )

                      let kk = S.fromList (fmap (M.fromList . filter ((`elem` ["id_project","andamento_description","andamento_date"] ) . keyValue . fst ) . concat . F.toList . fmap attrNonRec . unTB1) vp) :: S.Set (Map Key Showable)
                      adds <- traceShow ("KK " <> show kk <> " \n ARGS " <> show args) $ mapM (\kv -> (`catch` (\e -> return $ trace ( show (e :: SqlError)) Nothing )) $ insertMod conn  (M.toList kv) (andamento )) (S.toList $ args  `S.difference`  kk)
                      return $ mod : adds
                v <- insertAndamento tq2
                let mods =catMaybes $  modB : v
                mapM (C.lift . logTableModification inf conn) mods
                MaybeT $ return  $ (\case {[] -> Nothing ; i -> Just i }) mods )

queryAndamento3 conn inf  k  input = do
        tq <-  mapT (mapM (queryAndamento4 conn inf k ) ) input
        e <- UI.div # sink appendItems ( fmap (\i -> UI.div # set text (show i) ) . catMaybes  <$> facts tq  )
        return (e , pure Nothing)

updateMod conn kv old table = do
  (i,j) <- update conn  kv old table
  return $ Just j

insertMod conn kv table = do
  insert conn  kv table
  return $ Just $ TableModification table (Insert $ Just kv)

logTableModification inf conn (TableModification table i) = do
  let look k = fromJust $ M.lookup ("modification_table",k) (keyMap inf)
  insertPK fromShowableList conn [(look "table_name" ,SText $ tableName  table) , (look "modification_data", SText $ T.pack $ show i)] (fromJust $ M.lookup ("modification_table") (tableMap inf))

bradescoRead file = do
  file <- TE.decodeLatin1 <$> BS.readFile file
  let result =  fmap (fmap TE.unpack . L.take 5) $ filter (\(i:xs) -> isJust $ strptime "%d/%m/%y" (TE.unpack i)) $ filter ((>5) . length) $  TE.split (';'==) <$> TE.split (=='\r') file
  return result


bradescoExtractTxt  conn  inf  _ inputs = do
    pathInput <- UI.input -- # set UI.type_ "file"
    b <- UI.button # set UI.text "Import"
    bhInp <- stepper "" (UI.valueChange pathInput)
    let process (Just inp) path = do
          content <- bradescoRead  path
          let parse  = uncurry M.insert (lookInput inp )  . tkeys . parseField  <$> content
              lookInput = fromJust .L.find ((== "id_account") . keyValue . fst)
              tkeys v =  M.mapKeys (fromJust . flip M.lookup (keyMap inf) . ("transaction" :: Text,)  )  v
              parseField [d,desc,_,v,""] = M.fromList [("transaction_date",SDate $ Finite $ localDay $ fst $ fromJust $ strptime "%d/%m/%y" d),("transaction_description",SText $ T.pack desc),("transaction_price", SDouble $ read $ fmap (\i -> if i == ',' then '.' else i) $ filter (not . (`elem` ".\"")) v)]
              parseField [d,desc,_,"",v] = M.fromList [("transaction_date",SDate $ Finite $ localDay $ fst $ fromJust $ strptime "%d/%m/%y" d),("transaction_description",SText $ T.pack desc),("transaction_price", SDouble $ read $ fmap (\i -> if i == ',' then '.' else i) $ filter (not . (`elem` ".\"")) v)]
          vp <- doQueryAttr conn inf (projectAllRec' (tableMap inf)) (uncurry M.singleton $  fmap ( (\i->[i]) . Category . S.singleton . flip PK [].(\i->[i]) ) (lookInput inp ) ) ( (\(Raw _ _ pk _ _ _ ) -> pk ) $fromJust $  M.lookup  "transaction" (tableMap inf ))
          let kk = S.fromList (fmap (M.fromList . filter ((`elem` ["id_account","transaction_description","transaction_date","transaction_price"] ) . keyValue . fst ) . F.toList ) vp) :: S.Set (Map Key Showable)
          adds <- mapM (\kv -> (`catch` (\e -> return $ trace ( show (e :: SqlError)) Nothing )) $ fmap Just $ insertPK fromShowableList  conn  (M.toList kv) (fromJust $ M.lookup  "transaction" (tableMap inf) )) (S.toList $ ( S.fromList parse ) `S.difference` kk)
          return parse
        process Nothing _ = do return []
        j = unsafeMapIO id $ process  <$> facts inputs <*> bhInp <@ UI.click b
    outStp <- stepper "" (fmap show $ j)
    out <- UI.div # sink UI.text outStp
    (,pure Nothing) <$> UI.div # set children [pathInput,b,out]

itauExtractTxt  conn  inf  _ inputs = do
    pathInput <- UI.input -- # set UI.type_ "file"
    b <- UI.button # set UI.text "Import"
    bhInp <- stepper "" (UI.valueChange pathInput)
    let process (Just inp) path = do
          file <-  readFile (traceShowId path)
          let parse  = uncurry M.insert (lookInput inp )  . tkeys . parseField . unIntercalate (';'==) <$> lines (filter (/='\r') file)
              lookInput = fromJust .L.find ((== "id_account") . keyValue . fst)
              tkeys v =  M.mapKeys (fromJust . flip M.lookup (keyMap inf) . ("transaction" :: Text,)  )  v
              parseField [d,desc,v] = M.fromList [("transaction_date",SDate $ Finite $ localDay $ fst $ fromJust $ strptime "%d/%m/%Y" d),("transaction_description",SText $ T.pack desc),("transaction_price", SDouble $ read $ fmap (\i -> if i == ',' then '.' else i) v)]
          vp <- doQueryAttr conn inf (projectAllRec' (tableMap inf)) (uncurry M.singleton $  fmap ( (\i->[i]) . Category . S.singleton . flip PK [].(\i->[i]) ) (lookInput inp ) ) ( (\(Raw _ _ pk _ _ _ ) -> pk ) $fromJust $  M.lookup  "transaction" (tableMap inf ))
          let kk = S.fromList (fmap (M.fromList . filter ((`elem` ["id_account","transaction_description","transaction_date","transaction_price"] ) . keyValue . fst ) . F.toList ) vp) :: S.Set (Map Key Showable)
          adds <- mapM (\kv -> (`catch` (\e -> return $ trace ( show (e :: SqlError)) Nothing )) $ fmap Just $ insertPK fromShowableList  conn  (M.toList kv) (fromJust $ M.lookup  "transaction" (tableMap inf) )) (S.toList $ ( S.fromList parse ) `S.difference` kk)
          return parse
        process Nothing _ = do return []
        j = unsafeMapIO id $ process  <$> facts inputs <*> bhInp <@ UI.click b
    outStp <- stepper "" (fmap show $ j)
    out <- UI.div # sink UI.text outStp
    (,pure Nothing) <$> UI.div # set children [pathInput,b,out]

buildList' i j = foldr (liftA2 (:)) i j
        -- where buildList = foldr (liftA2 (:))  (pure [])
fkattrsB inputs fks = buildList'   inputs fks

lookAttr inp attr = justError ("Error looking Attr: " <> show attr <> " " <> show inp) $ M.lookup attr  inp
lookKeyMap inp attr = justError ("Error looking KeyMap: " <> show attr <> " " <> show inp) $ M.lookup attr  inp


translateMonth :: Text -> Text
translateMonth v = foldr (\i -> (uncurry T.replace) i )  v transTable
              where transTable = [("out","oct"),("dez","dec"),("set","sep"),("ago","aug"),("fev","feb"),("abr","apr"),("mai","may")]


wappImport conn inf _ _ = do
  let chat@(Raw _ _ pk desc ifk attrs) = lookTable inf "chat"
  pathInput <- UI.input  -- # set UI.type_ "file"
  b <- UI.button # set UI.text "Import"
  bhInp <- stepper "" (UI.valueChange pathInput)
  v <- mapM (fkUITable conn inf (pure Nothing)  . fmap snd . fkCase (tableMap inf) False PathRoot) $ S.toList ifk
  let
      ninputs = allMaybes <$> (fkattrsB (pure mempty) (snd <$> v))
  output <- UI.div # set children (fst <$> v)
  let process (Just inp) path = do
        file <-  liftIO $ T.readFile path
        let result =  S.fromList $ M.fromList <$>  (fmap  parse $ filter (\(i,xs) -> isJust $ strptime "%d de %b %R" (T.unpack $ translateMonth i)) $   T.breakOn ("-") <$> T.split (=='\n') file)
            parse (d,t) =  (\(k,s)-> (fromJust $ M.lookup ("chat",k) (keyMap inf),s) ) <$>  [("chat_instant",STimestamp $ Finite $ fst $ fromJust $ strptime "%d de %b %R %Y" (T.unpack (translateMonth d) <> " 2014")),("chat_text",SText $ T.drop 2 c), ("speaker_contact",snd $ head speaker )  ,("target_contact",snd $ head target)]
              where (p,c) =  T.breakOn (":") t
                    name = T.unpack $ T.drop 2 p
                    Just (FKT speaker _ )= F.find (L.isInfixOf name . show ) inp
                    Just (FKT target _ )= F.find (not . L.isInfixOf name. show ) inp
            queryFilter [(k1,v1),(k2,v2)] = M.fromList $  fmap (fmap ( (\i->[i]) . Category . S.singleton . flip PK [].(\i->[i]) )) [(lookKeyMap (keyMap inf) ("chat","speaker_contact"),v1),(lookKeyMap (keyMap inf) ("chat","target_contact"),v2)]
        vp <- mapM (\speaker -> doQueryAttr conn inf (projectAllRec' (tableMap inf)) (queryFilter (traceShowId $ (\(FKT [i] _ )-> i ) <$> speaker))  pk) (L.permutations inp)
        let kk = S.fromList (fmap (M.fromList . filter ((`elem` ["speaker_contact","target_contact","chat_text","chat_instant"] ) . keyValue . fst ) . F.toList ) (traceShowId $ concat vp)) :: S.Set (Map Key Showable)
        adds <- traceShow ( show kk  <> "/n" <> show result) $ mapM (\kv -> (`catch` (\e -> return $ trace ( show (e :: SomeException)) Nothing )) $ fmap Just $ insertPK fromShowableList  conn  (M.toList kv) chat ) (S.toList $  result  `S.difference` kk)
        return result
      process Nothing  path = do return S.empty
      j = unsafeMapIO id $ process  <$> ninputs <*> bhInp <@ UI.click b
  outStp <- stepper "" (fmap show $ j)
  out <- UI.div # sink UI.text outStp
  inpOut <- UI.div # sink UI.text (show <$> ninputs)
  (,pure Nothing) <$> UI.div # set children [output,pathInput,b,out,inpOut]

queryAndamento2 conn inf  k  input = do
        b <- UI.button # set UI.text "Submit"  # sink UI.enabled (maybe False (\i -> not $ elem "aproval_date" ((keyValue . fst)<$>  filter (not . isEmptyShowable. snd )i) ) <$> facts input)
        tq <-  mapT (\case {Just input -> queryAndamento4 conn inf k input ; Nothing -> return Nothing}) (shortCutClick input (UI.click b))
        e <- UI.div # sink UI.text (fmap (maybe "" show ) $ facts $ tq)
        body <-UI.div # set children [b,e]
        return (body , pure Nothing)

tailEmpty [] = []
tailEmpty i  = tail i


queryCEP2 _ inf  _ inputs =
  let open inputs =
		let res = case  fmap (normalize .  snd) $ L.find ((== "owner_cep") . keyValue . fst) inputs of
			Just (SText cnpj) -> Just cnpj
			i -> Nothing
		in res
      addrs ="http://cep.correiocontrol.com.br/"
      element = do
        b <- UI.button # set UI.text "Submit"
	tq <-   mapT (fmap ( \i -> fmap ( M.filter (/="")) $ decode i )  ) (  maybe (return "{}") ( (`catch` (\e ->  return $ trace (show (e :: IOException )) "{}" ) ). simpleGetRequest  . traceShowId .  (\i-> addrs <> i <> ".json") ) . fmap T.unpack . join .  fmap open <$> (flip shortCutClick (UI.click b) ) inputs )
 	let
	    Just table2 = M.lookup "owner" (tableMap inf)
            translate "localidade" =  "owner_municipio"
            translate "cep" =  "owner_cep"
            translate "uf" =  "owner_uf"
            translate "bairro" =  "owner_bairro"
	    translate i = i
	    tkeys = fmap (fmap SText . M.mapKeys (fromJust . flip M.lookup (keyMap inf) . ("owner",) . translate))  <$> tq
        e <- UI.div  # sink UI.text ( show  <$> facts tq)
 	body <-UI.div # set children [b,e]
	return (body ,tkeys)
  in  element


queryCnpjReceita _ _ _ inputs =
    let open inputs = case  fmap (normalize .  snd) $ L.find ((== "cgc_cpf") . keyValue . fst) inputs of
                  Just (SText cnpj) -> Just cnpj
                  i -> Nothing
        addrs ="http://www.receita.fazenda.gov.br/pessoajuridica/cnpj/cnpjreva/Cnpjreva_Solicitacao2.asp"
        element = mkElement "iframe" # sink UI.src (maybe addrs ((addrs <>"?cnpj=") <>) . fmap T.unpack . join . fmap open <$> facts inputs) # set style [("width","100%"),("height","300px")]
    in (,pure Nothing ) <$> element



keySetToMap ks = M.fromList $  fmap (\(Key k _ _ _ t)-> (toStrict $ encodeUtf8 k,t))  (F.toList ks)

projectKey
  :: Connection
     -> InformationSchema ->
     (forall t . Traversable t => QueryT Identity (t KAttribute)
         -> S.Set Key -> IO [t (Key,Showable)])
projectKey conn inf q  = (\(j,(h,i)) -> fmap (fmap (zipWithTF (,) (fmap (\(Metric i)-> i) j))) . queryWith_ (fromShowableList j) conn . traceShowId . buildQuery $ i ) . projectAllKeys (pkMap inf ) (hashedGraph inf) q

projectTable
  :: Connection
     -> InformationSchema ->
     (forall t . Traversable t => QueryT Identity (t KAttribute)
         -> S.Set Key -> IO (t Key ,[t Showable]))
projectTable conn inf q  = (\(j,(h,i)) -> fmap (fmap (\(Metric k) -> k) j,)  . queryWith_ (fromShowableList j) conn . traceShowId . buildQuery $ i ) . projectAllKeys (pkMap inf ) (hashedGraph inf) q




projectKey'
  :: Connection
     -> InformationSchema ->
     (forall t . Traversable t => QueryT Identity (t KAttribute)
         -> S.Set Key -> IO [t (KAttribute ,Showable)])
projectKey' conn inf q  = (\(j,(h,i)) -> fmap (fmap (zipWithTF (,) j)) . queryWith_ (fromShowableList j) conn . traceShowId . buildQuery $ i ) . projectAllKeys (pkMap inf ) (hashedGraph inf) q



topSortTables tables = flattenSCCs $ stronglyConnComp item
  where item = fmap (\n@(Raw _ t k _ fk _ ) -> (n,k,fmap (\(Path _ _ end)-> end) (S.toList fk) )) tables



main :: IO ()
main = do
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
  -- preview $ cvLabeled (graphP )
--  preview $ cvLabeled (warshall graphP )
  startGUI defaultConfig setup
  print "Finish"

