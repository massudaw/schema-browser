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
import Debug.Trace
import Schema
import Gpx
import GHC.Int
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

import qualified Graphics.UI.Threepenny as UI
import Graphics.UI.Threepenny.Core hiding (delete)
import Data.Monoid hiding (Product(..))
import Data.Time.Parse

import System.IO.Unsafe
import Debug.Trace
import qualified Data.Foldable as F
import qualified Data.Text.Lazy as T
import Data.ByteString.Lazy(toStrict)
import Data.Text.Lazy.Encoding
import qualified Data.Text.Encoding as TE
import Data.Text.Lazy (Text)
import qualified Data.Set as S


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
  ::Connection
     -> [Plugins]
     -> InformationSchema
     -> [S.Set Key] -> Window -> UI ()
setup conn pg inf k w = void $ do
  return w # set title "Data Browser"
  span <- chooserKey  conn pg inf k
  getBody w #+ [element span]



attrUI'  tAttr plugItens i
  | isSerial (keyType i) = do
      l<- UI.span # set text (show i)
      e <- UI.span # sink text (maybe "" renderShowable <$> facts tAttr )
      paint l ( pure $ Just undefined)
      sp <- UI.li # set children [l,e]
      return (sp,liftA2 (,) (fmap (i,) <$> facts tAttr ) (pure (Just (i,SSerial Nothing))))
  | otherwise = do
      l<- UI.span # set text (show i)

      let tdi = traceShowId . forceDefaultType i <$> foldrTds justCase plugItens [tAttr]
          justCase i j@(Just _) = j
          justCase i Nothing = i
      inputUI <- UI.input # sink UI.value (facts tdi) # set UI.name (T.unpack $ keyValue i) # set UI.id_ (T.unpack $ keyValue i) # set UI.type_ "text"
      let pke = foldl1 (unionWith justCase ) [readType (textToPrim <$> keyType i) <$> UI.valueChange inputUI,rumors $ foldrTds justCase plugItens [tAttr]]
      pk <- stepper (defaultType i)  pke
      let pkt = tidings pk pke
          ei (Just a) = Just a
          ei Nothing = defaultType i
          edited = (\o j-> if (renderShowable <$> o) == (renderShowable <$> ei j) then Nothing else liftA2 (,) o j) <$> pkt <*> tAttr
          editedFlag (Just i) = "#" <> renderShowable i
          editedFlag Nothing = ""
      e <- UI.span # sink text (editedFlag . fmap snd <$> (facts edited))
      paint l pk
      sp <- UI.li # set children [l,inputUI,e]
      return (sp,liftA2 (,) (fmap(i,) . fmap fst <$> (facts edited) ) (fmap (i,) <$> pk))

liftJust l (Just i) (Just j) = Just (l i j)
liftJust l Nothing (Just j) = Nothing
liftJust l (Just j) Nothing  = Just j
liftJust l Nothing Nothing  = Nothing
modifyList box =  (\ ml me -> trace ("liftJust " <> show me <> " _ " <> show ml ) $  liftJust (\l e -> F.toList e <> filter (\(i,j)-> not  $ S.member i (S.fromList $ fmap fst (F.toList e))  )  l) me ml ) <$> box

justError e (Just i) = i
justError e  _ = error e


generateUI (k,v) =
  case keyType k of
       Primitive i -> UI.input # set UI.value (forceDefaultType k v)
       i -> UI.div

fkUI
  :: Connection
  -> InformationSchema
  -> Tidings (Maybe [(Key,Showable)])
  -> Tidings (Maybe (Map Key Showable))
  -> Tidings (Maybe (TB1 (Key ,Showable)))
  -> Path Key (SqlOperation Text)
  -> UI (Element,Behavior (Maybe [(Key, Showable)], Maybe [(Key, Showable)]))
fkUI conn inf oldItems plugItens  oldItems1 (Path ifk table o1 ) = mdo
      res <- fmap (fmap allKVRec ) $ liftIO $ projectKey conn inf (projectAllRec' (tableMap inf )) o1
      let
          (PK oL _)  = allPKRec subtableAttrs
          o = S.fromList oL
          subtable :: Table
          subtable = fromJust $  M.lookup o1 (pkMap inf )
          subtableAttrs =  allRec False (tableMap inf) subtable
          lookupFKS :: (Functor f ,Show (f (Maybe (Key,Showable))),F.Foldable f) => f Key -> Tidings (Maybe [(Key,Showable)]) -> Tidings (Maybe (f (Key,Showable)))
          lookupFKS ks initialMap = allMaybes <$> (\m -> fmap (\ki->  join $ fmap (fmap (ki,) . M.lookup ki) m) ks) <$> (fmap M.fromList <$> initialMap )
              where keys =  allAttrsRec (tableMap inf) subtable
          tdi :: Tidings (Maybe (KV  (Key,Showable)))
          tdi =  fmap (\a -> fmap normalize <$> allKVRec a ) <$> lookupFKS subtableAttrs oldItems
      l <- UI.span # set text (show $ S.toList o)
      box <- UI.listBox res2 tdi (pure (\v-> UI.span # set text (show $ (\(KV k _)-> snd <$> k) v)))
      let
          pkt :: Tidings (Maybe (PK (Key,Showable)))
          pkt = fmap (\(KV i _) -> fmap (fmap normalize) i) <$> UI.userSelection box
          ei :: [Key] -> Maybe [Showable] -> Maybe [Showable]
          ei i Nothing = allMaybes $ fmap defaultType i
          ei i d = d
          olds :: Tidings (Maybe [(Key,Showable)])
          olds =  lookupFKS (F.toList o) oldItems
          edited :: Tidings (Maybe [((Key,Showable),(Key,Showable))])
          edited = (\i j-> if (fmap (fmap snd) $ fmap pkKey i) == (fmap normalize <$> ei (S.toList o) (fmap (fmap snd) j)) then Nothing else liftA2 zip (fmap pkKey i) j) <$> pkt <*> olds
          editedListFlag (Just i) = "#" <> L.intercalate "," (fmap renderShowable i)
          editedListFlag Nothing = ""
          fksel = fmap pkKey <$>  facts pkt
      e <- UI.span # sink text (editedListFlag . fmap (fmap (snd .snd)) <$> facts edited)
      paint (getElement l) fksel
      chw <- checkedWidget
      (celem,tcrud,evs) <- crudUI conn inf subtable (fmap F.toList <$> UI.userSelection box ) plugItens oldItems1
      let eres = fmap (addToList  (S.toList o)  (maybeToList $ description subtable) ( ( allAttrsRec (tableMap inf ) subtable )) <$> ) evs
      res2  <-  accumTds (pure $ fmap (fmap (fmap normalize)) res) eres
      -- let res2 = foldTds (pure $ fmap (fmap (fmap normalize)) res) eres
      -- TODO: Implement recursive selection after insertion
      -- tdi2 <- addTs (pure Nothing) $ (\i-> editedMod (S.toList o)  (maybeToList $ description subtable)   <$> i) <$> evs
      element celem
        # sink UI.style (noneShow <$> (facts $ triding chw))
        # set style [("padding-left","10px")]
      fk <- UI.li # set  children [l, getElement box,e,getElement chw,celem]
      let bres = liftA2 (,) (fmap (fmap fst) <$> facts edited ) fksel -- (liftA2 (liftA2 mappend) fksel tcrud)
      return (fk,bres)

forceDefaultType k (Just i ) = renderShowable i
forceDefaultType k (Nothing) = ""

paint e b = element e # sink UI.style (greenRed . isJust <$> b)

data Plugins
  = Plugins
  { _name :: String
  ,_inputs :: (Table, S.Set Key)
  , _action :: Connection -> InformationSchema -> Plugins -> Tidings (Maybe [(Key,Showable)]) -> UI (Element,Tidings (Maybe (Map Key Showable)) )
  }
data  PollingPlugins = PollingPlugins
  { _pollingName :: String
  , _pollingInputs :: (Table, S.Set Key)
  , _pollingAction :: Connection -> InformationSchema -> PollingPlugins -> Tidings ([[(Key,Showable)]]) -> UI (Element,Tidings (Maybe (Map Key Showable)) )
  }

classifyKeys (table@(Raw s t pk desc fk allI),keys) = (S.intersection keys attrSet,S.intersection keys fkSet)
    where fkSet = S.unions $ fmap (\(Path ifk t o) ->  ifk)  (S.toList fk)
          attrSet = S.fromList $ filter (not. (`S.member` fkSet)) $ (S.toList pk <> S.toList allI)

attrSet pkm (Raw s t pk desc fk allI) =  pk <> allI <>  foldr mappend mempty (catMaybes $ pathTable <$> (F.toList fk) )
    where pathTable (Path o t e) = attrSet pkm <$> M.lookup e pkm

pollingUI conn inf p@(PollingPlugins n (table@(Raw s t pk desc fk allI),keys) a) oldItems = do
  let plug = a conn inf p
  ev <- plug oldItems
  headerP <- UI.div # set text n
  body <- UI.div  # set children ((headerP:) . pure $  fst ev :: [Element])
  return (body, snd ev)


pluginUI conn inf p@(Plugins n (table@(Raw s t pk desc fk allI),keys) a) oldItems = do
  let plug = a conn inf p
  ev <- plug oldItems
  headerP <- UI.div # set text n
  body <- UI.div  # set children ((headerP:) . pure $  fst ev :: [Element])
  return (body, snd ev)



crudUI
  :: Connection
     -> InformationSchema
     -> Table
     -> Tidings (Maybe [(Key,Showable)])
     -> Tidings (Maybe (Map Key Showable))
     -> Tidings (Maybe (TB1 (Key ,Showable)))
     -> UI (Element,Behavior (Maybe [(Key,Showable)]),[Event(Modification Key Showable)])
crudUI conn inf table@(Raw s t pk desc fk allI) oldItems pluginItems oldItems1 = do
  let
    initialMap :: Tidings (Maybe (Map Key Showable))
    initialMap = fmap (M.fromList ) <$> oldItems
    lookupAttrs :: Key -> Tidings (Maybe Showable)
    lookupAttrs k = join . fmap ( M.lookup k) <$> initialMap
  body <- UI.div
  let fkSet = S.unions $ fmap (\(Path ifk t o) ->  ifk)  (S.toList fk)
  attrs <- mapM (\i -> attrUI' (lookupAttrs i) (join . fmap (M.lookup i ) <$> pluginItems) i )  $ filter (not. (`S.member` fkSet)) $ (S.toList pk <> S.toList allI)
  fks <- mapM (\i@(Path ifk  _ o ) -> fkUI conn inf oldItems pluginItems  oldItems1 i ) (S.toList fk)
  let
    buildList' i j = foldr (liftA2 (:)) (fmap (fmap pure) <$> buildList i) j
        where buildList = foldr (liftA2 (:))  (pure [])
    fkattrsB = buildList'  (fmap snd .snd <$> attrs) (fmap snd .snd <$> fks)
    efkattrsB = buildList' (fmap fst . snd <$> attrs) (fmap fst . snd <$> fks)
  (panelItems,evsa)<- processPanel conn efkattrsB fkattrsB table oldItems
  crudHeader <- UI.div # set text (T.unpack t)
  element body
    # set children (crudHeader : (fst <$> attrs) <> (fst <$> fks) <> panelItems)
    # set style [("border","1px"),("border-color","gray"),("border-style","solid")]
  return (body,fmap concat . allMaybes <$> fkattrsB,evsa)

-- interpret collection operations for lists
addToList i j a (Insert m) =  (\i->  mappend (fmap ((\(k,v)-> (k,normalize $ v)))  <$> maybeToList i) ) (editedMod  i j a m )
addToList i j a (Delete m ) =  (\i->  concat . L.delete (fmap ((\(k,v)-> (k,normalize $ v)))  <$> maybeToList i)  . fmap pure ) (editedMod  i j a m )
addToList i j a (Edit m n ) =  addToList i j a (Insert  m) . addToList i j a (Delete n)

-- lookup pk from attribute list
editedMod :: Ord a => [a] -> [a] -> [a] ->  Maybe [(a,b)] -> Maybe (KV (a,b))
editedMod  i j a m=  join $ fmap (\mn-> liftA3 (\ik jk ak -> KV (PK ik jk ) ak) (look mn i) (look mn j) (look mn a)) m
  where look mn k = allMaybes $ fmap (\ki -> fmap (ki,) $  M.lookup ki (M.fromList mn) ) k

data TableModification
  = TableModification Table (Modification Key Showable)
  deriving(Eq,Show)

data Modification a b
  = Edit (Maybe [(a,b)]) (Maybe [(a,b)])
  | Insert (Maybe [(a,b)])
  | Delete (Maybe [(a,b)])
  deriving(Eq,Show)


processPanel
     :: Connection
     -> Behavior [Maybe [(Key, Showable)]]
     -> Behavior [Maybe [(Key, Showable)]]
     -> Table
     -> Tidings (Maybe [(Key, Showable)])
     -> UI ([Element],[Event (Modification Key Showable)])
processPanel conn efkattrsB fkattrsB table oldItems = do
  editB <- UI.button # sink UI.enabled (liftA2 (&&) (any isJust <$>  efkattrsB) (all isJust  <$> fkattrsB)) # set text "EDIT"
  deleteB <- UI.button  # sink UI.enabled (isJust <$> facts oldItems) # set text "DELETE"
  insertB <- UI.button  # sink UI.enabled (all isJust <$> fkattrsB) # set text "INSERT"
  let
      editAction isM kM = do
        let i = catMaybes isM
            k = fromJust kM
        res <- liftIO $ catch (Right <$> update conn (concat i) k table) (\e -> return $ Left (show $ traceShowId (e :: SomeException) ))
        let updated = concat $ catMaybes isM
        return $ fmap (const (Edit (fmap (mappend updated) (filter (\(k,_) -> not $ k `elem` (fmap fst updated)) <$> kM) ) kM)) res
      deleteAction k =  do
        res <- liftIO $ catch (Right <$> delete conn (fromJust k) table) (\e -> return $ Left (show $ traceShowId  (e :: SomeException) ))
        return $ const (Delete k ) <$> res
      insertAction i = do
          res <- catch (Right <$> insertPK fromShowableList conn (concat i) table) (\e -> return $ Left (show $ traceShowId (e :: SomeException) ))
          return $ (\v -> Insert $ Just $ (v <> (filter (not . isEmptyShowable . snd) $ filter (not . flip elem (fst <$> v) . fst) (concat i)))) <$> res

      evir, evdr,ever :: Event (Modification Key Showable)
      (evid,evir) = spMap $ (insertAction . catMaybes <$> fkattrsB) <@ (UI.click insertB)
      (evdd,evdr) = spMap $ (deleteAction <$> facts oldItems) <@ UI.click deleteB
      (eved,ever) = spMap $ (editAction  <$> efkattrsB <*> (facts oldItems) ) <@ UI.click editB
      spMap = split . unsafeMapIO id

  -- (evid,evir) <- split <$> shortCut (insertAction . catMaybes <$> fkattrsB)  (UI.click insertB)
  -- (evdd,evdr) <- split <$> shortCut (deleteAction <$> facts oldItems) (UI.click deleteB)
  -- (eved,ever) <- split <$> shortCut (editAction  <$> efkattrsB <*> (facts oldItems) ) (UI.click editB)
  -- stp <- stepper [] (unions [evid,evdd,eved])
  -- end <- UI.div # sink text (show <$> stp)
  return ([insertB,editB,deleteB],[evir,ever,evdr])


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
      | otherwise = fmap catMaybes $ mapM (\k-> fmap (fmap (fst k,)) . (`Control.Exception.catch` (\e-> flip const (e :: SomeException)  $ return Nothing ) ) . fmap Just . doQueryTable conn inf projectDescAll i.  fst $ k ) j
  bp <- joinT $ (query <$> ff <*> invItems)
  body <- UI.div # sink items (fmap (\k -> (\i-> UI.div # set items (UI.div # set text (showVertex $ fst k) : [tableElem  (F.toList $ fst i) $ fmap F.toList (snd i)])) . snd  $ k ) <$> facts bp)
  UI.div # set children [body]


chooserKey conn pg inf kitems  = do
  -- Base Button Set
  bset <- buttonSet kitems showVertex
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
    aggQuery i j ka k
      | S.null j = return []
      | otherwise = doQuery conn inf (aggAll  (pkMap inf) (S.toList j) ka)  i k

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


  -- Final Query (Saved Filter <> Filter Map Selected)
  -- vp <- joinT $ doQueryAttr conn inf (projectDescAllRec (tableMap inf)) <$> (M.unionWith mappend <$> filterT <*> triding ff) <*>  bBset
  vp <- fmap (fmap (fmap allKVRec)) $ joinT $ doQueryAttr conn inf (projectAllRec' (tableMap inf)) <$> (M.unionWith mappend <$> filterT <*> triding ff) <*>  bBset

  -- Final Query ListBox
  filterInp <- UI.input
  filterInpBh <- stepper "" (UI.valueChange filterInp)

  let filterInpT = tidings filterInpBh (UI.valueChange filterInp)

  itemList <- UI.listBox ((\i j-> filter (L.isInfixOf i . show ) (F.toList j)) <$> filterInpT <*> res2 ) (pure Nothing) (pure (\i -> line $ (show . kvKey  ) $ fmap snd i))
  let
    categoryT1 :: Tidings (Map Key [Filter])
    categoryT1 = M.fromListWith mappend <$> (filterMaybe (fmap (\(fkv,kv)-> (fkv,[Category (S.fromList kv)]))) <$> arg)
      where arg :: Tidings (Maybe [(Key, [PK Showable])])
            arg = (\i j -> fmap (\nj -> zipWith (,) nj (L.transpose j) ) i) <$> (fmap S.toList  . Just <$> bBset ) <*> (fmap invertPK  . maybeToList . fmap (\i -> snd <$> kvKey i )  <$> UI.userSelection itemList)

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
        xs -> foldr1 (liftA2 appendMKV)  xs
      appendMKV (Just i ) (Just l )  =  Just (mappend i l )
      appendMKV Nothing  l   =   l
      appendMKV l  Nothing   =   l

  let
     filterOptions = case M.keys <$> M.lookup key (hashedGraph inf) of
               Just l -> key : fmap S.singleton l
               Nothing -> [key]
     convertPK i = case fmap F.toList i of
        Nothing -> Just []
        i -> i
     subtable = fromJust $ M.lookup key (pkMap inf)
  (crud,_,evs) <- crudUI conn inf  subtable  ( convertPK <$>  UI.userSelection  itemList)  tdi2 (pure Nothing ) -- UI.userSelection itemList)
  let eres = fmap (addToList  (S.toList key)  (maybeToList $ description subtable ) (F.toList $   allAttrsRec (tableMap inf ) subtable    ) <$> ) evs
  res2 <- accumTds (fmap (fmap (fmap normalize)) <$> vp)   eres
  resPoll  <- mapM (\i -> pollingUI conn inf i (fmap F.toList <$> vp ) )   (filter (\(PollingPlugins n tb _ )-> S.isSubsetOf  (snd tb) (attrSet (pkMap inf) (fromJust $ M.lookup key (pkMap inf)))  )   [pollingAndamento inf ])
  polling <- UI.div # set children (fst <$> resPoll)
  insertDiv <- UI.div # set children [crud]
  filterSel <- UI.div # set children [getElement ff,getElement fkbox,getElement range, getElement filterItemBox]
  -- aggr <- UI.div # set children [getElement sel , count]
  tab <- tabbed  [("CRUD",insertDiv),("FILTER",filterSel){-,("AGGREGATE", aggr)-}, ("POLLING",polling),("PLUGIN",plugins),("SELECTED",selected)]
  itemSel <- UI.div # set children [filterInp]
  UI.div # set children ([itemSel,getElement itemList,tab] )



queryCnpjProject conn inf (Plugins n (table@(Raw s t pk desc fk allI),keys) a) oldItems= fmap (,pure Nothing ) $ do
  let
    initialMap :: Tidings (Maybe (Map Key Showable))
    initialMap = fmap M.fromList <$> oldItems
    lookupFKS :: [Key] -> Tidings (Maybe [(Key,Showable)])
    lookupFKS ks = allMaybes <$> ((\m ks -> fmap (\ki->  join $ fmap (fmap (ki,) . M.lookup ki) m) ks) <$> initialMap <*> pure ks)
    lookupAttrs :: Key -> Tidings (Maybe Showable)
    lookupAttrs k = join . fmap ( M.lookup k) <$> initialMap
  let fkSet = S.unions $ fmap (\(Path ifk t o) ->  ifk)  (S.toList fk)
  attrs <- mapM (\i-> attrUI' (lookupAttrs i ) (pure Nothing) i) $ filter (not. (`S.member` fkSet)) $ S.toList keys
  fks <- mapM (\i@(Path ifk _ _ ) -> fkUI conn inf oldItems (pure Nothing)  (pure Nothing) i ) (S.toList fk)
  let
    buildList' i j = foldr (liftA2 (:)) (fmap (fmap (\i-> [i])) <$> buildList i) j
        where buildList = foldr (liftA2 (:))  (pure [])
    fkattrsB = buildList'  (fmap snd .snd <$> attrs) (fmap snd .snd <$> fks)
    efkattrsB = buildList' (fmap fst . snd <$> attrs) (fmap fst . snd <$> fks)
  process <- UI.input # set UI.type_ "submit"
  mapM_ (\i -> element i # set UI.style [("display","none")]) $ (fst <$> attrs) <> (fst <$> fks)
  formP <- UI.form # set UI.target (T.unpack t) # set UI.method "post"# set UI.action ("http://siapi.bombeiros.go.gov.br/consulta/consulta_cnpj_cpf.php")
    # set children ( (fst <$> attrs) <> (fst <$> fks) <> [process]  )
  iframe <- mkElement "iframe" # set UI.name (T.unpack t) # set UI.id_ (T.unpack t) # set style [("width","100%"),("height","300px")]
  body <- UI.div  # set children [formP,iframe]
  return body

pluginOrcamento inf =
  let
    Just table2 = M.lookup "pricing" (tableMap inf)
    keys2 = catMaybes $ fmap (flip M.lookup (keyMap inf) . ("pricing",)) ["pricing_price"]
    pg2 = Plugins "Pricing Document" (table2,S.fromList keys2) renderProjectPricing
  in pg2

pluginCEP inf =
  let
    Just table2 = M.lookup "owner" (tableMap inf)
    keys2 = catMaybes $ fmap (flip M.lookup (keyMap inf) . ("owner",)) ["id_owner"]
    pg2 = Plugins "CEP Correios" (table2,S.fromList keys2) queryCEP2
  in pg2

pluginProtocolId inf =
  let
    Just table2 = M.lookup "fire_project" (tableMap inf)
    keys2 = catMaybes $ fmap (flip M.lookup (keyMap inf) . ("fire_project",)) ["protocolo","ano"]
    pg2 = Plugins "Protocolo Id" (table2,S.fromList keys2) queryProtocoloId
  in pg2

pluginAndamentoId inf =
  let
    Just table2 = M.lookup "fire_project" (tableMap inf)
    keys2 = catMaybes $ fmap (flip M.lookup (keyMap inf) . ("fire_project",)) ["id_bombeiro"]
    pg2 = Plugins "Andamento" (table2,S.fromList keys2) queryAndamento2
  in pg2

pollingAndamento inf =
  let
    Just table2 = M.lookup "fire_project" (tableMap inf)
    keys2 = catMaybes $ fmap (flip M.lookup (keyMap inf) . ("fire_project",)) ["id_bombeiro"]
    pg2 = PollingPlugins "AndamentoPoll" (table2,S.fromList keys2) queryAndamento3
  in pg2



simpleGetRequest =  fmap BSL.pack . join . fmap HTTP.getResponseBody . HTTP.simpleHTTP . HTTP.getRequest


shortCutClick  t i = tidings (facts t) (facts t <@ i)

strAttr :: String -> WriteAttr Element String
strAttr name = mkWriteAttr (set' (attr name))

solicitationPlugin inf =
  let
    Just table2 = M.lookup "fire_project" (tableMap inf)
    keys2 = catMaybes $ fmap (flip M.lookup (keyMap inf) . ("fire_project",)) ["id_project"]
    pg2 = Plugins "Solicitacao Projeto Bombeiro" (table2,S.fromList keys2) solicitationForm
  in pg2

renderUrl' args url = address
  where
    kv i = catMaybes $ (\k ->   (\inp ->  fmap (snd k,) . M.lookup (fst k) . M.fromList $ fmap (\(k,v)-> (keyValue k,v)) inp ) $  i ) <$> args
    renderKv = HTTP.urlEncodeVars . fmap (\(k,v)-> (k , show v))
    address i =  url <> "?"  <> renderKv (kv i)

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


queryAndamento3 conn inf  k  input = do
        b <- UI.button # set UI.text "Submit" -- # sink UI.enabled (maybe False (\i -> not $ elem "aproval_date" ((keyValue . fst)<$>  filter (not . isEmptyShowable. snd )i) ) <$> facts input)
        bh <-stepper [] (rumors input)
        tq <-  mapT (mapM (\inputs-> fmap (snd $ fromJust .L.find ((== "project_description") . keyValue . fst )$ inputs,) <$> (  runMaybeT $ do
                MaybeT $ return $ if elem "aproval_date" ((keyValue . fst)<$>  filter (not . isEmptyShowable. snd ) inputs ) then Nothing else Just undefined
                let tableName = "fire_project"
                    addrs ="http://siapi.bombeiros.go.gov.br/consulta/consulta_protocolo.php"
                    translate = [("protocolo" , "protocolo"),("ano","ano")]
                    addrs_a ="http://siapi.bombeiros.go.gov.br/consulta/consulta_andamento.php"
                    translate_a = [("id_bombeiro" , "id")]
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
                tq <-  getRequest . traceShowId . (renderUrl translate_a addrs_a)  $  lkeys
                let
                  tq2 =  T.unpack $  decodeLatin1 tq
                  convertAndamento [da,desc] = [("andamento_date",SDate . Finite . localDay . fst . justError "wrong date parse" $  strptime "%d/%m/%y" da  ),("andamento_description",SText (T.filter (not . (`elem` "\n\r\t")) $ T.pack  desc))]
                  convertAndamento i = error $ "convertAndamento:  " <> show i
                  tkeys v =  M.mapKeys (fromJust . flip M.lookup (keyMap inf) . ("andamento" :: Text,)  )  v
                  prepareArgs  = fmap ( tkeys . M.fromList . convertAndamento ) .  tailEmpty . concat
                  lookInput = fromJust .L.find ((== "id_project") . keyValue . fst)
                  insertAndamento :: String -> MaybeT IO [Maybe TableModification]
                  insertAndamento i  =  C.lift $ do
                      html <- readHtml $ i
                      let
                          args :: [Map Key Showable]
                          args = fmap ( fmap normalize . uncurry M.insert  (lookInput inputs )) $ prepareArgs html
                      mod <- case filter ( maybe False (\(SText t) -> T.isInfixOf "Aprovado" t ) .  M.lookup "andamento_description" . M.mapKeys keyValue )  args of
                          [i] -> updateMod  conn [(fromJust . flip M.lookup (keyMap inf) $ (tableName,"aproval_date") , fromJust $ M.lookup "andamento_date"  $ M.mapKeys keyValue i)] inputs (fromJust $ M.lookup  tableName (tableMap inf) )
                          i -> return Nothing
                      vp <- doQueryAttr conn inf (projectAllRec' (tableMap inf)) (uncurry M.singleton $  fmap ( (\i->[i]) . Category . S.singleton . flip PK [].(\i->[i]) ) (lookInput inputs ) ) ( (\(Raw _ _ pk _ _ _ ) -> pk ) $fromJust $  M.lookup  "andamento" (tableMap inf ))
                      let kk = S.mapMonotonic (fmap normalize) $ S.fromList (fmap (M.fromList . filter ((`elem` ["id_project","andamento_description","andamento_date"] ) . keyValue . fst ) . F.toList ) vp) :: S.Set (Map Key Showable)
                      adds <- mapM (\kv -> (`catch` (\e -> return $ trace ( show (e :: SqlError)) Nothing )) $ insertMod conn  (M.toList kv) (fromJust $ M.lookup  "andamento" (tableMap inf) )) (S.toList $ (S.fromList args ) `S.difference` kk)
                      return $ mod : adds
                v <- insertAndamento tq2
                let mods =catMaybes $  modB : v
                mapM (C.lift . logTableModification inf conn) mods
                return mods )))  (tidings bh (facts input <@ (UI.click b)))
        e <- UI.div # sink UI.text (show . catMaybes <$> facts  tq  )
        body <-UI.div # set children [b,e]
        return (body , pure Nothing)

updateMod conn kv old table = do
  update conn  kv old table
  return $ Just $ TableModification table (Edit ( Just kv ) (Just old) )

insertMod conn kv table = do
  insert conn  kv table
  return $ Just $ TableModification table (Insert $ Just kv)

logTableModification inf conn (TableModification table i) = do
  let look k = fromJust $ M.lookup ("modification_table",k) (keyMap inf)
  insertPK fromShowableList conn [(look "table_name" ,SText $ tableName  table) , (look "modification_data", SText $ T.pack $ show i)] (fromJust $ M.lookup ("modification_table") (tableMap inf))


queryAndamento2 conn inf  k  input = do
        b <- UI.button # set UI.text "Submit" # sink UI.enabled (maybe False (\i -> not $ elem "aproval_date" ((keyValue . fst)<$>  filter (not . isEmptyShowable. snd )i) ) <$> facts input)

        tq <-  mapT (\inputs-> ( runMaybeT $ do
                -- MaybeT $ return $ (\i -> if not $ elem "aproval_date" ((keyValue . fst)<$>  filter (not . isEmptyShowable. snd ) i) then Nothing else Just undefined ) <$> inputs
                let tableName = "fire_project"
                    addrs ="http://siapi.bombeiros.go.gov.br/consulta/consulta_protocolo.php"
                    translate = [("protocolo" , "protocolo"),("ano","ano")]
                    addrs_a ="http://siapi.bombeiros.go.gov.br/consulta/consulta_andamento.php"
                    translate_a = [("id_bombeiro" , "id")]
                url <- MaybeT $ return $ renderUrlM translate addrs  $ filter (not . isEmptyShowable. snd )  <$>inputs
                lq <-  getRequest . traceShowId $ url
                let
                  lq2 =  Just . maybe M.empty (uncurry M.singleton . ("id_bombeiro",)) . fmap SNumeric . readMaybe.  fst .  break (=='&') . concat . tail .  splitL ("php?id=")  .traceShowId . T.unpack . decodeLatin1  $  lq
                  lkeys = fmap ( M.toList . M.mapKeys (fromJust . flip M.lookup (keyMap inf) . (tableName,)  ))  $ lq2
                tq <-  getRequest . traceShowId . (renderUrl translate_a addrs_a)  $  lkeys
                let
                  tq2 =  T.unpack $  decodeLatin1 tq
                  convertAndamento [da,desc] = [("andamento_date",SDate . Finite . localDay . fst . justError "wrong date parse" $  strptime "%d/%m/%y" da  ),("andamento_description",SText (T.pack desc))]
                  convertAndamento i = error $ "convertAndamento:  " <> show i
                  tkeys v =  M.mapKeys (fromJust . flip M.lookup (keyMap inf) . ("andamento" :: Text,)  )  v
                  prepareArgs  = fmap ( tkeys . M.fromList . convertAndamento ) .  tailEmpty . concat
                  lookInput = fromJust . L.find ((== "id_project") . keyValue . fst)
                  insertAndamento :: String -> Maybe [(Key,Showable)] -> MaybeT IO ()
                  insertAndamento i (Just j)  =  C.lift $ do
                      html <- readHtml $ traceShowId i
                      let args = fmap ( uncurry M.insert  (lookInput j)) $ prepareArgs html
                          isApproved = case filter ( maybe False (\(SText t) -> T.isInfixOf "Aprovado" t ) .  M.lookup "andamento_description" . M.mapKeys keyValue ) args of
                                            [] -> return ()
                                            [i] -> update conn [(fromJust . flip M.lookup (keyMap inf) $ (tableName,"aproval_date") , fromJust $ M.lookup "andamento_date"  $ M.mapKeys keyValue i)] (fromJust inputs)  (fromJust $ M.lookup  tableName (tableMap inf) ) >> return ()
                                            i -> return ()
                      isApproved
                      mapM_ (\kv -> (`catch` (\e -> return $ trace ( show (e :: SqlError)) undefined )) $ insert conn  (M.toList kv) (fromJust $ M.lookup  "andamento" (tableMap inf) )) args
                  insertAndamento i Nothing  =  return ()
                insertAndamento tq2 inputs )      ) (shortCutClick input (UI.click b))
        e <- UI.div # sink UI.text (fmap show $ facts $ tq)
        body <-UI.div # set children [b,e]
        return (body , pure Nothing)

tailEmpty [] = []
tailEmpty i  = tail i

queryProtocoloId _ inf  _ inputs =
  let
      element = do
        b <- UI.button # set UI.text "Submit"
        tkeys <-  mapT (\ip -> runMaybeT  $ do
                  let
                    tableName = "fire_project"
                    addrs ="http://siapi.bombeiros.go.gov.br/consulta/consulta_protocolo.php"
                    translate = [("protocolo" , "protocolo"),("ano","ano")]
                  url <- MaybeT $ return $ renderUrlM translate addrs  $ filter (not . isEmptyShowable. snd ) <$> ip
                  lq <-  getRequest . traceShowId $ url
                  let
                    decode = T.unpack . decodeLatin1
                    parse =  fst .  break (=='&') . concat . tailEmpty .  splitL ("php?id=")
                    convert  =  (uncurry M.singleton <$>) . join . lkeys . ("id_bombeiro",)
                    lkeys (k,v) = (\kf -> (kf,) <$> (readType (textToPrim <$> keyType kf) v) ) <$> M.lookup (tableName,k) (keyMap inf)
                  MaybeT . return . convert . parse . decode $ lq)
                      (shortCutClick inputs (UI.click b))
        body <-UI.div # set children [b]
        return (body , tkeys)
  in  element


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
  let open inputs =
		let res = case  fmap (normalize .  snd) $ L.find ((== "cgc_cpf") . keyValue . fst) inputs of
			Just (SText cnpj) -> Just cnpj
			i -> Nothing
		in res
      addrs ="http://www.receita.fazenda.gov.br/pessoajuridica/cnpj/cnpjreva/Cnpjreva_Solicitacao2.asp"
      element = mkElement "iframe" # sink UI.src (maybe addrs ((addrs <>"?cnpj=") <>) . fmap T.unpack . join . fmap open <$> facts inputs) # set style [("width","100%"),("height","300px")]
  in (,pure Nothing ) <$> element



keySetToMap ks = M.fromList $  fmap (\(Key k _ _ t)-> (toStrict $ encodeUtf8 k,t))  (F.toList ks)

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



zipWithTF g t f = snd (mapAccumL map_one (F.toList f) t)
  where map_one (x:xs) y = (xs, g y x)

topSortTables tables = flattenSCCs $ stronglyConnComp item
  where item = fmap (\n@(Raw _ t k _ fk _ ) -> (n,k,fmap (\(Path _ _ end)-> end) (S.toList fk) )) tables

fileKey = do
  i <- newUnique
  return $ Key "file" (Just "arquivo") i (Primitive "character varying")

pluginBombeiro :: InformationSchema -> Plugins
pluginBombeiro inf = pg1
  where
    Just table1 = M.lookup "fire_project" (tableMap inf)
    keys1 = catMaybes $ fmap (flip M.lookup (keyMap inf) . ("fire_project",)) ["id_owner","ano","protocolo"]
    pg1 = Plugins "ProjetoBombeiro" (table1,S.fromList (keys1)) queryCnpjProject

pluginCnpjReceita inf = pg2
  where
    Just table2 = M.lookup "owner" (tableMap inf)
    keys2 = catMaybes $ fmap (flip M.lookup (keyMap inf) . ("owner",)) ["id_owner"]
    pg2 = Plugins "CnpjReceita" (table2,S.fromList keys2) queryCnpjReceita


main :: IO ()
main = do
  --let schema = "public"
  --conn <- connectPostgreSQL "user=postgres password=queijo dbname=usda"
  let schemaN = "incendio"
  conn <- connectPostgreSQL "user=postgres dbname=incendio"
  --conn <- connectPostgreSQL "user=postgres password=queijo dbname=finance"
  inf@(k,baseTables,_,schema,invSchema,graphP) <- keyTables conn  schemaN
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
  {-let
    Just table = M.lookup "run" (tableMap inf)
    keys = catMaybes $ fmap (flip M.lookup (keyMap inf) . ("run",)) ["distance","id_shoes","id_person","id_place"]
    pg = Plugins (table,S.fromList (fkey : keys)) execKey
  fkey <- fileKey-}
  startGUI defaultConfig (setup conn  [pluginAndamentoId inf , pluginBombeiro inf ,pluginCnpjReceita inf ,pluginCEP inf,{-solicitationPlugin inf,-} pluginOrcamento inf,pluginProtocolId inf] inf (M.keys baseTables))
  print "Finish"

