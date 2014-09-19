{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE FlexibleInstances,RankNTypes,NoMonomorphismRestriction,UndecidableInstances,FlexibleContexts,OverloadedStrings ,TupleSections, ExistentialQuantification #-}

import Query
import Widgets
import Debug.Trace
import Schema
import Postgresql
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
import Data.Traversable (Traversable,traverse)
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

import qualified Graphics.UI.Threepenny as UI
import Graphics.UI.Threepenny.Core hiding (delete)
import Data.Monoid
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

type QueryCursor t =(t KAttribute, (HashSchema Key Table, Table))

setup
  ::Connection ->
     (forall t. Traversable t => (QueryCursor t -> IO [t Showable],
         QueryT Identity (t KAttribute)
         -> S.Set Key -> QueryCursor t ))
     -> InformationSchema
     -> [S.Set Key] -> Window -> UI ()
setup conn action inf k w = void $ do
  return w # set title "Data Browser"
  span <- chooseKey  conn action inf k
  getBody w #+ [element span]


allMaybes i = case all isJust i of
        True -> Just $ catMaybes i
        False -> Nothing
        {-
fileUpload
  :: Connection
     -> S.Set Key
     -> (t, Map (S.Set Key) Table, t2)
     -> ProjAction -> Table
     -> Tidings (Maybe [Showable])
     -> UI Element
fileUpload conn other tmap c@(proj,action) table@(Raw s t pk desc fk allI) initial = do
  let
    oldItems :: Tidings (Maybe [(Key,Showable)])
    oldItems = fmap (zip (S.toList $ pk <> allI)) <$> initial
    initialMap :: Tidings (Maybe (Map Key Showable))
    initialMap = fmap M.fromList <$> oldItems
    lookupFKS :: [Key] -> Tidings (Maybe [Showable])
    lookupFKS ks = allMaybes <$> ( (\m ks -> fmap (\ki->  join $ fmap (M.lookup ki) m) ks) <$> initialMap <*> pure ks)
    lookupAttrs :: Key -> Tidings (Maybe Showable)
    lookupAttrs k = join .fmap ( M.lookup k) <$> initialMap
    forceDefaultType k (Just i ) = renderShowable i
    forceDefaultType k (Nothing) = ""
  body <- UI.div
  let fkSet = S.unions $ fmap (\(Path o t ifk) ->  ifk)  (S.toList fk)
      paint e b = element e # sink UI.style (greenRed . isJust <$> b)
  attrs <- mapM (\i-> do
      l<- UI.span # set text (show i)
      let tdi = forceDefaultType i <$> lookupAttrs i
      m<- UI.input # sink UI.value (facts tdi)
      let pke = fmap (readType (textToPrim <$> keyType i)) $ unionWith const (UI.valueChange m) (rumors tdi)
      pk <- stepper (defaultType i)  pke
      let pkt = tidings pk pke
          ei (Just a) = Just a
          ei Nothing = defaultType i
          edited = (\o j-> if (renderShowable <$> o) == (renderShowable <$> (ei j)) then Nothing else liftA2 (,) o j) <$> pkt <*> lookupAttrs i
          editedFlag (Just i) = "#" <> renderShowable i
          editedFlag Nothing = ""
      e <- UI.span # sink text (editedFlag . fmap snd <$> (facts edited))
      paint l pk
      sp <- UI.li # set children [l,m,e]
      return (sp,liftA2 (,) (fmap(i,) . fmap fst <$> (facts edited) ) (fmap (i,) <$> pk))) $ filter (not. (`S.member` (fkSet <> other) )) $ S.toList (pk <> allI)
  fks <- mapM (\(Path o t ifk) -> do
      res <-  liftIO $ proj $ action projectDesc ifk
      let tdi = fmap (\i-> PK  i [] ) <$> lookupFKS ( S.toList ifk)
      box <- UI.listBox (pure res) tdi (pure (\v-> UI.span # set text (show v)))
      l<- UI.span # set text (show $ S.toList ifk)
      let
          pkt :: Tidings (Maybe (PK Showable))
          pkt = UI.userSelection box
          ei :: [Key] -> Maybe [Showable] -> Maybe [Showable]
          ei i Nothing = allMaybes $ fmap defaultType i
          ei i d = d
          olds :: Tidings (Maybe [Showable])
          olds = allMaybes <$> (foldr (liftA2 (:)) (pure []) $ fmap lookupAttrs (S.toList ifk))
          edited :: Tidings (Maybe [(Showable,Showable)])
          edited = (\k o j-> if (fmap pkKey o) == ei k j then Nothing else liftA2 zip (fmap pkKey o) j) <$> pure (S.toList ifk) <*> pkt <*> olds
          editedListFlag (Just i) = "#" <> L.intercalate "," (fmap renderShowable i)
          editedListFlag Nothing = ""
      e <- UI.span # sink text (editedListFlag . fmap (fmap snd) <$> facts edited)
      let fksel = fmap pkKey <$>  facts pkt
      paint (getElement l) fksel
      chw <- checkedWidget
      let
        -- Find when there is selection and the expand is checked
        findMaybe (Just i) True = Just <$> findQ c projectAll ifk i
        findMaybe _ _ = return Nothing
      exT <- joinT $ findMaybe <$> pkt <*> triding chw
      (celem ,tcelem) <- crudUI conn tmap c (fromJust $ M.lookup ifk (pkMap tmap)) exT
      element celem # sink UI.style (noneShow <$> (facts $ triding chw))
      fk <- UI.li # set  children [l, getElement box,e,getElement chw,celem]
      let bres = liftA2 (,) (fmap (zip (S.toList ifk)). fmap (fmap fst) <$> facts edited ) (fmap (zip (S.toList ifk)) <$> fksel)
      return (fk,bres)) $ filter (not. (`S.isSubsetOf` other ) . (\(Path _ _ ifk) -> ifk) ) $ (S.toList fk)
  let
    buildList' i j = foldr (liftA2 (:)) (fmap (fmap (\i-> [i])) <$> buildList i) j
        where buildList = foldr (liftA2 (:))  (pure [])
    fkattrsB = buildList'  (fmap snd .snd <$> attrs) (fmap snd .snd <$> fks)
    efkattrsB = buildList' (fmap fst . snd <$> attrs) (fmap fst . snd <$> fks)
  panelItems <- processPanel conn efkattrsB fkattrsB table oldItems
  crudHeader <- UI.div # set text "CRUD"
  element body # set children (crudHeader : (fst <$> attrs) <> (fst <$> fks) <> panelItems)
  return body
-}

attrUI  lookupAttrs i
  | isSerial (keyType i) =do
      l<- UI.span # set text (show i)
      e <- UI.span # sink text (maybe "" renderShowable <$> (facts (lookupAttrs i)))
      paint l ( pure $ Just undefined)
      sp <- UI.li # set children [l,e]
      return (sp,liftA2 (,) (fmap(i,) <$> (facts (lookupAttrs i)) ) (fmap (i,) <$> pure (Just $ SSerial Nothing)))
  | otherwise = do
      l<- UI.span # set text (show i)
      let tdi = forceDefaultType i <$> lookupAttrs i
      m<- UI.input # sink UI.value (facts tdi)
      let pke = fmap (readType (textToPrim <$> keyType i)) $ unionWith const (UI.valueChange m) (rumors tdi)
      pk <- stepper (defaultType i)  pke
      let pkt = tidings pk pke
          ei (Just a) = Just a
          ei Nothing = defaultType i
          edited = (\o j-> if (renderShowable <$> o) == (renderShowable <$> (ei j)) then Nothing else liftA2 (,) o j) <$> pkt <*> lookupAttrs i
          editedFlag (Just i) = "#" <> renderShowable i
          editedFlag Nothing = ""
      e <- UI.span # sink text (editedFlag . fmap snd <$> (facts edited))
      paint l pk
      sp <- UI.li # set children [l,m,e]
      return (sp,liftA2 (,) (fmap(i,) . fmap fst <$> (facts edited) ) (fmap (i,) <$> pk))

{-
fkUI conn tmap c@(proj,action) lookupAttrs lookupFKS (Path ifk t o) = do
      res <-  liftIO $ proj $ action projectDesc ifk
      let tdi =  fmap (\i-> PK  i [] ) <$> lookupFKS (S.toList ifk)
      box <- UI.listBox (fmap (fmap (fromJust.normalize)) <$> pure res) tdi (pure (\v-> UI.span # set text (show $ traceShowId v)))
      l<- UI.span # set text (show $ S.toList ifk)
      let
          pkt :: Tidings (Maybe (PK Showable))
          pkt = UI.userSelection box
          ei :: [Key] -> Maybe [Showable] -> Maybe [Showable]
          ei i Nothing = allMaybes $ fmap defaultType i
          ei i d = d
          olds :: Tidings (Maybe [Showable])
          olds = allMaybes <$> (foldr (liftA2 (:)) (pure []) $ fmap lookupAttrs (S.toList ifk))
          edited :: Tidings (Maybe [(Showable,Showable)])
          edited = (\k o j-> if (fmap pkKey o) == ei k j then Nothing else liftA2 zip (fmap pkKey o) j) <$> pure (S.toList ifk) <*> pkt <*> olds
          editedListFlag (Just i) = "#" <> L.intercalate "," (fmap renderShowable i)
          editedListFlag Nothing = ""
      e <- UI.span # sink text (editedListFlag . fmap (fmap snd) <$> facts edited)
      let fksel = fmap pkKey <$>  facts pkt
      paint (getElement l) fksel
      chw <- checkedWidget
      let
        -- Find when there is selection and the expand is checked
        findMaybe (Just i) True = Just <$> findQ c projectAll ifk i
        findMaybe _ _ = return Nothing
      exT <- joinT $ findMaybe <$> pkt <*> triding chw
      (celem,tcrud) <- crudUI conn tmap c (fromJust $ M.lookup ifk (pkMap tmap)) exT
      element celem # sink UI.style (noneShow <$> (facts $ triding chw))
      fk <- UI.li # set  children [l, getElement box,e,getElement chw,celem]
      let bres = liftA2 (,) (fmap (zip (S.toList ifk)). fmap (fmap fst) <$> facts edited ) (fmap (zip (S.toList ifk)) <$> fksel)
      return (fk,bres)
-}

forceDefaultType k (Just i ) = renderShowable i
forceDefaultType k (Nothing) = ""

paint e b = element e # sink UI.style (greenRed . isJust <$> b)

crudUI
  :: Connection
     -> (t, Map (S.Set Key) Table, t2)
     -> ProjAction -> Table
     -> Tidings (Maybe [Showable])
     -> UI (Element,Behavior (Maybe [(Key,Showable)]),[Event(Modification Key Showable)])
crudUI conn tmap c@(proj,action) table@(Raw s t pk desc fk allI) initial = do
  let
    oldItems :: Tidings (Maybe [(Key,Showable)])
    oldItems = fmap (zip (S.toList $ pk <> allI)) <$> initial
    initialMap :: Tidings (Maybe (Map Key Showable))
    initialMap = fmap M.fromList <$> oldItems
    lookupFKS :: [Key] -> Tidings (Maybe [Showable])
    lookupFKS ks = allMaybes <$> ((\m ks -> fmap (\ki->  join $ fmap (M.lookup ki) m) ks) <$> initialMap <*> pure ks)
    lookupAttrs :: Key -> Tidings (Maybe Showable)
    lookupAttrs k = join . fmap (M.lookup k) <$> initialMap
  body <- UI.div
  let fkSet = S.unions $ fmap (\(Path ifk t o) ->  ifk)  (S.toList fk)
  attrs <- mapM (attrUI lookupAttrs) $ filter (not. (`S.member` fkSet)) $ S.toList (pk <> allI)
  fks <- mapM (\(Path ifk t o) -> mdo
      l <- UI.span # set text (show $ S.toList ifk)
      let
          tdi =  fmap (\i-> PK  i [] ) <$> lookupFKS (S.toList ifk)
      box <- UI.listBox res2 tdi (pure (\v-> UI.span # set text (show v)))
      let
          pkt :: Tidings (Maybe (PK Showable))
          pkt = UI.userSelection box
          ei :: [Key] -> Maybe [Showable] -> Maybe [Showable]
          ei i Nothing = allMaybes $ fmap defaultType i
          ei i d = d
          olds :: Tidings (Maybe [Showable])
          olds = allMaybes <$> (foldr (liftA2 (:)) (pure []) $ fmap lookupAttrs (S.toList ifk))
          edited :: Tidings (Maybe [(Showable,Showable)])
          edited = (\k o j-> if (fmap pkKey o) == ei k j then Nothing else liftA2 zip (fmap pkKey o) j) <$> pure (S.toList ifk) <*> pkt <*> olds
          editedListFlag (Just i) = "#" <> L.intercalate "," (fmap renderShowable i)
          editedListFlag Nothing = ""
          fksel = fmap pkKey <$>  facts pkt
      e <- UI.span # sink text (editedListFlag . fmap (fmap snd) <$> facts edited)
      paint (getElement l) fksel
      chw <- checkedWidget
      let
        -- Find when there is selection and the expand is checked
        findMaybe (Just i) True = Just <$> findQ c projectAll ifk i
        findMaybe _ _ = return Nothing
      exT <- joinT $ findMaybe <$> pkt <*> triding chw
      let subtable = fromJust $ M.lookup ifk (pkMap tmap)
      (celem,tcrud,evs) <- crudUI conn tmap c subtable exT
      let eres = fmap (addToList  (S.toList o)  (maybeToList $ description subtable) <$> ) evs
      res <-  liftIO $ proj $ action projectDesc ifk
      res2 <- accumTs (fmap (fromJust.normalize) <$> res) eres
      -- TODO: Implement recursive selection after insertion
      -- tdi2 <- addTs (pure Nothing) $ (\i-> editedMod (S.toList o)  (maybeToList $ description subtable)   <$> i) <$> evs
      element celem # sink UI.style (noneShow <$> (facts $ triding chw))
      fk <- UI.li # set  children [l, getElement box,e,getElement chw,celem]
      let bres = liftA2 (,) (fmap (zip (S.toList ifk)). fmap (fmap fst) <$> facts edited ) (fmap (zip (S.toList ifk)) <$> fksel)
      return (fk,bres)) (S.toList fk)
  let
    buildList' i j = foldr (liftA2 (:)) (fmap (fmap (\i-> [i])) <$> buildList i) j
        where buildList = foldr (liftA2 (:))  (pure [])
    fkattrsB = buildList'  (fmap snd .snd <$> attrs) (fmap snd .snd <$> fks)
    efkattrsB = buildList' (fmap fst . snd <$> attrs) (fmap fst . snd <$> fks)
  (panelItems,evsa)<- processPanel conn efkattrsB fkattrsB table oldItems
  crudHeader <- UI.div # set text "CRUD"
  element body # set children (crudHeader : (fst <$> attrs) <> (fst <$> fks) <> panelItems)
  return (body,fmap concat . allMaybes <$> fkattrsB,evsa)

addToList i j  e@(Insert _) =  (\i-> concat . ((fmap (fromJust.normalize)  <$> maybeToList i):) . fmap pure) (editedMod  i j e )
addToList i j  e@(Delete m ) =  (\i->  traceShowId . concat . L.delete (traceShowId $ fmap (fromJust.normalize)  <$> maybeToList i)  . fmap pure .traceShowId ) (editedMod  i j e )
addToList i j  e@(Edit m n ) =  addToList i j (Insert m) . addToList i j (Delete n)

editedMod  i j (Delete m)=  join $ fmap (\mn-> liftA2 PK (look mn (traceShowId i)) (look mn (traceShowId j))) m
  where look mn k = allMaybes $ traceShowId $ fmap (flip M.lookup (M.fromList mn) ) k
editedMod  i j (Insert m)=  join $ fmap (\mn-> liftA2 PK (look mn (traceShowId i)) (look mn (traceShowId j))) m
  where look mn k = allMaybes $ traceShowId $ fmap (flip M.lookup (M.fromList mn) ) k

clickTiding :: Behavior a -> Event b -> Tidings a
clickTiding b e =  tidings b ev
  where ev = b <@ e


data Modification a b
  = Edit (Maybe [(a,b)]) (Maybe [(a,b)])
  | Insert (Maybe [(a,b)])
  | Delete (Maybe [(a,b)])

processPanel
     :: Connection
     -> Behavior [Maybe [(Key, Showable)]]
     -> Behavior [Maybe [(Key, Showable)]]
     -> Table
     -> Tidings (Maybe [(Key, Showable)])
     -> UI ([Element],[Event (Modification Key Showable)])
processPanel conn efkattrsB fkattrsB table oldItems = do
  editB <- UI.button # sink UI.enabled (liftA2 (&&) (fmap (any isJust)  (efkattrsB)) (fmap (all isJust)  (fkattrsB))) # set text "EDIT"
  end <- UI.div
  on UI.click editB $ const $ do
    i <- catMaybes <$> currentValue efkattrsB
    k <- fromJust <$> currentValue (facts oldItems)
    res <- liftIO $ catch (Right <$> update conn (concat i) k table) (\e -> return $ Left (show (e :: SqlError) ))
    case res of
      Right _ -> return ()
      Left v -> element end # set text v >> return ()
  deleteB <- UI.button  # sink UI.enabled (isJust <$> facts oldItems) # set text "DELETE"
  on UI.click deleteB $ const $ do
    k <- fromJust <$> currentValue (facts oldItems)
    res <- liftIO $ catch (Right <$> delete conn k table) (\e -> return $ Left (show (e :: SqlError) ))
    case res of
      Right _ -> return ()
      Left v -> element end # set text v >> return ()
  insertB <- UI.button  # sink UI.enabled (all isJust <$> fkattrsB) # set text "INSERT"
  let
      insertAction k = do
        case allMaybes k of
          Just i ->  do
            res <- catch (Right <$> insertPK fromShowableList conn (traceShowId $ concat i) table) (\e -> return $ Left (show (e :: SqlError) ))
            case res of
              Right v -> return (traceShowId (v <> filter (not . flip elem (fst <$> v) . fst) (concat i)))
              Left v -> return (traceShow v []) --element end # set text v >> return []
          Nothing -> return []
      evi :: Event ([(Key,Showable)])
      evi = unsafeMapIO id $ (insertAction <$> fkattrsB) <@ UI.click insertB
  let
    editT = flip Edit <$> facts oldItems <@> ((fmap concat . Just . catMaybes <$> efkattrsB) <@ (UI.click editB))
    insertT =  Insert . Just <$> evi
    deleteT = Delete <$> (traceShowId <$> facts oldItems) <@ (UI.click deleteB)
  return ([insertB,editB,deleteB,end],[insertT,editT,deleteT])

-- Split composite PKs in list of atomic pks
invertPK :: PK a -> [PK a]
invertPK  (PK k [] ) = fmap (\i -> PK [i] []) k
invertPK  (PK k d ) = zipWith (\i j -> PK [i] [j]) k d

projectFk action k = case M.keys <$> M.lookup k schema of
                Just l ->  fmap S.singleton l
                Nothing -> []
          where (_,(schema,table)) = action (project []) k

type ProjAction = (forall t. Traversable t =>
                    (QueryCursor t  -> IO [t Showable],
                      QueryT Identity (t KAttribute)
                      -> S.Set Key -> QueryCursor t ))



findQ :: Traversable t => ProjAction -> QueryT Identity (t KAttribute)  ->
                    (S.Set Key) -> PK Showable -> IO (t Showable)
findQ (p,a) q  arg f = fmap head $ p $ a (do
              predicate filter
              q ) arg
  where
    filter = zipWith (\s k -> (k,Category (S.singleton s))) (invertPK f) (S.toList arg)


doQuery :: Traversable t => ProjAction -> QueryT Identity (t KAttribute)  ->
                    (Map Key [Filter]) -> (S.Set Key) -> IO [t Showable]
doQuery (p,a) q f arg  = p $ a (do
              predicate (concat $ filterToPred <$> (M.toList f))
              q ) arg
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


filterWidget
  :: ProjAction
     -> Tidings (S.Set Key)
     -> Tidings (Map Key [Filter])
     -> UI (UI.MultiListBox (PK Showable ),UI.ListBox (S.Set Key ),RangeBox (PK Showable),TrivialWidget (Map Key [Filter]))
filterWidget c bBset filterT = do
  -- Filter Box (Saved Filter)
  ff  <- insdel (facts filterT)
  -- Filterable Keys
  let bFk = fmap (projectFk (snd c)) bBset
  fkbox <- UI.listBox (liftA2 (:) bBset bFk) (const <$> pure Nothing <*> fmap Just bBset) (pure (\i-> UI.li # set text (showVertex i)))
  -- Filter Query
  bp <- joinT $ (\i j-> maybe (return []) id (fmap (doQuery c projectDesc i) j)) <$> triding ff <*> UI.userSelection fkbox

  rangeWidget <- rangeBoxes (UI.userSelection fkbox)  bp

  -- Filter Selector
  filterItemBox <- UI.multiListBox bp (const <$> pure [] <*> UI.userSelection fkbox) (pure (\i-> UI.li # set text (show i)))
  return  (filterItemBox,fkbox, rangeWidget ,ff)

line n = UI.li # set  text n


chooseKey
  :: Connection -> ProjAction
     -> InformationSchema -> [S.Set Key] -> UI Element
chooseKey conn c@(proj,action) inf kitems = mdo
  -- Base Button Set
  bset <- buttonSet kitems showVertex
  let bBset = triding bset
  -- Filter Box (Saved Filter)

  (filterItemBox,fkbox,range,ff) <- filterWidget c bBset filterT

  -- countAll Query
  let
    bFk = fmap (projectFk (snd c)) bBset
    aggQuery i j ka k
      | S.null j = return []
      | otherwise = doQuery c (aggAll  (pkMap inf) (S.toList j) ka)  i k

  let pkFields = allAttrs . fromJust . (flip M.lookup (pkMap inf)) <$> bBset
      aggregators = (concat . fmap (\i->  flip availableAggregators i . primType $ i) . S.toList <$> pkFields )
  let aset = flip buttonSet show <$> facts aggregators

  -- Filter Map Selected
  let
    filterMaybe f (Just i ) = f i
    filterMaybe _ _  = []
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

  sel <- UI.multiListBox bFk bFk (pure (line . showVertex))
  t <- joinT $ aggQuery  <$> (M.unionWith mappend <$> filterT <*> triding ff) <*> (S.unions <$> UI.multiUserSelection sel) <*> aggregators <*> bBset
  count <- UI.div # sink text (fmap show $ facts t)

  -- Final Query (Saved Filter <> Filter Map Selected)
  vp <- joinT $ doQuery c projectAll <$> (M.unionWith mappend <$> filterT <*> triding ff) <*>  bBset

  -- Final Query ListBox
  itemList <- UI.listBox vp (const <$> pure Nothing <*> bBset) (pure (\i -> line $ show i))
  element (getElement itemList) # set UI.multiple True
  element (getElement filterItemBox) # set UI.multiple True
  let bCrud = fmap (\k -> pure $ do
        let (_,(schema,table)) = action (project (fmap Metric (S.toList k))) k
            filterOptions = case M.keys <$> M.lookup k schema of
               Just l -> k : fmap S.singleton l
               Nothing -> [k]
        (crud,_,_) <- atBase (crudUI conn inf c) table $ (UI.userSelection itemList)
        return crud) (facts bBset)
  insertDiv <- UI.div # sink items bCrud
  filterSel <- UI.div # set children [getElement fkbox]
  filterSel2 <- UI.div # set children [getElement filterItemBox]
  UI.div # set children [ getElement ff,getElement bset ,filterSel,filterSel2,getElement range,insertDiv,getElement itemList ,getElement sel,count]


keySetToMap ks = M.fromList $  fmap (\(Key k _ _ t)-> (toStrict $ encodeUtf8 k,t))  (F.toList ks)

selectQuery
  :: Traversable t => Connection
     -> M.Map (S.Set Key) Table
     -> HashSchema Key Table
     -> QueryT Identity (t KAttribute)
     -> S.Set Key -> IO [t Showable]
selectQuery conn baseTables hashGraph q k =  queryWith_ (fromShowableList j) conn (buildQuery i)
   where (j,(h,i)) =  projectAllKeys baseTables hashGraph  q k


projectKey
  :: Traversable t => Connection
     -> M.Map (S.Set Key) Table
     -> HashSchema Key Table ->
     (QueryCursor t -> IO [t Showable],
         QueryT Identity (t KAttribute)
         -> S.Set Key -> (QueryCursor t ))
projectKey conn baseTables hashGraph = (\(j,(h,i)) -> queryWith_ (fromShowableList j) conn . traceShowId . buildQuery $ i, projectAllKeys baseTables hashGraph )

topSortTables tables = flattenSCCs $ stronglyConnComp item
  where item = fmap (\n@(Raw _ t k _ fk _ ) -> (n,k,fmap (\(Path _ _ end)-> end) (S.toList fk) )) tables

main :: IO ()
main = do
  --let schema = "public"
  --conn <- connectPostgreSQL "user=postgres password=queijo dbname=usda"
  let schema = "incendio"
  conn <- connectPostgreSQL "user=postgres password=queijo dbname=incendio"
  --conn <- connectPostgreSQL "user=postgres password=queijo dbname=finance"
  inf@(k,baseTables,_) <- keyTables conn  schema
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
  graph <- fmap graphFromPath $ schemaKeys conn  schema inf
  -- preview $ cvLabeled graph
  graphAttributes <- fmap graphFromPath $ schemaAttributes conn  schema inf
  let
      g1 = warshall graph
      schema = hashGraph  g1
      schemaInv = hashGraphInv  g1
      q = projectKey conn  baseTables schema
  startGUI defaultConfig (setup conn q inf (M.keys baseTables))

