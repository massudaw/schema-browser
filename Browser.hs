{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances,RankNTypes,NoMonomorphismRestriction,UndecidableInstances,FlexibleContexts,OverloadedStrings ,TupleSections, ExistentialQuantification #-}

import Query
import Widgets
import Debug.Trace
import Schema
import Gpx
import Data.Unique
import Postgresql
import Data.Maybe
import Data.Distributive
import Data.Functor.Identity
import Data.Functor.Product
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
  span <- chooseKey  conn pg inf k
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
    oldItems = fmap (zip (S.toList  pk <>  S.toList allI)) <$> initial
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
      return (sp,liftA2 (,) (fmap(i,) . fmap fst <$> (facts edited) ) (fmap (i,) <$> pk))) $ filter (not. (`S.member` (fkSet <> other) )) $ (S.toList pk <> S.toList allI)
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
  | isSerial (keyType i) = do
      l<- UI.span # set text (show i)
      e <- UI.span # sink text (maybe "" renderShowable <$> (facts (lookupAttrs i)))
      paint l ( pure $ Just undefined)
      sp <- UI.li # set children [l,e]
      return (sp,liftA2 (,) (fmap(i,) <$> (facts (lookupAttrs i)) ) (fmap (i,) <$> pure (Just $ SSerial Nothing)))
  | otherwise = do
      l<- UI.span # set text (show i)
      let tdi = forceDefaultType i <$> lookupAttrs i
      m<- UI.input # sink UI.value (facts tdi) # set UI.name (T.unpack $ keyValue i) # set UI.id_ (T.unpack $ keyValue i) # set UI.type_ "text"
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


fkUI conn tmap lookupAttrs lookupFKS (Path ifk t o) = mdo
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
        findMaybe (Just i) _ = findMQ conn tmap projectAll ifk i
        findMaybe _ _ = return Nothing
      exT <- joinT $ findMaybe <$> pkt <*> triding chw
      let subtable = fromJust $ M.lookup ifk (pkMap tmap)
      (celem,tcrud,evs) <- crudUI conn tmap  subtable (fmap (fmap (\(Metric k, t)-> (k,t))) <$> exT)
      let eres = fmap (addToList  (S.toList o)  (maybeToList $ description subtable) <$> ) evs
      res <-  liftIO $ projectKey' conn tmap projectDesc ifk
      res2 <- accumTs (fmap (fromJust.normalize) <$> (fmap (fmap snd) res)) eres
      --let res2 = tidings (pure res) never
      -- TODO: Implement recursive selection after insertion
      -- tdi2 <- addTs (pure Nothing) $ (\i-> editedMod (S.toList o)  (maybeToList $ description subtable)   <$> i) <$> evs
      element celem
        # sink UI.style (noneShow <$> (facts $ triding chw))
        # set style [("padding-left","10px")]
      fk <- UI.li # set  children [l, getElement box,e,getElement chw,celem]
      let bres = liftA2 (,) (fmap (zip (S.toList ifk)). fmap (fmap fst) <$> facts edited ) (liftA2 (liftA2 mappend) (fmap (zip (S.toList ifk)) <$> fksel) tcrud)
      return (fk,bres)

forceDefaultType k (Just i ) = renderShowable i
forceDefaultType k (Nothing) = ""

paint e b = element e # sink UI.style (greenRed . isJust <$> b)

data Plugins
  = Plugins
  { _inputs :: (Table, S.Set Key)
  , _action :: [(Key,Showable)] -> IO (Maybe (UI Element) , [[(Key,Showable)]])
  }

classifyKeys (table@(Raw s t pk desc fk allI),keys) = (S.intersection keys attrSet,S.intersection keys fkSet)
  where fkSet = S.unions $ fmap (\(Path ifk t o) ->  ifk)  (S.toList fk)
        attrSet = S.fromList $ filter (not. (`S.member` fkSet)) $ (S.toList pk <> S.toList allI)

pluginUI conn inf (Plugins (table@(Raw s t pk desc fk allI),keys) a) oldItems = do
  let
    initialMap :: Tidings (Maybe (Map Key Showable))
    initialMap = fmap M.fromList <$> oldItems
    lookupFKS :: [Key] -> Tidings (Maybe [Showable])
    lookupFKS ks = allMaybes <$> ((\m ks -> fmap (\ki->  join $ fmap (M.lookup ki) m) ks) <$> initialMap <*> pure ks)
    lookupAttrs :: Key -> Tidings (Maybe Showable)
    lookupAttrs k = join . fmap (M.lookup k) <$> initialMap
  let fkSet = S.unions $ fmap (\(Path ifk t o) ->  ifk)  (S.toList fk)
  attrs <- mapM (attrUI lookupAttrs) $ filter (not. (`S.member` fkSet)) $ S.toList keys
  fks <- mapM (fkUI conn inf lookupAttrs lookupFKS) (S.toList fk)
  let
    buildList' i j = foldr (liftA2 (:)) (fmap (fmap (\i-> [i])) <$> buildList i) j
        where buildList = foldr (liftA2 (:))  (pure [])
    fkattrsB = buildList'  (fmap snd .snd <$> attrs) (fmap snd .snd <$> fks)
    efkattrsB = buildList' (fmap fst . snd <$> attrs) (fmap fst . snd <$> fks)
  process <- UI.input # set UI.type_ "submit" # set text "PROCESS"
  let ev = unsafeMapIO a (filterJust $ fmap (fmap concat . allMaybes) $ (fmap traceShowId fkattrsB) <@ UI.click process)
  resB <- stepper (Nothing,[]) ev
  res <- UI.div # sink  text (show . snd <$> resB)
  resElem <- UI.div # sink  items (maybeToList . fst <$> resB)
  crudHeader <- UI.div # set text (T.unpack t)
  formP <- UI.form # set UI.target (T.unpack t) # set UI.method "post"# set UI.action ("http://siapi.bombeiros.go.gov.br/consulta/consulta_cnpj_cpf.php")
    # set children (crudHeader : (fst <$> attrs) <> (fst <$> fks) <> [process] )
    # set style [("border","1px"),("border-color","gray"),("border-style","solid")]
  iframe <- mkElement "iframe" # set UI.name (T.unpack t) # set UI.id_ (T.unpack t) {- # set UI.src ("http://siapi.bombeiros.go.gov.br/consulta/consulta_cnpj_cpf.php")-} # set style [("width","100%"),("heigth","300px")]
  body <- UI.div  # set children [formP,res,iframe]
  return (body,fmap concat . allMaybes <$> fkattrsB)



crudUI
  :: Connection
     -> InformationSchema
     -> Table
     -> Tidings (Maybe [(Key,Showable)])
     -> UI (Element,Behavior (Maybe [(Key,Showable)]),[Event(Modification Key Showable)])
crudUI conn tmap  table@(Raw s t pk desc fk allI) oldItems= do
  let
    initialMap :: Tidings (Maybe (Map Key Showable))
    initialMap = fmap M.fromList <$> oldItems
    lookupFKS :: [Key] -> Tidings (Maybe [Showable])
    lookupFKS ks = allMaybes <$> ((\m ks -> fmap (\ki->  join $ fmap (M.lookup ki) m) ks) <$> initialMap <*> pure ks)
    lookupAttrs :: Key -> Tidings (Maybe Showable)
    lookupAttrs k = join . fmap (M.lookup k) <$> initialMap
  body <- UI.div
  let fkSet = S.unions $ fmap (\(Path ifk t o) ->  ifk)  (S.toList fk)
  attrs <- mapM (attrUI lookupAttrs) $ filter (not. (`S.member` fkSet)) $ (S.toList pk <> S.toList allI)
  fks <- mapM (fkUI conn tmap lookupAttrs lookupFKS) (S.toList fk)
  let
    buildList' i j = foldr (liftA2 (:)) (fmap (fmap (\i-> [i])) <$> buildList i) j
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
addToList i j  (Insert m) =  (\i->  mappend (fmap (fromJust.normalize)  <$> maybeToList i) ) (editedMod  i j m )
addToList i j  (Delete m ) =  (\i->  concat . L.delete (fmap (fromJust.normalize)  <$> maybeToList i)  . fmap pure ) (editedMod  i j m )
addToList i j  (Edit m n ) =  addToList i j (Insert m) . addToList i j (Delete n)

-- lookup pk from attribute list
editedMod :: Ord a => [a] -> [a] -> Maybe [(a,b)] -> Maybe (PK b)
editedMod  i j m=  join $ fmap (\mn-> liftA2 PK (look mn i) (look mn j)) m
  where look mn k = allMaybes $ fmap (flip M.lookup (M.fromList mn) ) k

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
  editB <- UI.button # sink UI.enabled (liftA2 (&&) (any isJust <$>  efkattrsB) (all isJust  <$> fkattrsB)) # set text "EDIT"
  deleteB <- UI.button  # sink UI.enabled (isJust <$> facts oldItems) # set text "DELETE"
  insertB <- UI.button  # sink UI.enabled (all isJust <$> fkattrsB) # set text "INSERT"

  let
      editAction isM kM = do
        let i = catMaybes isM
            k = fromJust kM
        res <- liftIO $ catch (Right <$> update conn (concat i) k table) (\e -> return $ Left (show (e :: SqlError) ))
        return $ fmap (const (Edit (concat <$> allMaybes isM) kM)) res
      deleteAction k =  do
        res <- liftIO $ catch (Right <$> delete conn (fromJust k) table) (\e -> return $ Left (show (e :: SqlError) ))
        return $ const (Delete k ) <$> res
      insertAction i = do
          res <- catch (Right <$> insertPK fromShowableList conn (concat i) table) (\e -> return $ Left (show (e :: SqlError) ))
          return $ (\v -> Insert $ Just $ (v <> filter (not . flip elem (fst <$> v) . fst) (concat i))) <$> res

      evi,evd,eve :: Event (Modification Key Showable)
      (evid,evi) = split $ unsafeMapIO id $ (insertAction . catMaybes <$> fkattrsB) <@ UI.click insertB
      (evdd,evd) = split $ unsafeMapIO id $ (deleteAction <$> facts oldItems) <@ UI.click deleteB
      (eved,eve) = split $ unsafeMapIO id $ (editAction <$> efkattrsB <*> facts oldItems ) <@ UI.click editB

 -- stp <- stepper [] (unions [evdd,eved])
--  end <- UI.div # sink text (show <$> stp)
  return ([insertB,editB,deleteB],[evi,eve,evd])

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

findMQ :: Traversable t => Connection -> InformationSchema -> QueryT Identity (t KAttribute)  ->
                    (S.Set Key) -> PK Showable -> IO (Maybe (t (KAttribute,Showable)))
findMQ conn inf q  arg f = fmap safeHead $ projectKey' conn inf (do
              predicate filter
              q ) arg
  where
    filter = zipWith (\s k -> (k,Category (S.singleton s))) (invertPK f) (S.toList arg)
    attrs = runQuery q
   	  



findQ :: Traversable t => Connection -> InformationSchema -> QueryT Identity (t KAttribute)  ->
                    (S.Set Key) -> PK Showable -> IO (t Showable)
findQ conn inf q  arg f = fmap (fmap snd) $  fmap head $ projectKey' conn inf (do
              predicate filter
              q ) arg
  where
    filter = zipWith (\s k -> (k,Category (S.singleton s))) (invertPK f) (S.toList arg)

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
  :: Connection -> InformationSchema
     -> Tidings (S.Set Key)
     -> Tidings (Map Key [Filter])
     -> UI (UI.MultiListBox (PK Showable ),UI.ListBox (S.Set Key ),RangeBox (PK Showable),TrivialWidget (Map Key [Filter]))
filterWidget conn inf bBset filterT = do
  -- Filter Box (Saved Filter)
  ff  <- insdel (facts filterT)
  -- Filterable Keys
  let bFk = fmap (projectFk (hashedGraph inf) ) bBset
  fkbox <- UI.listBox (liftA2 (:) bBset bFk) (const <$> pure Nothing <*> fmap Just bBset) (pure (\i-> UI.li # set text (showVertex i)))
  -- Filter Query
  bp <- joinT $ (\i j-> maybe (return []) id (fmap (doQuery conn inf projectDesc i) j)) <$> triding ff <*> UI.userSelection fkbox

  rangeWidget <- rangeBoxes (UI.userSelection fkbox)  bp

  -- Filter Selector
  filterItemBox <- UI.multiListBox bp (const <$> pure [] <*> UI.userSelection fkbox) (pure (\i-> UI.li # set text (show i)))
  return  (filterItemBox,fkbox, rangeWidget ,ff)

line n = UI.li # set  text n

selectedItems conn inf ff key = do
  let
    invItems :: Tidings [(S.Set Key , Path Key Table)]
    invItems = ((\k -> case  M.lookup k (hashedGraphInv inf) of
            Just invItems -> M.toList invItems
            Nothing -> [] )) <$> key
  bp <- joinT $ (\i j-> mapM (\k-> fmap (fst k,) . doQuery conn inf projectDescAll i.  fst $ k ) j) <$> ff <*>  invItems
  UI.div # sink items (fmap (\k -> (\i-> UI.div # set items (UI.div # set text (showVertex $ fst k ) : i)) . fmap (line.show.F.toList) . snd  $ k ) <$> facts bp)
  -- UI.div # sink items (fmap (line . show . fst) <$> facts invItems )


chooseKey
  :: Connection
     -> [Plugins]
     -> InformationSchema -> [S.Set Key] -> UI Element
chooseKey conn  pg inf kitems = mdo
  -- Base Button Set
  bset <- buttonSet kitems showVertex
  let bBset = triding bset
  -- Filter Box (Saved Filter)

  (filterItemBox,fkbox,range,ff) <- filterWidget conn inf bBset filterT

  -- countAll Query
  let
    bFk = fmap (projectFk (hashedGraph inf)) bBset
    aggQuery i j ka k
      | S.null j = return []
      | otherwise = doQuery conn inf (aggAll  (pkMap inf) (S.toList j) ka)  i k

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
  vp <- joinT $ doQueryAttr conn inf projectDescAll <$> (M.unionWith mappend <$> filterT <*> triding ff) <*>  bBset

  -- Final Query ListBox
  itemList <- UI.listBox (vp) (const <$> pure Nothing <*> bBset) (pure (\i -> line $ show  $ F.toList $ fmap snd i))
  let
    categoryT1 :: Tidings (Map Key [Filter])
    categoryT1 = M.fromListWith mappend <$> (filterMaybe (fmap (\(fkv,kv)-> (fkv,[Category (S.fromList kv)]))) <$> arg)
      where arg :: Tidings (Maybe [(Key, [PK Showable])])
            arg = (\i j -> fmap (\nj -> zipWith (,) nj (L.transpose j) ) i) <$> (fmap S.toList  . Just <$> bBset ) <*> (fmap invertPK  . maybeToList . fmap (\(Pair i _ ) -> fmap snd i ) <$> UI.userSelection itemList)

  selected <- selectedItems conn inf (M.unionWith mappend <$> categoryT1 <*> triding ff) bBset
  element (getElement itemList) # set UI.multiple True
  element (getElement filterItemBox) # set UI.multiple True
  let bCrud = (\k v -> pure $ do
        let -- (_,(schema,table)) = action (project (fmap Metric (S.toList k))) k
            filterOptions = case M.keys <$> M.lookup k (hashedGraph inf) of
               Just l -> k : fmap S.singleton l
               Nothing -> [k]
        (crud,_,evs) <- atBase (crudUI conn inf ) (fromJust $ M.lookup k (pkMap inf) ) $ fmap (F.toList ) <$> (UI.userSelection itemList)
        let eres = fmap (addToList  (S.toList k)  (maybeToList $ description (fromJust $ M.lookup k (pkMap inf) )) <$> ) evs
        res2 <- accumTs (fmap (fromJust.normalize) <$> v ) eres
        return crud) <$>  bBset  <*> (fmap (\(Pair  j _ )-> fmap snd j)<$> vp)
  let res = fmap (\i -> pluginUI conn inf i (fmap (F.toList) <$> UI.userSelection itemList  ) ) . (\i -> filter (\(Plugins (Raw _ _ pk _ _ _ ,_) _ )-> S.isSubsetOf  pk i ) pg) <$> bBset
  plugins <- UI.div # sink items (fmap (fmap fst) <$> facts res)
  insertDiv <- UI.div # sink items (facts bCrud)
  filterSel <- UI.div # set children [getElement fkbox,getElement range, getElement filterItemBox]
  aggr <- UI.div # set children [getElement sel , count]
  tab <- tabbed [("CRUD",insertDiv),("FILTER",filterSel),("AGGREGATE", aggr), ("PLUGIN",plugins),("SELECTED",selected)]
  UI.div # set children ([ getElement ff,getElement bset ,getElement itemList ,tab] )
 

queryCnpjProject inputs = do
  let Just (SText cnpj) = join $ fmap (normalize .  snd) $ L.find ((== "cgc_cpf") . keyValue . fst) inputs
      element = mkElement "iframe" # set UI.id_ "owner" {- # set UI.src ("http://siapi.bombeiros.go.gov.br/consulta/consulta_cnpj_cpf.php")-} # set style [("width","100%"),("heigth","300px")]
      form = mkElement "form" # set UI.target "owner"
      ediv = do
        e <- element
        f <- form
        UI.div # set children [f,e]
  return (Nothing ,[])



keySetToMap ks = M.fromList $  fmap (\(Key k _ _ t)-> (toStrict $ encodeUtf8 k,t))  (F.toList ks)

selectQuery
  :: Traversable t => Connection
     -> M.Map (S.Set Key) Table
     -> HashSchema Key Table
     -> QueryT Identity (t KAttribute)
     -> S.Set Key -> IO [t Showable]
selectQuery conn baseTables hashGraph q k =  queryWith_ (fromShowableList j) conn (buildQuery i)
   where (j,(h,i)) =  projectAllKeys baseTables hashGraph  q k

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

main :: IO ()
main = do
  --let schema = "public"
  --conn <- connectPostgreSQL "user=postgres password=queijo dbname=usda"
  let schemaN = "incendio"
  conn <- connectPostgreSQL "host=192.168.0.102 user=postgres password=queijo dbname=incendio"
  --conn <- connectPostgreSQL "user=postgres password=queijo dbname=finance"
  inf@(k,baseTables,_,schema,invSchema ) <- keyTables conn  schemaN
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
 -- graph <- fmap graphFromPath $ schemaKeys conn  schema inf
 -- preview $ cvLabeled graph
 -- graphAttributes <- fmap graphFromPath $ schemaAttributes conn  schema inf
  fkey <- fileKey
  let
    Just table = M.lookup "run" (tableMap inf)
    keys = catMaybes $ fmap (flip M.lookup (keyMap inf) . ("run",)) ["distance","id_shoes","id_person","id_place"]
    pg = Plugins (table,S.fromList (fkey : keys)) execKey
  fkey <- fileKey
  let
    Just table1 = M.lookup "fire_project" (tableMap inf)
    keys1 = catMaybes $ fmap (flip M.lookup (keyMap inf) . ("fire_project",)) ["id_owner","ano","protocolo"]
    pg1 = Plugins (table1,S.fromList (keys1)) queryCnpjProject
  startGUI defaultConfig (setup conn  [pg1] inf (M.keys baseTables))

