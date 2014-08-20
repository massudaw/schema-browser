{-# LANGUAGE RecursiveDo,FlexibleInstances,RankNTypes,NoMonomorphismRestriction,UndecidableInstances,FlexibleContexts,OverloadedStrings ,TupleSections, ExistentialQuantification #-}
import Query
import System.IO.Memoize
import Debug.Trace
import Schema
import Postgresql
import Data.Maybe
import Data.Distributive
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
import Control.Monad(void,mapM,replicateM,liftM,join)
import Data.Functor.Compose
import qualified Database.PostgreSQL.Simple.TypeInfo.Static as TI
import qualified Data.List as L
import Data.Vector(Vector)
import qualified Numeric.Interval as Interval
import qualified Numeric.Interval.Internal as NI
import qualified Data.ByteString.Char8 as BS

import qualified Graphics.UI.Threepenny as UI
import Graphics.UI.Threepenny.Core
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

type QueryCursor t =(t Key, (HashSchema Key Table, Table))

setup
  ::Connection ->
     (forall t. Traversable t => (QueryCursor t -> IO [t Showable],
         QueryT (t Key)
         -> S.Set Key -> QueryCursor t ))
     -> [S.Set Key] -> Window -> UI ()
setup conn action k w = void $ do
  return w # set title "Data Browser"
  dbInfo <- UI.span
  UI.button
  element dbInfo # set text (show db)
  span <- chooseKey  conn action k
  dbH <- UI.div # set children [dbInfo]
  getBody w #+ [element dbH]
  getBody w #+ [element span]


safeTail [] = []
safeTail i = tail i

allMaybes i = case all isJust i of
        True -> Just $ catMaybes i
        False -> Nothing

distMaybeList Nothing = []
distMaybeList (Just i) = fmap Just i

renderShowable (SOptional i ) = maybe "" show i
renderShowable (SInterval i)  = renderShowable (Interval.inf i) <> "," <> renderShowable (Interval.sup i)
renderShowable i = show i

crudUI conn (proj,action) table@(Raw s t pk desc fk allI) initial = do
  let
    initialMap :: Tidings (Maybe (Map Key Showable))
    initialMap = fmap (M.fromList . zip (S.toList $ pk <> allI)) <$> initial
    lookupIMs :: [Key] -> Tidings (Maybe [Showable])
    lookupIMs ks = allMaybes <$> ( (\m ks -> fmap (\ki->  join $ fmap (M.lookup ki) m) ks) <$> initialMap <*> pure ks)
    lookupIM :: Key -> Tidings (Maybe Showable)
    lookupIM k = join .fmap ( M.lookup k) <$> initialMap
    forceDefaultType k (Just i ) = renderShowable i
    forceDefaultType k (Nothing) = ""

  body <- UI.div
  let fkSet = S.unions $ fmap (\(Path o t ifk) ->  ifk)  (S.toList fk)
      paint e b = element e # sink UI.style (fmap (\i-> case i of
        Just _ -> [("background-color","green")]
        Nothing -> [("background-color","red")]) b )
  attrs <- mapM (\i-> do
      l<- UI.span # set text (show i)
      let tdi = forceDefaultType i <$> lookupIM i
      m<- UI.input # sink UI.value (facts tdi)
      let pke = fmap (readType i) $ unionWith const (UI.valueChange m) (rumors tdi)
      pk <- stepper (defaultType i)  pke
      let pkt = tidings pk pke
          ei (Just a) = Just a
          ei Nothing = defaultType i
          edited = (\o j-> if o == ei j then Nothing else j) <$> pkt <*> lookupIM i
          editedFlag (Just i) = "*" <> renderShowable i
          editedFlag Nothing = ""
      edited <- UI.span # sink text (fmap editedFlag (facts edited))
      paint l pk
      sp <- UI.li # set children [l,m,edited]
      return (sp,fmap (i,) <$> pk)) $ filter (not. (`S.member` fkSet)) $ S.toList (pk <> allI)
  fks <- mapM (\(Path o t ifk) -> do
      res <- liftIO $ proj $ action projectDesc ifk
      let tdi = fmap (\i-> PK  i i ) <$> lookupIMs ( S.toList ifk)
      box <- UI.listBox (pure res) tdi (pure (\v-> UI.span # set text (show v)))
      l<- UI.span # set text (show $ S.toList ifk)
      let
          pkt :: Tidings (Maybe (PK Showable))
          pkt = UI.userSelection box
          ei i (Just a) = Just a
          ei i Nothing = defaultType i
          olds :: Tidings [Maybe Showable]
          olds = foldr (liftA2 (:)) (pure []) $ fmap lookupIM (S.toList ifk)
          edited :: Tidings [Maybe Showable]
          edited = (\k o j-> if (distMaybeList $ fmap pkKey o) == liftA2 ei k j then fmap (const Nothing) k else j) <$> pure (S.toList ifk) <*> pkt <*> olds
          editedListFlag (Just i) = "*" <> L.intercalate "," (fmap renderShowable i)
          editedListFlag Nothing = ""
      edited <- UI.span # sink text (editedListFlag . allMaybes <$> (facts edited))
      let fksel = fmap pkKey <$>  facts (UI.userSelection box)
      paint (getElement l) fksel

      fk <- UI.li # set  children [l, getElement box,edited]
      return (fk,fmap (zip (S.toList ifk)) <$> fksel )) (S.toList fk)
  let attrsB = foldr (liftA2 (:))  (pure [])  (snd <$> attrs)
  let fkattrsB = foldr (liftA2 (:)) (fmap (fmap (\i-> [i])) <$> attrsB) (snd <$> fks)
  insertB <- UI.button  # sink UI.enabled (fmap (all isJust)  fkattrsB) # set text "INSERT"
  end <- UI.div
  on UI.click insertB $ const $ do
    k <- currentValue fkattrsB
    case allMaybes k of
      Just i ->  do
        res <- liftIO $ catch (Right <$> insert conn (concat i) table) (\e -> return $ Left (show (e :: SqlError) ))
        case res of
          Right _ -> return ()
          Left v -> element end # set text v >> return ()
      Nothing -> return ()
  element body # set children ((fst <$> attrs ) <> (fst <$> fks) <> [insertB,end])
  return body


insdel :: (Ord a,Ord b,Show a,Show b) => Behavior (Map a [b]) -> UI (TrivialWidget (Map a [b]))
insdel binsK =do
  add <- UI.button # set text "Save"
  remove <- UI.button # set text "Delete"
  res <- filterWB (UI.click add) (UI.click remove) binsK
  out <- UI.div # set children [getElement res,add,remove]
  return $ TrivialWidget (triding res ) out

filterWB emap erem bkin = mdo
  let initialB = pure map
      insB =  M.unionWith mappend <$> bkin
      delB = fmap M.delete <$> bsel2
      recAdd = insB <@ emap
      recDel = filterJust $ delB <@ erem
  let recE = (unionWith (.) recAdd recDel )
  recB <- accumB M.empty  (unionWith (.) recAdd recDel )
  let sk i = UI.li # set text (show i)
  resSpan <- UI.listBox  (fmap M.toList recB) (pure Nothing) (pure sk)
  element resSpan # set (attr "size") "10" # set style [("width","400px")]
  let ev = fmap fst <$> rumors (UI.userSelection resSpan)
  bsel2 <- stepper Nothing ev
  -- Return the widget and create an event after addition and removal
  return $ tri (getElement resSpan) recB (recB <@ recE)

data TrivialWidget a =
  TrivialWidget { triding :: (Tidings a) , trielem ::  Element}

tri e b v = TrivialWidget (tidings  b v) e

instance Widget (TrivialWidget  a) where
  getElement (TrivialWidget t e) = e




buttonSet ks h =do
  buttons <- mapM (buttonString h)ks
  dv <- UI.div # set children (fst <$> buttons)
  let evs = foldr1 (unionWith (const) )  (snd <$> buttons)
  bv <-stepper (head ks) (evs)
  return (dv,tidings bv evs)


buttonString  h  k= do
  b <- UI.button # set text (h k)
  let ev = pure k <@ UI.click  b
  return (b,ev)

invertPK  (PK k [] ) = fmap (\i -> PK [i] []) k
invertPK  (PK k d ) = zipWith (\i j -> PK [i] [j]) k d

projectFk action k = case M.keys <$> M.lookup k schema of
                Just l -> k : fmap S.singleton l
                Nothing -> [k]
          where (_,(schema,table)) = action (project []) k

doQuery :: Traversable t => (forall t. Traversable t =>
                    (QueryCursor t  -> IO [t Showable],
                      QueryT (t Key)
                      -> S.Set Key -> QueryCursor t ))-> QueryT (t Key)  ->
                    (Map Key [Filter]) -> (S.Set Key) -> IO [t Showable]
doQuery (p,a) q f arg  = p $ a (do
              predicate (concat $ filterToPred <$> (M.toList f))
              q ) arg
  where
    filterToPred (k,f) = fmap (k,) f


items :: WriteAttr Element [UI Element]
items = mkWriteAttr $ \i x -> void $ return x # set children [] #+ i

joinT :: MonadIO m => Tidings (IO a) -> m (Tidings a)
joinT = mapT id

delayT :: MonadIO m => Tidings a -> m (Tidings a)
delayT x = do
  c <- currentValue  (facts x)
  bh <- stepper c (rumors x)
  return $ tidings bh (rumors x)

mapT :: MonadIO m => (a -> IO b) -> Tidings a -> m (Tidings b)
mapT f x =  do
  let ev = unsafeMapIO (trace "executed" . f) $ rumors x
  c <- currentValue  (facts x)
  b <- liftIO $ f c
  bh <- stepper b ev
  return $ tidings bh ev



chooseKey
  :: Connection ->
     (forall t. Traversable t => (QueryCursor t  -> IO [t Showable],
         QueryT (t Key)
         -> S.Set Key -> QueryCursor t ))
     -> [S.Set Key] -> UI Element
chooseKey conn c@(proj,action) kitems = mdo
  -- Base Button Set
  (eBset,bBset) <- buttonSet kitems showVertex
  -- Filter Box (Saved Filter)
  ff  <- insdel (facts filterT)
  -- Filterable Keys
  let bFk = fmap (projectFk action) bBset
  fkbox <- UI.listBox (facts bFk) (fmap Just bBset) (pure (\i-> UI.li # set text (showVertex i)))
  let bkev =  filterJust (rumors $ UI.userSelection fkbox)
  -- Filter Query
  bp <- joinT $ doQuery c projectDesc <$> triding ff <*> (fmap fromJust $ UI.userSelection fkbox)
  -- Filter Selector
  let line n = UI.li # set  text (show n)
  filterItemBox <- UI.listBox (facts bp) (pure Nothing) (pure (\i-> UI.li # set text (show i)))
  -- Filter Map Selected
  let
    filterMaybe f (Just i ) = f i
    filterMaybe _ _  = []
    filterT :: Tidings (Map Key [Filter])
    filterT = M.fromListWith mappend <$> (filterMaybe (fmap (\(fkv,kv)-> (fkv,[Category (S.fromList [kv])]))) <$> arg)
      where arg :: Tidings (Maybe [(Key, PK Showable)])
            arg = liftA2 (zipWith (,)) <$> (fmap S.toList  <$> UI.userSelection fkbox ) <*> (fmap invertPK <$> UI.userSelection filterItemBox)

  -- Final Query (Saved Filter <> Filter Map Selected)
  vp <- joinT $ doQuery c projectAll <$> (M.unionWith mappend <$>  filterT <*> triding ff ) <*>  bBset
  -- Final Query ListBox
  itemList <- UI.listBox (facts vp) (const <$> pure Nothing <*> bFk) (pure (\i -> line i))
  element (getElement itemList) # set UI.multiple True
  element (getElement filterItemBox) # set UI.multiple True
  let bCrud  = fmap (\k -> [do
      let (_,(schema,table)) = action (project (fmap Metric (S.toList k))) k
          filterOptions = case M.keys <$> M.lookup k schema of
                    Just l -> k : fmap S.singleton l
                    Nothing -> [k]
      crud <- atBase (crudUI conn c) table $ (UI.userSelection itemList)
      return crud]) (facts bBset)
  insertDiv <- UI.div # sink items bCrud
  filterSel <- UI.div # set children [getElement fkbox]
  filterSel2 <- UI.div # set children [getElement filterItemBox]
  UI.div # set children [getElement ff,eBset,filterSel,filterSel2,insertDiv,getElement itemList ]
  -- Result


keySetToMap ks = M.fromList $  fmap (\(Key k _ _ t)-> (toStrict $ encodeUtf8 k,t))  (F.toList ks)

projectKey
  :: Traversable t => Connection
     -> M.Map (S.Set Key) Table
     -> HashSchema Key Table ->
     ((t Key, (HashSchema Key Table, Table)) -> IO [t Showable],
         QueryT (t Key)
         -> S.Set Key -> (t Key, (HashSchema Key Table, Table)))
projectKey conn baseTables hashGraph = (\(j,(h,i)) -> queryWith_ (fromShowableList j) conn . traceShowId . buildQuery $ i, projectAllKeys baseTables hashGraph )

topSortTables tables = flattenSCCs $ stronglyConnComp item
  where item = fmap (\n@(Raw _ t k _ fk _ ) -> (n,k,fmap (\(Path _ _ end)-> end) (S.toList fk) )) tables

main :: IO ()
main = do
  --let schema = "public"
  --conn <- connectPostgreSQL "user=postgres password=queijo dbname=usda"
  let schema = "health"
  conn <- connectPostgreSQL "user=postgres password=queijo dbname=test"
  inf@(k,baseTables,_) <- keyTables conn  schema
  {-  let sorted = topSortTables (M.elems baseTables)

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
  --preview $ cvLabeled graph
  graphAttributes <- fmap graphFromPath $ schemaAttributes conn  schema inf
  let
      g1 = warshall graph
      schema = hashGraph  g1
      q = projectKey conn  baseTables schema
  startGUI defaultConfig (setup conn q (M.keys baseTables))
  print "END"

