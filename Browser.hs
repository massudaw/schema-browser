{-# LANGUAGE RecursiveDo,RankNTypes,NoMonomorphismRestriction,FlexibleContexts,OverloadedStrings ,TupleSections, ExistentialQuantification #-}
import Query
import Schema
import Data.Maybe
import Text.Read
import Reactive.Threepenny
import Data.Graph(stronglyConnComp,flattenSCCs)
import Control.Exception
import Data.Traversable (Traversable,traverse)
import Warshal
import Data.IORef
import Control.Monad(void,mapM,replicateM,liftM,join)
import Data.Functor.Compose
import qualified Data.List as L
import Data.Vector(Vector)
import qualified Data.ByteString.Char8 as BS

import qualified Graphics.UI.Threepenny as UI
import Graphics.UI.Threepenny.Core
import Data.Monoid

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
import qualified Database.PostgreSQL.Simple.FromField as F
import qualified Database.PostgreSQL.Simple.ToField as TF
import qualified Database.PostgreSQL.Simple.FromRow as FR
import Data.GraphViz (preview)
import qualified Data.Map as M
import Data.Map (Map)
import Data.String

data DB = DB { dbName :: String
          , dbUser :: String
          , dbPassword :: String
          , dbHost :: String
          , dbPort :: String
          }deriving(Show)

renderPostgresqlConn (DB n u p h pt)
  = "user=" <> u <> " password=" <> p <> " dbname=" <> n

db = DB "usda" "postgres" "queijo" "localhost" "5432"


instance TF.ToField Showable where
  toField (Showable t) = TF.toField t
  toField (Numeric t) = TF.toField t
  toField (DDate t) = TF.toField t
  toField (DTimestamp t) = TF.toField t
  toField (DNumeric t) = TF.toField t
  toField (SOptional t) = TF.toField t
  toField (SComposite t) = TF.toField t

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
  --kH <- UI.div # set children (fmap snd keys)
  getBody w #+ [element dbH]
  getBody w #+ [element span]

defaultType t =
    case keyType t of
      KOptional i -> Just (SOptional Nothing)
      i -> Nothing

readType t =
    case fmap textToPrim $ keyType t of
      Primitive PText -> readText
      Primitive PDouble ->  readDouble
      Primitive PInt -> readInt
      Primitive PTimestamp -> readInt
      Primitive PDate-> readInt
      KOptional (Primitive PText ) -> readMaybeText
      KOptional (Primitive PInt )-> readMaybeInt
      KOptional (Primitive PDouble ) -> readMaybeDouble
      KOptional (Primitive PTimestamp) -> readMaybeDouble
      KOptional (Primitive PDate) -> readMaybeDouble
      i -> error ( "Missing type: " <> show (keyType t))
    where
      readInt ""= Nothing
      readInt i = fmap Numeric . readMaybe $ i
      readDouble ""= Nothing
      readDouble i = fmap DNumeric . readMaybe $ i
      readText "" = Nothing
      readText i = fmap Showable . readMaybe $  "\"" <> i <> "\""
      readMaybeText "" = Just $ SOptional Nothing
      readMaybeText i = fmap (SOptional . Just . Showable) . readMaybe $  "\"" <> i <> "\""
      readMaybeInt "" = Just $ SOptional Nothing
      readMaybeInt i = fmap (SOptional . Just . Numeric) . readMaybe $ i
      readMaybeDouble "" = Just $ SOptional Nothing
      readMaybeDouble i = fmap (SOptional . Just . DNumeric) . readMaybe $i

allMaybes i = case all isJust i of
        True -> Just $ catMaybes i
        False -> Nothing

crudUI conn (proj,action) table@(Raw s t pk desc fk allI) = do
  body <- UI.div
  let fkSet = S.unions $ fmap (\(Path o t ifk) ->  ifk)  (S.toList fk)
      paint e b = element e # sink UI.style (fmap (\i-> case i of
        Just _ -> [("background-color","green")]
        Nothing -> [("background-color","red")]) b )
  attrs <- mapM (\i-> do
      l<- UI.span # set text (show i)
      m<- UI.input
      pk <- stepper (defaultType i) $ fmap (readType i) $ UI.valueChange m
      paint l pk
      sp <- UI.li # set children [l,m]
      return (sp,fmap (i,) <$> pk)) $ filter (not. (`S.member` fkSet)) $ S.toList (pk <> allI)
  fks <- mapM (\(Path o t ifk) -> do
      res <- liftIO $ proj $ action projectDesc ifk
      box <- UI.listBox (pure res) (pure Nothing)  (pure (\v-> UI.span # set text (show v)))
      l<- UI.span # set text (show $ S.toList ifk)
      let fksel = fmap pkKey <$> facts (UI.userSelection box)
      paint (getElement l) fksel
      fk <- UI.li # set  children [l, getElement box]
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



filterKey (k,f) = do
  label <- UI.span # set text (show k)
  elems <- mapM (\(Category i)-> mapM (\j-> UI.li # set text (show j)) (S.toList i)) f
  body <- UI.span # set children (concat elems )
  remove <- UI.button # set text "Remove"
  UI.div # set children [label,remove,body]

insdel :: (Ord a,Ord b,Show a,Show b) => Behavior [(a,[b])] -> UI (TrivialWidget (Map a [b]))
insdel binsK =do
  add <- UI.button # set text "ADD"
  remove <- UI.button # set text "REMOVE"
  res <- filterWB (UI.click add) (UI.click remove) binsK
  out <- UI.div # set children [getElement res,add,remove]
  return $ TrivialWidget (triding res ) out

filterWB emap erem bkin = mdo
  let initialB = pure map
      insB = concatenate . fmap (uncurry $ M.insertWith (<>)) <$> bkin
      delB = fmap M.delete <$> bsel2
      recAdd = insB <@ emap
      recDel = filterJust $  delB <@ erem
  let recE = (unionWith (.) recAdd recDel )
  recB <- accumB M.empty  (unionWith (.) recAdd recDel )
  let sk i = UI.li # set text (show i)
  resSpan <- UI.listBox  (fmap M.toList recB) (pure Nothing) (pure sk)
  element resSpan # set (attr "size") "10" # set style [("width","400px")]
  let ev = rumors (UI.userSelection resSpan)
  bsel2 <- stepper Nothing (fmap fst <$> ev)
  -- Return the widget and create an event after addition and removal
  return $ tri (getElement resSpan) recB (recB <@ recE)

data TrivialWidget a =
  TrivialWidget { triding :: (Tidings a) , trielem ::  Element}

tri e b v = TrivialWidget (tidings  b v) e

instance Widget (TrivialWidget  a) where
  getElement (TrivialWidget t e) = e


filterDiv f = do
  keys <- mapM filterKey (M.toList f)
  UI.div # set children keys


buttonSet ks h =do
  buttons <- mapM (buttonString h)ks
  dv <- UI.div # set children (fst <$> buttons)
  let evs = foldr1 (unionWith (const) )  (snd <$> buttons)
  bv <-stepper (head ks) (evs)
  return (dv,tidings bv evs)

invertPK  (PK k [] ) = fmap (\i -> PK [i] []) k
invertPK  (PK k d ) = zipWith (\i j -> PK [i] [j]) k d

buttonString  h  k= do
  b <- UI.button # set text (h k)
  let ev = pure k <@ UI.click  b
  return (b,ev)

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

unsafeMapIOT :: (a -> IO b) -> Tidings a -> Tidings b
unsafeMapIOT f x = tidings (unsafeMapIOB f $ facts x) (unsafeMapIO f $ rumors x)


chooseKey
  :: Connection ->
     (forall t. Traversable t => (QueryCursor t  -> IO [t Showable],
         QueryT (t Key)
         -> S.Set Key -> QueryCursor t ))
     -> [S.Set Key] -> UI Element
chooseKey conn c@(proj,action) kitems = mdo
  (eBset,bBset) <- buttonSet kitems showVertex
  let bFk = fmap (projectFk action) (facts bBset)
  fkbox <- UI.listBox bFk (fmap Just $ facts bBset) (pure (\i-> UI.li # set text (showVertex i)))
  let bkev =  filterJust (rumors $ UI.userSelection fkbox)
  ff  <- insdel filterB
  let
    bp =  unsafeMapIOT id $ doQuery c projectDesc <$> triding ff <*> (fmap fromJust $ UI.userSelection fkbox)
    vp = unsafeMapIOT id $ doQuery c projectAll <$> (M.unionWith mappend <$> (M.fromListWith mappend <$> filterT) <*> triding ff ) <*>  bBset
  let line n = UI.li # set  text (show n)
  filterItemBox <- UI.listBox (facts bp) (pure Nothing) (pure (\i-> UI.li # set text (show i)))
  -- Filter Selector Behaviour
  let
    filterMaybe f (Just i ) = f i
    filterMaybe _ _  = []
    filterB = facts filterT
    filterT :: Tidings [(Key,[Filter])]
    filterT = filterMaybe (fmap (\(fkv,kv)-> (fkv,[Category (S.fromList [kv])]))) <$> arg
      where arg :: Tidings (Maybe [(Key, PK Showable)])
            arg = liftA2 (zipWith (,)) <$> (fmap S.toList  <$> UI.userSelection fkbox ) <*> (fmap invertPK <$> UI.userSelection filterItemBox)

  bDivRes <- UI.div  # sink items (fmap line <$> (facts vp))
  let bCrud  = fmap (\k -> [do
      let (_,(schema,table)) = action (project (fmap Metric (S.toList k))) k
          filterOptions = case M.keys <$> M.lookup k schema of
                    Just l -> k : fmap S.singleton l
                    Nothing -> [k]
      crud <- atBase (crudUI conn c) table
      return crud]) (facts bBset)
  insertDiv <- UI.div # sink items bCrud
  UI.span # set children [getElement ff,eBset,getElement fkbox,getElement filterItemBox,insertDiv,bDivRes]
  -- Result


renderedType key = \f b ->
   case F.name f  of
      Just name -> let
          go ::  KType Text
                -> F.Conversion Showable
          go t = case t of
            (KOptional (Primitive i)) -> SOptional <$> prim name (textToPrim i) f b
            (Array (Primitive i)) -> SComposite <$> prim name (textToPrim i) f b
            (KOptional (Array (Primitive i))) ->  fmap (SOptional . fmap SComposite . getCompose ) $ prim name (textToPrim i) f b
            (Primitive i) ->  fmap unOnly $ prim  name (textToPrim i) f b
          in case (keyValue key == T.fromStrict (TE.decodeUtf8 name)) of
              True ->  go (keyType key)
              False -> error $ "no match type for " <> BS.unpack name <> " with key" <> show key
      Nothing -> error "no name for field"
     where


unOnly :: Only a -> a
unOnly (Only i) = i

prim :: (F.FromField (f1 LocalTimestamp),F.FromField (f1 Date),F.FromField (f1 Text), F.FromField (f1 Double), F.FromField (f1 Int), Functor f1) =>
          BS.ByteString
        -> Prim
        -> F.Field
        -> Maybe BS.ByteString
        -> F.Conversion (f1 Showable)
prim  name p f b = case p of
            PText ->  s $ F.fromField f b
            PInt -> n $ F.fromField  f b
            PDouble -> d $ F.fromField  f b
            PDate -> da $ F.fromField  f b
            PTimestamp -> t $ F.fromField  f b
  where
    s = fmap (fmap Showable)
    n = fmap (fmap Numeric)
    d = fmap (fmap DNumeric)
    da = fmap (fmap DDate)
    t = fmap (fmap DTimestamp)

instance (F.FromField (f (g a))) => F.FromField (Compose f g a) where
   fromField = fmap (fmap (fmap (Compose ) )) $ F.fromField

instance F.FromField a => F.FromField (Only a) where
  fromField = fmap (fmap (fmap Only)) F.fromField


fromShowableList foldable = do
    let keyMap = keySetToMap foldable
    n <- FR.numFieldsRemaining
    traverse (FR.fieldWith . renderedType) foldable

keySetToMap ks = M.fromList $  fmap (\(Key k _ _ t)-> (toStrict $ encodeUtf8 k,t))  (F.toList ks)

projectKey
  :: Traversable t => Connection
     -> M.Map (S.Set Key) Table
     -> HashSchema Key Table ->
     ((t Key, (HashSchema Key Table, Table)) -> IO [t Showable],
         QueryT (t Key)
         -> S.Set Key -> (t Key, (HashSchema Key Table, Table)))
projectKey conn baseTables hashGraph = (\(j,(h,i)) -> queryWith_ (fromShowableList j) conn . traceShowId . buildQuery $ i, projectAllKeys baseTables hashGraph )

withConn action = do
  conn <- connectPostgreSQL "user=postgres password=queijo dbname=usda "
  action conn

topSortTables tables = flattenSCCs $ stronglyConnComp item
  where item = fmap (\n@(Raw _ t k _ fk _ ) -> (n,k,fmap (\(Path _ _ end)-> end) (S.toList fk) )) tables

main :: IO ()
main = do
  let schema = "public"
  conn <- connectPostgreSQL "user=postgres password=queijo dbname=usda"
  --conn <- connectPostgreSQL "user=postgres password=queijo dbname=test"
  inf@(k,baseTables) <- keyTables conn  schema
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

