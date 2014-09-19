{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}

module Query where

import Warshal
import Data.Typeable
import Data.Vector(Vector)
import qualified Data.Foldable as F
import Data.Foldable (Foldable)
import Data.Char ( isAlpha )
import Data.Maybe
import qualified Numeric.Interval as Interval
import Data.Monoid hiding (Product)

import qualified Data.Text.Lazy as T

import GHC.Int
import Data.GraphViz (preview)
import Data.Graph.Inductive.PatriciaTree
import qualified Data.Graph.Inductive.Graph as PG
import qualified Data.GraphViz.Attributes as GA
import qualified Data.GraphViz.Attributes.Complete as GAC

import Data.Traversable(Traversable)
import Database.PostgreSQL.Simple
import Database.PostgreSQL.Simple.Time
import Database.PostgreSQL.Simple.ToField

import Data.Time
import Control.Monad
import GHC.Exts
import System.IO.Unsafe
import Data.Tuple
import Control.Applicative
import Data.List ( nubBy,nub, sort,intercalate,sortBy,isInfixOf )
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Map (Map)
import Data.Set (Set)
import Control.Monad.State
import Control.Monad.State.Class
import System.Environment ( getArgs )
import Text.Parsec hiding(State)
import Text.Parsec.String
import Text.Printf ( printf )
import Data.Text.Lazy(Text)
import Debug.Trace

import Data.Unique

data KPrim
   = PText
   | PBoolean
   | PInt
   | PDouble
   | PDate
   | PTimestamp
   | PInterval
   | PPosition
   deriving(Show,Eq,Ord)


data KType a
   = Primitive a
   | KSerial (KType a)
   | KArray (KType a)
   | KInterval (KType a)
   | KOptional (KType a)
   deriving(Eq,Ord,Functor)

isSerial (KSerial _) = True
isSerial _ = False
isOptional (KOptional _) = True
isOptional _ = False

foldKType f (KOptional k) = f k
foldKType f (KInterval k) = f k
foldKType f (KArray k) = f k
foldKType f (KSerial k) = f k
foldKType f k@(Primitive _) = f k

instance Show (KType KPrim) where
  show =  showTy show

instance Show (KType Text) where
  show = T.unpack . showTy id

showTy f (Primitive i ) = f i
showTy f (KArray i) = showTy f i <> "[]"
showTy f (KOptional i) = showTy f i <> "*"
showTy f (KInterval i) = showTy f i <> "()"
showTy f (KSerial i) = showTy f i <> "?"

data Key
    = Key
    { keyValue :: Text
    , keyTranslation :: Maybe Text
    , keyFastUnique :: Unique
    , keyType :: KType Text
    }

instance Eq Key where
   k == l = keyFastUnique k == keyFastUnique l
   k /= l = keyFastUnique k /= keyFastUnique l

instance Ord Key where
   k > l = keyFastUnique k > keyFastUnique l
   k < l = keyFastUnique k < keyFastUnique l
   k <= l = keyFastUnique k <= keyFastUnique l
   k >= l = keyFastUnique k >= keyFastUnique l


instance Show Key where
   show = T.unpack . showKey
  --show (Key v u _) = show v <> show (hashUnique u)
showKey k  = maybe (keyValue k) id (keyTranslation k) <> "::" <> T.pack ( show $ hashUnique $ keyFastUnique k )<> "::"  <> showTy id (keyType k)

data JoinPath a b
    = From b (Set a)
    | Join b (Set a) (Set (b ,a)) (JoinPath a b)
    deriving(Eq,Ord,Show)

instance Foldable (JoinPath a) where
  foldMap f (Join a _ _ p) = f a <>  F.foldMap f p
  foldMap f (From p _) = f p

data Aggregate a
   = Aggregate [a] Text
   deriving(Show,Eq,Ord)


type KAttribute = FAttribute Key
data FAttribute a
   = Metric a
   | Operator (FAttribute a) Text Text (FAttribute a)
   -- | Rate FAttribute KAttribute
   | Agg (Aggregate (FAttribute a ))
   | Fun [FAttribute a] Text
   deriving(Eq,Ord,Show)

attrInputSet (Metric k ) = [k]
attrInputSet (Operator l k n r ) = concat $ [attrInputSet l, attrInputSet r]
attrInputSet (Fun args k ) = concat $ attrInputSet <$> args
attrInputSet (Agg (Aggregate args k) ) = concat $ attrInputSet <$> args

attrName (Metric k ) = keyValue k
attrName (Operator l k n r ) = attrName l  <> n <>  attrName r
attrName (Fun args n ) =  T.concat (fmap attrName args) <>  n
attrName (Agg (Aggregate args n)) = T.concat (fmap attrName args) <>  n

renderAttribute :: KAttribute -> Text
renderAttribute (Metric s ) = keyValue s
renderAttribute (Operator l k n r ) = renderAttribute l <>  " " <> k <> " " <> renderAttribute r
-- renderAttribute (Prod m1 m2 ) =  renderAttribute m1 <> "*" <> renderAttribute m2
renderAttribute (Fun arg n ) = n <> "(" <> T.intercalate "," (renderAttribute <$> arg) <>")"
renderAttribute a@(Agg m2  ) = renderAggr renderAttribute m2 <> " as " <> attrName a
  where renderAggr f (Aggregate l s )  = s  <> "(" <> T.intercalate ","  (fmap f l)  <> ")"

newtype Position = Position (Double,Double,Double) deriving(Eq,Ord,Typeable,Show,Read)

data Showable
  = SText Text
  | SNumeric Int
  | SBoolean Bool
  | SDouble Double
  | STimestamp LocalTimestamp
  | SPInterval DiffTime
  | SPosition Position
  | SDate Date
  | SSerial (Maybe Showable)
  | SOptional (Maybe Showable)
  | SComposite (Vector Showable)
  | SInterval (Interval.Interval Showable)
  deriving(Ord,Eq)

normalize (SSerial a ) = join $ fmap normalize a
normalize (SOptional a ) = join  $ fmap normalize a
normalize i = Just i


instance Show Showable where
  show (SText a) = T.unpack a
  show (SNumeric a) = show a
  show (SBoolean a) = show a
  show (SDouble a) = show a
  show (STimestamp a) = show a
  show (SDate a) = show a
  show (SSerial a) = show a
  show (SPosition a) = show a
  show (SOptional a) = show a
  show (SInterval a) = show a
  show (SPInterval a) = show a
  show (SComposite a) = show a


data Filter
   -- Set containement
   = Category (Set (PK Showable))
   -- Range Intersection
   | RangeFilter (Interval.Interval (PK Showable))
   | And [Filter]
   | Or [Filter]
   deriving(Eq,Ord)

instance Show Filter where
  show (Category i ) = intercalate "," $ fmap show $ S.toList i
instance Monoid Filter where
  mempty = Category S.empty
  mappend (Category i ) (Category j ) = Category (S.union i j)

-- Pretty Print Filter
renderFilter (table ,name,Category i) = tableName table <> "." <> keyValue name <> " IN( " <>  T.intercalate "," (fmap (\s -> "'" <> T.pack (show $ head (pkKey s)) <> "'" ) $ S.toList i) <> ")"
renderFilter (table ,name,And i) =  T.intercalate " AND "  (fmap (renderFilter . (table ,name,)) i)
renderFilter (table ,name,RangeFilter i) =  tableName table <> "." <> keyValue name <> " BETWEEN " <> T.intercalate " AND "  (fmap (\s -> "'" <> T.pack (show $ head (pkKey s)) <> "'" ) [Interval.inf i,Interval.sup i])


data Table
    =  Base (Set Key) (JoinPath Key Table)
    -- Schema | PKS | Description | FKS | Attrs
    |  Raw Text Text (Set Key) (Maybe Key) (Set (Path Key Text)) (Set Key)
    |  Filtered [(Key,Filter)] Table
    |  Project [KAttribute ] Table
    |  Reduce (Set Key) (Set (Aggregate (KAttribute ) ) )  Table
    |  Limit Table Int
    deriving(Eq,Ord,Show)

description (Raw _ _ _ desc _ _ ) = desc

atTables f t@(Raw _ _ _ _ _ _ ) = f t
atTables f (Filtered _ t ) = atTables f t
atTables f (Project _ t ) = atTables f t
atTables f (Reduce _ _ t ) = atTables f t
atTables f (Limit t _) = atTables f t
atTables f (Base _ p ) = from p
  where from (From t _) = atTables f t
        from (Join t _ _ p) = atTables f t <> from p


atBase f t@(Raw _ _ _ _ _ _ ) = f t
atBase f (Filtered _ t ) = atBase f t
atBase f (Project _ t ) = atBase f t
atBase f (Reduce _ _ t ) = atBase f t
atBase f (Limit t _) = atBase f t
atBase f (Base _ p ) = from p
  where from (From t _) = atBase f t
        from (Join _ _ _ p) = from p

normalizing = atBase (\(Raw _ _ t _ _ _ )-> t)
tableName = atBase (\(Raw _ t _ _ _ _ )-> t)
tablesName = atBase (\(Raw _ t _ _ _ _ )-> S.singleton t)

--- Traverse the joinPath returning the keyList
joinKeys (From b k ) = fmap (b,) (S.toList k)
joinKeys (Join b k _ p) = fmap (b,) (S.toList k) <> joinKeys p


renderNamespacedKeySet (t,k) = tableName t <> "." <> keyValue k

isKOptional (KOptional i) = True
isKOptional (KInterval i) = isKOptional i
isKOptional (Primitive _ ) = False
isKOptional (KArray i)  = isKOptional i

-- Generate a sql query from the AST
showTable :: Table -> Text
showTable (Filtered f t) = filterTable (fmap (\(k,f) -> (t,k,f) ) f ) t
  where
      filterTable [] b =  showTable b
      filterTable filters b =  "(SELECT *  FROM " <> showTable b <>  " WHERE " <> T.intercalate " AND " (fmap renderFilter filters)  <> ") as " <> ( tableName b )
showTable (Raw s t _ _  _ _) = s <> "." <> t
showTable b@(Base k p) = " from (SELECT " <> (T.intercalate "," $ ( S.toList attrs) <> fmap renderNamespacedKeySet jattrs ) <> joinQuerySet p <>") as " <> tableName b
  where
    attrs = S.mapMonotonic attrName $ S.filter (not . (`S.member` (S.fromList $ fmap (Metric. snd) jattrs) )) $ allAttrs b
    jattrs =  nubBy (\ i j-> snd i == snd j) $ joinKeys p
    joinQuerySet (From b _) =  " FROM " <>  showTable b
    joinQuerySet (Join b _ r p)
      |  any (\(Key _ _ _ k )-> isKOptional k ) (snd <$> S.toList r)  = joinQuerySet p <>  " LEFT JOIN " <> showTable b <> joinPredicate (S.toList r) b
      | otherwise  = joinQuerySet p <>  " JOIN " <> showTable b <> joinPredicate (S.toList r) b
      where joinPredicate r b = " ON " <> T.intercalate " AND " (fmap (\(t,f) -> tableName t <> "." <> keyValue f <> " = " <> tableName b <> "." <> keyValue f )  r )


showTable (Project [] t) = "(SELECT " <>  showTable t  <> ") as " <> tableName t
showTable (Project s t) = "(SELECT " <> T.intercalate ","  (nub $ attrName <$> s)  <>  showTable t  <> ") as " <> tableName t
showTable (Reduce j t p) =  "(SELECT " <> T.intercalate "," (fmap keyValue (S.toList j)  <> fmap (renderAttribute.Agg )  (S.toList t ) )   <> " FROM " <>   showTable p  <> " GROUP BY " <> T.intercalate "," (fmap keyValue (S.toList j)) <> " ) as " <> tableName p
showTable (Limit t v) = showTable t <> " LIMIT " <> T.pack (show v)

delete
  :: ToField b =>
     Connection ->  [(Key, b)] -> Table -> IO GHC.Int.Int64
delete conn kold (Raw sch tbl pk _ _ _) = execute conn (fromString $ traceShowId $ T.unpack del) (fmap snd koldPk)
  where
    koldM = M.fromList kold
    equality (k,_)= keyValue k <> "="  <> "?"
    koldPk = fmap (\i-> (i,fromJust $ M.lookup i koldM)) (S.toList pk)
    pred   =" WHERE " <> T.intercalate " AND " (fmap  equality koldPk)
    del = "DELETE FROM " <> sch <>"."<> tbl <>   pred


update
  :: ToField b =>
     Connection -> [(Key, b)] -> [(Key, b)] -> Table -> IO GHC.Int.Int64
update conn kv kold (Raw sch tbl pk _ _ _) = execute conn (fromString $ traceShowId $ T.unpack up)  (fmap snd kv <> fmap snd koldPk)
  where
    koldM = M.fromList kold
    equality (k,_)= keyValue k <> "="  <> "?"
    koldPk = fmap (\i-> (i,fromJust $ M.lookup i koldM)) (S.toList pk)
    pred   =" WHERE " <> T.intercalate " AND " (fmap  equality koldPk)
    setter = " SET " <> T.intercalate "," (fmap equality kv)
    up = "UPDATE " <> sch <>"."<> tbl <> setter <>  pred

insertPK f conn kva (Raw sch tbl pk  _ _ _) = fmap (zip pkList . head) $ liftIO $ queryWith (f $ Metric <$> pkList) conn (fromString $ traceShowId $ T.unpack $ "INSERT INTO " <> sch <>"."<> tbl <>" ( " <> T.intercalate "," (fmap (keyValue . fst) kv) <> ") VALUES (" <> T.intercalate "," (fmap (const "?") kv) <> ")" <> " RETURNING " <>  T.intercalate "," (keyValue <$> pkList)) (fmap snd kv)
  where pkList = S.toList pk
        kv = filter ( not . isSerial . keyType . fst) kva

insert conn kva (Raw sch tbl _ _ _ _) = execute conn (fromString $ traceShowId $ T.unpack $ "INSERT INTO " <> sch <>"."<> tbl <>" ( " <> T.intercalate "," (fmap (keyValue . fst) kv) <> ") VALUES (" <> T.intercalate "," (fmap (const "?") kv) <> ")") (fmap snd kv)
  where kv = filter ( not . isSerial . keyType . fst) kva

dropTable (Raw sch tbl _ _ _ _ )= "DROP TABLE "<> sch <>"."<> tbl

createTable (Raw sch tbl pk _ fk attr) = "CREATE TABLE " <> sch <>"."<> tbl <> "\n(\n" <> T.intercalate "," commands <> "\n)"
  where commands = (renderAttr <$> S.toList attr ) <> [renderPK] <> fmap renderFK (S.toList fk)
        renderAttr k = keyValue k <> " " <> renderTy (keyType k)
        renderKeySet pk = T.intercalate "," (fmap keyValue (S.toList pk ))
        renderTy (KOptional ty) = renderTy ty <> " NOT NULL"
        renderTy (KArray ty) = renderTy ty <> "[] "
        renderTy (Primitive ty ) = ty
        renderPK = "CONSTRAINT " <> tbl <> "_PK PRIMARY KEY (" <>  renderKeySet pk <> ")"
        renderFK (Path origin table end) = "CONSTRAINT " <> tbl <> "_FK_" <> table <> " FOREIGN KEY (" <>  renderKeySet origin <> ") REFERENCES " <> table <> "(" <> renderKeySet end <> ")  MATCH SIMPLE  ON UPDATE  NO ACTION ON DELETE NO ACTION"


joinPath (Path i ll j) (Just p) = Just $ addJoin  ll ( i `S.union` j)  p
joinPath (Path i ll j) Nothing  =  Just $ From ll   ( i `S.union` j)
joinPath (ComposePath i (l,ij,k) j ) m = foldr joinPath  m  (S.toList l <> S.toList k)
joinPath (PathOption i p j ) m =  joinPath ( head $ S.toList p ) m


--addJoin :: (Show a,Show b,Ord b,Ord a) => a -> Set b -> JoinPath b a -> JoinPath b a
addJoin tnew f p = case mapPath tnew f p of
            -- Add new case
            Left accnew -> Join tnew f accnew p
            -- Just update with new joins
            Right i -> i
    where
        --mapPath :: (Show a,Show b,Ord b,Ord a) => a -> Set b -> JoinPath b a -> Either (Set (a,b)) (JoinPath b a)
        mapPath tnew f (From t   s ) =  if tablesName tnew `S.isSubsetOf`  tablesName t
                then  (Right $ From t  snew )
                else  (Left $ S.mapMonotonic (t,) $  s `S.intersection` f)
            where snew =  s `S.union` f
        mapPath tnew  f (Join t  s clause p ) = res
            where  res = case mapPath tnew f p  of
                    Right pnew  -> Right $ Join t s (clause `S.union` (S.mapMonotonic (tnew,) $  s `S.intersection` f)) pnew
                    Left accnew -> if tablesName tnew `S.isSubsetOf`  tablesName t
                        then Right $ Join t  (s `S.union` f)  (clause `S.union` accnew ) p
                        else Left $ (S.mapMonotonic (t,) $ s `S.intersection` f)  `S.union` accnew



addFilterTable [] b = b
addFilterTable ff b@(Filtered fi _ ) = Filtered (fi<>ff) b
addFilterTable ff b = Filtered ff b

-- Label each table with filter clauses
specializeJoin
  :: Map Key Filter
    -> JoinPath Key Table
    -> (Map Key Filter,JoinPath Key Table )
specializeJoin f (From t s) =  (M.fromList ff , From (addFilterTable ff t) s)
    where ff = catMaybes  (fmap (\ i -> fmap (i,). (flip M.lookup) f $ i) (S.toList s))
specializeJoin f (Join t s r p) =  (ms1,Join (addFilterTable ff t) s r ss)
    where (ms,ss) = specializeJoin f p
          ff = catMaybes  (fmap (\ i -> fmap (i,). (flip M.lookup) f $ i) (S.toList s))
          ms1 = foldr (\(i,j) s -> M.insert i  j s) ms ff

createFilter
  :: Map Key Filter
  ->  HashSchema Key Table
  -> Table
  -> (Map Key Filter, Table)
createFilter filters schema (Base k j) = (m,Base k spec)
    where
      path = queryHash (M.keys  filters)  schema k
      Just join =  foldr joinPath (Just j) (catMaybes path)
      (m,spec) = specializeJoin filters join
createFilter filters schema (Project a t) = fmap (Project a) (createFilter filters schema t)
createFilter filters schema (Reduce  k a t) = fmap (Reduce k a) (createFilter filters schema t)


createAggregate  schema key attr  old
    = Reduce (S.fromList key) (S.fromList attr) (addAggregate schema  key attr (Project (fmap Metric key) old))

addAggregate
  :: HashSchema Key Table
     -> [Key] -> [Aggregate KAttribute] -> Table -> Table
addAggregate schema key attr (Base k s) =   case   catMaybes $ queryHash key  schema k  of
                        [] -> Base k  s
                        l -> Base k  (fromJust $ foldr joinPath  (Just s) l)

addAggregate schema key aggr (Project a t) =  Project (foldr (:) a attr )  (addAggregate schema key aggr t)
  where attr =  concat $ fmap (fmap Metric . attrInputSet. Agg) aggr
addAggregate schema key attr (Reduce j t  p) =  case concat $  fmap (\ki -> catMaybes $  queryHash key  schema (S.singleton ki))  (S.toList j)  of
                        [] -> Reduce (foldr S.insert j key) (foldr S.insert t attr)  (addAggregate schema key attr p )
                        l -> Reduce  j t  p


reduce :: Monad m => [Key]
     -> [Aggregate KAttribute]
     -> QueryT m [KAttribute]
reduce group aggr = do
  (schema,table) <- get
  put (schema,createAggregate schema group aggr table)
  return (fmap Metric group <> fmap Agg aggr)

aggAll ::Monad m => Map (Set Key) Table ->  [Key] -> [Aggregate KAttribute] -> QueryT m [KAttribute]
aggAll tmap i agg = do
  reduce i  agg
  (schema,table) <- get
  let
    paths = catMaybes $ fmap (\ti-> (\k -> Path (S.singleton ti) k (S.singleton ti )) <$> M.lookup (S.singleton ti) tmap ) i
    Just res = foldr joinPath (Just $ From table (S.fromList i)) paths
    attrs = nub $ (fmap Metric $ concat $ fmap F.toList $ fmap (\ti->  baseDescKeys (fromJust $ M.lookup (S.singleton ti) tmap)) i ) <> fmap Agg agg
  put (schema,Project attrs $ Base (S.fromList i) res )
  return attrs


countAll :: Monad m =>Map (Set Key) Table ->  [Key] -> QueryT m [KAttribute ]
countAll tmap i = do
  let agg = [ Aggregate [Metric $ Key "distance" Nothing (unsafePerformIO $ newUnique) (Primitive "double precision")] "sum"]
  reduce i  agg
  (schema,table) <- get
  let
    paths = catMaybes $ fmap (\ti-> (\k -> Path (S.singleton ti) k (S.singleton ti )) <$> M.lookup (S.singleton ti) tmap ) i
    Just res = foldr joinPath (Just $ From table (S.fromList i)) paths
    attrs = ( fmap Metric $ concat $ fmap F.toList $ fmap (\ti->  baseDescKeys (fromJust $ M.lookup (S.singleton ti) tmap)) i ) <> fmap Agg agg

  put (schema,Project attrs $ Base (S.fromList i) res )
  return attrs

{-
countAll :: Map (Set Key) Table ->  [Key] -> QueryT m [KAttribute]
countAll tmap i = do
  let agg = [ Aggregate [Metric $ Key "*" Nothing (unsafePerformIO $ newUnique) (Primitive "integer")] "count"]
  reduce i  agg
  (schema,table) <- get
  let
    paths = catMaybes $ fmap (\ti-> (\k -> Path (S.singleton ti) k (S.singleton ti )) <$> M.lookup (S.singleton ti) tmap ) i
    Just res = foldr joinPath (Just $ From table (S.fromList i)) paths
    attrs = (traceShowId $ fmap Metric $ concat $ fmap F.toList $ fmap (\ti->  baseDescKeys (fromJust $ M.lookup (S.singleton ti) tmap)) i ) <> fmap Agg agg

  put (schema,Project attrs $ Base (S.fromList i) res )
  return attrs
-}

freeVars (Metric c) = [c]
-- freeVars (Rate c k ) = freeVars c <> freeVars k
-- freeVars (Prod c k ) = freeVars c <> freeVars k
freeVars (Agg (Aggregate l _ ) ) = concatMap freeVars l

predicate
  :: Monad m =>[(Key,Filter)]
     -> QueryT m ()
predicate filters = do
  (schema,table) <- get
  put (schema, snd  $ createFilter (M.fromList filters) schema table)


data PK a
  = PK { pkKey:: [a], pkDescription :: [a]} deriving(Functor,Foldable,Traversable)


instance Eq a => Eq (PK a) where
  i == j = pkKey i == pkKey j

instance Ord a => Ord (PK a) where
  compare i j = compare (pkKey i) (pkKey j)

instance Show a => Show (PK a)  where
  show (PK i []) = intercalate "," $ fmap show i
  show (PK i j ) = intercalate "," (fmap show i) <> "-"<> intercalate  "," ( fmap show j)

projectDesc
     :: Monad m =>QueryT m (PK (KAttribute ))
projectDesc =  do
  (schema,table) <- get
  let pk = baseDescKeys table
  put (schema,Limit (Project (fmap Metric (F.toList pk) ) table) 200)
  return (fmap Metric pk)


project
  :: Monad m =>[KAttribute ]
     -> QueryT m [KAttribute ]
project attributes =  do
  (schema,table) <- get
  let result = filter (`elem` attributes) (fmap Metric $ S.toList $ allKeys table)
  put (schema,Limit (Project result table) 200 )
  return  result


projectAll
     :: Monad m => QueryT m [KAttribute]
projectAll =  do
  (schema,table) <- get
  let result = fmap Metric $ S.toList $ allKeys table
  put (schema,Limit (Project result  table) 200)
  return result

baseDescKeys :: Table -> PK Key
baseDescKeys (Raw _ _ pk Nothing _ _ ) = PK (S.toList pk)  []
baseDescKeys (Raw _ _ pk (Just d) _ _ ) = PK (S.toList pk) [d]
baseDescKeys (Limit p _ ) = baseDescKeys p
baseDescKeys (Filtered _ p) = baseDescKeys p
baseDescKeys (Project _ p) = baseDescKeys p
baseDescKeys (Reduce _ _ p) = baseDescKeys p
baseDescKeys (Base _ p) = from baseDescKeys p
  where from f (From t _ ) = f t
        from f (Join _ _ _ p) =  from f p

allAttrs :: Table -> Set KAttribute
allAttrs (Raw _ _ pk _ fk p) = S.mapMonotonic Metric $ S.union pk p
allAttrs (Limit p _ ) = allAttrs p
allAttrs (Filtered _ p) = allAttrs p
allAttrs (Project a p) = S.fromList a
allAttrs (Reduce g r p) = S.mapMonotonic Metric g <> S.mapMonotonic Agg r
allAttrs (Base _ p) = F.foldMap allAttrs p



allKeys :: Table -> Set Key
allKeys (Raw _ _ pk _ fk p) = S.union pk p
allKeys (Limit p _ ) = allKeys p
allKeys (Filtered _ p) = allKeys p
allKeys (Project _ p) = allKeys p
allKeys (Reduce _ _ p) = allKeys p
allKeys (Base _ p) = F.foldMap allKeys p


newtype QueryT m a
  = QueryT {runQueryT :: StateT  (HashSchema Key Table, Table)  m a} deriving(Functor,Applicative,Monad,MonadState (HashSchema Key Table, Table) )

runQuery t =  runState ( runQueryT t)

{-
--- Read Schema Graph
edgeK :: Parser (Path Key Table)
edgeK = do
  let valid = noneOf ('\n':" -|")
      key (i,j) =  Key i (Primitive j)
  i <- (fmap (key . break (==':')) $ many1 valid) `sepBy1` spaces
  string "->" >> spaces
  v <- (fmap (key . break (==':')) $ many1 valid) `sepBy1` spaces
  string "|" >> spaces
  o <- many1 valid
  spaces
  return $ Path (S.fromList i)   ((\(i,j)->Raw  i (T.tail j) S.empty ) $ T.break (=='.') o)(S.fromList v)


readGraph :: FilePath -> IO (Graph Key Table)
readGraph fp = do
  r <- parseFromFile (many1 edgeK) fp
  case r of
    Left err -> error (show err)
    Right es -> return $ Graph { edges = pathMap es
                              , hvertices = nub .  map (fst .pbound) $ es
                              , tvertices = nub .  map (snd .pbound) $ es  }
-}

pathLabel (ComposePath i (p1,p12,p2) j) = T.intercalate "," $  fmap pathLabel (S.toList p1) <> fmap pathLabel (S.toList p2)
pathLabel (PathOption i p j) = T.intercalate "\n" (fmap pathLabel (S.toList p))
pathLabel (Path i t j) = tableName t

instance GA.Labellable (Path Key Table) where
  toLabelValue l  = GAC.StrLabel (pathLabel l)
instance GA.Labellable (Set Key ) where
  toLabelValue i = GAC.StrLabel (T.intercalate "," (keyValue <$> S.toList i))

cvLabeled :: Graph Key Table -> Gr (Set Key) (Path Key Table)
cvLabeled g = PG.mkGraph lvertices ledges
  where v = M.fromList $ zip set [0..]
        set = nub $ hvertices g <> tvertices g
        lvertices = fmap (\e -> (fromJust (M.lookup e v),e)) set
        ledges = fmap (\e -> case pbound e of
                            (t,h) -> (fromJust (M.lookup t v) ,fromJust (M.lookup h v) ,e)) (fmap snd $ M.toList $ edges g)


instance IsString Showable where
  fromString i = SText (T.pack i)

instance Num Showable where
  SNumeric i +  SNumeric j = SNumeric (i + j)
  SNumeric i *  SNumeric j = SNumeric (i * j)
  fromInteger i = SNumeric $ fromIntegral i
  negate (SNumeric i) = SNumeric $ negate i
  abs (SNumeric i) = SNumeric $ abs i
  signum (SNumeric i) = SNumeric $ signum i

instance Fractional Showable where
  fromRational i = SDouble (fromRational i)
  recip (SDouble i) = SDouble (recip i)

