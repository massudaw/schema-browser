{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE LambdaCase #-}
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
import Data.Tuple
import Data.Functor.Apply
import Data.Functor.Compose
import Data.Typeable
import Data.Distributive
import Data.Vector(Vector)
import Data.Functor.Classes
import qualified Data.Foldable as F
import Data.Foldable (Foldable)
import Data.Traversable (mapAccumL)
import qualified Data.Traversable as Tra
import Data.Char ( isAlpha )
import Data.Maybe
import qualified Numeric.Interval as Interval
import Data.Monoid hiding (Product)
import Data.Functor.Product

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
   | PBounding
   | PLineString
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

instance Show (KType KPrim) where
  show =  showTy show

instance Show (KType Text) where
  show = T.unpack . showTy id

showTy f (Primitive i ) = f i
showTy f (KArray i) = "[" <>  showTy f i <> "]"
showTy f (KOptional i) = showTy f i <> "*"
showTy f (KInterval i) = showTy f i <> "()"
showTy f (KSerial i) = showTy f i <> "?"

-- keyValue k = keyName k <> (T.pack $ show $ hashUnique $ keyFastUnique k)

data Key
    = Key
    { keyValue :: Text
    , keyAlias :: Maybe Text
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
    show k = T.unpack $ maybe (keyValue k) id (keyTranslation  k)
   -- show k = T.unpack $ showKey k
   -- show (Key v u _ _ ) = T.unpack v -- <> show (hashUnique u)
showKey k  = keyValue k  <>  maybe "" ("-"<>) (keyTranslation k) <> "::" <> T.pack ( show $ hashUnique $ keyFastUnique k )<> "::"  <> showTy id (keyType k)


instance Foldable (JoinPath a) where
  foldMap f (Join ty a  _ p) = f a <>  F.foldMap f p
  foldMap f (From p _) = f p

data Aggregate a
   = Aggregate [a] Text
   deriving(Show,Eq,Ord)


type KAttribute = FAttribute Key
data FAttribute a
   = Metric a
   | Operator (FAttribute a) Text Text (FAttribute a)
   | Agg (Aggregate (FAttribute a ))
   | Fun [FAttribute a] Text
   deriving(Eq,Ord,Show)

attrInputSet (Metric k ) = [k]
attrInputSet (Operator l k n r ) = concat $ [attrInputSet l, attrInputSet r]
attrInputSet (Fun args k ) = concat $ attrInputSet <$> args
attrInputSet (Agg (Aggregate args k) ) = concat $ attrInputSet <$> args

attrName (Metric k ) = maybe (keyValue k ) id (keyAlias k)
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

newtype Bounding = Bounding (Interval.Interval Position) deriving(Eq,Ord,Typeable,Show)
newtype LineString = LineString (Vector Position) deriving(Eq,Ord,Typeable,Show,Read)

data Showable
  = SText Text
  | SNumeric Int
  | SBoolean Bool
  | SDouble Double
  | STimestamp LocalTimestamp
  | SPInterval DiffTime
  | SPosition Position
  | SBounding Bounding
  | SLineString LineString
  | SDate Date
  | SSerial (Maybe Showable)
  | SOptional (Maybe Showable)
  | SComposite (Vector Showable)
  | SInterval (Interval.Interval Showable)
  | SScopedKeySet (Map Key Showable)
  deriving(Ord,Eq,Show)

normalize (SSerial (Just a) ) =  a
normalize a@(SSerial Nothing  ) =  a
normalize (SOptional (Just a) ) = a
normalize a@(SOptional Nothing ) = a
normalize i = i

transformKey (KSerial i)  (KOptional j) (SSerial v)  | i == j = (SOptional v)
transformKey (KOptional i)  (KSerial j) (SOptional v)  | i == j = (SSerial v)
transformKey (KSerial j)  l@(Primitive _ ) (SSerial v) | j == l  && isJust v =  (\(Just i)-> i) v
transformKey (KOptional j)  l@(Primitive _ ) (SOptional v) | j == l  && isJust v = (\(Just i)-> i) v
transformKey l@(Primitive _)  (KOptional j ) v | j == l  = SOptional $ Just v
transformKey l@(Primitive _)  (KSerial j ) v | j == l  = SSerial $ Just v
transformKey ki kr v | ki == kr = v
transformKey ki kr  v = error  ("No key transform defined for : " <> show ki <> " " <> show kr <> " " <> show v )


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
  show (RangeFilter i ) =  show i
  show (And i ) =  show i
  show (Or i ) =  show i

instance Monoid Filter where
  mempty = Category S.empty
  mappend (Category i ) (Category j ) = Category (S.union i j)

-- Pretty Print Filter
renderFilter (table ,name,Category i) = tableName table <> "." <> keyValue name <> " IN( " <>  T.intercalate "," (fmap (\s -> "'" <> T.pack (renderShowable $ head (pkKey s)) <> "'" ) $ S.toList i) <> ")"
renderFilter (table ,name,And i) =  T.intercalate " AND "  (fmap (renderFilter . (table ,name,)) i)
renderFilter (table ,name,RangeFilter i) =  tableName table <> "." <> keyValue name <> " BETWEEN " <> T.intercalate " AND "  (fmap (\s -> "'" <> T.pack (renderShowable$ head (pkKey s)) <> "'" ) [Interval.inf i,Interval.sup i])

data SqlOperation a
  = FetchTable a
  | FKJoinTable a [(Key,Key)] a
  deriving(Eq,Ord,Show,Functor)


instance Show Table where
  show = T.unpack . tableName

data TableType
   = ReadOnly
   | WriteOnly
   | ReadWrite
   deriving(Eq,Ord,Show)

data Table
    =  Base (Set Key) (JoinPath Key Table)
    -- Schema | PKS | Description | FKS | Attrs
    |  Raw { rawSchema :: (Text,TableType)
           , rawName :: Text
           , rawPK :: (Set Key)
           , rawDescription :: (Maybe Key)
           , rawFKS ::  (Set (Path Key (SqlOperation Text)))
           , rawAttrs :: (Set Key)
           }
    |  Filtered [(Key,Filter)] Table
    |  Project [ KAttribute ] Table
    |  Reduce (Set Key) (Set (Aggregate (KAttribute ) ) )  Table
    |  Limit Table Int
     deriving(Eq,Ord)

description (Raw _ _ _ desc _ _ ) = desc

atTables f t@(Raw _ _ _ _ _ _ ) = f t
atTables f (Filtered _ t ) = atTables f t
atTables f (Project _ t ) = atTables f t
atTables f (Reduce _ _ t ) = atTables f t
atTables f (Limit t _) = atTables f t
atTables f (Base _ p ) = from p
  where from (From t _) = atTables f t
        from (Join ty t _ p) = atTables f t <> from p
        from (SplitJoin _ t  _ p) = atTables f t <> from p

renderShowable :: Showable -> String
renderShowable (SOptional i ) = maybe "" renderShowable i
renderShowable (SSerial i ) = maybe "" renderShowable i
renderShowable (SInterval i)  = renderShowable (Interval.inf i) <> "," <> renderShowable (Interval.sup i)
renderShowable (SComposite i)  = unlines $ F.toList $ fmap renderShowable i
renderShowable i = shw i
 where
  shw (SText a) = T.unpack a
  shw (SNumeric a) = show a
  shw (SBoolean a) = show a
  shw (SDouble a) = show a
  shw (STimestamp a) = show a
  shw (SLineString a ) = show a
  shw (SBounding a ) = show a
  shw (SDate a) = show a
  shw (SSerial a) = maybe " " ((" "<>) . shw) a
  -- show (SSerial a) = show a
  shw (SPosition a) = show a
  --show (SOptional a) = show a
  shw (SOptional a) = maybe "  " (("  "<>). shw) a
  shw (SInterval a) = shw (Interval.inf a) <> " , " <> shw (Interval.sup a)
  shw (SPInterval a) = show a
  shw (SComposite a) = intercalate "," $ F.toList (fmap shw a)




atBase f t@(Raw _ _ _ _ _ _ ) = f t
atBase f (Filtered _ t ) = atBase f t
atBase f (Project _ t ) = atBase f t
atBase f (Reduce _ _ t ) = atBase f t
atBase f (Limit t _) = atBase f t
atBase f (Base _ p ) = from p
  where from (From t _) = atBase f t
        from (Join _ _ _ p) = from p
        from (SplitJoin _ _  _ p ) = from p

normalizing = atBase (\(Raw _ _ t _ _ _ )-> t)
tableName = atBase (\(Raw _ t _ _ _ _ )-> t)
alterTableName f = atBase (\(Raw s t p i j l )-> (Raw s (f t)  p i j l))
tablesName = atBase (\(Raw _ t _ _ _ _ )-> S.singleton t)

--- Traverse the joinPath returning the keyList

aliasedKey (PathRoot  ,v) = keyValue v
aliasedKey (v ,k) =  path v   <> "_" <> keyValue k
  where path PathRoot  = ""
        path (PathCons i) = T.intercalate "_" $ fmap (\(k,p)-> (\case {PathRoot -> "" ; m@(PathCons _ ) -> (path m <> "_")}) p <> keyValue k  ) $ S.toList i



renderAliasedKey (PathRoot  ,v)  a = renderNamespacedKeySet v <> " AS " <> a
  where renderNamespacedKeySet (t,k) = tableName t <> "." <> keyValue k
renderAliasedKey (v ,(t,k)) a = tableName t <> "." <> keyValue k <> " AS " <> a


isKOptional (KOptional i) = True
isKOptional (KSerial i) = isKOptional i
isKOptional (KInterval i) = isKOptional i
isKOptional (Primitive _) = False
isKOptional (KArray i)  = isKOptional i

data JoinType
  = JInner
  | JLeft
  deriving(Eq,Show,Ord)

data JoinPath a b
    = From b (Set a)
    | Join  JoinType b (Set (b,Set (a,a))) (JoinPath a b)
    | SplitJoin JoinType b  [(Set a,[(b,Set (a,a))])] (JoinPath a b)
    deriving(Eq,Ord,Show)


splitJoins j@(From p r ) = j
splitJoins j@(Join ty b r p) = case {-all (<2) $ fmap (length. snd )  -} length mapK  <2 of
                                     True -> Join ty b r $ splitJoins p
                                     False ->  SplitJoin ty b   mapK (splitJoins p)
      where
        mapK :: [(Set Key,[(Table,Set (Key, Key))])]
        mapK = M.toList $ M.fromListWith (<>) $ fmap (fmap pure) $ concat $ concat $ fmap snd $ M.toList mapkPre
        mapkPre :: Map (Set Key) ([[(Set Key,(Table,Set (Key,Key)))]])
        mapkPre = fmap (fmap (\(i,j)-> fmap (i,) j) . M.toList . M.fromListWith (<>)) groupJoins
        groupJoins ::  Map (Set Key) [(Set Key,[(Table,Set (Key,Key))])]
        groupJoins =  M.fromListWith (<>) ((\f@(t,a)-> ( S.map snd a , [( S.map fst a , [( t , a )] )] )) <$> S.toList r)
splitJoins j = j


aliasJoin b@(Base k1 p) =   zipWith (\i (j,l)-> (j,(i,l))) (T.pack . ("v" <> ). show <$> [0..]) aliasMap
  where
    aliasMap =  fmap (\i -> ( (\(p,(t,k))-> (p,k))i,i)) attrs
    attrs = S.toList $ allAttrs' b

fullTableName  i = (T.intercalate "_" $ fmap (\k -> keyValue k <> (T.pack $ show $ hashUnique (keyFastUnique k))) $ S.toList i)

-- Generate a sql query from the AST
showTable :: Table -> Text
showTable (Filtered f t) = filterTable (fmap (\(k,f) -> (t,k,f) ) f ) t
  where
      filterTable [] b =  showTable b
      filterTable filters b =  "(SELECT *  FROM " <> showTable b <>  " WHERE " <> T.intercalate " AND " (fmap renderFilter filters)  <> ") as " <> ( tableName b )
showTable (Raw s t _ _  _ _) = fst s <> "." <> t
showTable b@(Base k1 p) = " from (SELECT " <> T.intercalate ","  ((\(a,p)-> renderAliasedKey p a) . snd <$> attrs )  <> joinQuerySet p <>") as " <> tableName b
  where
    attrs = aliasJoin b
    joinQuerySet (From b _) =  " FROM " <>  showTable b
    joinQuerySet (SplitJoin t b  r p) =  F.foldl' joinType (joinQuerySet p) r
        where joinType  l ir@(_,r)
                | t == JLeft = l <> " LEFT JOIN " <> joinPredicate2 b ir
                | otherwise =  l <> " JOIN " <> joinPredicate2 b ir
              joinPredicate2 b (i,r)  = showTable b <> " AS " <> tempName  <> " ON " <> T.intercalate " AND " (fmap (\(t,fs) -> T.intercalate " AND " $ fmap (\f-> tableName t <> "." <> keyValue (fst f) <> " = " <> tempName  <> "." <> keyValue (snd f)) $ S.toList fs )  r )
                where tempName = tableName b <> fullTableName  i
    joinQuerySet (Join ty b  r p)  = joinType (joinQuerySet p)  r
        where
            joinType  l ir
                | ty == JLeft = l <> " LEFT JOIN " <> joinPredicate b ir
                | otherwise =  l <> " JOIN " <> joinPredicate b ir
            joinPredicate  b  r  = showTable b <> " ON " <> T.intercalate " AND " (fmap (\(t,fs) -> T.intercalate " AND " $ fmap (\f-> tableName t <> "." <> keyValue (fst f) <> " = " <> tableName b <> "." <> keyValue (snd f)) $ S.toList fs )  $ S.toList r )

showTable (Project s t)
  |  F.all (const False) s  = "(SELECT " <>  showTable t  <> ") as " <> tableName t
  | otherwise = "(SELECT " <> T.intercalate ","  (F.toList $ attrName <$> s)  <>  showTable t  <> ") as " <> tableName t
showTable (Reduce j t p) =  "(SELECT " <> T.intercalate "," (fmap keyValue (S.toList j)  <> fmap (renderAttribute.Agg )  (S.toList t ) )   <> " FROM " <>   showTable p  <> " GROUP BY " <> T.intercalate "," (fmap keyValue (S.toList j)) <> " ) as " <> tableName p
showTable (Limit t v) = showTable t <> " LIMIT " <> T.pack (show v)

delete
  :: ToField b =>
     Connection ->  [(Key, b)] -> Table -> IO GHC.Int.Int64
delete conn kold t@(Raw sch tbl pk _ _ _) = execute conn (fromString $ traceShowId $ T.unpack del) (fmap snd koldPk)
  where
    koldM = M.fromList kold
    equality (k,_)= keyValue k <> "="  <> "?"
    memberPK k = S.member (keyValue $ fst k) (S.fromList $ fmap  keyValue $ S.toList  pk)
    koldPk = filter memberPK kold
    pred   =" WHERE " <> T.intercalate " AND " (fmap  equality koldPk)
    del = "DELETE FROM " <> rawFullName t <>   pred

data TableModification b
  = TableModification Table (Modification Key b)
  deriving(Eq,Show)

data Modification a b
  = Edit (Maybe [(a,b)]) (Maybe [(a,b)])
  | Insert (Maybe [(a,b)])
  | Delete (Maybe [(a,b)])
  deriving(Eq,Show)


update
  :: ToField b =>
     Connection -> [(Key, b)] -> [(Key, b)] -> Table -> IO (GHC.Int.Int64,TableModification b)
update conn kv kold t@(Raw sch tbl pk _ _ _) = fmap (,TableModification t (Edit (Just skv) (Just koldPk ) )) $ execute conn (fromString $ traceShowId $ T.unpack up)  (fmap snd skv <> fmap snd koldPk)
  where
    koldM = M.fromList kold
    equality (k,_)= keyValue k <> "="  <> "?"
    memberPK k = S.member (keyValue $ fst k) (S.fromList $ fmap  keyValue $ S.toList  pk)
    koldPk = filter memberPK kold
    pred   =" WHERE " <> T.intercalate " AND " (fmap  equality koldPk)
    setter = " SET " <> T.intercalate "," (fmap equality skv )
    up = "UPDATE " <> rawFullName t <> setter <>  pred
    skv = nubBy (\(i,j) (k,l) -> i == k)  kv

insertPK f conn kva t@(Raw sch tbl pk  _ _ attr ) = case pkListM of
                                                      Just reti ->  fmap ( zip pkList . head) $ liftIO $ queryWith (f $ Metric <$> pkList) conn (fromString $ traceShowId $ T.unpack $ "INSERT INTO " <> rawFullName t <>" ( " <> T.intercalate "," (fmap (keyValue . fst) kv) <> ") VALUES (" <> T.intercalate "," (fmap (const "?") kv) <> ")" <> " RETURNING " <>  T.intercalate "," (keyValue <$> reti )  ) (fmap snd  kv)
                                                      Nothing ->   liftIO $ execute conn (fromString $ traceShowId $ T.unpack $ "INSERT INTO " <> rawFullName t <>" ( " <> T.intercalate "," (fmap (keyValue . fst) kv) <> ") VALUES (" <> T.intercalate "," (fmap (const "?") kv) <> ")"   ) (fmap snd  kv) >> return []
  where pkList = S.toList $ S.filter (isSerial . keyType )  pk
        pkListM= case pkList of
                  [] -> Nothing
                  i -> Just i
        kv = nub $ filter (\(k,_) -> memberPK k || memberAttr k ) $    kva
        memberPK k = S.member (keyValue k) (S.fromList $ fmap  keyValue $ S.toList $ S.filter (not . isSerial . keyType ) pk)
        memberAttr k = S.member (keyValue k) (S.fromList $ fmap  keyValue $ S.toList attr)

getKey  (Raw sch tbl pk desc fk attr) k =  M.lookup k table
  where table = M.fromList $ fmap (\i-> (keyValue i, i)) $ S.toList (pk <> attr)

isEmptyShowable (SOptional Nothing ) = True
isEmptyShowable (SSerial Nothing ) = True
isEmptyShowable i = False


insert conn kva t@(Raw sch tbl pk _ _ attr ) = execute conn (fromString $ traceShowId $ T.unpack $ "INSERT INTO " <> rawFullName t  <>" ( " <> T.intercalate "," (fmap (keyValue . fst) kv) <> ") VALUES (" <> T.intercalate "," (fmap (const "?") kv) <> ")") (fmap snd kv)
  where kv = filter (\(k,_) -> S.member k pk || S.member k attr ) $ filter ( not . isSerial . keyType . fst)  kvb
        kvb = catMaybes $ fmap (\i-> fmap (,snd i) . getKey t . keyValue . fst $ i  ) kva

dropTable r@(Raw sch tbl _ _ _ _ )= "DROP TABLE "<> rawFullName r

rawFullName (Raw (sch,tt) tbl _ _ _ _) = sch <> "." <> tbl

createTable r@(Raw sch tbl pk _ fk attr) = "CREATE TABLE " <> rawFullName r  <> "\n(\n" <> T.intercalate "," commands <> "\n)"
  where commands = (renderAttr <$> S.toList attr ) <> [renderPK] <> fmap renderFK (S.toList fk)
        renderAttr k = keyValue k <> " " <> renderTy (keyType k)
        renderKeySet pk = T.intercalate "," (fmap keyValue (S.toList pk ))
        renderTy (KOptional ty) = renderTy ty <> " NOT NULL"
        renderTy (KArray ty) = renderTy ty <> "[] "

        renderTy (Primitive ty ) = ty
        renderPK = "CONSTRAINT " <> tbl <> "_PK PRIMARY KEY (" <>  renderKeySet pk <> ")"
        renderFK (Path origin (FKJoinTable _ ks table) end) = "CONSTRAINT " <> tbl <> "_FK_" <> table <> " FOREIGN KEY " <>  renderKeySet origin <> ") REFERENCES " <> table <> "(" <> renderKeySet end <> ")  MATCH SIMPLE  ON UPDATE  NO ACTION ON DELETE NO ACTION"

joinPath (Path i (FKJoinTable _ ks ll ) j) (Just p) = Just $ addJoin  ll (S.fromList ks)  p
joinPath (Path i (FetchTable ll ) j) (Just p) = Just $ addJoin  ll ((S.fromList $ zip (S.toList i) (S.toList j)))  p
-- joinPath (Path i (FetchTable ll) j) Nothing  =  Just $ From ll   (i `S.union` j)
joinPath (ComposePath i (l,ij,k) j ) m = F.foldl' (flip joinPath)  m  ((S.toList l)  <> ( S.toList k))
joinPath (PathOption i p j ) m =  joinPath ( head $ S.toList p ) m

joinPathL (Path i (FKJoinTable ll  ks _ ) j) (Just p) = Just $ addJoin  ll (S.fromList $ fmap swap ks)  p
joinPathL (Path i (FetchTable ll ) j) (Just p) = Just $ addJoin  ll ((S.fromList $ zip (S.toList i) (S.toList j)))  p
joinPathL (ComposePath i (l,ij,k) j ) m = F.foldr joinPathL  m  ((S.toList l)  <> ( S.toList k))
joinPathL (PathOption i p j ) m =  error "option" -- joinPathL ( head $ S.toList p ) m

{-
attrPath  (Path i (FetchTable ll) _ )  = const  (TB1 (KV (PK [] [] ) []))
attrPath  (Path i (FKJoinTable ll ks tt ) j) = \i-> TB1 (KV (PK [FKT (S.toList j) i ] [] ) [] )
attrPath  (ComposePath _ (l,ij,k) _)  = attrPath (head $ S.toList k) . attrPath (head $ S.toList l)
-}

addJoin
  :: Table
  -> Set (Key, Key) -> JoinPath Key Table -> JoinPath Key Table
addJoin tnew f p = case mapPath tnew  f p of
            -- Add new case
            Left accnew -> case any (isKOptional . keyType  ) (concat $ fmap fst . S.toList .  snd <$> S.toList accnew ) of
                             True ->  Join JLeft tnew  accnew  p
                             False ->  Join JInner tnew accnew  p
            -- Just update with new joins
            Right i -> i
    where
        filterFst t elem=  if S.null filtered then Nothing else Just (t,filtered)
          where filtered = S.filter ((`S.member` (S.map (snd.snd) $   allAttrs' t)) . fst ) elem

        --mapPath :: (Show a,Show b,Ord b,Ord a) => a -> Set b -> JoinPath b a -> Either (Set (a,b)) (JoinPath b a)
        mapPath tnew f (From t   s ) =  if tablesName tnew `S.isSubsetOf`  tablesName t
                then  Right $ From t  snew
                else  Left $ maybe S.empty S.singleton   (filterFst t f)
            where snew =  s `S.union` (S.map snd f)
        mapPath tnew f (Join ty t clause p ) = res
            where  res = case mapPath tnew  f p  of
                    Right pnew  -> Right $ Join ty t  (maybe clause (`S.insert` clause ) (filterFst t f)) pnew
                    Left accnew -> if tablesName tnew `S.isSubsetOf`  tablesName t
                        then Right $ Join ty t   (clause `S.union` accnew ) p
                        else Left $ maybe accnew (`S.insert`accnew) (filterFst t  f)



addFilterTable [] b = b
addFilterTable ff b@(Filtered fi _ ) = Filtered (fi<>ff) b
addFilterTable ff b = Filtered ff b

-- Label each table with filter clauses
specializeJoin
  :: Map Key Filter
    -> JoinPath Key Table
    -> (Map Key Filter,JoinPath Key Table )
specializeJoin f (From t s) =  (M.fromList ff , From (addFilterTable ff t) s)
    where ff = catMaybes  (fmap (\ i -> fmap (i,). (flip M.lookup) f $ i) (fmap (snd . snd) $ S.toList $ allAttrs' t))
specializeJoin f (Join ty t r p) =  (ms1,Join ty (addFilterTable ff t) r sp)
    where (ms,sp) = specializeJoin f p
          ff = catMaybes  (fmap (\ i -> fmap (i,). flip M.lookup f  $ i) (fmap (snd . snd) $ S.toList $ allAttrs' t))
          ms1 = foldr (\(i,j) s -> M.insert i  j s) ms ff

specializeJoin f i = error $ "specializeJoin " <> show f <> " --- "<> show i

addPath
  :: Monad m => [Path Key (SqlOperation Table) ]
  -> QueryT m ()
addPath  p = do
  (schema,Base k j ) <- get
  put (schema,Base k ((\(Just i)-> i) $ F.foldl' (flip joinPathL) (Just j) p))



createFilter
  :: Map Key Filter
  ->  HashSchema Key (SqlOperation Table)
  -> Table
  -> (Map Key Filter, Table)
createFilter filters schema (Base k j) = (m,Base k spec)
    where
      path = queryHash (M.keys  filters)  schema k
      Just join =  foldr joinPath (Just j) (catMaybes path)
      (m,spec) = specializeJoin filters join
createFilter filters schema (Project a t) = fmap (Project a) (createFilter filters schema t)
createFilter filters schema (Reduce  k a t) = fmap (Reduce k a) (createFilter filters schema t)

{-
createAggregate  schema key attr  old
    = Reduce (S.fromList key) (S.fromList attr) (addAggregate schema  key attr (Project (fmap Metric key) old))

addAggregate
  :: HashSchema Key (SqlOperation Table)
     -> [Key] -> [Aggregate KAttribute] -> Table -> Table
addAggregate schema key attr (Base k s) =   case   catMaybes $ queryHash key  schema k  of
                        [] -> Base k  s
                        l -> Base k  ((\(Just i)-> i) $ foldr joinPath  (Just s) l)

addAggregate schema key aggr (Project a t) =  Project (F.foldr (:) a attr )  (addAggregate schema key aggr t)
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
    paths = catMaybes $ fmap (\ti-> (\k -> Path (S.singleton ti) (FetchTable k) (S.singleton ti )) <$> M.lookup (S.singleton ti) tmap ) i
    Just res = foldr joinPath (Just $ From table (S.fromList i)) paths
    attrs = nub $ (fmap Metric $ concat $ fmap F.toList $ fmap (\ti->  baseDescKeys ((\(Just i)-> i) $ M.lookup (S.singleton ti) tmap)) i ) <> fmap Agg agg
  put (schema,Project attrs $ Base (S.fromList i) res )
  return attrs


countAll :: Monad m =>Map (Set Key) Table ->  [Key] -> QueryT m [KAttribute ]
countAll tmap i = do
  let agg = [ Aggregate [Metric $ Key "distance" Nothing (unsafePerformIO $ newUnique) (Primitive "double precision")] "sum"]
  reduce i  agg
  (schema,table) <- get
  let
    paths = catMaybes $ fmap (\ti-> (\k -> Path (S.singleton ti) (FetchTable k) (S.singleton ti )) <$> M.lookup (S.singleton ti) tmap ) i
    Just res = foldr joinPath (Just $ From table (S.fromList i)) paths
    attrs = ( fmap Metric $ concat $ fmap F.toList $ fmap (\ti->  baseDescKeys ((\(Just i)-> i) $ M.lookup (S.singleton ti) tmap)) i ) <> fmap Agg agg

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


data KV a
  = KV {kvKey  :: PK a , kvAttr ::  [a] }deriving(Functor,Foldable,Traversable)

data PK a
  = PK { pkKey:: [a], pkDescription :: [a]} deriving(Functor,Foldable,Traversable)

instance Show1 KV  where
  showsPrec1 i (KV a b ) =  showsPrec1 i a <> showsPrec1 (i + length (F.toList a)) b

instance Show1 PK where
  showsPrec1 i (PK a b ) =  showsPrec1 i a <> showsPrec1 (i + length a) b

instance Ord1 PK where
  compare1 (PK i j) (PK a b) = compare (compare1 i a ) (compare1 j b)

instance Ord1 KV where
  compare1 (KV i j) (KV a b) = compare (compare1 i a ) (compare1 j b)

instance Eq1 PK where
  eq1 (PK i j) (PK a b) = eq1 i a == eq1 j b

instance Eq1 KV where
  eq1 (KV i j) (KV a b) = eq1 i a == eq1 j b

instance Eq a => Eq (PK a) where
  i == j = pkKey i == pkKey j

instance Eq a => Eq (KV a) where
  i == j = kvKey i == kvKey j

instance Ord a => Ord (PK a) where
  compare i j = compare (pkKey i) (pkKey j)

instance Ord a => Ord (KV a) where
  compare i j = compare (kvKey i) (kvKey j)

instance Show a => Show (PK a)  where
  show (PK i []) = intercalate "," $ fmap show i
  show (PK i j ) = intercalate "," (fmap show i) <> "-"<> intercalate  "," ( fmap show j)

instance Show a => Show (KV a)  where
  show (KV i []) =  show i
  show (KV i j ) = (show i) <> "|"<> intercalate  "," ( fmap show j)


recursePath invSchema (Path i (FetchTable t) e)  = Path i (FetchTable nextT ) e : recursePaths invSchema nextT
  where nextT@(Raw _ _ _ _ fk _ ) = (\(Just i)-> i) (M.lookup t (invSchema))
recursePath invSchema (Path i (FKJoinTable w ks t) e)  = Path i (FKJoinTable backT ks nextT ) e : recursePaths invSchema nextT
  where nextT@(Raw _ _ _ _ fk _ ) = (\(Just i)-> i) (M.lookup t (invSchema))
        backT = (\(Just i)-> i) (M.lookup w (invSchema))

recursePaths invSchema (Raw _ _ _ _ fk _ )  = concat $ recursePath invSchema <$> S.toList fk

newtype TB1 a = TB1 {unTB1 :: (KV (TB a)) }deriving(Eq,Ord,Show,Functor,Foldable,Traversable)

instance Apply TB1 where
  TB1 a <.> TB1 a1 =  TB1 (getCompose $ Compose a <.> Compose a1)

instance Apply KV where
  KV pk i <.> KV pk1 i1 = KV (pk <.> pk1) (getZipList $ ZipList i <.> ZipList i1)

instance Apply PK where
  PK i j <.> PK i1 j1 = PK (getZipList $ ZipList i <.> ZipList i1 ) ( getZipList $ ZipList j <.> ZipList j1)

instance Apply TB where
  Attr a <.>  Attr a1 = Attr $ a a1
  FKT l t <.> FKT l1 t1 = FKT (l <.> l1) (t <.> t1)

data TB a
  = FKT [a] (TB1 a)
  | Attr a
  deriving(Eq,Ord,Show,Functor,Foldable,Traversable)

tbPK (TB1 (KV (PK i _)  _)) = concat $ fmap go i
  where go (FKT _ tb) = tbPK tb
        go (Attr a) = [a]

data Tag = TAttr | TPK

allKVRec  (TB1 (KV (PK k d) e ))= F.foldr zipPK (KV (PK [] []) []) $ (go TPK (\i -> KV (PK i []) [])  <$> k) <> (go TAttr (\i-> KV (PK [] i) [] ) <$> d) <> ( go TAttr (\i-> KV (PK [] []) i) <$> e)
  where zipPK (KV (PK i j) k) (KV (PK m n) o) = KV (PK (i <> m) (j <> n)) (k <> o )
        go  TAttr l (FKT _ tb) =  l $ F.toList $ allKVRec  tb
        go  TPK l (FKT _ tb) =  allKVRec  tb
        go  _ l (Attr a) = l [a]


allPKRec  (TB1 (KV (PK k d) i ))=  F.foldr zipPK (PK [] []) $ (go (flip PK []) <$> k) <> (go (PK []) <$> d)
  where zipPK (PK i j) (PK m n) = (PK (i <> m) (j <> n))
        go l (FKT _ tb) = allPKRec tb
        go l (Attr a) = l [a]


allRec i t = fmap snd $ allAliasedRec i t
allAliasedRec i t = tb1Rec False PathRoot i t

tb1Rec isOpt p  invSchema ta@(Raw _ _ k desc fk attr) =
  let
      baseCase = KV (PK (fun k) (fun (S.fromList $ F.toList desc)))  (fun (maybe attr (`S.delete` attr) desc))
      leftFst True keys = fmap (fmap (\((Key a al b c  e) ) -> ( Key a al b c  (KOptional e)))) keys
      leftFst False keys = keys
      fun items = fmap Attr (fmap (p,) $ F.toList $ items `S.difference` fkSet ) <> (fkCase invSchema isOpt p <$> filter (\(Path ifk _ _) -> ifk `S.isSubsetOf` items ) (F.toList fk) )
      fkSet = S.unions $  fmap (\(Path ifk _ _) -> ifk)  $S.toList fk
  in leftFst isOpt  $ TB1 baseCase

fkCase invSchema isOpt p (Path ifk (FKJoinTable bt kv nt)  o ) = FKT  ((p,) <$>S.toList ifk)  {- $ fmap substBind -} (tb1Rec isOptional (aliasKeyValue ifk ) invSchema ((\(Just i)-> i) (M.lookup nt  invSchema )))
            where isOptional = any (isKOptional . keyType ) (F.toList ifk)
                  bindMap = M.fromList $ fmap swap kv
                  aliasKeyValue k
                     =  (PathCons $ S.map (,p) k)
                  substBind k = case M.lookup k bindMap of
                                    Just i -> i
                                    Nothing -> k


projectAllRec'
     :: Monad m => Map Text Table ->  QueryT m (TB1 KAttribute)
projectAllRec' invSchema =  do
  (schema,table@(Base _ t  )) <- get
  let
      ta@(Raw _ _ k _ _ _ ) = atBase id table
      table1 = case  M.lookup k schema of
        Just pv -> Base k $ splitJoins  ((\(Just i)-> i) $ F.foldl' (flip joinPath) (Just t)  ( recursePaths invSchema ta))
        Nothing -> table
      attrs =  Metric . alterName <$> (allAliasedRec invSchema ta )
      aliasMap =   fmap fst $ M.fromList $ aliasJoin table1
      alterName ak@(p,Key k al a b c ) = (Key k (Just $ justError ("lookupAlias "  <> show ak <> " " <> show aliasMap  <> T.unpack (showTable table1 )  ) $ M.lookup ak aliasMap ) a b c )
  put (schema,Project (F.toList attrs )  table1 )
  return {-$ trace ("projectDescAllRec: " <> show attrs )-} attrs


justError e (Just i) = i
justError e  _ = error e

getTableKV (Raw _ _ pk desc _ attrs) = KV (PK (F.toList pk) (F.toList desc) ) (F.toList $ maybe attrs (`S.delete` attrs) desc )

projectTableAttrs
     :: Monad m => Table -> QueryT m (KV  KAttribute)
projectTableAttrs r@(Raw _ _ pk desc _ _) =  do
  (schema,Base k  table) <- get
  let
      table1 = Base k $ splitJoins table
      kv =  fmap (\i-> Metric $ alterName . (\(Just i)-> i) $ F.find (\k-> i == snd k ) (M.keys aliasMap) ) $ getTableKV r
      aliasMap =  M.fromList $ aliasJoin  table1
      alterName ak@(p,Key k al a b c ) = (Key k (Just $ fst $justError ("lookupAlias "  <> show ak <> " " <> show aliasMap  <> T.unpack (showTable table1 )  ) $ M.lookup ak aliasMap ) a b c )
  put (schema,Limit (Project (F.toList kv) $ table1) 500)
  return {- trace ("projectTableAttrs : " <> show  kv ) -}  kv


data AliasPath a
    = PathCons (Set (a,AliasPath a))
    | PathRoot
    deriving(Show,Eq,Ord,Foldable)

allAttrs' :: Table -> Set (AliasPath Key,(Table,Key))
allAttrs' r@(Raw _ _ _ _ _ _) = S.map ((PathRoot,) . (r,)) $ rawKeys r
allAttrs' (Limit p _ ) = allAttrs' p
allAttrs' (Filtered _ p) = allAttrs' p
allAttrs' (Base _ p) =  snd $  from allAttrs' p
  where from f (From t pk ) = {-traceShow ("from " <> show t <> " " <> show pk <> " " <> show sm1 )-} (sm1,ft)
          where ft = f t
                sm1 =  foldr (\i m -> M.insert (snd $ snd i) PathRoot m ) M.empty (S.toList ft) :: Map Key (AliasPath Key)
        from f s@(SplitJoin _ t  rel p) =  (sm , (foldr (<>) S.empty $ fmap (\(n,_) -> S.map (\(_,(ta,k))-> (pth $  n,(alterTableName (<> fullTableName n  ) ta,k))) (f t) ) rel )  <> sp)
          where
                (sm,sp) = from f p
                -- pth1 = fmap (\(n,_) -> S.map (\(_,(ta,k))-> ([ pth $ S.singleton n],(alterTableName (<> (keyValue n) ) ta,k))) (f t) ) rel
                pth n = PathCons (S.map (\nk -> (nk,(justError $ "allAttrs' pathSplit KEY " <> show nk <> " MAP " <> show sm  <> " JOIN " <> show s )$ M.lookup nk sm) )n )
                ft = f t
        from f (Join ty t r p) = (sm1,S.map (\(_,(ta,k))-> (pth ,(ta,k))) ft  <>   sp)
          where n = S.map (justError "allAttrs' filterSet") $ S.filter isJust $ S.map (\i -> M.lookup i  (M.fromList $ concat $ fmap (fmap swap . S.toList .snd) $ S.toList r) ) pk
                (sm,sp) = from f p
                sm1 =  foldr (\i m -> M.insert (snd $ snd i) pth  m ) sm (S.toList ft)
                pth = PathCons (S.map (\nk -> (nk,(justError "allAttrs' pathLeft") (M.lookup nk sm)) ) n )
                ft = f t
                pk = atBase (\(Raw _ _ p _ _ _) -> p) t



rawKeys r = S.union (rawPK r ) (rawAttrs r)



newtype QueryT m a
  = QueryT {runQueryT :: StateT  (HashSchema Key (SqlOperation Table), Table)  m a} deriving(Functor,Applicative,Monad,MonadState (HashSchema Key (SqlOperation Table), Table) )

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
        lvertices = fmap (\e -> ((\(Just i)-> i) (M.lookup e v),e)) set
        ledges = fmap (\e -> case pbound e of
                            (t,h) -> ((\(Just i)-> i) (M.lookup t v) ,(\(Just i)-> i) (M.lookup h v) ,e)) (fmap snd $ M.toList $ fmap head $ edges g)

zipWithTF g t f = snd (mapAccumL map_one (F.toList f) t)
  where map_one (x:xs) y = (xs, g y x)



instance IsString Showable where
  fromString i = SText (T.pack i)

instance Num Showable where
  SNumeric i +  SNumeric j = SNumeric (i + j)
  SDouble i +  SDouble j = SDouble (i + j)
  SNumeric i *  SNumeric j = SNumeric (i * j)
  SDouble i *  SDouble j = SDouble (i * j)
  fromInteger i = SNumeric $ fromIntegral i
  negate (SNumeric i) = SNumeric $ negate i
  abs (SNumeric i) = SNumeric $ abs i
  abs (SDouble i) = SDouble $ abs i
  signum (SNumeric i) = SNumeric $ signum i

instance Fractional Showable where
  fromRational i = SDouble (fromRational i)
  recip (SDouble i) = SDouble (recip i)

groupSplit f = fmap (\i-> (f $ head i , i)) . groupWith f

