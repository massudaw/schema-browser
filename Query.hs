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
{-# LANGUAGE TemplateHaskell #-}

module Query where

import Warshal
import Control.Lens.TH
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
import qualified Data.Interval as Interval
import Data.Monoid hiding (Product)
import Data.Functor.Product
import Data.Bifunctor

import qualified Data.Text.Lazy as T
import qualified Data.ExtendedReal as ER

import GHC.Int

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
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Map (Map)
import Data.Set (Set)
import Control.Monad.State
import Control.Monad.State.Class
import System.Environment ( getArgs )
import Text.Parsec hiding(label,State)
import Text.Parsec.String
import Text.Printf ( printf )
import Data.Text.Lazy(Text)
import Debug.Trace
import GHC.Stack

import Data.Unique

instance Ord a => Ord (Interval.Interval a ) where
  compare i j = compare (Interval.upperBound i )  (Interval.upperBound j)

textToPrim "character varying" = PText
textToPrim "name" = PText
textToPrim "varchar" = PText
textToPrim "text" = PText
textToPrim "character" = PText
textToPrim "char" = PText
textToPrim "double precision" = PDouble
textToPrim "numeric" = PDouble
textToPrim "float8" = PDouble
textToPrim "int4" = PInt
-- textToPrim "bank_account" = PBackAccount
textToPrim "cnpj" = PCnpj
textToPrim "sql_identifier" =  PText
textToPrim "cpf" = PCpf
textToPrim "int8" = PInt
textToPrim "integer" = PInt
textToPrim "bigint" = PInt
textToPrim "boolean" = PBoolean
textToPrim "smallint" = PInt
textToPrim "timestamp without time zone" = PTimestamp
textToPrim "interval" = PInterval
textToPrim "date" = PDate
textToPrim "POINT" = PPosition
textToPrim "LINESTRING" = PLineString
textToPrim "box3d" = PBounding
textToPrim i = error $ "no case for type " <> T.unpack i

data PK a
  = PK { _pkKey:: [a], _pkDescription :: [a]} deriving(Functor,Foldable,Traversable,Show)

data KV a
  = KV {_kvKey  :: PK a , _kvAttr ::  [a] }deriving(Functor,Foldable,Traversable,Show)


data Labeled l v
  = Labeled
  { label :: l
  , labelValue :: v
  }
  | Unlabeled
  { labelValue :: v
  } deriving(Eq,Show,Ord,Foldable,Functor,Traversable)

data AliasPath a
    = PathCons (Set (a,AliasPath a))
    | PathRoot
    deriving(Show,Eq,Ord,Foldable)


isReflexive (FKT _  r _ ) = r
isReflexive (LFKT _  r _ ) = r
isReflexive _ = True

data TBRel  i
  = TBLeft (Maybe (TBRel i))
  | TBIdent i
  | TBArray [TBRel i]

data TB a
  = FKT
    { _tbref :: ! [TB a]
    , _reflexive :: ! Bool
    , _fkttable :: ! (TB1 a)
    }
  | LFKT
    { _ltbref :: ! [Labeled Text (TB a)]
    , _reflexive :: ! Bool
    , _fkttable :: ! (TB1 a)
    }
  | AKT
    { _tbref :: ! [TB a]
    , _reflexive :: ! Bool
    , _akttable :: ! [TB1 a]
    }
  | LAKT
    { _ltbreef :: ! [Labeled Text (TB a)]
    , _reflexive :: ! Bool
    , _akttable :: ! [TB1 a]
    }
  | Attr
    { _tbattr :: ! a
    }
  deriving(Eq,Ord,Show,Functor,Foldable,Traversable)


data TB1 a
  = TB1 {_unTB1 :: ! (KV (TB a)) }
  | LB1 {unLB1 :: ! (KV (Labeled Text (TB a))) }
  deriving(Eq,Ord,Show,Functor,Foldable,Traversable)



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
   | PCnpj
   | PCpf
   | PLineString
   deriving(Show,Eq,Ord)


data KType a
   = Primitive a
   | KSerial (KType a)
   | KArray (KType a)
   | KInterval (KType a)
   | KOptional (KType a)
   | KTable [KType a]
   deriving(Eq,Ord,Functor)

isSerial (KSerial _) = True
isSerial _ = False
isPrim (Primitive i) = True
isPrim i = False
isOptional (KOptional _) = True
isOptional _ = False
isArray (KArray _) = True
isArray (KOptional i) = isArray i
isArray _ = False

instance Show (KType KPrim) where
  show =  showTy show

instance Show (KType Text) where
  show = T.unpack . showTy id

showTy f (Primitive i ) = f i
showTy f (KArray i) = "{" <>  showTy f i <> "}"
showTy f (KOptional i) = showTy f i <> "*"
showTy f (KInterval i) = "(" <>  showTy f i <> ")"
showTy f (KSerial i) = showTy f i <> "?"


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
   -- show  =  T.unpack .showKey
showKey k  = keyValue k  <>  maybe "" ("-"<>) (keyTranslation k) <> {-"::" <> T.pack ( show $ hashUnique $ keyFastUnique k )<> -} "::"  <> showTy id (keyType k)


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
  = SText !Text
  | SNumeric !Int
  | SBoolean !Bool
  | SDouble !Double
  | STimestamp !LocalTimestamp
  | SPInterval !DiffTime
  | SPosition !Position
  | SBounding !Bounding
  | SLineString !LineString
  | SDate !Date
  | SSerial !(Maybe Showable)
  | SOptional !(Maybe Showable)
  | SComposite !(Vector Showable)
  | SInterval !(Interval.Interval Showable)
  | SScopedKeySet !(Map Key Showable)
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
renderFilter (table ,name,Category i) = tableName table <> "." <> keyValue name <> " IN( " <>  T.intercalate "," (fmap (\s -> "'" <> T.pack (renderShowable $ head (_pkKey s)) <> "'" ) $ S.toList i) <> ")"
renderFilter (table ,name,And i) =  T.intercalate " AND "  (fmap (renderFilter . (table ,name,)) i)
-- renderFilter (table ,name,RangeFilter i) =  tableName table <> "." <> keyValue name <> " BETWEEN " <> T.intercalate " AND "  (fmap (\s -> "'" <> T.pack (renderShowable$ head (_pkKey s)) <> "'" ) [Interval.inf i,Interval.sup i])

data SqlOperation a
  = FetchTable a
  | FKJoinTable a [(Key,Key)] a
  deriving(Eq,Ord,Show,Functor)



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
           , rawFKS ::  (Set (Path (Set Key) (SqlOperation Text)))
           , rawAttrs :: (Set Key)
           }
    |  Filtered [(Key,Filter)] Table
    |  Project [ KAttribute ] Table
    |  Reduce (Set Key) (Set (Aggregate (KAttribute ) ) )  Table
    |  Limit Table Int
     deriving(Eq,Ord)

instance Show Table where
  show = T.unpack . tableName

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
renderShowable (SInterval i)  = showInterval i
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
  shw (SInterval a) = showInterval a
  shw (SPInterval a) = show a
  shw (SComposite a) = intercalate "," $ F.toList (fmap shw a)

showInterval i | i == Interval.empty = show i
showInterval (Interval.Interval (ER.Finite i,j) (ER.Finite l,m) ) = ocl j <> renderShowable i <> "," <> renderShowable l <> ocr m
    where
      ocl j = if j then "[" else "("
      ocr j = if j then "]" else ")"



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

-- transform a multiple intersecting join in independent ones
splitJoins j@(From p r ) = j
splitJoins j@(Join ty b r p) = case hasSplit of
                                     True -> Join ty b r (splitJoins p)
                                     False ->  SplitJoin ty b   mapK (splitJoins p)
      where
        mapK :: [(Set Key,[(Table,Set (Key, Key))])]
        mapK = M.toList $ M.fromListWith (<>) $ fmap (fmap pure) $ concat $ concat $ fmap snd $ M.toList mapkPre
        mapkPre :: Map (Set Key) ([[(Set Key,(Table,Set (Key,Key)))]])
        mapkPre = fmap (fmap (\(i,j)-> fmap (i,) j) . M.toList . M.fromListWith (<>)) groupJoins
        groupJoins ::  Map (Set Key) [(Set Key,[(Table,Set (Key,Key))])]
        groupJoins =  M.fromListWith (<>) ((\f@(t,a)-> ( S.map snd a , [( S.map fst a , [( t , a )] )] )) <$> S.toList r)
        -- hasSplit ::  Map (Set Key) [(Set Key,[(Table,Set (Key,Key))])]
        hasSplit =   all (\i -> length (snd i) <2) $ M.toList $  M.fromListWith (<>) ((\f@(t,a)-> (  ( S.map snd a , [( t , a )] ) )) <$> S.toList r)
splitJoins j = j


aliasJoin b@(Base k1 p) = zipWith (\i (j,l)-> (j,(i,l))) (T.pack . ("v" <> ). show <$> [0..]) aliasMap
  where
    aliasMap =  fmap (\i -> ( (\(p,(t,k))-> (p,k))i,i)) attrs
    attrs = S.toList $ allAttrs' b

fullTableName = T.intercalate "_" . fmap (\k -> keyValue k <> (T.pack $ show $ hashUnique (keyFastUnique k))) . S.toList


getPrim i@(Primitive _ ) = textToPrim <$> i
getPrim (KOptional j) =  getPrim j
getPrim (KSerial j) =  getPrim j
getPrim (KArray j) =  getPrim j
getPrim (KInterval j) =  getPrim j

inner b l m = l <> b <> m
intersectionOp (KOptional i) (KOptional j) = intersectionOp i j
intersectionOp i (KOptional j) = intersectionOp i j
intersectionOp (KOptional i) j = intersectionOp i j
intersectionOp (KInterval i) (KInterval j )  = inner " = "
intersectionOp (KArray i) (KArray j )  = inner " = "
intersectionOp (KInterval i) j
    | getPrim i == getPrim j =  inner " @> "
    | otherwise = error $ "wrong type intersectionOp " <> show i <> " /= " <> show j
intersectionOp i (KInterval j)
    | getPrim i == getPrim j = inner " <@ "
    | otherwise = error $ "wrong type intersectionOp " <> show i <> " /= " <> show j
intersectionOp (KArray i ) j
    | fmap textToPrim i == getPrim j = (\j i -> i <> " IN (select * from unnest("<> j <> ") ) ")
    | otherwise = error $ "wrong type intersectionOp {*} - * " <> show i <> " /= " <> show j
intersectionOp j (KArray i )
    | getPrim i == getPrim j = (\ i j  -> i <> " IN (select * from unnest("<> j <> ") ) ")
    | otherwise = error $ "wrong type intersectionOp * - {*} " <> show j <> " /= " <> show i
intersectionOp i j = inner " = "

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
                | any (isKOptional . keyType) (concat $ fmap fst . S.toList .  snd <$> r ) = l <> " LEFT JOIN " <> joinPredicate2 b ir
                | otherwise =  l <> " JOIN " <> joinPredicate2 b ir
              joinPredicate2 b (i,r)  = showTable b <> " AS " <> tempName  <> " ON " <> T.intercalate " AND " (fmap (\(t,fs) -> T.intercalate " AND " $ fmap (\f-> intersectionOp ( keyType (fst f)) (keyType (snd f)) (tableName t <> "." <> keyValue (fst f)) (tempName <> "." <> keyValue (snd f))) $ S.toList fs )  r )
                where tempName = tableName b <> fullTableName  i
    joinQuerySet (Join ty b  r p)  = joinType (joinQuerySet p)  r
        where
            joinType  l ir
                | ty == JLeft = l <> " LEFT JOIN " <> joinPredicate b ir
                | otherwise =  l <> " JOIN " <> joinPredicate b ir
            joinPredicate  b  r  = showTable b <> " ON " <> T.intercalate " AND " (fmap (\(t,fs) -> T.intercalate " AND " $ fmap (\f-> intersectionOp (keyType (fst f)) (keyType (snd f)) (tableName t <> "." <> keyValue (fst f) ) (tableName b <> "." <> keyValue (snd f)) )  $ S.toList fs )  $ S.toList r )

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
  = TableModification (Maybe Int) Table (Modification Key b)
  deriving(Eq,Show,Functor)

data Modification a b
  = Edit (Maybe [(a,b)]) (Maybe [(a,b)])
  | Insert (Maybe [(a,b)])
  | Delete (Maybe [(a,b)])
  deriving(Eq,Show,Functor)


update
  :: ToField b =>
     Connection -> [(Key, b)] -> [(Key, b)] -> Table -> IO (GHC.Int.Int64,TableModification b)
update conn kv kold t@(Raw sch tbl pk _ _ _) = fmap (,TableModification Nothing t (Edit (Just skv) (Just koldPk ) )) $ execute conn (fromString $ traceShowId $ T.unpack up)  (fmap snd skv <> fmap snd koldPk)
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
        kv = nub $ filter (\(k,_) -> memberPK k || memberAttr k || memberDesc k) $    kva
        memberPK k = S.member (keyValue k) (S.fromList $ fmap  keyValue $ S.toList $ S.filter (not . isSerial . keyType ) pk)
        memberAttr k = S.member (keyValue k) (S.fromList $ fmap  keyValue $ S.toList attr)
        memberDesc k = S.member (keyValue k) (S.map keyValue $ maybe S.empty S.singleton $ rawDescription t )

getKey  (Raw sch tbl pk desc fk attr) k =  M.lookup k table
  where table = M.fromList $ fmap (\i-> (keyValue i, i)) $ S.toList (pk <> attr)

isEmptyShowable (SOptional Nothing ) = True
isEmptyShowable (SSerial Nothing ) = True
isEmptyShowable i = False


insert conn kva t@(Raw sch tbl pk desc _ attr ) = execute conn (fromString $ traceShowId $ T.unpack $ "INSERT INTO " <> rawFullName t  <>" ( " <> T.intercalate "," (fmap (keyValue . fst) kv) <> ") VALUES (" <> T.intercalate "," (fmap (const "?") kv) <> ")") (fmap snd kv)
  where kv = filter (\(k,_) -> S.member k (maybe S.empty S.singleton desc )|| S.member k pk || S.member k attr ) $ filter ( not . isSerial . keyType . fst)  kvb
        kvb = catMaybes $ fmap (\i-> fmap (,snd i) . getKey t . keyValue . fst $ i  ) kva

dropTable r@(Raw sch tbl _ _ _ _ )= "DROP TABLE "<> rawFullName r

rawFullName (Raw (sch,tt) tbl _ _ _ _) = sch <> "." <> tbl

createTable r@(Raw sch tbl pk _ fk attr) = "CREATE TABLE " <> rawFullName r  <> "\n(\n\t" <> T.intercalate ",\n\t" commands <> "\n)"
  where commands = (renderAttr <$> S.toList attr ) <> [renderPK] <> fmap renderFK (S.toList fk)
        renderAttr k = keyValue k <> " " <> renderTy (keyType k) <> if  (isKOptional (keyType k)) then "" else " NOT NULL"
        renderKeySet pk = T.intercalate "," (fmap keyValue (S.toList pk ))
        renderTy (KOptional ty) = renderTy ty <> ""
        renderTy (KSerial ty) = renderTy ty <> ""
        renderTy (KInterval ty) = renderTy ty <> ""
        renderTy (KArray ty) = renderTy ty <> "[] "
        renderTy (Primitive ty ) = ty
        renderPK = "CONSTRAINT " <> tbl <> "_PK PRIMARY KEY (" <>  renderKeySet pk <> ")"
        renderFK (Path origin (FKJoinTable _ ks table) end) = "CONSTRAINT " <> tbl <> "_FK_" <> table <> " FOREIGN KEY " <>  renderKeySet origin <> ") REFERENCES " <> table <> "(" <> renderKeySet end <> ")  MATCH SIMPLE  ON UPDATE  NO ACTION ON DELETE NO ACTION"

joinPath (Path i (FKJoinTable _ ks ll ) j) (Just p) = Just $ addJoin  ll (S.fromList ks)  p
joinPath (Path i (FetchTable ll ) j) (Just p) = Just $ addJoin  ll ((S.fromList $ zip (S.toList i) (S.toList j)))  p
-- joinPath (Path i (FetchTable ll) j) Nothing  =  Just $ From ll   (i `S.union` j)
joinPath (ComposePath i (l,ij,k) j ) m = F.foldl' (flip joinPath)  m  ((S.toList l)  <> ( S.toList k))

joinPathL (Path i (FKJoinTable ll  ks _ ) j) (Just p) = Just $ addJoin  ll (S.fromList $ fmap swap ks)  p
joinPathL (Path i (FetchTable ll ) j) (Just p) = Just $ addJoin  ll ((S.fromList $ zip (S.toList i) (S.toList j)))  p
joinPathL (ComposePath i (l,ij,k) j ) m = F.foldr joinPathL  m  ((S.toList l)  <> ( S.toList k))

makeOpt (Key a b c d ty) = (Key a b c d (KOptional ty))

addJoin
  :: Table
  -> Set (Key, Key) -> JoinPath Key Table -> JoinPath Key Table
addJoin tnew f p = case mapPath tnew  f p of
            -- Add new case
            Left (Left accnew) -> case any (isKOptional . keyType) (concat $ fmap fst . S.toList .  snd <$> S.toList accnew) of
                             True ->  Join JLeft tnew  accnew  p
                             False ->  Join JInner tnew accnew  p
            -- Just update with new joins
            Left (Right i) -> i
            Right i -> i
    where
        filterFst JInner t elem=  if S.null filtered then Nothing else Just (t,filtered)
          where filtered = S.filter ((`S.member` (S.map (snd.snd) $ allAttrs' t)) . fst ) elem
        filterFst JLeft t elem=  if S.null filtered then Nothing else Just (t,filtered)
          where filtered = S.map (\(i,j) -> (makeOpt i ,j) )$ S.filter ((`S.member` (S.map (snd.snd) $ allAttrs' t)) . fst ) elem

        --mapPath :: (Show a,Show b,Ord b,Ord a) => a -> Set b -> JoinPath b a -> Either (Set (a,b)) (JoinPath b a)
        mapPath tnew f (From t   s ) =  if tablesName tnew `S.isSubsetOf`  tablesName t
                then  Right $ From t  snew
                else  Left $ Left $ maybe S.empty S.singleton   (filterFst JInner t f)
            where snew =  s `S.union` (S.map snd f)
        mapPath tnew f (Join ty t clause p ) = res
            where  res = case mapPath tnew  f p  of
                    Right pnew  -> case (filterFst ty t f) of
                        Just i -> Right $ Join ty t  (i `S.insert` clause )  pnew
                        Nothing -> Right $ Join ty t  clause pnew
                    Left (Right (Join ty1 t1 clause1 p1 )) ->
                        Left $ Right (Join ty1 t1 (maybe clause1 (`S.insert` clause1) (filterFst ty t f))(Join ty t clause p1))
                    Left (Left accnew) -> if tablesName tnew `S.isSubsetOf`  tablesName t
                        then Left $  Right $ Join ty t  (clause `S.union` accnew ) p
                        else Left $ case filterFst ty t f of
                                    Just i -> Left $ S.insert i accnew
                                    Nothing -> Left accnew




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
  :: Monad m => [Path (Set Key) (SqlOperation Table) ]
  -> QueryT m ()
addPath  p = do
  (schema,Base k j ) <- get
  put (schema,Base k ((\(Just i)-> i) $ F.foldl' (flip joinPathL) (Just j) p))


type HashQuery =  HashSchema (Set Key) (SqlOperation Table)
type PathQuery = Path (Set Key) (SqlOperation Table)

createFilter
  :: Map Key Filter
  ->  HashQuery
  -> Table
  -> (Map Key Filter, Table)
createFilter filters schema (Base k j) = (m,Base k spec)
    where
      path = queryHash (fmap S.singleton $ M.keys  filters)  schema k
      Just join =  foldr joinPath (Just j) (concat $ catMaybes path)
      (m,spec) = specializeJoin filters join
createFilter filters schema (Project a t) = fmap (Project a) (createFilter filters schema t)
createFilter filters schema (Reduce  k a t) = fmap (Reduce k a) (createFilter filters schema t)

{-
createAggregate  schema key attr  old
    = Reduce (S.fromList key) (S.fromList attr) (addAggregate schema  key attr (Project (fmap Metric key) old))

addAggregate
  :: HashQuery
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

{-
instance Show1 KV  where
  showsPrec1 i (KV a b ) =  showsPrec1 i a <> showsPrec1 (i + length (F.toList a)) b

instance Show1 PK where
  showsPrec1 i (PK a b ) =  showsPrec1 i a <> showsPrec1 (i + length a) b
-}
instance Ord1 PK where
  compare1 (PK i j) (PK a b) = compare (compare1 i a ) (compare1 j b)

instance Ord1 KV where
  compare1 (KV i j) (KV a b) = compare (compare1 i a ) (compare1 j b)

instance Eq1 PK where
  eq1 (PK i j) (PK a b) = eq1 i a == eq1 j b

instance Eq1 KV where
  eq1 (KV i j) (KV a b) = eq1 i a == eq1 j b

instance Eq a => Eq (PK a) where
  i == j = _pkKey i == _pkKey j

instance Eq a => Eq (KV a) where
  i == j = _kvKey i == _kvKey j

instance Ord a => Ord (PK a) where
  compare i j = compare (_pkKey i) (_pkKey j)

instance Ord a => Ord (KV a) where
  compare i j = compare (_kvKey i) (_kvKey j)
{-
instance Show a => Show (PK a)  where
  show (PK i []) = intercalate "," $ fmap show i
  show (PK i j ) = intercalate "," (fmap show i) <> "-"<> intercalate  "," ( fmap show j)

instance Show a => Show (KV a)  where
  show (KV i []) =  show i
  show (KV i j ) = (show i) <> "|"<> intercalate  "," ( fmap show j)
-}
instance Apply TB1 where
  TB1 a <.> TB1 a1 =  TB1 (getCompose $ Compose a <.> Compose a1)

instance Apply KV where
  KV pk i <.> KV pk1 i1 = KV (pk <.> pk1) (getZipList $ ZipList i <.> ZipList i1)

instance Apply PK where
  PK i j <.> PK i1 j1 = PK (getZipList $ ZipList i <.> ZipList i1 ) ( getZipList $ ZipList j <.> ZipList j1)

instance Apply TB where
  Attr a <.>  Attr a1 = Attr $ a a1
  FKT l i t <.> FKT l1 i1 t1 = FKT (zipWith (<.>) l   l1) (i && i1)  (t <.> t1)
  AKT l i t <.> AKT l1 i1 t1 = AKT (zipWith (<.>) l   l1) (i && i1 ) (getZipList $ liftF2 (<.>) (ZipList t) (ZipList t1))
  l <.> j = error  "cant apply"

unIntercalate :: ( Char -> Bool) -> String -> [String]
unIntercalate pred s                 =  case dropWhile pred s of
                                "" -> []
                                s' -> w : unIntercalate pred s''
                                      where (w, s'') =
                                             break pred s'

tbPK (TB1 (KV (PK i _)  _)) = concat $ fmap go i
  where go (FKT _ _ tb) = tbPK tb
        go (Attr a) = [a]

data Tag = TAttr | TPK

allKVRec  (TB1 (KV (PK k d) e ))= F.foldr zipPK (KV (PK [] []) []) $ (go TPK (\i -> KV (PK i []) [])  <$> k) <> (go TAttr (\i-> KV (PK [] i) [] ) <$> d) <> ( go TAttr (\i-> KV (PK [] []) i) <$> e)
  where zipPK (KV (PK i j) k) (KV (PK m n) o) = KV (PK (i <> m) (j <> n)) (k <> o )
        go  TAttr l (FKT _ _ tb) =  l $ F.toList $ allKVRec  tb
        go  TPK l (FKT _ _ tb) =  allKVRec  tb
        go  TAttr l (AKT _ _ tb) = l $ concat $  F.toList . allKVRec <$> tb
        go  _ l (Attr a) = l [a]


allPKRec  (TB1 (KV (PK k d) i ))=  F.foldr zipPK (PK [] []) $ (go (flip PK []) <$> k) <> (go (PK []) <$> d)
  where zipPK (PK i j) (PK m n) = (PK (i <> m) (j <> n))
        go l (FKT _ _ tb) = allPKRec tb
        go l (Attr a) = l [a]




allAliasedRec i t = tb1Rec False PathRoot i t

tb1Rec isOpt p  invSchema ta@(Raw _ _ k desc fk attr) =
  let
      baseCase = KV (PK (fun k) (fun (S.fromList $ F.toList desc)))  (fun (maybe attr (`S.delete` attr) desc))
      leftFst True keys = fmap (fmap (\((Key a al b c  e) ) -> ( Key a al b c  (KOptional e)))) keys
      leftFst False keys = keys
      fun items = fmap Attr (fmap (p,) $ F.toList $ items `S.difference` fkSet ) <> (fkCase invSchema isOpt p <$> filter (\(Path ifk _ _) -> ifk `S.isSubsetOf` items ) (F.toList fk) )
      fkSet = S.unions $  fmap (\(Path ifk _ _) -> ifk)  $S.toList fk
  in leftFst isOpt  $ TB1 baseCase


fkCase invSchema isOpt p (Path ifk (FKJoinTable bt kv nt)  o ) = FKT  (Attr. (p,) <$>S.toList ifk) True (tb1Rec isOptional (aliasKeyValue ifk ) invSchema ((\(Just i)-> i) (M.lookup nt  invSchema )))
            where isOptional = any (isKOptional . keyType ) (F.toList ifk)
                  bindMap = M.fromList $ fmap swap kv
                  aliasKeyValue k =  (PathCons $ S.map (,p) k)
                  substBind k = case M.lookup k bindMap of
                                    Just i -> i
                                    Nothing -> k

recursePath invSchema (Path i (FetchTable t) e)  = Path i (FetchTable nextT) e : recursePaths invSchema nextT
  where nextT@(Raw _ _ _ _ fk _ ) = (\(Just i)-> i) (M.lookup t (invSchema))
recursePath invSchema (Path i (FKJoinTable w ks t) e)  = Path i (FKJoinTable backT ks nextT) e : recursePaths invSchema nextT
  where nextT@(Raw _ _ _ _ fk _ ) = (\(Just i)-> i) (M.lookup t (invSchema))
        backT = (\(Just i)-> i) (M.lookup w (invSchema))

type QueryRef = State ((Int,Map Int Table ),(Int,Map Int Key))

recursePaths invSchema (Raw _ _ _ _ fk _ )  = concat $ recursePath invSchema <$> S.toList fk


rawLPK t@(Labeled b i ) = (t,) . (\i -> Labeled (keyValue i) (Attr i) ) <$> S.toList (rawPK i)

tableToKV r =   do
  KV (PK (S.toList (rawPK r)) (maybeToList (rawDescription r)) ) (S.toList (rawAttrs r))

labelTable i = do
   t <- tname i
   name <- Tra.traverse (kname t) (tableToKV i)
   let query = "(SELECT " <>  T.intercalate "," (F.toList $ aliasKeys <$> name) <> " FROM " <> aliasTable t <> ") as " <> label t
   return (t,LB1 $ fmap snd $ name,query)


isPairReflexive (Primitive i ) (KInterval (Primitive j)) | i == j = False
isPairReflexive (Primitive j) (KArray (Primitive i) )   = False
isPairReflexive (Primitive i ) (Primitive j) | i == j = True
isPairReflexive (KOptional i ) j = isPairReflexive i j
isPairReflexive i  (KOptional j) = isPairReflexive i j
isPairReflexive i  (KSerial j) = isPairReflexive i j
isPairReflexive (KArray i )   j = True
isPairReflexive i j = error $ "isPairReflexive " <> show i <> " - "<> show  j

isPathReflexive (FKJoinTable _ ks _)
  = all id $ fmap (\(i,j)-> isPairReflexive (textToPrim <$> keyType i ) (textToPrim <$> keyType j)) ks

intersectionOpK i j = intersectionOp (keyType i ) (keyType j)


recursePath' isLeft (ksbn,bn) invSchema (Path ifk jo@(FKJoinTable w ks tn) e)
    | any (isArray . keyType . fst) (ks)  =   do
          (bt,ksb,bq) <- labelTable backT
          let pksb = (_pkKey $ _kvKey $ unLB1 ksb )
              -- pksbn = (_pkKey $ _kvKey $ ksbn )
          (nt,ksn@(LB1 (KV (PK npk ndesc) nattr)),nq) <- labelTable nextT
          let pksn = (_pkKey $ _kvKey $ unLB1 ksn )
              -- fun :: [Labeled Text (TB Key) ]-> State ((Int, Map Int Table), (Int, Map Int Key))  ([Labeled Text (TB Key)], [Text])
              fun items =  do
                  let attrs :: [Labeled Text (TB Key)]
                      attrs = filter (\i -> not $ S.member (unAttr.labelValue $ i) fkSet) items
                      itemSet :: S.Set Key
                      itemSet = S.fromList $ fmap (unAttr.labelValue) items
                  pt <- mapM (recursePath' nextLeft (F.toList .unLB1 $ ksn ,nt) invSchema) (filter (\(Path ifk jo  _) ->  ifk `S.isSubsetOf`  itemSet ) (F.toList $ rawFKS nextT ))
                  return (attrs <> (concat $ fst <$> pt), snd <$> pt)
              mapOpt = fmap (\i -> if any (isKOptional.keyType.fst) ks then  makeOpt i else i)
          let nkv pk desc attr = (mapOpt $ LB1 (KV (PK (fst pk) (fst desc)) (fst attr)), foldl mappend "" $ snd pk <> snd desc <> snd attr)
          (tb,q) <-liftA3 nkv (fun npk) (fun ndesc) (fun nattr)
          tas <- tname nextT
          let knas =(Key (tableName nextT) Nothing Nothing (unsafePerformIO newUnique) (Primitive "integer" ))
          kas <- kname tas  knas
          let jt = if nextLeft  then " LEFT JOIN " else " JOIN "
              query =  jt <> "(SELECT " <> T.intercalate "," (label <$> pksb) <> "," <> "array_agg((" <> (T.intercalate ","  (fmap explodeLabel $ (F.toList $ unLB1 $ tb ) )) <> ")) as " <> label (snd kas) <> " FROM " <> bq <> (jt <> nq <> " ON "  <> joinLPredicate (fkm (F.toList $ unLB1 $ ksb) (F.toList $ unLB1  ksn)) )<> q <>   " GROUP BY " <>  T.intercalate "," (label <$> pksb ) <> ") as " <>  label tas  <> " ON " <>  joinLPredicate (zip ksbn pksb)
          return $ ([Labeled (label $ snd kas) (LAKT (fmap (\i -> justError ("cant find " <> show i). L.find ((== i) . unAttr. labelValue  )$ ksbn) (S.toList ifk )) (isPathReflexive jo )  [tb  ]) ] , query)

    | otherwise = do
          (nt,ksn@(LB1 (KV (PK npk ndesc) nattr)),nq) <- labelTable nextT
          let pksn = (_pkKey $ _kvKey $ unLB1 ksn )
              fun items =  do
                  let attrs :: [Labeled Text (TB Key)]
                      attrs = filter (\i -> not $ S.member (unAttr.labelValue $ i) fkSet) items
                      itemSet :: S.Set Key
                      itemSet = S.fromList $ fmap (unAttr.labelValue) items
                  pt <- mapM (recursePath' nextLeft (F.toList .unLB1 $ ksn ,nt) invSchema) (filter (\(Path ifk jo _) ->  ifk `S.isSubsetOf`  itemSet ) (F.toList $ rawFKS nextT ))
                  return (attrs <> (concat $ fst <$> pt), snd <$> pt)
              mapOpt = fmap (\i -> if any (isKOptional.keyType.fst) ks then  makeOpt i else i)
              nkv pk desc attr = (mapOpt $ LB1 (KV (PK (fst pk) (fst desc)) (fst attr)), foldl mappend "" $ snd pk <> snd desc <> snd attr)
          (tb,q) <-liftA3 nkv (fun npk) (fun ndesc) (fun nattr)
          let jt = if nextLeft  then " LEFT JOIN " else " JOIN "
          return $ ( [Labeled ""  $ LFKT (fmap (\i -> justError ("cant find " <> show i). L.find ((== i) . unAttr. labelValue  )$ ksbn) (S.toList ifk )) (isPathReflexive jo ) (tb ) ]  ,(jt <> nq <> " ON "  <> joinLPredicate (fkm ksbn pksn) <>  q))
  where nextT@(Raw _ _ _ _ fk _ ) = (\(Just i)-> i) (M.lookup tn (invSchema))
        backT = (\(Just i)-> i) (M.lookup w (invSchema))
        joinLPredicate   =   T.intercalate " AND " . fmap (\(l,r)->  intersectionOpK (unAttr . labelValue $ l) (unAttr . labelValue $ r) (label l)  (label r ))
        fkSet = S.unions $ fmap (\(Path ifk _ _) -> ifk)$ filter (\(Path _ ifk  _) -> isPathReflexive ifk)  $ S.toList (rawFKS nextT)
        nextLeft = any (isKOptional.keyType.fst) ks || isLeft
        fkm m n = zip (look (fst <$> ks) m) (look (snd <$> ks) n)
          where
            look ki i = justError ("missing FK on " <> show ki <> show i ) $ allMaybes $ fmap (\j-> L.find (\v -> unAttr (labelValue v) == j) i  ) ki

unAttr (Attr i) = i
unAttr i = errorWithStackTrace $ "cant find attr" <> (show i)

mkKey i = do
  (c,m) <- snd <$> get
  let next = (c+1,M.insert (c+1) i m)
  modify (\(j,_) -> (j,next))
  return (c+1,i)

mkTable i = do
  (c,m) <- fst <$> get
  let next = (c+1,M.insert (c+1) i m)
  modify (\(_,j) -> (next,j))
  return (c+1)

aliasKeys (t,Labeled  a (Attr (Key n _  _ _ _)))  = label t <> "." <> n <> " as " <> a

nonAliasKeys (t,Labeled a (Attr (Key n _  _ _ _)))  = label t <> "." <> n

aliasTable (Labeled t r) = showTable r <> " as " <> t

kname :: Labeled Text Table -> Key -> QueryRef (Labeled Text Table ,Labeled Text (TB Key))
kname t i = do
  n <- mkKey i
  return $ (t,Labeled ("k" <> (T.pack $  show $ fst n)) (Attr i) )

tname :: Table -> QueryRef (Labeled Text Table)
tname i = do
  n <- mkTable i
  return $ Labeled ("t" <> (T.pack $  show n)) i

explodeLabel (Labeled l (Attr _)) = l
-- explodeLabel (Labeled l (FKT i _ (LB1 t) )) = "(" <> T.intercalate "," (( F.toList $ fmap explodeLabel t))  <> ")"
explodeLabel (Labeled l (LFKT i refl (LB1 t) )) = T.intercalate "," (( F.toList $ fmap explodeLabel i)) <> ",(" <> T.intercalate "," (( F.toList $ fmap explodeLabel t))  <> ")"
explodeLabel (Labeled l (LAKT i _ _ )) = T.intercalate "," (( F.toList $ fmap explodeLabel i)) <> "," <> l

unTlabel (LB1 kv ) = TB1 $ fmap unlabel kv
unlabel (Labeled l (LFKT i refl t) ) = (FKT (fmap unlabel i) refl (unTlabel t ))
unlabel (Labeled l (LAKT i refl [t]) ) = (AKT (fmap unlabel i) refl [unTlabel t])
unlabel (Labeled l a@(Attr i )) = a

allRec' i t = unTlabel $ fst $ rootPaths' i t

rootPaths' invSchema r@(Raw _ _ _ _ fk _ ) = fst $ flip runState ((0,M.empty),(0,M.empty)) $ do
  (t,ks@(LB1 (KV (PK npk ndesc) nattr)),q) <- labelTable r
  let fkSet = S.unions $ fmap (\(Path ifk _ _) -> ifk)$ filter (\(Path _ ifk  _) -> isPathReflexive ifk) $ S.toList fk
      fun items =  do
                  let attrs :: [Labeled Text (TB Key)]
                      attrs = filter (\i -> not $ S.member (unAttr.labelValue $ i) fkSet) items
                      itemSet :: S.Set Key
                      itemSet = S.fromList $ fmap (unAttr.labelValue) items
                  pt <- mapM (recursePath' False (F.toList .unLB1 $ ks ,t) invSchema) (filter (\(Path ifk jo _)-> ifk `S.isSubsetOf`  itemSet ) (F.toList fk ))
                  return (attrs <> (concat $ fst <$> pt), snd <$> pt)
      nkv pk desc attr = (LB1 (KV (PK (fst pk) (fst desc)) (fst attr)), foldl mappend "" $ snd pk <> snd desc <> snd attr)
  (tb,js) <-liftA3 nkv (fun npk) (fun ndesc) (fun nattr)
  return ( tb , "SELECT (" <> T.intercalate "," (fmap explodeLabel $ (F.toList $ unLB1 tb))  <> (") FROM " <> q ) <> js)


backPK (Path i _ j)  = S.toList i


projectAllRec'
     :: Monad m => Map Text Table ->  QueryT m (TB1 KAttribute)
projectAllRec' invSchema =  do
  (schema,table@(Base _ t  )) <- get
  let
      ta@(Raw _ _ k _ _ _ ) = atBase id table
      path = ( recursePaths invSchema ta)
      table1 = Base k $ splitJoins  ((\(Just i)-> i) $ F.foldl' (flip joinPath) (Just t)  ( recursePaths invSchema ta))
      attrs =  Metric . alterName <$> (allAliasedRec invSchema ta )
      aliasMap =   fmap fst $ M.fromList $ aliasJoin table1
      alterName ak@(p,Key k al a b c ) = (Key k (Just $ justError ("lookupAlias "  <> show ak <> " " <> show aliasMap   <> " -- paths " <> show path <> T.unpack (showTable table1 )  ) $ M.lookup ak aliasMap ) a b c )
  put (schema,Project (F.toList attrs )  table1 )
  return  attrs


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
      alterName ak@(p,Key k al a b c ) = (Key k (Just $ fst $ justError ("lookupAlias "  <> show ak <> " " <> show aliasMap  <> T.unpack (showTable table1 )  ) $ M.lookup ak aliasMap ) a b c )
  put (schema,Limit (Project (F.toList kv) $ table1) 500)
  return kv



allAttrs' :: Table -> Set (AliasPath Key,(Table,Key))
allAttrs' r@(Raw _ _ _ _ _ _) = S.map ((PathRoot,) . (r,)) $ rawKeys r
allAttrs' (Limit p _ ) = allAttrs' p
allAttrs' (Filtered _ p) = allAttrs' p
allAttrs' (Base _ p) =  snd $  from allAttrs' p
  where from f (From t pk ) = (sm1,ft)
          where ft = f t
                sm1 =  foldr (\i m -> M.insert (snd $ snd i) PathRoot m ) M.empty (S.toList ft)
        from f s@(SplitJoin _ t  rel p) =  (sm1 , (foldr (<>) sp $ fmap (\(n,_) -> S.map (\(_,(ta,k))-> (pth  n,(alterTableName (<> fullTableName n  ) ta,k))) (f t) ) rel )  <> sp)
          where
                (sm,sp) = from f p
                sm1 =  foldr (\(n,_) m -> foldr (\i mi -> M.insert   (snd $ snd i) (pth  n) mi ) m  (S.toList ft) ) sm rel
                pth n = PathCons (S.map (\nk -> (nk,(justError $ "allAttrs' pathSplit KEY " <> (T.unpack $ showKey nk ) )$ M.lookup nk sm) ) n )
                ft = f t
        from f (Join ty t r p) = (sm1,S.map (\(_,(ta,k))-> (pth ,(ta,k))) ft  <>   sp)
          where n = S.map (justError "allAttrs' filterSet") $ S.filter isJust $ S.map (\i -> M.lookup i  (M.fromList $ concat $ fmap (fmap swap . S.toList .snd) $ S.toList r) ) pk
                (sm,sp) = from f p
                sm1 =  foldr (\i m -> M.insert (snd $ snd i) pth  m ) sm (S.toList ft)
                pth = PathCons (S.map (\nk -> (nk,(justError "allAttrs' pathLeft") (M.lookup nk sm)) ) n )
                ft = f t
                pk = atBase (\(Raw _ _ p _ _ _) -> p) t

rawKeys r = (rawPK r ) <> (maybe S.empty S.singleton (rawDescription r) ) <> (rawAttrs r)

newtype QueryT m a
  = QueryT {runQueryT :: StateT  (HashQuery, Table)  m a} deriving(Functor,Applicative,Monad,MonadState (HashQuery, Table) )

runQuery t =  runState (runQueryT t)

pathLabel (ComposePath i (p1,p12,p2) j) = T.intercalate "," $  fmap pathLabel (S.toList p1) <> fmap pathLabel (S.toList p2)
pathLabel (Path i t j) = tableName t

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

-- interval' i j = Interval.interval (ER.Finite i ,True) (ER.Finite j , True)
inf' = (\(ER.Finite i) -> i) . Interval.lowerBound
sup' = (\(ER.Finite i) -> i) . Interval.upperBound


unSOptional (SOptional i) = i
unSOptional i = traceShow ("unSOptional No Pattern Match SOptional-" <> show i) Nothing

unSSerial (SSerial i) = i
unSSerial i = traceShow ("unSSerial No Pattern Match SSerial-" <> show i) Nothing

unRSOptional (SOptional i) = join $ fmap unRSOptional i
unRSOptional i = traceShow ("unRSOptional No Pattern Match SOptional-" <> show i) Nothing

unRSOptional' (SOptional i) = join $ unRSOptional' <$> i
unRSOptional' (SSerial i )  = join $ unRSOptional' <$>i
unRSOptional' i   = Just i

allMaybes i | F.all (const False) i  = Nothing
allMaybes i = case F.all isJust i of
        True -> Just $ fmap (justError "wrong invariant allMaybes") i
        False -> Nothing


makeLenses ''KV
makeLenses ''PK
makeLenses ''TB
makeLenses ''TB1
