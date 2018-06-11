{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}

module Types.Primitive where

import Control.Applicative
import Control.DeepSeq
import qualified Control.Lens as Le
import Control.Lens.TH
import Control.Monad
import Data.Aeson
import Data.Bifunctor
import Data.Binary (Binary)
import qualified Data.Binary as B
import qualified Data.ByteString as BS
import Data.Dynamic
import Data.Foldable (Foldable)
import qualified Data.Foldable as F
import qualified Data.HashMap.Strict as HM
import qualified Data.Interval as Interval
import qualified Data.List as L
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Monoid hiding (Product)
import Data.Ord
import qualified Data.Poset as P
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Set as S
import qualified Data.Text as T
import Data.Text (Text)
import Data.Time
import Data.Traversable (traverse)
import Data.Unique
import Data.Vector (Vector)
import GHC.Exts
import GHC.Generics
import qualified NonEmpty as Non
import NonEmpty (NonEmpty(..))
import Safe
import System.IO.Unsafe
import Types.Common
import Utils

makeLenses ''KV
makeLenses ''TB

data KTypePrim
  = KSerial
  | KArray
  | KInterval
  | KOptional
  | KDelayed
  deriving (Eq, Ord, Show, Generic)

instance Binary Order

instance NFData Order

showOrder Asc = "ASC"
showOrder Desc = "DESC"

data Order
  = Asc
  | Desc
  deriving (Eq, Ord, Show, Generic)

data KType a = Primitive
  { _keyFunc :: [KTypePrim]
  , _keyAtom :: a
  } deriving (Eq, Ord, Functor, Generic, Foldable, Show)

makeLenses ''KType

isSerial (Primitive (KSerial:_) _) = True
isSerial _ = False

isPrim (Primitive [] i) = True
isPrim i = False

isOptional (Primitive (KOptional:_) _) = True
isOptional _ = False

isArray :: KType i -> Bool
isArray (Primitive (KOptional:KArray:_) _) = True
isArray (Primitive (KArray:_) _) = True
isArray _ = False

newtype TBIndex a =
  Idex [FTB a]
  deriving (Eq, Show, Ord, Functor, Generic)

data Union a
  = Many [Union a]
  | ISum [Union a]
  | One a
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable, Generic)

instance (Binary k) => Binary (Union k)

instance (NFData k) => NFData (Union k)
data Access a
  = IProd (Maybe UnaryOperator) a
  | Nested [a] (Union (Access a))
  | Rec Int  (Union (Access a))
  | Point Int
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable, Generic)

instance (Binary k) => Binary (Access k)

instance (NFData k) => NFData (Access k)

data Constant
  = CurrentTime
  | CurrentDate
  deriving (Eq, Ord, Show, Generic)

instance NFData Constant

instance Binary Constant

data UnaryOperator
  = IsNull
  | Not UnaryOperator
  | Range Bool
          UnaryOperator
  | BinaryConstant BinaryOperator
                   Constant
  deriving (Eq, Ord, Show, Generic)

instance NFData UnaryOperator

instance Binary UnaryOperator

type CorePrim = Prim KPrim (Text, Text)

type CoreKey = FKey (KType CorePrim)

showableDef (Primitive (KOptional:xs) i) =
  Just $ LeftTB1 (showableDef (Primitive xs i))
showableDef (Primitive (KSerial:xs) i) =
  Just $ LeftTB1 (showableDef (Primitive xs i))
showableDef (Primitive (KArray:xs) i) = Nothing -- Just (SComposite Vector.empty)
showableDef i = Nothing

type SqlOperationK = SqlOperationTK (Text, Text)

data SqlOperationTK t k
  = FKJoinTable [Rel k]
                t
  | RecJoin (MutRec [[Rel k]])
            (SqlOperationTK t k)
  | FKInlineTable k
                  t
  | FunctionField k
                  Expr
                  [Rel k]
  deriving (Eq, Ord, Show, Functor, Foldable, Generic)

newtype MutRec a = MutRec
  { unMutRec :: [a]
  } deriving (Eq, Ord, Show, Functor, Foldable, Generic, Binary, NFData)

instance Binary k => Binary (SqlOperationK k)

instance NFData k => NFData (SqlOperationK k)

isFunction :: SqlOperationK k -> Bool
isFunction (FunctionField _ _ _) = True
isFunction i = False

isRecRel (RecJoin _ _) = True
isRecRel i = False

pathRelOri :: Ord k => SqlOperationK k -> Set k
pathRelOri = S.map _relOrigin . pathRelRel

pathRelRel :: Ord k => SqlOperationK k -> Set (Rel k)
pathRelRel (FKJoinTable rel _) = Set.fromList rel
pathRelRel (FKInlineTable r _) = Set.singleton $ Inline r
pathRelRel (RecJoin l rel) = pathRelRel rel
pathRelRel (FunctionField r e a) = S.singleton $ RelFun r e a

pathRelRel' :: Ord k => SqlOperationK k -> MutRec [Set (Rel k)]
pathRelRel' (RecJoin l rel)
  | L.null (unMutRec l) = MutRec [[pathRelRel rel]]
  | otherwise = fmap ((pathRelRel rel :) . fmap (Set.fromList)) l

type Column k a = TB k a

type Key = CoreKey

data FKey a = Key
  { keyValue :: Text
  , keyTranslation :: (Maybe Text)
  , keyModifier :: [FieldModifier]
  , keyPosition :: Int
  , keyStatic :: Maybe (FExpr Text (FTB Showable))
  , keyTable :: Int
  , _keyTypes :: a
  } deriving (Functor, Generic)

keyFastUnique k = (keyTable k, keyPosition k)

type KeyUnique = (Int, Int)

instance NFData a => NFData (FKey a)

keyType = _keyTypes

instance Binary KTypePrim

instance Binary a => Binary (KType a)

instance Binary Position

instance Binary a => Binary (FKey a)

instance Binary FieldModifier

instance Binary KPrim

instance Binary GeomType

instance Binary TimeType

instance (Binary i, Binary j) => Binary (Prim i j)

instance NFData Position

instance Binary Bounding

instance NFData Bounding

instance Binary LineString

instance NFData LineString

instance Binary Showable

instance NFData Showable

instance Binary SGeo

instance NFData SGeo

instance Binary STime

instance NFData STime

instance (NFData l) => NFData (TableK l)

instance NFData (TableType)

instance (NFData l) => NFData (TableTransform l)

data GeomType
  = MultiGeom GeomType
  | PPolygon
  | PLineString
  | PPosition
  | PBounding
  deriving (Eq, Show, Ord, Generic)

data TimeType
  = PTimestamp (Maybe TimeZone)
  | PDate
  | PDayTime
  | PInterval
  deriving (Show, Eq, Ord, Generic)

data KPrim
  = PText
  | PBoolean
  | PAddress
  | PInt Int
  | PDouble
  | PDimensional Int
                 (Int, Int, Int, Int, Int, Int, Int)
  | PGeom Int
          GeomType
  | PTime TimeType
  | PMime Text
  | PCnpj
  | PCpf
  | PBinary
  | PColor
  | PAny
  | PDynamic String
  deriving (Show, Eq, Ord, Generic)

instance NFData KPrim

instance NFData GeomType

instance NFData TimeType

data Prim a b
  = AtomicPrim a
  | RecordPrim b
  deriving (Eq, Ord, Show, Generic)

instance (NFData a, NFData b) => NFData (Prim a b)

instance NFData KTypePrim

instance NFData a => NFData (KType a)

showTy f (Primitive l i) = f i ++ join (showT <$> l)
  where
    showT KArray = "[]"
    showT KOptional = "?"
    showT KInterval = "()"
    showT KSerial = "*"
    showT KDelayed = "_"

instance Eq (FKey a) where
  k == l = keyFastUnique k == keyFastUnique l

instance Ord (FKey a) where
  compare i j = compare (keyFastUnique i) (keyFastUnique j)

instance Show a => Show (FKey a)
  -- show = T.unpack . showKey
                               where
  show k = T.unpack $ maybe (keyValue k) id (keyTranslation k)

showKey k =
  maybe (keyValue k) (\t -> keyValue k <> "-" <> t) (keyTranslation k) <> "::" <>
  T.pack (show $ keyFastUnique k) <>
  "::" <>
  T.pack (show $ keyStatic k) <>
  "::" <>
  T.pack
    (show (keyType k) <> "::" <> show (keyModifier k) <> "::" <>
     show (keyPosition k))

data Position
  = Position (Double, Double, Double)
  | Position2D (Double, Double)
  deriving (Eq, Typeable, Show, Read, Generic)

instance Ord Position where
  (Position (x, y, z)) <= (Position (a, b, c)) = x <= a && y <= b && z <= c
  (Position2D (x, y)) <= (Position2D (a, b)) = x <= a && y <= b
  (Position (x, y, z)) >= (Position (a, b, c)) = x >= a && y >= b && z >= c
  (Position2D (x, y)) >= (Position2D (a, b)) = x >= a && y >= b

newtype Bounding =
  Bounding (Interval.Interval Position)
  deriving (Eq, Ord, Typeable, Show, Generic)

newtype LineString =
  LineString (Vector Position)
  deriving (Eq, Ord, Typeable, Show, Read, Generic)

--- Geo Data Runtime Representations
data SGeo
  = SPosition !Position
  | SLineString !LineString
  | SPolygon !LineString
             ![LineString]
  | SMultiGeom ![SGeo]
  | SBounding !Bounding
  deriving (Ord, Eq, Show, Generic)

--- Time Data Runtime Representations
data STime
  = STimestamp !UTCTime
  | SDate !Day
  | SDayTime !TimeOfDay
  | SPInterval !DiffTime
  deriving (Ord, Eq, Show, Generic)

newtype HDynamic =
  HDynamic Dynamic

instance Eq HDynamic where
  i == j = True

instance Ord HDynamic where
  compare i j = EQ

instance NFData HDynamic where
  rnf (HDynamic i) = ()

instance Binary HDynamic where
  put (HDynamic i) = return ()
  get = undefined

instance Show HDynamic where
  show (HDynamic i) = show i

deriving instance Ord Value

instance Ord (HM.HashMap Text Value) where
  compare i j = foldl (<>) EQ (HM.intersectionWith compare i j)

data Showable
  = SText Text
  | SJSON Value
  | SNumeric Int
  | SBoolean Bool
  | SDouble Double
  | SGeo SGeo
  | STime STime
  | SBinary BS.ByteString
  | SDynamic HDynamic
  deriving (Ord, Eq, Show, Generic)

type SqlOperation = SqlOperationK Key

fkTargetTable (FKJoinTable r tn) = snd tn
fkTargetTable (FKInlineTable _ tn) = snd tn
fkTargetTable (RecJoin t tn) = fkTargetTable tn

data FieldModifier
  = FRead
  | FWrite
  | FPatch
  deriving (Eq, Ord, Show, Generic)

instance NFData FieldModifier

data TableType
  = ReadOnly
  | WriteOnly
  | ReadWrite
  deriving (Eq, Ord, Show, Generic)

type Table = TableK Key

instance Show Unique where
  show i = show (hashUnique i)

instance Eq (TableK k) where
  i == j = tableUnique i == tableUnique j

instance Ord (TableK k) where
  compare i j = compare (tableUnique i) (tableUnique j)

rawIsSum (Project i _) = __rawIsSum i
rawIsSum i = __rawIsSum i

rawTableType (Project i _) = rawTableType i
rawTableType i = _rawTableTypeL i

data TableK k
  = Raw { tableUniqueR :: Int
        , _rawSchemaL :: Text
        , _rawTableTypeL :: TableType
        , rawTranslation :: Maybe Text
        , rawDelayed :: [k]
        , __rawIsSum :: Bool
        , _rawNameL :: Text
        , uniqueConstraint :: [[k]]
        , _rawIndexes :: [[k]]
        , _rawScope :: [k]
        , _rawPKL :: [k]
        , _rawDescriptionL :: [k]
        , _rawFKSL :: [SqlOperationK k]
        , _rawAttrsR :: [k] }
  | Project (TableK k)
            (TableTransform k)
  deriving (Functor, Generic, Show)

data TableTransform k
  = Union [TableK k]
  | From (TableK k)
  | Join (TableTransform k)
         (TableK k)
         [Rel k]
  | Filter (TableTransform k)
           (BoolCollection (Rel k, [(k, AccessOp Showable)]))
  deriving (Eq, Ord, Functor, Generic, Show)

type AccessOp a = Either (FTB a, BinaryOperator) UnaryOperator

unRecRel (RecJoin _ l) = l
unRecRel l = l

data BoolCollection a
  = AndColl [BoolCollection a]
  | OrColl [BoolCollection a]
  | PrimColl a
  deriving (Show, Eq, Ord, Functor, Foldable, Generic, Traversable)

instance NFData a => NFData (BoolCollection a)

instance Binary a => Binary (BoolCollection a)

tableUnique (Project i _) = tableUniqueR i
tableUnique i = tableUniqueR i

rawFKS (Project i _) = _rawFKSL i
rawFKS i = _rawFKSL i

rawUnion (Project i (Union l)) = l
rawUnion _ = []

rawPK (Project i _) = _rawPKL i
rawPK i = _rawPKL i

rawDescription (Project i _) = _rawDescriptionL i
rawDescription i = _rawDescriptionL i

rawName (Project i _) = _rawNameL i
rawName i = _rawNameL i

rawSchema (Project i _) = _rawSchemaL i
rawSchema i = _rawSchemaL i

rawAttrs (Project i _) = _rawAttrsR i
rawAttrs i = _rawAttrsR i

tableName = rawName

translatedName tb = maybe (rawName tb) id (rawTranslation tb)

-- Literals Instances
instance IsString Showable where
  fromString i = SText (T.pack i)

instance Enum Showable where
  toEnum = SNumeric . toEnum
  fromEnum (SNumeric i) = fromEnum i

instance Real Showable where
  toRational (SNumeric i) = toRational i
  toRational (SDouble i) = toRational i

instance RealFrac Showable where
  properFraction (SDouble i) = second SDouble $ properFraction i --toRational (SDouble i )=  toRational i
  properFraction (SNumeric j) = (fromIntegral j, SNumeric 0)

instance Integral Showable where
  toInteger (SNumeric i) = toInteger i
  quotRem (SNumeric i) (SNumeric j) =
    (\(l, m) -> (SNumeric l, SNumeric m)) $ quotRem i j

instance Num Showable where
  SNumeric i + SNumeric j = SNumeric (i + j)
  SDouble i + SDouble j = SDouble (i + j)
  SDouble i + SNumeric j = SDouble $ i + fromIntegral j
  SNumeric j + SDouble i = SDouble $ i + fromIntegral j
  v + k = error (show (v, k))
  STime (STimestamp i) - STime (STimestamp j) =
    STime $ SPInterval $ realToFrac $ diffUTCTime i j
  SNumeric i - SNumeric j = SNumeric (i - j)
  SDouble i - SDouble j = SDouble (i - j)
  SDouble i - SNumeric j = SDouble $ i - fromIntegral j
  SNumeric j - SDouble i = SDouble $ i - fromIntegral j
  v - k = error (show (v, k))
  SNumeric i * SNumeric j = SNumeric (i * j)
  SNumeric i * SDouble j = SDouble (fromIntegral i * j)
  SDouble i * SNumeric j = SDouble (i * fromIntegral j)
  SDouble i * SDouble j = SDouble (i * j)
  SDouble i * (STime (SPInterval j)) = SDouble (i * realToFrac j)
  (STime (SPInterval i)) * SDouble j = SDouble (j * realToFrac i)
  STime (SPInterval i) * STime (SPInterval j) = STime $ SPInterval (i * j)
  i * j = error (show (i, j))
  fromInteger i = SDouble $ fromIntegral i
  negate (SNumeric i) = SNumeric $ negate i
  negate (SDouble i) = SDouble $ negate i
  negate i = error (show i)
  abs (SNumeric i) = SNumeric $ abs i
  abs (SDouble i) = SDouble $ abs i
  signum (SNumeric i) = SNumeric $ signum i
  signum (SDouble i) = SDouble $ signum i

instance Fractional Showable where
  fromRational i = SDouble (fromRational i)
  recip (SDouble i) = SDouble (recip i)
  recip (STime (SPInterval i)) = STime $ SPInterval (recip i)
  recip (SNumeric i) = SDouble (recip $ fromIntegral i)
  recip i = error (show i)

-- type HashQuery =  HashSchema (Set Key) (SqlOperation Table)
type PathQuery = SqlOperation

tableAttr :: Ord k => KV k a -> [TB k a]
tableAttr n = concat (nonRef <$> unkvlist n)
  where
    nonRef i@(Fun _ _ _) = [i]
    nonRef i@(Attr _ _) = [i]
    nonRef (FKT i _ _) = concat (nonRef <$> unkvlist i)
    nonRef j@(IT k v) = [j]

addDefault :: Ord d => TB d a -> TB d b
addDefault = def
  where
    def (Attr k i) = Attr k (LeftTB1 Nothing)
    def (Fun k i _) = Fun k i (LeftTB1 Nothing)
    def (IT rel j) = IT rel (LeftTB1 Nothing)
    def (FKT at rel j) =
      FKT (kvlist $ addDefault <$> unkvlist at) rel (LeftTB1 Nothing)

instance Eq (KVMetadata k) where
  i == j = _kvschema i == _kvschema j && _kvname i == _kvname j

instance Eq k => Ord (KVMetadata k) where
  compare = comparing _kvschema <> comparing _kvname

instance Show k => Show (KVMetadata k) where
  show k = T.unpack (_kvname k)

kvMetaFullName m = _kvschema m <> "." <> _kvname m

kvAttrs m = L.nub $ _kvattrs m <> _kvpk m <> _kvdesc m

data KVMetadata k = KVMetadata
  { _kvname :: Text
  , _kvschema :: Text
  , _kvscopes :: [k]
  , _kvpk :: [k]
  , _kvdesc :: [k]
  , _kvuniques :: [[k]]
  , _kvattrs :: [k]
  , _kvdelayed :: [k]
  , _kvjoins :: [SqlOperationK k]
  , _kvrecrels :: [MutRec [[Rel k]]]
  } deriving (Functor, Foldable, Generic)

kvempty = KVMetadata "" "" [] [] [] [] [] [] [] []

instance Binary k => Binary (KVMetadata k)

instance NFData k => NFData (KVMetadata k)

tableMeta :: Ord k => TableK k -> KVMetadata k
tableMeta (Project s _) = tableMeta s
tableMeta t =
  KVMetadata
    (rawName t)
    (rawSchema t)
    (_rawScope t)
    (rawPK t)
    (rawDescription t)
    (fmap F.toList $ uniqueConstraint t)
    (F.toList $ rawAttrs t)
    (F.toList $ rawDelayed t)
    (rawFKS t)
    (paths' <> paths)
  where
    rec = filter isRecRel (rawFKS t)
    same = filter ((tableName t ==) . fkTargetTable) rec
    notsame = filter (not . (tableName t ==) . fkTargetTable) rec
    paths = fmap (fmap (fmap F.toList) . pathRelRel') notsame
    paths' =
      (\i ->
         if L.null i
           then []
           else [MutRec i]) $
      concat $ fmap ((unMutRec) . fmap (fmap F.toList) . pathRelRel') same

isInline (Primitive _ (RecordPrim _)) = True
isInline _ = False

-- Intersections and relations
makeLenses ''Rel

makeLenses ''FKey

makeLenses ''TableK

--
--- Attr Cons/Uncons
--
unIndexItens ::
     (Show (KType k), Show a)
  => Int
  -> Int
  -> TB (FKey (KType k)) a
  -> (Maybe (TB (FKey (KType k)) a))
unIndexItens ix o = unIndex (ix + o)

unIndex ::
     (Show (KType k), Show a)
  => Int
  -> TB (FKey (KType k)) a
  -> Maybe (TB (FKey (KType k)) a)
unIndex o (Attr k (ArrayTB1 v)) = Attr (unKArray k) <$> Non.atMay v o
unIndex o (IT na (ArrayTB1 j)) = IT na <$> Non.atMay j o
unIndex o (FKT els rel (ArrayTB1 m)) =
  (\li mi ->
     FKT
       (kvlist $ nonl <> fmap ((firstTB unKArray)) li)
       (Le.over
          relOri
          (\i ->
             if isArray (keyType i)
               then unKArray i
               else i) <$>
        rel)
       mi) <$>
  (maybe (Just []) (Just . pure) (join ((traFAttr (indexArray o)) <$> l))) <*>
  (Non.atMay m o)
  where
    l =
      L.find
        (all (isArray . keyType) . fmap _relOrigin . keyattr)
        (unkvlist els)
    nonl =
      L.filter
        (not . all (isArray . keyType) . fmap _relOrigin . keyattr)
        (unkvlist els)
    indexArray ix s = Non.atMay (unArray s) ix
unIndex o i = error (show (o, i))

unLeftKey ::
     (Show k, Ord b, Show b) => TB (FKey (KType k)) b -> TB (FKey (KType k)) b
unLeftKey (Attr k v) = (Attr (unKOptional k) v)
unLeftKey (IT na (LeftTB1 (Just tb1))) = IT na tb1
unLeftKey i@(IT na (TB1 _)) = i
unLeftKey (FKT ilk rel (LeftTB1 (Just tb1))) =
  (FKT
     (kvlist $ (firstTB unKOptional) <$> unkvlist ilk)
     (Le.over relOri unKOptional <$> rel)
     tb1)
unLeftKey i@(FKT ilk rel (TB1 _)) = i
unLeftKey i = error (show i)

unLeftItens ::
     (Show k, Show a) => TB (FKey (KType k)) a -> Maybe (TB (FKey (KType k)) a)
unLeftItens = unLeftTB
  where
    unLeftTB (Attr k v) = Attr (unKOptional k) <$> unSOptional v
    unLeftTB (Fun k rel v) = Fun (unKOptional k) rel <$> unSOptional v
    unLeftTB (IT na (LeftTB1 l)) = IT (unKOptional na) <$> l
    unLeftTB i@(IT na (TB1 l)) = Just i
    unLeftTB (FKT ifk rel (LeftTB1 tb)) =
      (\ik -> FKT (kvlist ik) (Le.over relOri unKOptional <$> rel)) <$>
      traverse ((traFAttr unSOptional) . (firstTB unKOptional)) (unkvlist ifk) <*>
      tb
    unLeftTB i@(FKT ifk rel (TB1 _)) = Just i
    unLeftTB i = error (show i)

attrOptional :: TB (FKey (KType k)) a -> TB (FKey (KType k)) a
attrOptional (Attr k v) = Attr (kOptional k) (LeftTB1 . Just $ v)
attrOptional (Fun k rel v) = Fun (kOptional k) rel (LeftTB1 . Just $ v)
attrOptional (FKT ifk rel tb) =
  FKT (tbOptional ifk) (Le.over relOri kOptional <$> rel) (LeftTB1 (Just tb))
  where
    tbOptional = mapKey' kOptional . mapFValue (LeftTB1 . Just)
attrOptional (IT na j) = IT (kOptional na) (LeftTB1 (Just j))

leftItens ::
     TB (FKey (KType k)) a
  -> Maybe (TB (FKey (KType k)) a)
  -> Maybe (TB (FKey (KType k)) a)
leftItens tb@(Fun k rel _) = maybe emptyAttr (Just . attrOptional)
  where
    emptyAttr = Fun k rel <$> (showableDef (keyType k))
leftItens tb@(Attr k _) = maybe emptyAttr (Just . attrOptional)
  where
    emptyAttr = Attr k <$> (showableDef (keyType k))
leftItens tb@(IT na _) = Just . maybe emptyIT attrOptional
  where
    emptyIT = IT na (LeftTB1 Nothing)
leftItens tb@(FKT ilk rel _) = Just . maybe emptyFKT attrOptional
  where
    emptyFKT =
      FKT (mapFValue (const (LeftTB1 Nothing)) ilk) rel (LeftTB1 Nothing)

attrArray :: TB Key b -> NonEmpty (TB Key Showable) -> TB Key Showable
attrArray back@(Attr k _) oldItems =
  (\tb -> Attr k (ArrayTB1 tb)) $ (\(Attr _ v) -> v) <$> oldItems
attrArray back@(FKT _ _ _) oldItems =
  (\(lc, tb) ->
     FKT
       (kvlist
          [ Attr
              (kArray $
               _relOrigin $
               justError "no head1" $ headMay $ keyattr (Non.head lc))
              (ArrayTB1 $ join $ Non.fromList . kattr <$> lc)
          ])
       (_fkrelation back)
       (ArrayTB1 tb)) $
  Non.unzip $
  (\(FKT lc rel tb) ->
     ( justError ("no head1" ++ show (lc, rel, tb)) $
       headMay $ F.toList $ unkvlist lc
     , tb)) <$>
  oldItems
attrArray back@(IT _ _) oldItems =
  (\tb -> IT (_tbattrkey back) (ArrayTB1 tb)) $ (\(IT _ tb) -> tb) <$> oldItems

unFin (Interval.Finite i) = Just i
unFin i = Nothing

kOptional = Le.over (keyTypes . keyFunc) (KOptional :)

kArray = Le.over (keyTypes . keyFunc) (KArray :)

kDelayed = Le.over (keyTypes . keyFunc) (KDelayed :)

unKOptional (Key a v c m n d (Primitive (KOptional:cs) e)) =
  Key a v c m n d (Primitive cs e)
unKOptional (Key a v c m n d (Primitive (KSerial:cs) e)) =
  Key a v c m n d (Primitive cs e)
unKOptional (Key a v c m n d (Primitive [] e)) =
  Key a v c m n d (Primitive [] e)
unKOptional i = i -- error ("unKOptional" <> show i)

unKTDelayed (KDelayed:e) = e
unKTDelayed (KSerial:e) = e
unKTDelayed (KOptional:e) = KOptional : unKTDelayed e
unKTDelayed (KArray:e) = KArray : unKTDelayed e
unKTDelayed i = i

unKDelayed (Key v a c m n d e) =
  (Key v a c m n d (Le.over keyFunc unKTDelayed e))
unKDelayed i = error ("unKDelayed" <> show i)

unKArray (Key a v c d m n (Primitive (KArray:xs) e)) =
  Key a v c d m n (Primitive xs e)
unKArray (Key a v c d m n e) = Key a v c d m n e

recOverAttr ::
     Ord k
  => [Set (Rel k)]
  -> TB k a
  -> (Map (Set (Rel k)) (TB k a) -> Map (Set (Rel k)) (TB k a))
recOverAttr (k:[]) attr = Map.insert k attr
recOverAttr (k:xs) attr =
  Map.alter
    (fmap (Le.over ifkttable (fmap (KV . recOverAttr xs attr . _kvvalues))))
    k

recOverMAttr' ::
     [Set (Rel Key)]
  -> [[Set (Rel Key)]]
  -> Map (Set (Rel Key)) (TB Key b)
  -> Map (Set (Rel Key)) (TB Key b)
recOverMAttr' tag tar m = foldr go m tar
  where
    go (k:[]) =
      Map.alter
        (fmap
           ((Le.over
               ifkttable
               ((fmap ((KV . recOverAttr tag recv . _kvvalues)))))))
        k
      where
        recv = gt tag m
    go (k:xs) =
      Map.alter
        (fmap ((Le.over ifkttable ((fmap ((KV . go xs . _kvvalues)))))))
        k
    gt (k:[]) = justError "no key" . Map.lookup k
    gt (k:xs) =
      gt xs .
      _kvvalues .
      head . F.toList . _fkttable . justError "no key" . Map.lookup k

replaceRecRel ::
     Map (Set (Rel Key)) (TB Key b)
  -> [MutRec [Set (Rel Key)]]
  -> Map (Set (Rel Key)) (TB Key b)
replaceRecRel = foldr (\(MutRec l) v -> foldr (\a -> recOverMAttr' a l) v l)

unKOptionalAttr (Attr k i) = Attr (unKOptional k) i
unKOptionalAttr (Fun k rel i) = Fun (unKOptional k) rel i
unKOptionalAttr (IT r (LeftTB1 (Just j))) = (\j -> IT r j) j
unKOptionalAttr (FKT i l (LeftTB1 (Just j))) =
  FKT (fmap ((first unKOptional)) i) l j

unOptionalAttr (Attr k i) = Attr (unKOptional k) <$> unSOptional i
unOptionalAttr (Fun k rel i) = Fun (unKOptional k) rel <$> unSOptional i
unOptionalAttr (IT r (LeftTB1 j)) = (\j -> IT r j) <$> j
unOptionalAttr (FKT i l (LeftTB1 j)) =
  liftA2
    (\i j -> FKT i l j)
    (traverseKV ((traFAttr unSOptional) . ((firstTB unKOptional))) i)
    j

-- unOptionalAttr (FKT i  l (LeftTB1 j)  ) = liftA2 (\i j -> FKT i  l j) (traverseKV ( (traFAValue unSOptional) . ((firstATB unKOptional)) ) i)  j
data RelSort k =
  RelSort [Rel k]
  deriving (Eq, Ord)

-- To Topologically sort the elements we compare  both inputs and outputs for intersection if one matches we flip the
instance (Ord k, Show k, P.Poset k) => P.Poset (RelSort k) where
  compare (RelSort i) (RelSort j) =
    case ( comp (out i) (inp j)
         , (comp (out j) (inp i))
         , P.compare (inp i) (inp j)
         , P.compare (out i) (out j))
            -- Reverse order
          of
      (_, P.LT, _, _) ->
        if S.size (out j) == L.length j
          then P.GT
          else P.EQ
            -- Right order
      (P.LT, _, _, _) -> P.LT
            -- No intersection  between elements sort by inputset
      (_, _, P.EQ, o) -> o
      (_, _, i, _) -> i
    where
      inp j = norm $ _relInputs <$> j
      out j = norm $ _relOutputs <$> j
      norm = S.fromList . concat . catMaybes
      comp i j
        | S.null (S.intersection i j) = P.EQ
      comp i j
        | S.empty == i = P.EQ
      comp i j
        | S.empty == j = P.EQ
      comp i j = P.compare i j
  compare (RelSort [i]) (RelSort [j]) = P.compare i j
  compare (RelSort [i]) (RelSort j) =
    P.compare (S.singleton i) (S.fromList j) <>
    if L.any (== P.EQ) (P.compare i <$> j)
      then P.LT
      else foldl1 mappend (P.compare i <$> j)
  compare (RelSort i) (RelSort [j]) =
    P.compare (S.fromList i) (S.singleton j) <>
    if L.any (== P.EQ) (flip P.compare j <$> i)
      then P.GT
      else foldl1 mappend (flip P.compare j <$> i)
  compare (RelSort i) (RelSort j) = P.compare (S.fromList i) (S.fromList j)

instance (Show i, P.Poset i) => P.Poset (Rel i) where
  compare (Inline i) (Inline j) = P.compare i j
  compare (Rel i _ a) (Inline j) =
    case i == j of
      True -> P.GT
      False -> P.compare i j
  compare (Inline j) (Rel i _ a) =
    case i == j of
      True -> P.LT
      False -> P.compare j i
  compare (Rel i _ a) (Rel j _ b) = P.compare i j <> P.compare a b
  compare n@(RelFun i ex a) o@(RelFun j ex2 k) =
    case (L.any (== Inline j) a, L.any (== Inline i) k) of
      (True, _) -> P.GT
      (_, True) -> P.LT
      (False, False) -> P.compare (Inline i) (Inline j)
  compare (RelFun i e a) j =
    case L.any (== j) a of
      True -> P.GT
      False -> P.compare (Inline i) j
  compare j (RelFun i e a) =
    case L.any (== j) a of
      True -> P.LT
      False -> P.compare j (Inline i)
  compare i j = error (show ("cant compare", i, j))

instance P.Poset (FKey i) where
  compare i j =
    case compare (keyPosition i) (keyPosition j) of
      EQ -> P.EQ
      LT -> P.LT
      GT -> P.GT

tbUn :: Ord k => Set k -> KV k a -> KV k a
tbUn un item =
  (\kv -> (\(KV item) -> KV $ Map.filterWithKey (\k _ -> pred kv k) $ item) item)
    un
  where
    pred kv k = (S.isSubsetOf (S.map _relOrigin k) kv)

generateUn :: Ord k => KVMetadata k -> [k] -> [Set (Rel k)]
generateUn m un = inline <> rels
  where
    pks = S.fromList un
    inline =
      fmap (S.singleton . Inline) $
      F.toList $ S.difference pks (S.map _relOrigin refs)
    rels =
      L.filter
        (\i -> S.isSubsetOf (S.map _relOrigin i) pks)
        (pathRelRel <$> _kvjoins m)
    refs = S.unions rels

generatePK :: Ord k => KVMetadata k -> [Set (Rel k)]
generatePK m = generateUn m (_kvpk m)

getPKM :: (Show k, Ord k) => KVMetadata k -> KV k a -> Map k (FTB a)
getPKM m = Map.fromList . getPKL m

getPKL :: (Show k, Ord k) => KVMetadata k -> KV k a -> [(k, FTB a)]
getPKL m = getUn m (S.fromList $ _kvpk m)

getUn :: (Show k, Ord k) => KVMetadata k -> Set k -> KV k a -> [(k, FTB a)]
getUn m un k =
  concat $
  F.toList
    ((\ix ->
        justError ("no unique : " ++ show (ix, un, Map.keys (_kvvalues k))) $
        (fmap aattr $ kvLookup ix k)) <$>
     pks)
  where
    pks =
      L.filter (\i -> S.isSubsetOf (S.map _relOrigin i) un) $
      Map.keys (_kvvalues k)

inlineName (Primitive _ (RecordPrim (s, i))) = (s, i)

inlineFullName (Primitive _ (RecordPrim (s, i))) = s <> "." <> i

attrT :: (a, FTB b) -> TB a b
attrT (i, j) = Attr i j

-- mergeFKRef  $ keyType . _relOrigin <$>rel
mergeFKRel :: [Rel CoreKey] -> KType [(Rel CoreKey, KType CorePrim)]
mergeFKRel ls =
  Primitive
    (F.foldr mergeRel [] ((\i -> _keyFunc $ keyType (_relOrigin i)) <$> ls))
    ((\i -> (i, keyType (_relTarget i))) <$> ls)
  where
    mergeRel (KOptional:o) (KOptional:kl) = KOptional : mergeRel o kl
    mergeRel (KArray:o) (KArray:kl) = KArray : mergeRel o kl
    mergeRel [] [] = []
    mergeRel (KOptional:o) kt = KOptional : mergeRel o kt
    mergeRel o (KOptional:kt) = KOptional : mergeRel o kt
    mergeRel (KArray:o) kl = KArray : mergeRel o kl
    mergeRel o (KArray:kl) = KArray : mergeRel o kl
    mergeRel i j = error ("mergeOpt" <> show (i, j))

mergeFKRef :: [KType a] -> KType [a]
mergeFKRef ls = Primitive (foldl1 mergeOpt (_keyFunc <$> ls)) (_keyAtom <$> ls)
  where
    mergeOpt (KOptional:i) (KOptional:j) = KOptional : (mergeOpt i j)
    mergeOpt (KOptional:i) j = KOptional : mergeOpt i j
    mergeOpt i (KOptional:j) = KOptional : mergeOpt i j
    mergeOpt (KArray:i) (KArray:j) = KArray : mergeOpt i j
    mergeOpt (KArray:i) j = KArray : mergeOpt i j
    mergeOpt i (KArray:j) = KArray : mergeOpt i j
    mergeOpt (KInterval:i) (KInterval:j) = KInterval : mergeOpt i j
    mergeOpt (KInterval:i) j = KInterval : mergeOpt i j
    mergeOpt i (KInterval:j) = KInterval : mergeOpt i j
    mergeOpt [] [] = []
    mergeOpt i j = error ("mergeOpt" <> show (i, j))

relType :: Show a => Rel (FKey (KType a)) -> KType a
relType (Inline k) = keyType k
relType (RelAccess xs n) =
  Primitive (_keyFunc (mergeFKRef $ keyType . _relOrigin <$> xs) ++ ty) at
  where
    Primitive ty at = relType n
relType i = error (show i)

srange l m =
  IntervalTB1 $
  Interval.interval (Interval.Finite l, True) (Interval.Finite m, True)

txt = TB1 . SText

int = TB1 . SNumeric

pos = TB1 . SGeo . SPosition

double = TB1 . SDouble

timestamp = TB1 . STime . STimestamp

date = TB1 . STime . SDate

array f = ArrayTB1 . fmap f

opt i = LeftTB1 . fmap i

class ConstantGen v where
  generate :: Constant -> v

instance ConstantGen (FTB Showable) where
  generate = generateConstant

keyattrs :: Ord k => TB k b -> Set (Rel k)
keyattrs = S.fromList . keyattr

generateConstant CurrentDate =
  unsafePerformIO $ do
    i <- getCurrentTime
    return (TB1 $ STime $ SDate (utctDay i))
generateConstant CurrentTime =
  unsafePerformIO $ do
    i <- getCurrentTime
    return (TB1 $ STime $ STimestamp i)

replaceRel rel (Attr k v) =
  (justError "no replaceRel" $ L.find ((== k) . _relOrigin) rel, v)

atTBValue ::
     (Applicative f, Ord k)
  => [Rel k]
  -> (FTB b -> f (FTB b))
  -> (FTB (KV k b) -> f (FTB (KV k b)))
  -> (FTB (TBRef k b) -> f (FTB (TBRef k b)))
  -> (KV k b)
  -> f (KV k b)
atTBValue l f g h v = traTable (Le.at (Set.fromList l) (traverse modify)) v
  where
    modify i =
      case i of
        Attr k j -> Attr k <$> f j
        IT l j -> IT l <$> g j
        t@(FKT l i j) ->
          recoverFK (concat $ fmap _relOrigin . keyattr <$> (unkvlist l)) i <$>
          h (liftFK t)

{-
          APrim j -> APrim <$> f j
          ARef j -> ARef <$> g j
          ti -> case recoverAttr (F.toList key,ti) of
                 t@(FKT l i j) ->   valueattr . recoverFK  (concat $ fmap _relOrigin . keyattr <$> (unkvlist l )) i <$> h (liftFK t)
-}
keyRef k = Inline k

iprodRef (IProd _ l) = l

notNull = Just $ Not IsNull

renderUnary (Not i) = "not " <> renderUnary i
renderUnary IsNull = "null"
renderUnary (Range b i) =
  (if b
     then " upper"
     else " lower")
renderUnary i = error (show i)

accesRelGen' :: Rel k -> Access k
accesRelGen' (Inline i) = IProd Nothing i
accesRelGen' (RelAccess l m) =
  Nested (_relOrigin <$> l) (Many [One (accesRelGen' m)])

relAccesGen :: Access k -> Rel k
relAccesGen (IProd i l) = Inline l
relAccesGen (Nested l (Many [One m])) =
  RelAccess ((\(i) -> Inline i) <$> l) (relAccesGen m)
