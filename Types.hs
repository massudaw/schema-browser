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
{-# LANGUAGE UndecidableInstances #-}

module Types where

-- import Warshal
import Control.Lens.TH
import Data.Functor.Apply
import Data.Bifunctor
import Data.Maybe
import Data.Functor.Identity
import Data.Typeable
import Data.Traversable(traverse)
import Data.Vector(Vector)
import Data.Functor.Classes
import Data.Foldable (Foldable)
import qualified Data.Foldable as F
import qualified Data.Interval as Interval
import Data.Monoid hiding (Product)

import qualified Data.Text.Lazy as T
import qualified Data.ByteString as BS


import GHC.Stack

import Data.Traversable(Traversable)
import Database.PostgreSQL.Simple.Time

import Data.Time
import Control.Monad
import GHC.Exts
import Control.Applicative
import qualified Data.List as L
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Control.Monad.State
import Data.Text.Lazy(Text)

import Data.Unique

instance Ord a => Ord (Interval.Interval a ) where
  compare i j = compare (Interval.upperBound i )  (Interval.upperBound j)


data Compose f g k a = Compose {getCompose :: f (g k a) } deriving (Functor,Foldable,Traversable,Ord,Eq,Show)

data Path a b
  -- Trivial Path
  = Path  a  b  a
  -- | TagPath  (Cardinality (Set a))  b  (Cardinality (Set a))
  -- Path Composition And Product
  | ComposePath a (Set (Path a b),a,Set (Path a b)) a
  deriving(Eq,Ord,Show )


data PK a
  = PK { _pkKey:: [a], _pkDescription :: [a]} deriving(Eq,Ord,Functor,Foldable,Traversable,Show)

data KV f k a
  = KV {_kvvalues :: Map (Set k) (f k a)  }deriving(Eq,Ord,Functor,Foldable,Traversable,Show)


data KVMetadata k
  = KVMetadata
  { _kvname :: Text
  , _kvschema :: Text
  , _kvpk :: Set k
  , _kvdesc :: Set k
  , _kvattrs :: Set k
  , _kvdelayed :: Set k
  }deriving(Eq,Ord,Show)

kvMetaFullName m = _kvschema m <> "." <> _kvname m

filterTB1 f (TB1 m i) = TB1 m $ mapComp (filterKV f ) i
mapTB1  f (TB1 m i)  =  TB1 m (mapComp (mapKV f) i )
mapKV f (KV  n) =  KV  (fmap f n)
filterKV i (KV n) =  KV $ Map.fromList $ L.filter (i . snd) $ Map.toList  n
findKV i (KV  n) =  L.find (i . snd) $Map.toList  n
findTB1  i (TB1 m j )  = mapComp (Compose . findKV i) j



mapTBF f (Attr i k) = (Attr i k )
mapTBF f (IT i k) = IT i ((mapFTBF f) k)
mapTBF f (FKT i j r k) = FKT  (fmap (Compose .  fmap (mapTBF f) . f .   getCompose) i)  j r  (mapFTBF f k)

mapFTBF f (TB1 m i) = TB1 m $ mapComp (KV . fmap (Compose .  fmap (mapTBF f) . f . getCompose). _kvvalues ) i

-- Reference labeling
-- exchange label reference for values when labeled
-- inline values reference when unlabeled

data Labeled l v
  = Labeled
  { label :: l
  , labelValue :: v
  }
  | Unlabeled
  { labelValue :: v
  } deriving(Eq,Show,Ord,Foldable,Functor,Traversable)

{-instance (Functor f,Eq1 f,Eq a) => Eq1 (TB  f a) where
  eq1 i j = i == j

instance (Functor f,Ord1 f,Ord a) => Ord1 (TB f a ) where
  compare1 i j = compare i j

instance (Functor f,Show1 f,Show a) => Show1 (TB f  a) where
  showsPrec1 = showsPrec
-}

instance (Show f) =>  Show1 (Labeled f  ) where
  showsPrec1 = showsPrec

type Key = FKey (KType Text)

data FKey a
    = Key
    { keyValue :: ! Text
    , keyTranslation :: ! (Maybe Text)
    , keyFastUnique :: ! Unique
    , keyType :: ! a
    }

instance (Functor f ,Bifunctor g)  => Bifunctor (Compose f g ) where
  first f  = Compose . fmap (first f) . getCompose
  second f = Compose . fmap (second f) . getCompose





data TB f k a
  = FKT -- Foreign Table
    { _tbref :: ! [Compose f (TB f) k  a]
    , _reflexive ::  ! Bool
    , _fkrelation :: ! [(k ,k)]
    , _fkttable ::  ! (FTB1 f  k a)
    }
  | IT -- Inline Table
    { _ittableName :: ! (Compose f (TB f ) k ())
    , _fkttable ::  ! (FTB1 f  k a)
    }
  | TBEither
    { _tbeithername :: ! k
    , _tbeitherref :: ! [(Compose f (TB f ) k () )]
    , _tbeithervalue:: ! (Maybe (Compose f (TB f ) k a))
    }
  | Attr
    { _tbattrkey :: ! k
    ,_tbattr :: ! a   }
  -- Attribute

  deriving(Functor,Foldable,Traversable)

deriving instance (Eq (f (TB f k a )), Eq (f (TB f k () )) , Eq ( (FTB1 f  k a )) ,Eq a , Eq k ) => Eq (TB f k a)
deriving instance (Ord (f (TB f k a )), Ord (f (TB f k () )) , Ord ( (FTB1 f  k a )) ,Ord a , Ord k ) => Ord (TB f k a)
deriving instance (Show (f (TB f k a )), Show (f (TB f k () )) , Show ( (FTB1 f k a )) ,Show a , Show k ) =>Show (TB f k a)

type TB1 = TB2 Key
type TB2 k = TB3 Identity k
type TB3 f = FTB1 f

mapKVMeta f (KVMetadata tn sch s j k l ) =KVMetadata tn sch (Set.map f s) (Set.map f j) (Set.map f k) (Set.map f l)


filterKey f (TB1 m k ) = TB1 m . mapComp (\(KV kv) -> KV $ Map.filterWithKey f kv )  $  k
filterKey f (LeftTB1 k ) = LeftTB1 (filterKey f <$> k)
filterKey f (ArrayTB1 k ) = ArrayTB1 (filterKey f <$> k)
  where
    --frstTB :: (Ord k, Functor f) => (c -> k) -> TB f c a -> TB f k a
    frstTB f (Attr k i) = Attr  k i
    frstTB f (IT k i) = IT  k (filterKey f i)
    frstTB f (FKT k l m  i) = FKT   k l m (filterKey  f i)
    frstTB f (TBEither k l m ) = TBEither  k l (fmap (mapComp (frstTB f))  m)




mapKey f (TB1 m k ) = TB1 (mapKVMeta f m) . mapComp (firstKV f)  $  k
mapKey f (LeftTB1 k ) = LeftTB1 (mapKey f <$> k)
mapKey f (ArrayTB1 k ) = ArrayTB1 (mapKey f <$> k)


firstKV  f (KV m ) = KV . fmap (mapComp (firstTB f) ) . Map.mapKeys (Set.map f) $ m
secondKV  f (KV m ) = KV . fmap (second f ) $ m

firstTB :: (Ord k, Functor f) => (c -> k) -> TB f c a -> TB f k a
firstTB f (Attr k i) = Attr (f k) i
firstTB f (IT k i) = IT (mapComp (firstTB f) k) ((mapKey f) i)
firstTB f (FKT k l m  i) = FKT  (fmap (mapComp (firstTB f) ) k) l (fmap (first f . second f) m   ) ((mapKey f) i)
firstTB f (TBEither k l m ) = TBEither (f k) ( fmap (mapComp (firstTB f)) l) (fmap (mapComp (firstTB f))  m)


data FTB1 f k a
  = TB1 (KVMetadata k) ! (Compose f (KV (Compose f (TB f))) k a)
  | LeftTB1 ! (Maybe (FTB1 f k a))
  | ArrayTB1 ! [(FTB1 f k a)]
  deriving(Functor,Foldable,Traversable)

deriving instance (Eq (f (TB f k a )), Eq (f (TB f k () )) , Eq (f (KV (Compose f (TB f))  k a )) ,Eq a , Eq k ) => Eq (FTB1 f k a)
deriving instance (Ord (f (TB f k a )), Ord (f (TB f k () )) , Ord (f (KV (Compose f (TB f)) k a )) ,Ord a , Ord k ) => Ord (FTB1 f k a)
deriving instance (Show (f (TB f k a )), Show (f (TB f k () )) , Show (f (KV (Compose f (TB f)) k a )) ,Show a , Show k ) =>Show (FTB1 f k a)

data KPrim
   = PText
   | PBoolean
   | PInt
   | PDouble
   | PDate
   | PDayTime
   | PTimestamp
   | PInterval
   | PPosition
   | PBounding
   | PCnpj
   | PMime Text
   | PCpf
   | PLineString
   deriving(Show,Eq,Ord)


data KType a
   = Primitive a
   | InlineTable {- schema -} Text {- tablename -} Text
   | KEither [KType a]
   | KSerial (KType a)
   | KArray (KType a)
   | KInterval (KType a)
   | KOptional (KType a)
   | KDelayed (KType a)
   | KTable [KType a]
   deriving(Eq,Ord,Functor)


instance Show (KType KPrim) where
  show =  showTy show

instance Show (KType Text) where
  show = T.unpack . showTy id

showTy f (Primitive i ) = f i
showTy f (InlineTable s i ) = "[" <>  fromString (T.unpack $ s <> "." <>  i) <> "]"
showTy f (KArray i) = "{" <>  showTy f i <> "}"
showTy f (KOptional i) = showTy f i <> "*"
showTy f (KInterval i) = "(" <>  showTy f i <> ")"
showTy f (KSerial i) = showTy f i <> "?"


instance Eq Key where
   k == l = keyFastUnique k == keyFastUnique l
   k /= l = keyFastUnique k /= keyFastUnique l

instance Ord Key where
   compare i j = compare (keyFastUnique i) (keyFastUnique j)

instance Show Key where
   show k = T.unpack $ maybe (keyValue k) id (keyTranslation  k)
showKey k  = keyValue k  <>  maybe "" ("-"<>) (keyTranslation k) <> {-"::" <> T.pack ( show $ hashUnique $ keyFastUnique k )<> -} "::"  <> showTy id (keyType k)

newtype Position = Position (Double,Double,Double) deriving(Eq,Ord,Typeable,Show,Read)

newtype Bounding = Bounding (Interval.Interval Position) deriving(Eq,Ord,Typeable,Show)

newtype LineString = LineString (Vector Position) deriving(Eq,Ord,Typeable,Show,Read)

data Showable
  = SText !Text
  | SNumeric !Int
  | SBoolean !Bool
  | SDouble !Double
  | STimestamp !LocalTime
  | SPInterval !DiffTime
  | SPosition !Position
  | SBounding !Bounding
  | SLineString !LineString
  | SDate !Day
  | SDayTime !TimeOfDay
  | SSerial !(Maybe Showable)
  | SBinary !BS.ByteString
  | SOptional !(Maybe Showable)
  | SComposite !(Vector Showable)
  | SDelayed !(Maybe Showable)
  | SInterval !(Interval.Interval Showable)
  | SScopedKeySet !(Map Key Showable)
  deriving(Ord,Eq,Show)


data SqlOperation
  = FetchTable Text
  | FKJoinTable Text [(Key,Key)] Text
  | FKInlineTable Text
  | FKEitherField Key [Key]
  deriving(Eq,Ord,Show)


data TableType
   = ReadOnly
   | WriteOnly
   | ReadWrite
   deriving(Eq,Ord,Show)

data Table
    =  Raw { rawSchema :: Text
           , rawTableType :: TableType
           , rawTranslation :: Maybe Text
           , rawDelayed :: (Set Key)
           , rawName :: Text
           , rawAuthorization :: [Text]
           , rawPK :: (Set Key)
           , rawDescription :: (Maybe Key)
           , rawFKS ::  (Set (Path (Set Key) (SqlOperation )))
           , rawAttrs :: (Set Key)
           }
     deriving(Eq,Ord)

instance Show Table where
  show = T.unpack . tableName


tableName = rawName
translatedName tb =  maybe (rawName tb) id (rawTranslation tb )


data TableModification b
  = TableModification (Maybe Int) Table (Modification Key b)
  deriving(Eq,Show,Functor)


data Modification a b
  = EditTB (TB2 a b) (TB2 a b)
  | InsertTB (TB2 a b)
  | DeleteTB (TB2 a b)
  deriving(Eq,Show,Functor)

instance (Ord k,Apply (f k) ,Functor (f k )) =>Apply  (KV f k) where
  KV pk  <.> KV pk1 = KV (Map.intersectionWith (<.>) pk pk1)

instance Apply PK where
  PK i j <.> PK i1 j1 = PK (getZipList $ ZipList i <.> ZipList i1 ) ( getZipList $ ZipList j <.> ZipList j1)


type QueryRef = State ((Int,Map Int Table ),(Int,Map Int Key))

-- Literals Instances
instance IsString Showable where
    fromString i = SText (T.pack i)

instance Enum Showable where
    toEnum = SNumeric . toEnum
    fromEnum (SNumeric i ) = fromEnum i

instance Real Showable where
  toRational (SDouble i )=  toRational i

instance Integral Showable where
  -- quotRem i = quotRem i
  toInteger (SNumeric i) = toInteger i
  quotRem (SNumeric i ) (SNumeric j ) = (\(l,m) -> (SNumeric l , SNumeric m)) $ quotRem i j


instance Num Showable where
    SNumeric i +  SNumeric j = SNumeric (i + j)
    SDouble i +  SDouble j = SDouble (i + j)
    SNumeric i *  SNumeric j = SNumeric (i * j)
    SDouble i *  SDouble j = SDouble (i * j)
    fromInteger i = SDouble $ fromIntegral i
    negate (SNumeric i) = SNumeric $ negate i
    negate (SDouble i) = SDouble $ negate i
    abs (SNumeric i) = SNumeric $ abs i
    abs (SDouble i) = SDouble $ abs i
    signum (SNumeric i) = SNumeric $ signum i

instance Fractional Showable where
  fromRational i = SDouble (fromRational i)
  recip (SDouble i) = SDouble (recip i)
  recip (SNumeric i) = SDouble (recip $ fromIntegral i)
  recip i = errorWithStackTrace (show i)

-- type HashQuery =  HashSchema (Set Key) (SqlOperation Table)
type PathQuery = Path (Set Key) (SqlOperation )

type TBLabel =  Compose (Labeled Text) (TB (Labeled Text) ) Key
type TBIdent =  Compose Identity  (TB Identity ) Key

overComp f =  f . runIdentity . getCompose

mapFromTBList :: Ord k => [Compose Identity (TB Identity) k  a] -> Map (Set k) (Compose Identity ( TB Identity ) k  a)
mapFromTBList = Map.fromList . fmap (\i -> (Set.fromList (keyattr  i),i))

keyattr :: Compose Identity (TB Identity ) k  a -> [k]
keyattr = keyattri . runIdentity . getCompose
keyattri (Attr i  _ ) = [i]
keyattri (TBEither k i l  ) =[k]
keyattri (FKT i _ _ _ ) =  (L.concat $ keyattr  <$> i)
keyattri (IT i  _ ) =  keyattr i

-- tableAttr :: (Traversable f ,Ord k) => TB3 f k () -> [Compose f (TB f) k ()]
-- tableAttr (ArrayTB1 i) = tableAttr <$> i
-- tableAttr (LeftTB1 i ) = tableAttr<$> i
tableAttr (TB1 m (Compose (Labeled _ (KV  n)))  ) = concat  $ F.toList (nonRef <$> n)

nonRef :: (Eq f,Show k ,Show f,Ord k) => Compose (Labeled f ) (TB (Labeled f) ) k () -> [Compose (Labeled f ) (TB (Labeled f) ) k ()]
nonRef i@(Compose (Labeled _ (Attr _ _ ))) =[i]
nonRef i@(Compose (Unlabeled  (Attr _ _ ))) =[i]
nonRef (Compose (Unlabeled  ((FKT i _ _ _ )))) = concat (nonRef <$> i)
nonRef (Compose (Labeled _ ((FKT i _ _ _ )))) = concat (nonRef <$> i)
nonRef (Compose (Unlabeled (IT j k ))) = nonRef j
nonRef (Compose (Labeled _ (IT j k ))) = nonRef j
nonRef (Compose (Unlabeled (TBEither n kj j ))) = concat $  fmap nonRef  $ maybe (addDefaultK <$> kj) (\jl -> fmap (\i -> if i == fmap (const ()) jl  then jl else addDefaultK i) kj) j
nonRef i = errorWithStackTrace (show i)



tableNonRef :: Ord k => TB2 k a -> TB3 Identity k a
tableNonRef (ArrayTB1 i) = ArrayTB1 $ tableNonRef <$> i
tableNonRef (LeftTB1 i ) = LeftTB1 $ tableNonRef <$> i
tableNonRef (TB1 m n  )  = TB1 m (mapComp (\(KV n)-> KV  (mapFromTBList $ fmap (Compose . Identity ) $ concat $ F.toList $  overComp nonRef <$> n)) n)
  where
    nonRef :: Ord k => TB Identity k a -> [(TB Identity ) k a]
    nonRef (Attr k v ) = [Attr k v]
    nonRef (TBEither n l j ) = [TBEither n (concat $ traComp nonRef <$> l) (join $ fmap listToMaybe $ traComp nonRef <$> j) ]
    nonRef (FKT i True _ _ ) = concat (overComp nonRef <$> i)
    nonRef (FKT i False _ _ ) = []
    nonRef it@(IT j k ) = [(IT  j (tableNonRef k )) ]


tableNonRefK :: TB2 Key Showable -> TB3 Identity Key Showable
tableNonRefK (ArrayTB1 i) = ArrayTB1 $ tableNonRefK <$> i
tableNonRefK (LeftTB1 i ) = LeftTB1 $ tableNonRefK <$> i
tableNonRefK (TB1 m n   )  = TB1 m (mapComp (\(KV n)-> KV (mapFromTBList $ fmap (Compose . Identity ) $ concat $ F.toList $  overComp nonRef <$> n)) n)
  where
    nonRef :: TB Identity Key Showable -> [(TB Identity ) Key Showable]
    nonRef (Attr k v ) = [ Attr k v ]
    nonRef (TBEither n kj j ) =   concat $  fmap (overComp nonRef ) $ maybe (addDefault <$> kj) (\jl -> fmap (\i -> if i == fmap (const ()) jl  then jl else addDefault i) kj) j
    nonRef (FKT i True _ _ ) = concat  (overComp nonRef <$> i)
    nonRef (FKT i False _ _ ) = []
    nonRef (IT j k ) = [(IT  j (tableNonRefK k )) ]

addDefaultK
  :: Functor g => Compose g (TB f) d a
     -> Compose g (TB f) d ()
addDefaultK = mapComp def
  where
    def ((Attr k i)) = (Attr k ())
    def ((IT  rel j )) = (IT  rel (LeftTB1 Nothing)  )


addDefault
  :: Functor g => Compose g (TB f) d a
     -> Compose g (TB f) d Showable
addDefault = mapComp def
  where
    def ((Attr k i)) = (Attr k (SOptional Nothing))
    def ((IT  rel j )) = (IT  rel (LeftTB1 Nothing)  )


mapComp :: (Functor t) => (f c a -> g d b) ->  Compose t f c a -> Compose t g d b
mapComp f =  Compose. fmap  f . getCompose

traComp :: (Applicative k ,Traversable t ,Functor t )=> (f c a -> k (g d b)) ->  Compose t f c a -> k (Compose t g d b)
traComp f =  fmap Compose. traverse f . getCompose

concatComp  =  Compose . concat . fmap getCompose

tableMeta t = KVMetadata (rawName t) (rawSchema t) (rawPK t) (maybe Set.empty Set.singleton $ rawDescription t) (rawAttrs t) (rawDelayed t)

tbmap :: Ord k => Map (Set k ) (Compose Identity  (TB Identity) k a) -> TB3 Identity k a
tbmap = TB1 (KVMetadata "" ""  Set.empty Set.empty Set.empty Set.empty) . Compose . Identity . KV

tblist :: Ord k => [Compose Identity  (TB Identity) k a] -> TB3 Identity k a
tblist = tbmap . mapFromTBList

tblist' :: Table -> [Compose Identity  (TB Identity) Key a] -> TB3 Identity Key a
tblist' t  = TB1 (tableMeta t) . Compose . Identity . KV . mapFromTBList

instance Ord k => Monoid (KV f k a) where
  mempty = KV Map.empty
  mappend (KV i ) (KV j)   =    KV (Map.union i  j)

makeLenses ''KV
makeLenses ''PK
makeLenses ''TB



