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
import Data.Functor.Compose
import Data.Bifunctor
import Data.Functor.Identity
import Data.Typeable
import Data.Void
import Data.Aeson
import Data.Aeson.TH
import Data.Vector(Vector)
import Data.Functor.Classes
import Data.Foldable (Foldable)
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
import Data.Set (Set)
import Control.Monad.State
import Data.Text.Lazy(Text)

import Data.Unique

instance Ord a => Ord (Interval.Interval a ) where
  compare i j = compare (Interval.upperBound i )  (Interval.upperBound j)

data Path a b
  -- Trivial Path
  = Path  a  b  a
  -- | TagPath  (Cardinality (Set a))  b  (Cardinality (Set a))
  -- Path Composition And Product
  | ComposePath a (Set (Path a b),a,Set (Path a b)) a
  deriving(Eq,Ord,Show )


data PK a
  = PK { _pkKey:: [a], _pkDescription :: [a]} deriving(Eq,Ord,Functor,Foldable,Traversable,Show)

data KV a
  = KV {_kvKey  :: PK a , _kvAttr ::  [a] }deriving(Eq,Ord,Functor,Foldable,Traversable,Show)

filterTB1 f (TB1 i) = TB1 $ filterKV f i


mapTB1  f (TB1 i)  =  TB1 (mapKV f i )
mapKV f (KV (PK l m) n) =  KV (PK (map f l)(map f m)) (map f n)
filterKV i (KV (PK l m) n) = KV (PK (filter i l) (filter i m )) (filter i n)
findKV i (KV (PK l m) n) =  (L.find i l)  `mplus` (L.find i m ) `mplus` (L.find i n)
findTB1  i (TB1 j )  =  findKV i j


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

instance (Functor f,Eq1 f,Eq a) => Eq1 (TB  f a) where
  eq1 i j = i == j

instance (Functor f,Ord1 f,Ord a) => Ord1 (TB f a ) where
  compare1 i j = compare i j

instance (Functor f,Show1 f,Show a) => Show1 (TB f  a) where
  showsPrec1 = showsPrec

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

instance Bifunctor (TB Identity ) where
  first f (Attr k i) = Attr (f k) i
  first f (IT k i) = IT (f k) (mapKey f i)
  first f (FKT k l m  i) = FKT  (fmap (Compose . Identity . first f . runIdentity . getCompose) k) l (fmap (first f . second f) m   ) (mapKey f i)
  first f (TBEither k l m ) = TBEither (f k) ( fmap ( (Compose . Identity . first f . runIdentity . getCompose)) l) (fmap ((Compose . Identity . first f . runIdentity . getCompose))  m)

  second = fmap

data TB f k a
  = FKT -- Foreign Table
    { _tbref :: [Compose f (TB f k) a]
    , _reflexive ::  Bool
    , _fkrelation :: [(k ,k)]
    , _fkttable ::  (FTB1 (Compose f (TB f k)) a)
    }

  | IT -- Inline Table
    { _ittableName :: k
    , _fkttable ::  (FTB1 (Compose f (TB f k)) a)
    }
  | TBEither
    k [(Compose f (TB f k) () )]  (Maybe (Compose f (TB f k) a))
  | Attr
    { _tbattrkey :: k
    ,_tbattr :: a   }
  -- Attribute
  deriving(Show,Eq,Ord,Functor,Foldable,Traversable)

type TB1 = FTB1 (Compose Identity (TB Identity Key) )
type TB2 k = FTB1 (Compose Identity (TB Identity k ) )

mapKey f (TB1 k ) = TB1 . fmap (Compose . Identity . first f . runIdentity . getCompose) $  k
mapKey f (LeftTB1 k ) = LeftTB1 (mapKey f <$> k)
mapKey f (ArrayTB1 k ) = ArrayTB1 (mapKey f <$> k)

data FTB1 f a
  = TB1 (KV (f a))
  | LeftTB1 (Maybe (FTB1 f a))
  | ArrayTB1 [(FTB1 f a)]
  deriving(Eq,Ord,Show,Functor,Foldable,Traversable)


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
  | SEitherR Showable
  | SEitherL Showable
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

instance Apply KV where
  KV pk i <.> KV pk1 i1 = KV (pk <.> pk1) (getZipList $ ZipList i <.> ZipList i1)

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

makeLenses ''KV
makeLenses ''PK
makeLenses ''TB


