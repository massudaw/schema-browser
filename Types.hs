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
import Data.Functor.Identity
import Data.Typeable
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

-- Utility functions for kv
mapKV f (KV (PK l m) n) =  KV (PK (map f l)(map f m)) (map f n)
filterKV i (KV (PK l m) n) = KV (PK (filter i l) (filter i m )) (filter i n)
findKV i (KV (PK l m) n) =  (L.find i l)  `mplus` (L.find i m ) `mplus` (L.find i n)


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

instance (Functor f,Eq1 f) => Eq1 (TB  f) where
  eq1 i j = i == j

instance (Functor f,Ord1 f) => Ord1 (TB f ) where
  compare1 i j = compare i j

instance (Functor f,Show1 f) => Show1 (TB f  ) where
  showsPrec1 = showsPrec


type Key = FKey (KType Text)

data FKey a
    = Key
    { keyValue :: ! Text
    , keyTranslation :: ! (Maybe Text)
    , keyFastUnique :: ! Unique
    , keyType :: ! a
    }

data TB f a
  = FKT -- Foreign Table
    { _tbref :: ![Compose f (TB f) a]
    , _reflexive :: ! Bool
    , _fkrelation :: [(Key,Key)]
    , _fkttable :: ! (FTB1 (Compose f (TB f)) a)
    }

  | IT -- Inline Table
    { _tbref :: ![Compose f (TB f) a]
    , ittableName :: Text
    , _fkttable :: ! (FTB1 (Compose f (TB f)) a)
    }
  | TBEither
    (Compose f (TB f) Key ) (Compose f (TB f) Key ) (Maybe (Compose f (TB f) a)) (Maybe (Compose f (TB f) a))
  | Attr
    { _tbattr :: ! a }
  -- Attribute
  deriving(Show,Eq,Ord,Functor,Foldable,Traversable)

type TB1 = FTB1 (Compose Identity (TB Identity) )


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
   | KEither (KType a) (KType a)
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
  | STimestamp !LocalTimestamp
  | SPInterval !DiffTime
  | SPosition !Position
  | SBounding !Bounding
  | SLineString !LineString
  | SDate !Date
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
  | FKEitherField Key (Key,Key)
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
  = EditTB (TB1 (a,b)) (TB1 (a,b))
  | InsertTB (TB1 (a,b))
  | DeleteTB (TB1 (a,b))
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


