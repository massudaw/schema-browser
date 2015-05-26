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

import Warshal
import Control.Lens.TH
import Data.Tuple
import Data.Functor.Apply
import Data.Functor.Compose
import Data.Functor.Identity
import Data.Typeable
import Data.Distributive
import Data.Vector(Vector)
import qualified Data.Vector as Vector
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
import qualified Data.ByteString as BS
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

data PK a
  = PK { _pkKey:: [a], _pkDescription :: [a]} deriving(Functor,Foldable,Traversable,Show)

data KV a
  = KV {_kvKey  :: PK a , _kvAttr ::  [a] }deriving(Functor,Foldable,Traversable,Show)

mapKV f (KV (PK l m) n) =  KV (PK (map f l)(map f m)) (map f n)

filterKV i (KV (PK l m) n) = KV (PK (filter i l) (filter i m )) (filter i n)
findKV i (KV (PK l m) n) =  (L.find i l)  `mplus` (L.find i m ) `mplus` (L.find i n)


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


instance (Functor f,Eq1 f) => Eq1 (TB  f) where
  eq1 i j = i == j

instance (Functor f,Ord1 f) => Ord1 (TB f ) where
  compare1 i j = compare i j

instance (Functor f,Show1 f) => Show1 (TB f  ) where
  showsPrec1 = showsPrec

instance Eq f => Eq1 (Labeled f ) where
  eq1 i j = i == j
instance Ord f => Ord1 (Labeled f ) where
  compare1 i j  = compare i j
instance Show f => Show1 (Labeled f ) where
  showsPrec1 = showsPrec

data TBRel  i
  = TBLeft (Maybe (TBRel i))
  | TBIdent i
  | TBArray [TBRel i]

type Key = FKey (KType Text)

data FKey a
    = Key
    { keyValue :: ! Text
    , keyAlias :: ! (Maybe Text)
    , keyTranslation :: ! (Maybe Text)
    , keyFastUnique :: ! Unique
    , keyType :: ! a
    }



data TB f a
  = FKT
    { _tbref :: ![Compose f (TB f) a]
    , _reflexive :: ! Bool
    , _fkrelation :: [(Key,Key)]
    , _fkttable :: ! (FTB1 (Compose f (TB f)) a)
    }
  {-| ForeignRel Bool [(Key,Key)] (TB f a)
  | Relation [Compose f (TB f) a] (TB f a)
  | BaseTable (FTB1 (Compose f (TB f)) a)
  | ArrayRel [TB f a]
  -}
  | IT
    { _tbref :: ![Compose f (TB f) a]
    , _fkttable :: ! (FTB1 (Compose f (TB f)) a)
    }
  | AKT
    { _tbref :: ! [Compose f (TB f) a]
    , _reflexive :: ! Bool
    , _fkrelation :: [(Key,Key)]
    , _akttable :: ! (FTB1 (Compose f (TB f)) a)
    }
  | Attr
    { _tbattr :: ! a
    }
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
   | InlineTable Text Text
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
   k > l = keyFastUnique k > keyFastUnique l
   k < l = keyFastUnique k < keyFastUnique l
   k <= l = keyFastUnique k <= keyFastUnique l
   k >= l = keyFastUnique k >= keyFastUnique l

instance Show Key where
   show k = T.unpack $ maybe (keyValue k) id (keyTranslation  k)
   -- show  =  T.unpack .showKey
showKey k  = keyValue k  <>  maybe "" ("-"<>) (keyTranslation k) <> {-"::" <> T.pack ( show $ hashUnique $ keyFastUnique k )<> -} "::"  <> showTy id (keyType k)


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
  | SBinary !BS.ByteString
  | SOptional !(Maybe Showable)
  | SComposite !(Vector Showable)
  | SInterval !(Interval.Interval Showable)
  | SScopedKeySet !(Map Key Showable)
  deriving(Ord,Eq,Show)

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

data SqlOperation a
  = FetchTable a
  | FKJoinTable a [(Key,Key)] a
  | FKInlineTable a
  deriving(Eq,Ord,Show,Functor)



data TableType
   = ReadOnly
   | WriteOnly
   | ReadWrite
   deriving(Eq,Ord,Show)

data Table
    =  Raw { rawSchema :: (Text,(TableType,Maybe Text))
           , rawName :: Text
           , rawPK :: (Set Key)
           , rawDescription :: (Maybe Key)
           , rawFKS ::  (Set (Path (Set Key) (SqlOperation Text)))
           , rawAttrs :: (Set Key)
           }
     deriving(Eq,Ord)

instance Show Table where
  show = T.unpack . tableName


tableName = rawName
translatedName (Raw (_,(_,trans))  t _ _ _ _ ) =  maybe t id trans




data TableModification b
  = TableModification (Maybe Int) Table (Modification Key b)
  deriving(Eq,Show,Functor)

data Modification a b
  = EditTB (TB1 (a,b)) (TB1 (a,b))
  | InsertTB (TB1 (a,b))
  | DeleteTB (TB1 (a,b))
  deriving(Eq,Show,Functor)


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

instance Apply f => Apply (FTB1 f ) where
  TB1 a <.> TB1 a1 =  TB1 (getCompose $ Compose a <.> Compose a1)

instance Apply KV where
  KV pk i <.> KV pk1 i1 = KV (pk <.> pk1) (getZipList $ ZipList i <.> ZipList i1)

instance Apply PK where
  PK i j <.> PK i1 j1 = PK (getZipList $ ZipList i <.> ZipList i1 ) ( getZipList $ ZipList j <.> ZipList j1)

instance Apply f => Apply (TB f) where
  Attr a <.>  Attr a1 = Attr $ a a1
  FKT l i m t <.> FKT l1 i1 m1 t1 = FKT (zipWith (<.>) l l1) (i && i1) m1 (t <.> t1)
  AKT l i m t <.> AKT l1 i1 m1 t1 = AKT (zipWith (<.>) l l1) (i && i1) m1 ((<.>) t t1)
  IT l t <.> IT l1 t1 = IT (zipWith (<.>) l l1) (t <.> t1)
  l <.> j = error  "cant apply"

type QueryRef = State ((Int,Map Int Table ),(Int,Map Int Key))

-- Literals Instances
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



makeLenses ''KV
makeLenses ''PK
makeLenses ''TB
-- makeLenses ''FTB1

