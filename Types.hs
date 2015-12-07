{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveGeneric #-}
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

import Control.Lens.TH
import qualified Control.Lens as Le
import Data.Functor.Apply
import qualified Network.Wreq.Session as Sess
import Data.Bifunctor
import Safe
import Prelude hiding(head)
import Data.Maybe
import GHC.Generics
import Data.Binary (Binary)
import Data.Vector.Binary
import qualified Data.Binary as B
import Data.Text.Binary
import Data.Functor.Identity
import Data.Typeable
import Data.Vector(Vector)
import Data.Functor.Classes
import Data.Foldable (Foldable)
import qualified Data.Foldable as F
import qualified Data.Interval as Interval
import qualified Data.ExtendedReal as ER
import Data.Monoid hiding (Product)
import qualified Data.Text as T
import qualified Data.ByteString as BS
import GHC.Stack
import Data.Traversable(Traversable,traverse)
import Data.Time
import Data.Time.Clock.POSIX
import Control.Monad
import GHC.Exts
import Control.Applicative
import qualified Data.List as L
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Set as  S
import Control.Monad.State
import Data.Text (Text)

import Debug.Trace
import Data.Unique

head [] = errorWithStackTrace "no head error"
head l = L.head l

isSerial (KSerial _) = True
isSerial _ = False

isPrim (Primitive i) = True
isPrim i = False

isOptional (KOptional _) = True
isOptional _ = False

isArray :: KType i -> Bool
isArray (KArray _) = True
isArray (KOptional i) = isArray i
isArray _ = False

unArray (ArrayTB1 s) =  s
unArray o  = errorWithStackTrace $ "unArray no pattern " <> show o

unSOptional (LeftTB1 i) = i
unSOptional i = traceShow ("unSOptional No Pattern Match SOptional-" <> show i) (Just i)

unSOptional' (LeftTB1 i ) = i
unSOptional' (SerialTB1 i )  = i
unSOptional' i   = Just i


unSDelayed (DelayedTB1 i) = i
unSDelayed i = traceShow ("unSDelayed No Pattern Match" <> show i) Nothing

unSSerial (SerialTB1 i) = i
unSSerial i = traceShow ("unSSerial No Pattern Match SSerial-" <> show i) Nothing

unRSOptional (LeftTB1 i) = join $ fmap unRSOptional i
unRSOptional i = traceShow ("unRSOptional No Pattern Match SOptional-" <> show i) Nothing

unRSOptional2 (LeftTB1 i) = join $ unRSOptional2 <$> i
unRSOptional2 i   = Just i

unRSOptional' (LeftTB1 i) = join $ unRSOptional' <$> i
unRSOptional' (SerialTB1 i )  = join $ unRSOptional' <$> i
unRSOptional' i   = Just i



showableDef (KOptional i) = Just $ LeftTB1 (showableDef i)
showableDef (KSerial i) = Just $ SerialTB1 (showableDef i)
showableDef (KArray i ) = Nothing -- Just (SComposite Vector.empty)
showableDef i = Nothing

isRecRel (RecJoin _ _ ) =  True
isRecRel i = False

pathRel (Path _ rel _ ) = rel
pathRelRef (Path ifk _ _ ) = ifk
pathRelStore (Path _ _ ifk ) = ifk

pathRelRel :: Ord k => Path (Set k ) (SqlOperationK k) -> Set (Rel k)
pathRelRel (Path _ (FKJoinTable _ rel  _ ) _ ) = Set.fromList rel
pathRelRel (Path r (FKInlineTable  _   )  _ ) = Set.map Inline r
pathRelRel (Path r (RecJoin l rel )  a ) =  pathRelRel (Path r rel a)

pathRelRel' :: Ord k => Path (Set k ) (SqlOperationK k) -> MutRec [Set (Rel k )]
pathRelRel' (Path r (RecJoin l rel )  a )
  | L.null (unMutRec l) =  MutRec [[pathRelRel (Path r rel a)]]
  | otherwise = fmap ((pathRelRel (Path r rel a) :) . fmap (Set.fromList)) l



data Compose f g k a = Compose {getCompose :: f (g k a) } deriving (Functor,Foldable,Traversable,Ord,Eq,Show,Generic)

data Path a b
  = Path  a  b  a
  deriving(Eq,Ord,Show )


data KV f k a
  = KV {_kvvalues :: Map (Set (Rel k)) (f k a)  }deriving(Eq,Ord,Functor,Foldable,Traversable,Show,Generic)

showOrder Asc = "ASC"
showOrder Desc = "DESC"
data Order
  = Asc
  | Desc
  deriving(Eq,Ord,Show,Generic)


type Column k a = TB Identity k a
type TBData k a = (KVMetadata k,Compose Identity (KV (Compose Identity (TB Identity))) k a )
type TB3Data  f k a = (KVMetadata k,Compose f (KV (Compose f (TB f ))) k a )


data KVMetadata k
  = KVMetadata
  { _kvname :: Text
  , _kvschema :: Text
  , _kvpk :: [k]
  , _kvdesc :: [k]
  , _kvuniques :: [Set k]
  , _kvorder :: [(k,Order)]
  , _kvattrs :: [k]
  , _kvdelayed :: Set k
  , _kvrecrels :: [MutRec [[Rel k]]]
  }deriving(Eq,Ord,Generic)

instance Show k => Show (KVMetadata k) where
  show k = T.unpack (_kvname k)
kvMetaFullName m = _kvschema m <> "." <> _kvname m
filterTB1 f = fmap (filterTB1' f)
filterTB1' f ((m ,i)) = (m , mapComp (filterKV f) i)
mapTB1  f (TB1 (m, i))  =  TB1 (m ,mapComp (mapKV f) i )
mapKV f (KV  n) =  KV  (fmap f n)
filterKV i (KV n) =  KV $ Map.fromList $ L.filter (i . snd) $ Map.toList  n
findKV i (KV  n) =  L.find (i . snd) $Map.toList  n
findTB1  i (TB1 (m, j) )  = mapComp (Compose . findKV i) j
-- findTB1  l (LeftTB1  j )  = join $ findTB1  l <$> j -- errorWithStackTrace (show m)

findTB1'  i (TB1 (m, j) )  = Map.lookup  i (_kvvalues $ runIdentity $ getCompose j  )
findTB1'  i (LeftTB1  j )  = join $ findTB1' i <$> j


mapTBF f (Attr i k) = (Attr i k )
mapTBF f (IT i k) = IT i ((mapFTBF f) k)
mapTBF f (FKT i  r k) = FKT  (fmap (Compose .  fmap (mapTBF f) . f .   getCompose) i)   r  (mapFTBF f k)

mapFTBF f (TB1 (m, i)) = TB1 (m , mapComp (KV . fmap (Compose .  fmap (mapTBF f) . f . getCompose). _kvvalues ) i)

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

instance (Show f) =>  Show1 (Labeled f  ) where
  showsPrec1 = showsPrec

type Key = FKey (KType  (Prim (Text,Text) (Text,Text)))

data FKeyPath j
data FKey a
    = Key
    { keyValue :: ! Text
    , keyTranslation :: ! (Maybe Text)
    , keyModifier :: [FieldModifier]
    , keyPosition :: Int
    , keyStatic :: Maybe (FTB Showable)
    , keyFastUnique :: ! Unique
    , _keyTypes :: ! a
    }deriving(Functor,Generic)

instance (Functor f ,Bifunctor g)  => Bifunctor (Compose f g ) where
  first f  = Compose . fmap (first f) . getCompose
  second f = Compose . fmap (second f) . getCompose

keyType = _keyTypes
data Rel k
  = Inline  {_relOrigin :: k}
  | Rel
  { _relOrigin :: k
  , _relOperator:: Text
  , _relTarget :: k
  }
  deriving(Eq,Show,Ord,Functor,Foldable,Generic)

deriving instance Generic (Identity a)


instance Binary Order
instance Binary a => Binary (KType a)
instance (Binary (f (g k a)) ) => Binary (Compose f g k a )
instance (Binary (f k a) ,Binary k ) => Binary (KV f k a)
instance Binary k => Binary (Rel k)
instance Binary a => Binary (Identity a)
instance (Binary (f (KV (Compose f (TB f)) g k)) , Binary (f (KV (Compose f (TB f)) g ())) , Binary (f (TB f g ())) ,Binary (f (TB f g k)), Binary k ,Binary g) => Binary (TB f g k )
instance Binary a => Binary (FTB a)
instance Binary k => Binary (KVMetadata k )

data TB f k a
  = Attr
    { _tbattrkey :: ! k
    ,_tbattr :: ! (FTB a)
    }
  | IT -- Inline Table
    { _ittableName :: ! (Compose f (TB f ) k ())
    , _fkttable ::  ! (FTB1 f  k a)
    }
  | FKT -- Foreign Table
    { _tbref :: ! [Compose f (TB f) k  a]
    , _fkrelation :: ! [Rel k]
    , _fkttable ::  ! (FTB1 f  k a)
    }
  deriving(Functor,Foldable,Traversable,Generic)

deriving instance (Eq (f (TB f k a )), Eq (f (KV (Compose f (TB f)) k ())) ,Eq (f (TB f k () )) , Eq ( (FTB1 f  k a )) ,Eq a , Eq k ) => Eq (TB f k a)
deriving instance (Ord (f (TB f k a )), Ord (f (KV (Compose f (TB f)) k ())), Ord (f (TB f k () )) , Ord ( (FTB1 f  k a )) ,Ord a , Ord k ) => Ord (TB f k a)
deriving instance (Show (f (TB f k a )), Show (f (KV (Compose f (TB f)) k ())),Show (f (TB f k () )) , Show ( (FTB1 f k a )) ,Show (FTB a),Show a , Show k ) =>Show (TB f k a)

type TB1 a = TB2 Key a
type TB2 k a = TB3 Identity k a
type TB3 f k a = FTB1 f k a

mapKVMeta f (KVMetadata tn sch s j m o k l r ) =KVMetadata tn sch (map f s) (map f j) (map (Set.map f) m ) (fmap (first f) o) (map f k) (Set.map f l) (fmap (fmap (fmap (fmap f)) ) <$> r)


filterKey' f ((m ,k) ) = (m,) . mapComp (\(KV kv) -> KV $ Map.filterWithKey f kv )  $  k
filterKey f = fmap f


newtype MutRec a = MutRec {unMutRec ::  [a] }deriving(Eq,Ord,Show,Functor,Foldable,Generic,Binary)

traFAttr :: (Traversable g ,Applicative f) => ( FTB a -> f (FTB a) ) -> TB g k a -> f (TB g k a)
traFAttr f (Attr i v)  = Attr i <$> f v
traFAttr f (IT i v)  = IT i <$> traverse (traFValue f) v
traFAttr f (FKT  i rel v)  = liftA2 (\a b -> FKT a rel b)  (traverse (traComp (traFAttr f)) i) (traverse (traFValue f) v)
traFValue f (m ,k) =  fmap ((m,)). traComp (fmap KV . traverse (traComp (traFAttr f)) . _kvvalues )  $  k



mapFAttr f (Attr i v)  = (Attr i (f v))
mapFAttr f (IT i v)  = IT i (mapFValue f v)
mapFAttr f (FKT  i rel v)  = FKT (mapComp (mapFAttr f) <$> i) rel  (mapFValue f v)

mapFValue f = fmap (mapFValue' f)
mapFValue' f ((m ,k) ) = (m,) . mapComp (KV . fmap (mapComp (mapFAttr f)) . _kvvalues )  $  k

mapRecord  f (m ,k)  = (m,) . mapComp (fmap  f)  $  k

mapValue' f ((m ,k) ) = (m,) . mapComp (fmap  f)  $  k
mapValue f = fmap (mapValue' f)


mapTable f (kv,m) = (kv,mapComp (KV. fmap (mapComp (mapTableAttr f )) . _kvvalues )  m )

mapTableAttr  f (IT l j ) =  IT l (f  (mapTable f <$> j))
mapTableAttr  f (FKT l rel j ) =  FKT l rel (f  (mapTable f <$> j))
mapTableAttr f  i = i

mapKey f = fmap (mapKey' f)
mapKey' f ((m ,k) ) = (mapKVMeta f m,) . mapComp (firstKV f)  $  k



firstKV  f (KV m ) = KV . fmap (mapComp (firstTB f) ) . Map.mapKeys (Set.map (fmap f)) $ m
secondKV  f (KV m ) = KV . fmap (second f ) $ m

firstTB :: (Ord k, Functor f) => (c -> k) -> TB f c a -> TB f k a
firstTB f (Attr k i) = Attr (f k) i
firstTB f (IT k i) = IT (mapComp (firstTB f) k) ((mapKey f) i)
firstTB f (FKT k  m  i) = FKT  (fmap (mapComp (firstTB f) ) k)  (fmap f  <$> m) ((mapKey f) i)

data FTB a
  = TB1 a
  | LeftTB1  ! (Maybe (FTB a))
  | SerialTB1 !(Maybe (FTB a))
  | IntervalTB1 !(Interval.Interval (FTB a))
  | DelayedTB1 !(Maybe (FTB a))
  | ArrayTB1 ![(FTB a)]
  deriving(Eq,Ord,Show,Functor,Foldable,Traversable,Generic)

instance Applicative FTB where
  pure = TB1
  LeftTB1 i <*> LeftTB1 j = LeftTB1 $ liftA2 (<*>) i j
  DelayedTB1 i <*> DelayedTB1 j = DelayedTB1 $ liftA2 (<*>) i j
  SerialTB1 i <*> SerialTB1 j = SerialTB1 $ liftA2 (<*>) i j
  ArrayTB1 i <*> ArrayTB1 j = ArrayTB1 $ liftA2 (<*>) i j

deriving instance Functor Interval.Interval
deriving instance Foldable Interval.Interval
deriving instance Foldable Interval.Extended
deriving instance Traversable Interval.Interval
deriving instance Traversable Interval.Extended

type FTB1 f k a = FTB (KVMetadata k, Compose f (KV (Compose f (TB f))) k a)

data KPrim
   = PText
   | PBoolean
   | PInt
   | PDouble
   | PDate
   | PDayTime
   | PTimestamp (Maybe TimeZone)
   | PInterval
   | PPosition
   | PBounding
   | PCnpj
   | PMime Text
   | PCpf
   | PBinary
   | PLineString
   | PSession
   | PDynamic
   deriving(Show,Eq,Ord)

data Prim a b
  = AtomicPrim a
  | RecordPrim b
  deriving(Eq,Ord,Show)

data KType a
   = Primitive a
   | KSerial (KType a)
   | KArray (KType a)
   | KInterval (KType a)
   | KOptional (KType a)
   | KDelayed (KType a)
   | KTable [KType a]
   deriving(Eq,Ord,Functor,Generic)

instance Show (KType KPrim ) where
  show =  showTy show

instance Show (KType (Prim KPrim (Text,Text))) where
  show =  showTy show

instance Show (KType (Prim (Text,Text) (Text,Text))) where
  show = T.unpack . showTy (T.pack . show)

showTy f (Primitive i ) = f i
showTy f (KArray i) = "{" <>  showTy f i <> "}"
showTy f (KOptional i) = showTy f i <> "*"
showTy f (KInterval i) = "(" <>  showTy f i <> ")"
showTy f (KSerial i) = showTy f i <> "?"
showTy f (KDelayed i) = showTy f i <> "-"
showTy f (KTable i) = "t"
-- showTy f i = errorWithStackTrace ("no ty for " <> show   i)


instance Eq (FKey a) where
   k == l = keyFastUnique k == keyFastUnique l
   k /= l = keyFastUnique k /= keyFastUnique l

instance Ord (FKey a) where
   compare i j = compare (keyFastUnique i) (keyFastUnique j)

instance Show a => Show (FKey a)where
   show k = T.unpack $ maybe (keyValue k) id (keyTranslation  k)

showKey k  =   maybe (keyValue k)  (\t -> keyValue k <> "-" <> t ) (keyTranslation k) <> "::" <> T.pack ( show $ hashUnique $ keyFastUnique k )<> "::" <> T.pack (show $ keyStatic k) <>  "::" <> T.pack (show (keyType k) <> "::" <> show (keyModifier k) <> "::" <> show (keyPosition k )  )


instance Binary a => Binary (Interval.Extended a) where
  put (Interval.Finite a ) = B.put a
  get = Interval.Finite <$> B.get
instance Binary a => Binary ( Interval.Interval a)  where
  put (Interval.Interval i j ) = B.put i >> B.put j
  get = liftA2 Interval.Interval B.get B.get


instance Binary Position
instance Binary Bounding
instance Binary LineString

newtype Position = Position (Double,Double,Double) deriving(Eq,Ord,Typeable,Show,Read,Generic)

newtype Bounding = Bounding (Interval.Interval Position) deriving(Eq,Ord,Typeable,Show,Generic)

newtype LineString = LineString (Vector Position) deriving(Eq,Ord,Typeable,Show,Read,Generic)

instance Binary Showable

instance Binary DiffTime where
  put i = B.put (round  (realToFrac i :: Double) :: Int )
  get  = secondsToDiffTime <$> B.get

instance Binary LocalTime where
  put i = B.put (realToFrac $ utcTimeToPOSIXSeconds $ localTimeToUTC utc i :: Double)
  get = utcToLocalTime utc . posixSecondsToUTCTime . realToFrac <$> (B.get :: B.Get Double)

instance Binary Day where
  put (ModifiedJulianDay i ) = B.put i
  get = ModifiedJulianDay <$> B.get

instance Binary TimeOfDay where
  put i = B.put (timeOfDayToTime  i )
  get = timeToTimeOfDay  <$> B.get

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
  | SBinary !BS.ByteString
  | SDynamic ! (FTB Showable)
  | SSession !Sess.Session
  deriving(Ord,Eq,Show,Generic)

instance Eq Sess.Session where
   i==  j = True

instance Ord Sess.Session where
  compare i j = compare 1 2

instance Binary Sess.Session where
  put i = return ()
  get = error ""

type SqlOperation = SqlOperationK Key
data SqlOperationK k
  = FetchTable Text
  | FKJoinTable Text [Rel k ] Text
  | RecJoin (MutRec [[Rel k ]])  (SqlOperationK k)
  | FKInlineTable Text
  deriving(Eq,Ord,Show)

fkTargetTable (FKJoinTable t r tn) = tn
fkTargetTable (FKInlineTable tn) = tn
fkTargetTable (RecJoin t tn) = fkTargetTable tn

data FieldModifier
   = FRead
   | FWrite
   | FPatch
   deriving(Eq,Ord,Show)

data TableType
   = ReadOnly
   | WriteOnly
   | ReadWrite
   deriving(Eq,Ord,Show)

type Table = TableK Key

mapTableK f (Raw  s tt tr de is rn  un ra rp rd rf inv rat ) = Raw s tt tr (S.map f de) is rn (fmap (S.map f) un) ra (map f rp) (fmap f rd) S.empty  S.empty (S.map f rat)
data TableK k
    =  Raw { rawSchema :: Text
           , rawTableType :: TableType
           , rawTranslation :: Maybe Text
           , rawDelayed :: (Set k)
           , rawIsSum :: Bool
           , rawName :: Text
           , uniqueConstraint :: [Set k]
           , rawAuthorization :: [Text]
           , rawPK :: [k]
           , rawDescription :: [k]
           , _rawFKSL ::  (Set (Path (Set k) (SqlOperationK k )))
           , rawInvFKS ::  (Set (Path (Set k) (SqlOperationK k)))
           , rawAttrs :: (Set k)
           }
     deriving(Eq,Ord)

rawFKS = _rawFKSL

instance Show Table where
  show = T.unpack . tableName


tableName = rawName
translatedName tb =  maybe (rawName tb) id (rawTranslation tb )


data TableModification p
  = TableModification
  { tableId :: (Maybe Int)
  , tableObj :: Table
  , tableDiff ::  p
  }
  deriving(Eq,Show,Functor,Generic)



unTB = runIdentity . getCompose
_tb = Compose . Identity


instance (Ord k,Apply (f k) ,Functor (f k )) =>Apply  (KV f k) where
  KV pk  <.> KV pk1 = KV (Map.intersectionWith (<.>) pk pk1)



type QueryRef = State ((Int,Map Int Table ),(Int,Map Int Key))

-- Literals Instances
instance IsString Showable where
    fromString i = SText (T.pack i)

instance Enum a => Enum (FTB a) where
    toEnum = TB1 . toEnum
    fromEnum (TB1 i ) = fromEnum i

instance Enum Showable where
    toEnum = SNumeric . toEnum
    fromEnum (SNumeric i ) = fromEnum i

instance Real a => Real (FTB a) where
  toRational (TB1 i )=  toRational i

instance Real Showable where
  toRational (SDouble i )=  toRational i

instance Integral a => Integral (FTB a) where
  toInteger (TB1 i) = toInteger i
  quotRem (TB1 i ) (TB1 j ) = (\(l,m) -> (TB1 l , TB1 m)) $ quotRem i j

instance Integral Showable where
  toInteger (SNumeric i) = toInteger i
  quotRem (SNumeric i ) (SNumeric j ) = (\(l,m) -> (SNumeric l , SNumeric m)) $ quotRem i j


instance Num a => Num (FTB a) where
    TB1 i + TB1 j = TB1 (i + j)
    TB1 i - TB1 j = TB1 (i - j)
    TB1 i * TB1 j = TB1 (i * j)
    abs (TB1 i)  = TB1 (abs i )
    signum (TB1 i)  = TB1 (signum i )
    fromInteger i  = TB1 (fromInteger i )

instance Num Showable where
    SNumeric i +  SNumeric j = SNumeric (i + j)
    SDouble i +  SDouble j = SDouble (i + j)
    SNumeric i *  SNumeric j = SNumeric (i * j)
    SDouble i *  SDouble j = SDouble (i * j)
    fromInteger i = SDouble $ fromIntegral i
    negate (SNumeric i) = SNumeric $ negate i
    negate (SDouble i) = SDouble $ negate i
    negate i = errorWithStackTrace (show i)
    abs (SNumeric i) = SNumeric $ abs i
    abs (SDouble i) = SDouble $ abs i
    signum (SNumeric i) = SNumeric $ signum i

instance Fractional a => Fractional (FTB a) where
  fromRational i = TB1 (fromRational i)
  recip (TB1 i) = TB1 $ recip i

instance Fractional Showable where
  fromRational i = SDouble (fromRational i)
  recip (SDouble i) = SDouble (recip i)
  recip (SNumeric i) = SDouble (recip $ fromIntegral i)
  recip i = errorWithStackTrace (show i)

-- type HashQuery =  HashSchema (Set Key) (SqlOperation Table)
type PathQuery = Path (Set Key) (SqlOperation )

type TBLabel =  Compose (Labeled Text) (TB (Labeled Text) ) Key
type TBIdent =  Compose Identity  (TB Identity ) Key

overComp f =  f . unTB

instance Applicative (Labeled Text) where
  pure =Unlabeled
  Labeled t l <*> Labeled j k = Labeled t (l  k)
  Unlabeled  l <*> Labeled t k = Labeled t (l  k)
  Labeled t l <*> Unlabeled  k = Labeled t (l  k)
  Unlabeled l <*> Unlabeled  k = Unlabeled  (l  k)

instance Monad (Labeled Text) where
  return = Unlabeled
  Unlabeled i >>= j = j i
  Labeled t i >>= j = case j i of
                    Unlabeled i -> Labeled t i
                    Labeled t0 i -> Labeled t  i

mapFromTBList :: Ord k => [Compose Identity (TB Identity) k  a] -> Map (Set (Rel k) ) (Compose Identity ( TB Identity ) k  a)
mapFromTBList = Map.fromList . fmap (\i -> (Set.fromList (keyattr  i),i))

keyattr :: Foldable f => Compose f (TB f ) k  a -> [Rel k]
keyattr = keyattri . head . F.toList . getCompose
keyattri (Attr i  _ ) = [Inline i]
keyattri (FKT i  rel _ ) = rel
keyattri (IT i  _ ) =  keyattr i

-- tableAttr :: (Traversable f ,Ord k) => TB3 f k () -> [Compose f (TB f) k ()]
-- tableAttr (ArrayTB1 i) = tableAttr <$> i
-- tableAttr (LeftTB1 i ) = tableAttr<$> i
tableAttr (DelayedTB1 (Just tb)) = tableAttr tb
tableAttr (TB1 (m ,(Compose (Labeled _ (KV  n)))) ) =   concat  $ F.toList (nonRef <$> n)
tableAttr (TB1 (m ,(Compose (Unlabeled (KV  n)))) ) =   concat  $ F.toList (nonRef <$> n)

nonRef :: (Ord f,Show k ,Show f,Ord k) => Compose (Labeled f ) (TB (Labeled f) ) k () -> [Compose (Labeled f ) (TB (Labeled f) ) k ()]
nonRef i@(Compose (Labeled _ (Attr _ _ ))) =[i]
nonRef i@(Compose (Unlabeled  (Attr _ _ ))) =[i]
nonRef (Compose (Unlabeled  ((FKT i  _ _ )))) = concat (nonRef <$> i)
nonRef (Compose (Labeled _ ((FKT i  _ _ )))) = concat (nonRef <$> i)
nonRef (Compose (Unlabeled (IT j k ))) = nonRef j
nonRef (Compose (Labeled _ (IT j k ))) = nonRef j

-- nonRef i = errorWithStackTrace (show i)

-- joinNonRef :: Ord k => TB2 k a -> TB2 k a
-- joinNonRef = fmap joinNonRef'

-- joinNonRef' :: Ord k => TB3Data f k a -> TB3Data f k a
joinNonRef' (m,n)  = (m, mapComp (rebuildTable . _kvvalues) n)
  where
    -- compJoin :: Monad f => Compose f (Compose f g ) k  a -> Compose f g k a
    compJoin :: (Functor f, Monad f) =>
         Compose f (Compose f g) k a -> Compose f g k a
    compJoin = Compose . join . fmap getCompose . getCompose
    rebuildTable n =     fmap compJoin . traComp nonRef <$> n
    nonRef :: (Monad f,Traversable  f,Ord k) => TB f k a -> [Compose f (TB f ) k a]
    nonRef (Attr k v ) = [Compose . return $ Attr k v]
    nonRef (FKT i _ _ ) = tra
        where tra = concat ( fmap compJoin   . traComp  nonRef <$> i)
    nonRef it@(IT j k ) =  [Compose . return $ (IT  j k ) ]

flattenMap ::  Ord k => TB3Data (Labeled Text) k a -> [Compose (Labeled Text) (TB (Labeled Text) )  k a]
flattenMap (m,n)  = (concat . fmap nonRef . F.toList . _kvvalues) (head . F.toList $  getCompose n)
  where
    -- compJoin :: Monad f => Compose f (Compose f g ) k  a -> Compose f g k a
    nonRef :: (Ord k) => Compose (Labeled Text) (TB (Labeled Text)) k a ->  [Compose (Labeled Text) (TB (Labeled Text) )  k a]
    nonRef (Compose (Labeled l (Attr k v ))) = [Compose (Labeled l ( Attr k v))]
    -- nonRef (FKT i _ _ ) = tra
        -- where tra = concat ( fmap compJoin   . traComp  nonRef <$> i)
    nonRef (Compose (Labeled l it@(IT j k ))) =   concat $ flattenMap <$> (F.toList k  )
    nonRef (Compose (Unlabeled it@(IT j k ))) =   concat $ flattenMap <$> (F.toList k  )

flattenNonRec ::  Ord k => [MutRec [[Rel k]]] -> TB3Data (Labeled Text) k a -> [Compose (Labeled Text) (TB (Labeled Text) )  k a]
flattenNonRec rels (m,n)  = (concat . fmap (\r -> if pred rels r then nonRef (fmap (L.drop 1) <$>   (L.filter (\(MutRec rel) -> L.any (\rel -> keyattr r == head rel )rel) rels )) r  else []  ) . F.toList . _kvvalues) (head . F.toList $  getCompose n)
  where
    -- compJoin :: Monad f => Compose f (Compose f g ) k  a -> Compose f g k a
    pred rs v = not $ L.any (\(MutRec r) ->  L.any (\r -> L.length r == 1 && last r == keyattr  v ) r ) rs
    nonRef :: (Ord k) => [MutRec [[Rel k]]] -> Compose (Labeled Text) (TB (Labeled Text)) k a ->  [Compose (Labeled Text) (TB (Labeled Text) )  k a]
    nonRef r (Compose (Labeled l (Attr k v ))) = [Compose (Labeled l ( Attr k v))]
    nonRef r (Compose (Labeled l (FKT i _ k ))) = tra
        where tra = i <> concat  (flattenNonRec r <$> (F.toList k))
    nonRef r (Compose (Unlabeled (FKT i _ k ))) = tra
        where tra = i <> concat  (flattenNonRec r <$> (F.toList k))
    nonRef r (Compose (Labeled l it@(IT j k ))) =   concat $ flattenNonRec r <$> (F.toList k  )
    nonRef r (Compose (Unlabeled it@(IT j k ))) =   concat $ flattenNonRec r <$> (F.toList k  )

flattenRec ::  (Show a, Show k ,Ord k) => [MutRec [Set (Rel k)]] -> TB3Data (Labeled Text) k a -> [Compose (Labeled Text) (TB (Labeled Text) )  k a]
flattenRec rels (m,n)  = (concat . fmap (\r -> if pred rels r then nonRef (fmap (L.drop 1)   <$> (L.filter (\(MutRec rel) -> L.any (\rel -> Set.fromList (keyattr r ) == head rel ) rel ) rels )) r  else []  ) . F.toList . _kvvalues) (head . F.toList $  getCompose n)
  where
    -- compJoin :: Monad f => Compose f (Compose f g ) k  a -> Compose f g k a
    pred rs v = L.any (\(MutRec r) ->   L.any (\r -> head r == Set.fromList (keyattr  v )) r  ) rs
    nonRef :: (Show a, Show k,Ord k) => [MutRec [Set (Rel k)]] -> Compose (Labeled Text) (TB (Labeled Text)) k a ->  [Compose (Labeled Text) (TB (Labeled Text) )  k a]
    nonRef r  v | concat (fmap Set.toList $ concat (concat (fmap unMutRec r))) == []  = [v]
    nonRef r (Compose (Labeled l (Attr k v ))) = [Compose (Labeled l ( Attr k v))]
    nonRef r (Compose (Labeled l (FKT i _ k ))) = tra
        where tra = i <> concat  (flattenRec r <$> (F.toList k))
    nonRef r (Compose (Unlabeled (FKT i _ k ))) = tra
        where tra = i <> concat  (flattenRec r <$> (F.toList k))
    nonRef r (Compose (Labeled l it@(IT j k ))) =   concat $ flattenRec r <$> (F.toList k  )
    nonRef r (Compose (Unlabeled it@(IT j k ))) =   concat $ flattenRec r <$> (F.toList k  )

filterRec ::  (Functor f,Show a, Show k ,Ord k) => [MutRec [[Rel k]]] -> TB3Data f k a -> TB3Data f k a
filterRec rels (m,n)  = (m, mapComp (KV . fmap (mapComp (nonRef (fmap (L.drop 1) <$> rels))) . Map.filterWithKey (\k _ -> pred rels  k ) . _kvvalues )  n  )
  where
    pred rs v = L.any (\(MutRec r) ->  L.any (\r ->   Set.fromList (head r) == v ) r ) rs
    nonRef :: (Functor f,Show a, Show k,Ord k) => [MutRec [[Rel k]]] -> TB f k a ->  TB f   k a
    nonRef r  v | concat (concat (concat (fmap unMutRec r))) == []  = v
    nonRef r (FKT i rel k) = FKT i rel (filterRec r <$> k)
    nonRef r (IT j k ) =   IT j (filterRec r <$> k )
    nonRef r i = i

filterNonRec ::  (Functor f,Show a, Show k ,Ord k) => [MutRec [[Rel k]]] -> TB3Data f k a -> TB3Data f k a
filterNonRec rels (m,n)  = (m, mapComp (KV . fmap (mapComp (nonRef (fmap (L.drop 1) <$> rels))) . Map.filterWithKey (\k _ -> pred rels  k ) . _kvvalues )  n  )
  where
    pred rs v = not $ L.any (\(MutRec r) ->  L.any (\r -> L.length r == 1 && Set.fromList (last r) == v) r   ) rs
    nonRef :: (Functor f,Show a, Show k,Ord k) => [MutRec [[Rel k]]] -> TB f k a ->  TB f   k a
    nonRef r (FKT i rel k) = FKT i rel (filterNonRec r <$> k)
    nonRef r (IT j k ) =   IT j (filterNonRec r <$> k )
    nonRef r i = i


-- unlabelIT ::  (Functor f,Show a, Show k ,Ord k) => [[[Rel k]]] -> TB3Data f k a -> TB3Data f k a
unlabelIT (m,n)  = (m, mapComp (KV . fmap (Compose . nonRef  .getCompose) . _kvvalues )  n  )
  where
    nonRef  (Labeled l (IT j k )) =   Unlabeled (IT j (unlabelIT  <$> k ))
    nonRef  i = i





tableNonRef :: Ord k => TB2 k a -> TB2 k a
tableNonRef = fmap tableNonRef'

tableNonRef' :: Ord k => TBData k a -> TBData k a
tableNonRef' (m,n)  = (m, mapComp (KV . rebuildTable . _kvvalues) n)
  where
    rebuildTable n = mapFromTBList .  concat . F.toList $  traComp nonRef <$> n
    nonRef :: Ord k => TB Identity k a -> [(TB Identity ) k a]
    nonRef (Attr k v ) = [Attr k v]
    nonRef (FKT i _ _ ) = concat (overComp nonRef <$> i)
    nonRef it@(IT j k ) = [(IT  j (tableNonRef k )) ]

nonRefTB :: Ord k => TB Identity k a -> [(TB Identity ) k a]
nonRefTB (Attr k v ) = [Attr k v]
nonRefTB (FKT i _ _ ) = concat (overComp nonRefTB <$> i)
nonRefTB it@(IT j k ) = [(IT  j (tableNonRef k )) ]


addDefault
  :: Functor g => Compose g (TB g) d a
     -> Compose g (TB g) d b
addDefault = mapComp def
  where
    def ((Attr k i)) = (Attr k (LeftTB1 Nothing))
    def ((IT  rel j )) = (IT  rel (LeftTB1 Nothing)  )
    def ((FKT at rel j )) = (FKT (addDefault <$> at) rel (LeftTB1 Nothing)  )

kattr :: Compose Identity (TB Identity  ) k a -> [FTB a]
kattr = kattri . runIdentity . getCompose
kattri (Attr _ i ) = [i]
kattri (FKT i  _ _ ) =  (L.concat $ kattr  <$> i)
kattri (IT _  i ) =  recTB i
  where recTB (TB1 (m, i) ) =  L.concat $ fmap kattr (F.toList $ _kvvalues $ runIdentity $ getCompose i)
        recTB (ArrayTB1 i ) = L.concat $ fmap recTB i
        recTB (LeftTB1 i ) = L.concat $ F.toList $ fmap recTB i

aattr = aattri . runIdentity . getCompose
aattri (Attr k i ) = [(k,i)]
aattri (FKT i  _ _ ) =  (L.concat $ aattr  <$> i)
aattri (IT _ _) = []





mapComp :: (Functor t) => (f c a -> g d b) ->  Compose t f c a -> Compose t g d b
mapComp f =  Compose. fmap  f . getCompose

traComp :: (Applicative k ,Traversable t ,Functor t )=> (f c a -> k (g d b)) ->  Compose t f c a -> k (Compose t g d b)
traComp f =  fmap Compose. traverse f . getCompose

concatComp  =  Compose . concat . fmap getCompose

tableMeta :: Ord k => TableK k -> KVMetadata k
tableMeta t = KVMetadata (rawName t) (rawSchema t) (rawPK t) (rawDescription t) (uniqueConstraint t)[] (F.toList $ rawAttrs t) (rawDelayed t) (paths' <> paths)
  where rec = filter (isRecRel.pathRel)  (Set.toList $ rawFKS t)
        same = filter ((tableName t ==). fkTargetTable . pathRel) rec
        notsame = filter (not . (tableName t ==). fkTargetTable . pathRel) rec
        paths = fmap (fmap (fmap F.toList). pathRelRel' ) notsame
        paths' = (\i -> if L.null i then [] else [MutRec i]) $ fmap ((head .unMutRec). fmap (fmap F.toList). pathRelRel' ) same


tbmap :: Ord k => Map (Set (Rel k) ) (Compose Identity  (TB Identity) k a) -> TBData k a
tbmap = (kvempty,) . Compose . Identity . KV

tbmapPK :: Ord k => Set k -> Map (Set (Rel k) ) (Compose Identity  (TB Identity) k a) -> TBData k a
tbmapPK pk = (kvempty,) . Compose . Identity . KV

tblist :: Ord k => [Compose Identity  (TB Identity) k a] -> TBData k a
tblist = tbmap . mapFromTBList

tblistPK :: Ord k => Set k -> [Compose Identity  (TB Identity) k a] -> TBData k a
tblistPK s = tbmapPK s . mapFromTBList

tblist' :: Ord k => TableK k -> [Compose Identity  (TB Identity) k a] -> TBData k a
tblist' t  = (tableMeta t, ) . Compose . Identity . KV . mapFromTBList

reclist' :: Table -> [Compose Identity  (TB Identity) Key a] -> TBData Key a
reclist' t  = (tableMeta t, ) . Compose . Identity . KV . mapFromTBList

kvempty  = KVMetadata "" ""  [] [] []  [] [] Set.empty []

instance Ord a => Ord (Interval.Interval a ) where
  compare i j = compare (Interval.upperBound i )  (Interval.upperBound j)

instance Ord k => Monoid (KV f k a) where
  mempty = KV Map.empty
  mappend (KV i ) (KV j)   =    KV (Map.union i  j)

unKV = _kvvalues . unTB

isInline (KOptional i ) = isInline i
isInline (KArray i ) = isInline i
isInline (Primitive (RecordPrim _ ) ) = True
isInline _ = False

unTB1 i = head . F.toList $ i
unTB1 i = errorWithStackTrace (show i)

-- Intersections and relations

keyAttr (Attr i _ ) = i
keyAttr i = errorWithStackTrace $ "cant find keyattr " <> (show i)

unAttr (Attr _ i) = i
unAttr i = errorWithStackTrace $ "cant find attr" <> (show i)

srange l m = IntervalTB1 $ Interval.interval (Interval.Finite l,True) (Interval.Finite m ,True)

intersectPred p@(Primitive _) op  (KInterval i) j (IntervalTB1 l )  | p == i =  Interval.member j l
intersectPred p@(KInterval j) "<@" (KInterval i) (IntervalTB1 k)  (IntervalTB1  l)  =  Interval.isSubsetOf k  l
intersectPred p@(KInterval j) "@>" (KInterval i) (IntervalTB1 k)  (IntervalTB1 l) =  flip Interval.isSubsetOf k l
intersectPred p@(KInterval j) "=" (KInterval i) (IntervalTB1 k)  (IntervalTB1 l)   =  k == l
intersectPred p@(KArray j) "<@" (KArray i) (ArrayTB1 k)  (ArrayTB1 l )   =  Set.fromList (F.toList k) `Set.isSubsetOf` Set.fromList  (F.toList l)
intersectPred p@(KArray j) "@>" (KArray i) (ArrayTB1 k)  (ArrayTB1 l )   =  Set.fromList (F.toList l) `Set.isSubsetOf` Set.fromList  (F.toList k)
intersectPred p@(KArray j) "=" (KArray i) (ArrayTB1 k)  (ArrayTB1 l )   =  k == l
intersectPred p@(Primitive _) op (KArray i) j (ArrayTB1 l )  | p == i =  elem j l
intersectPred p1@(Primitive _) op  p2@(Primitive _) j l   | p1 == p2 =  case op of
                                                                             "=" -> j ==  l
                                                                             "<" -> j < l
                                                                             ">" -> j > l
                                                                             ">=" -> j >= l
                                                                             "<=" -> j <= l
                                                                             "/=" -> j /= l

intersectPred p1 op  (KSerial p2) j (SerialTB1 l)   | p1 == p2 =  maybe False (j ==) l
intersectPred p1 op (KOptional p2) j (LeftTB1 l)   | p1 == p2 =  maybe False (j ==) l
intersectPred p1@(KOptional i ) op p2 (LeftTB1 j) l  =  maybe False id $ fmap (\m -> intersectPred i op p2 m l) j
intersectPred p1 op p2 j l   = error ("intersectPred = " <> show p1 <> show p2 <>  show j <> show l)

interPoint
  :: (Ord a ,Show a) => [Rel (FKey (KType (Prim KPrim (Text,Text))))]
     -> [TB Identity (FKey (KType (Prim KPrim (Text,Text)))) a]
     -> [TB Identity (FKey (KType (Prim KPrim (Text,Text)))) a]
     -> Bool
interPoint ks i j = (\i -> if L.null i then False else  all id  i)$  catMaybes $ fmap (\(Rel l op  m) -> {-justError "interPoint wrong fields" $-}  liftA2 (intersectPredTuple  op) (L.find ((==l).keyAttr ) i )   (L.find ((==m).keyAttr ) j)) ks

intersectPredTuple  op = (\i j-> intersectPred ( keyType (keyAttr i)) op  (keyType (keyAttr j)) (unAttr i) (unAttr j))

nonRefAttr l = concat $  fmap (uncurry Attr) . aattr <$> ( l )

makeLenses ''KV
makeLenses ''TB
makeLenses ''Rel
makeLenses ''FKey
makeLenses ''TableK

--
--- Attr Cons/Uncons
--
unIndexItens ::  Int -> Int -> Maybe (TB Identity  Key Showable) -> Maybe (TB Identity  Key Showable)
unIndexItens ix o =  join . fmap (unIndex (ix+ o) )

unIndex :: Show a => Int -> TB Identity Key a -> Maybe (TB Identity Key a )
unIndex o (Attr k (ArrayTB1 v)) = Attr (unKArray k) <$> atMay v o
unIndex o (IT na (ArrayTB1 j))
  =  IT  na <$>  atMay j o
unIndex o (FKT els rel (ArrayTB1 m)  ) = (\li mi ->  FKT  (nonl <> fmap (mapComp (firstTB unKArray) )li) (Le.over relOrigin (\i -> if isArray (keyType i) then unKArray i else i ) <$> rel) mi ) <$> (maybe (Just []) (Just .pure ) (join (traComp (traFAttr (indexArray o))  <$> l))) <*> (atMay m o)
  where
    l = L.find (all (isArray.keyType) . fmap _relOrigin . keyattr)  els
    nonl = L.filter (not .all (isArray.keyType) . fmap _relOrigin . keyattr) els
    indexArray ix s =  atMay (unArray s) ix
unIndex o i = errorWithStackTrace (show (o,i))

unLeftKey :: (Ord b,Show b) => TB Identity Key b -> TB Identity Key b
unLeftKey (Attr k v ) = (Attr (unKOptional k) v)
unLeftKey (IT na (LeftTB1 (Just tb1))) = IT na tb1
unLeftKey i@(IT na (TB1  _ )) = i
unLeftKey (FKT ilk rel  (LeftTB1 (Just tb1))) = (FKT (mapComp (firstTB unKOptional) <$> ilk) (Le.over relOrigin unKOptional <$> rel) tb1)
unLeftKey i@(FKT ilk rel  (TB1  _ )) = i
unLeftKey i = errorWithStackTrace (show i)

unLeftItens  :: Show a => TB Identity  Key a -> Maybe (TB Identity  Key a )
unLeftItens = unLeftTB
  where
    unLeftTB (Attr k v)
      = Attr (unKOptional k) <$> unSOptional v
    unLeftTB (IT na (LeftTB1 l))
      = IT (mapComp (firstTB unKOptional) na) <$>  l
    unLeftTB i@(IT na (TB1 (_,l)))
      = Just i
    unLeftTB (FKT ifk rel  (LeftTB1 tb))
      = (\ik -> FKT ik  (Le.over relOrigin unKOptional <$> rel))
          <$> traverse ( traComp (traFAttr unSOptional) . mapComp (firstTB unKOptional )  ) ifk
          <*>  tb
    unLeftTB i@(FKT ifk rel  (TB1  _ )) = Just i
    unLeftTB i = errorWithStackTrace (show i)

renderShowable :: FTB Showable -> String
renderShowable (LeftTB1 i ) = maybe "" renderShowable i
renderShowable (DelayedTB1 i ) =  maybe "<NotLoaded>" (\i -> "<Loaded| " <> renderShowable i <> "|>") i
renderShowable (SerialTB1 i ) = maybe "" renderShowable i
renderShowable (ArrayTB1 i)  = L.intercalate "," $ F.toList $ fmap renderShowable i
renderShowable (IntervalTB1 i)  = showInterval renderShowable i
  where
    showInterval f i | i == Interval.empty = show i
    showInterval f (Interval.Interval (ER.Finite i,j) (ER.Finite l,m) ) = ocl j <> f i <> "," <> f l <> ocr m
      where
        ocl j = if j then "[" else "("
        ocr j = if j then "]" else ")"
    showInterval f i = show i -- errorWithStackTrace (show i)


renderShowable (TB1  i) = renderPrim i

renderPrim :: Showable -> String
renderPrim (SText a) = T.unpack a
renderPrim (SNumeric a) = show a
renderPrim (SBoolean a) = show a
renderPrim (SDouble a) = show a
renderPrim (STimestamp a) = show a
renderPrim (SLineString a ) = show a
renderPrim (SBounding a ) = show a
renderPrim (SDate a) = show a
renderPrim (SDayTime a) = show a
renderPrim (SBinary _) = show "<Binary>"
renderPrim (SDynamic s) = renderShowable s
renderPrim (SPosition a) = show a
renderPrim (SPInterval a) = show a



attrOptional :: TB Identity Key Showable ->  (TB Identity  Key Showable)
attrOptional (Attr k v) =  Attr (kOptional k) (LeftTB1 . Just $ v)
attrOptional (FKT ifk rel  tb)  = FKT (tbOptional <$> ifk) (Le.over relOrigin kOptional <$> rel) (LeftTB1 (Just tb))
  where tbOptional = mapComp (firstTB kOptional) . mapComp (mapFAttr (LeftTB1 . Just))
attrOptional (IT na j) = IT  na (LeftTB1 (Just j))

leftItens :: TB Identity Key a -> Maybe (TB Identity  Key Showable) -> Maybe (TB Identity  Key Showable)
leftItens tb@(Attr k _ ) =  maybe emptyAttr (Just .attrOptional)
  where emptyAttr = Attr k <$> (showableDef (keyType k))
leftItens tb@(IT na _ ) =   Just . maybe  emptyIT attrOptional
  where emptyIT = IT  na  (LeftTB1 Nothing)
leftItens tb@(FKT ilk rel _) = Just . maybe  emptyFKT attrOptional
  where emptyFKT = FKT (mapComp (mapFAttr (const (LeftTB1 Nothing))) <$> ilk) rel (LeftTB1 Nothing)


attrArray back@(Attr  k _) oldItems  = (\tb -> Attr k (ArrayTB1 tb)) $ (\(Attr _ v) -> v) <$> oldItems
attrArray back@(FKT _ _ _) oldItems  = (\(lc,tb) ->  FKT [Compose $ Identity $ Attr (kArray $ _relOrigin $  head $ keyattr (head lc )) (ArrayTB1 $ concat  $  kattr  <$> lc)] (_fkrelation back) (ArrayTB1 tb  ) )  $ unzip $ (\(FKT [lc] rel tb ) -> (lc , tb)) <$> oldItems
attrArray back@(IT _ _) oldItems  = (\tb ->  IT  (_ittableName back) (ArrayTB1 tb  ) )  $ (\(IT _ tb ) -> tb) <$> oldItems


keyOptional (k,v) = (kOptional k ,LeftTB1 $ Just v)

unKeyOptional (k  ,(LeftTB1 v) ) = fmap (unKOptional k,) v

kOptional = Le.over keyTypes KOptional
kArray = Le.over keyTypes KArray
kDelayed = Le.over keyTypes KDelayed

unKOptional (Key a  v c m n d (KOptional e)) = (Key a  v c m n d e )
unKOptional (Key a  v c m n d (e@(Primitive _))) = (Key a  v c m n d e )
unKOptional i = errorWithStackTrace ("unKOptional" <> show i)

unKDelayed (Key v a  c m n d (KDelayed e)) = (Key v a  c m n d e )
unKDelayed i = errorWithStackTrace ("unKDelayed" <> show i)

unKArray (Key a v c d m n (KArray e)) = Key a v  c d  m n e
unKArray (Key a v c d m n e) = Key a  v c d  m n e

tableKeys (TB1  (_,k) ) = concat $ fmap (fmap _relOrigin.keyattr) (F.toList $ _kvvalues $  runIdentity $ getCompose $ k)
tableKeys (LeftTB1 (Just i)) = tableKeys i
tableKeys (ArrayTB1 [i]) = tableKeys i

recOverAttr :: Ord k => [Set(Rel k)] -> TB Identity k a -> (Map (Set (Rel k )) (Compose Identity (TB Identity) k a ) -> Map (Set (Rel k )) (Compose Identity (TB Identity) k a ))
recOverAttr (k:[]) attr = Map.insert k (_tb attr )
recOverAttr (k:xs) attr = Map.alter (fmap (mapComp (Le.over fkttable (fmap (fmap (mapComp (KV . recOverAttr xs attr . _kvvalues )))))))  k

recOverMAttr' :: [Set (Rel Key)] -> [[Set (Rel Key)]] -> Map (Set (Rel Key)) (Compose Identity (TB Identity ) Key b ) ->Map (Set (Rel Key)) (Compose Identity (TB Identity ) Key b )
recOverMAttr' tag tar  m =   foldr go m tar
  where
    go (k:[]) = Map.alter (fmap (mapComp (Le.over fkttable (fmap (fmap (mapComp (KV . recOverAttr tag  recv . _kvvalues ))))) )) k
      where recv = gt tag m
    go (k:xs) = Map.alter (fmap (mapComp (Le.over fkttable (fmap (fmap (mapComp (KV . go xs . _kvvalues )))) ))) k

    gt (k:[]) = unTB . fromJust  . Map.lookup k
    gt (k:xs) = gt xs . _kvvalues . unTB . snd . head .F.toList. _fkttable . unTB  . fromJust . Map.lookup k

replaceRecRel :: Map (Set (Rel Key)) (Compose Identity (TB Identity ) Key b ) -> [MutRec [Set (Rel Key) ]] -> Map (Set (Rel Key)) (Compose Identity (TB Identity ) Key b )
replaceRecRel = foldr (\(MutRec l) v  -> foldr (\a -> recOverMAttr' a l )   v l)

unKOptionalAttr (Attr k i ) = Attr (unKOptional k) i
unKOptionalAttr (IT  r (LeftTB1 (Just j))  ) = (\j-> IT   r j )    j
unKOptionalAttr (FKT i  l (LeftTB1 (Just j))  ) = FKT (fmap (mapComp (first unKOptional) ) i)  l j

unOptionalAttr (Attr k i ) = Attr (unKOptional k) <$> unSOptional i
unOptionalAttr (IT r (LeftTB1 j)  ) = (\j-> IT   r j ) <$>     j
unOptionalAttr (FKT i  l (LeftTB1 j)  ) = liftA2 (\i j -> FKT i  l j) (traverse ( traComp (traFAttr unSOptional) . (mapComp (firstTB unKOptional)) ) i)  j



