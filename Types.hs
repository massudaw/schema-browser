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

-- import Warshal
import Control.Lens.TH
import Data.Functor.Apply
import Data.Bifunctor
import Data.Maybe
import GHC.Generics
import Data.Text.Binary
import Data.Binary (Binary)
import Data.Vector.Binary
import qualified Data.Binary as B
import Data.Functor.Identity
import Data.Ord
import Utils
import Data.Typeable
import qualified Data.Traversable as Tra
import Data.Vector(Vector)
import qualified Data.Vector as Vector
import Data.Functor.Classes
import Data.Foldable (Foldable)
import qualified Data.Foldable as F
import qualified Data.Interval as Interval
import Data.Monoid hiding (Product)

import qualified Data.Text.Lazy as T
import qualified Data.ByteString as BS


import GHC.Stack

import Data.Traversable(Traversable,traverse)
import Database.PostgreSQL.Simple.Time

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
import Control.Monad.State
import Data.Text.Lazy(Text)

import Data.Unique




data Compose f g k a = Compose {getCompose :: f (g k a) } deriving (Functor,Foldable,Traversable,Ord,Eq,Show,Generic)

data Path a b
  -- Trivial Path
  = Path  a  b  a
  -- | TagPath  (Cardinality (Set a))  b  (Cardinality (Set a))
  -- Path Composition And Product
  | ComposePath a (Set (Path a b),a,Set (Path a b)) a
  deriving(Eq,Ord,Show )


data KV f k a
  = KV {_kvvalues :: Map (Set (Rel k)) (f k a)  }deriving(Eq,Ord,Functor,Foldable,Traversable,Show,Generic)


data KVMetadata k
  = KVMetadata
  { _kvname :: Text
  , _kvschema :: Text
  , _kvpk :: Set k
  , _kvdesc :: [k]
  , _kvuniques :: [Set k]
  , _kvattrs :: Set k
  , _kvdelayed :: Set k
  }deriving(Eq,Ord,Show,Generic)

kvMetaFullName m = _kvschema m <> "." <> _kvname m

filterTB1 f (TB1 (m ,i)) = TB1 (m , mapComp (filterKV f) i)
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

type Key = FKey (KType Text)

data FKeyPath j
data FKey a
    = Key
    { keyValue :: ! Text
    , keyTranslation :: ! (Maybe Text)
    , keyPosition :: Int
    , keyStatic :: Maybe (FTB Showable)
    , keyFastUnique :: ! Unique
    , keyType :: ! a
    }

instance (Functor f ,Bifunctor g)  => Bifunctor (Compose f g ) where
  first f  = Compose . fmap (first f) . getCompose
  second f = Compose . fmap (second f) . getCompose


data Rel k
  = Inline  {_relOrigin :: k}
  | Rel
  { _relOrigin :: k
  , _relOperator:: Text
  , _relTarget :: k
  }
  deriving(Eq,Show,Ord,Functor,Foldable,Generic)

deriving instance Generic (Identity a)


instance (Binary a ,Binary k) => Binary (Modification k   a)
instance (Binary (f (g k a)) ) => Binary (Compose f g k a )
instance (Binary (f k a) ,Binary k ) => Binary (KV f k a)
instance Binary k => Binary (Rel k)
instance Binary a => Binary (Identity a)
instance (Binary (f (KV (Compose f (TB f)) g k)) , Binary (f (TB f g ())) ,Binary (f (TB f g k)), Binary k ,Binary g) => Binary (TB f g k )
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

deriving instance (Eq (f (TB f k a )), Eq (f (TB f k () )) , Eq ( (FTB1 f  k a )) ,Eq a , Eq k ) => Eq (TB f k a)
deriving instance (Ord (f (TB f k a )), Ord (f (TB f k () )) , Ord ( (FTB1 f  k a )) ,Ord a , Ord k ) => Ord (TB f k a)
deriving instance (Show (f (TB f k a )), Show (f (TB f k () )) , Show ( (FTB1 f k a )) ,Show (FTB a),Show a , Show k ) =>Show (TB f k a)

type TB1 a = TB2 Key a
type TB2 k a = TB3 Identity k a
type TB3 f k a = FTB1 f k a

mapKVMeta f (KVMetadata tn sch s j m k l ) =KVMetadata tn sch (Set.map f s) (map f j) (map (Set.map f) m ) (Set.map f k) (Set.map f l)


filterKey f (TB1 (m ,k) ) = TB1 . (m,) . mapComp (\(KV kv) -> KV $ Map.filterWithKey f kv )  $  k
filterKey f (LeftTB1 k ) = LeftTB1 (filterKey f <$> k)
filterKey f (ArrayTB1 k ) = ArrayTB1 (filterKey f <$> k)
  where
    frstTB f (Attr k i) = Attr  k i
    frstTB f (IT k i) = IT  k (filterKey f i)
    frstTB f (FKT k  m  i) = FKT   k  m (filterKey  f i)

traFAttr :: (Traversable g ,Applicative f) => ( FTB a -> f (FTB a) ) -> TB g k a -> f (TB g k a)
traFAttr f (Attr i v)  = Attr i <$> f v
traFAttr f (IT i v)  = IT i <$> traverse (traFValue f) v
traFAttr f (FKT  i rel v)  = liftA2 (\a b -> FKT a rel b)  (traverse (traComp (traFAttr f)) i) (traverse (traFValue f) v)

traFValue f (m ,k) =  fmap ((m,)). traComp (fmap KV . traverse (traComp (traFAttr f)) . _kvvalues )  $  k



mapFAttr f (Attr i v)  = (Attr i (f v))
mapFAttr f (IT i v)  = IT i (mapFValue f v)
mapFAttr f (FKT  i rel v)  = FKT (mapComp (mapFAttr f) <$> i) rel  (mapFValue f v)

mapFValue f (TB1 (m ,k) ) = TB1 . (m,) . mapComp (KV . fmap (mapComp (mapFAttr f)) . _kvvalues )  $  k
mapFValue f (LeftTB1 k ) = LeftTB1 (mapFValue f <$> k)
mapFValue f (DelayedTB1 k ) = DelayedTB1 (mapFValue f <$> k)
mapFValue f (ArrayTB1 k ) = ArrayTB1 (mapFValue f <$> k)



mapValue f (TB1 (m ,k) ) = TB1 . (m,) . mapComp (fmap  f)  $  k
mapValue f (LeftTB1 k ) = LeftTB1 (mapValue f <$> k)
mapValue f (DelayedTB1 k ) = DelayedTB1 (mapValue f <$> k)
mapValue f (ArrayTB1 k ) = ArrayTB1 (mapValue f <$> k)



mapKey f (TB1 (m ,k) ) = TB1 . (mapKVMeta f m,) . mapComp (firstKV f)  $  k
mapKey f (LeftTB1 k ) = LeftTB1 (mapKey f <$> k)
mapKey f (DelayedTB1 k ) = DelayedTB1 (mapKey f <$> k)
mapKey f (ArrayTB1 k ) = ArrayTB1 (mapKey f <$> k)


firstKV  f (KV m ) = KV . fmap (mapComp (firstTB f) ) . Map.mapKeys (Set.map (fmap f)) $ m
secondKV  f (KV m ) = KV . fmap (second f ) $ m

firstTB :: (Ord k, Functor f) => (c -> k) -> TB f c a -> TB f k a
firstTB f (Attr k i) = Attr (f k) i
firstTB f (IT k i) = IT (mapComp (firstTB f) k) ((mapKey f) i)
firstTB f (FKT k  m  i) = FKT  (fmap (mapComp (firstTB f) ) k)  (fmap f  <$> m) ((mapKey f) i)

data FTB a
  = TB1 a
  | LeftTB1  (Maybe (FTB a))
  | SerialTB1 (Maybe (FTB a))
  | IntervalTB1 (Interval.Interval (FTB a))
  | DelayedTB1 (Maybe (FTB a))
  | ArrayTB1 [(FTB a)]
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
   | PTimestamp
   | PInterval
   | PPosition
   | PBounding
   | PCnpj
   | PMime Text
   | PCpf
   | PBinary
   | PLineString
   deriving(Show,Eq,Ord)


data KType a
   = Primitive a
   | InlineTable {- schema -} Text {- tablename -} Text
   | KEither {- schema -} Text {- tablename -} Text
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
showTy f (KEither s i ) = "|" <>  fromString (T.unpack $ s <> "." <>  i) <> "|"
showTy f (KArray i) = "{" <>  showTy f i <> "}"
showTy f (KOptional i) = showTy f i <> "*"
showTy f (KInterval i) = "(" <>  showTy f i <> ")"
showTy f (KSerial i) = showTy f i <> "?"
showTy f (KDelayed i) = showTy f i <> "-"
showTy f (KTable i) = "t"
showTy f i = errorWithStackTrace ("no ty for " <> show   i)


instance Eq Key where
   k == l = keyFastUnique k == keyFastUnique l
   k /= l = keyFastUnique k /= keyFastUnique l

instance Ord Key where
   compare i j = compare (keyFastUnique i) (keyFastUnique j)

instance Show Key where
   -- show k = T.unpack $ maybe (keyValue k) id (keyTranslation  k)
   show k = T.unpack $ showKey k

showKey k  =   maybe (keyValue k) id  (keyTranslation k) {-<> "::" <> T.pack ( show $ hashUnique $ keyFastUnique k )<> "::" <> T.pack (show $ keyStatic k)-} <>  "::"   <> showTy id (keyType k)


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
  deriving(Ord,Eq,Show,Generic)


data SqlOperation
  = FetchTable Text
  | FKJoinTable Text [Rel Key] Text
  | RecJoin (SqlOperation)
  | FKInlineTable Text
  | FKEitherField Text
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
           , uniqueConstraint :: [Set Key]
           , rawAuthorization :: [Text]
           , rawPK :: (Set Key)
           , rawDescription :: [Key]
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
  deriving(Eq,Show,Functor,Generic)


mapMod f (EditTB i j ) = EditTB ( mapKey f i ) (mapKey f j)
mapMod f (InsertTB i  ) = InsertTB ( mapKey f i )
mapMod f (DeleteTB i  ) = DeleteTB ( mapKey f i )

unTB = runIdentity . getCompose
_tb = Compose . Identity

data Modification a b
  = EditTB (TB2 a b) (TB2 a b)
  | InsertTB (TB2 a b)
  | DeleteTB (TB2 a b)
  deriving(Eq,Show,Functor,Generic)

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
  -- quotRem i = quotRem i

instance Integral a => Integral (FTB a) where
  toInteger (TB1 i) = toInteger i

instance Integral Showable where
  toInteger (SNumeric i) = toInteger i
  quotRem (SNumeric i ) (SNumeric j ) = (\(l,m) -> (SNumeric l , SNumeric m)) $ quotRem i j


instance Num a => Num (FTB a) where
    TB1 i + TB1 j = TB1 (i + j)

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

mapFromTBList :: Ord k => [Compose Identity (TB Identity) k  a] -> Map (Set (Rel k) ) (Compose Identity ( TB Identity ) k  a)
mapFromTBList = Map.fromList . fmap (\i -> (Set.fromList (keyattr  i),i))

keyattr :: Compose Identity (TB Identity ) k  a -> [Rel k]
keyattr = keyattri . runIdentity . getCompose
keyattri (Attr i  _ ) = [Inline i]
keyattri (FKT i  rel _ ) = rel
keyattri (IT i  _ ) =  keyattr i

-- tableAttr :: (Traversable f ,Ord k) => TB3 f k () -> [Compose f (TB f) k ()]
-- tableAttr (ArrayTB1 i) = tableAttr <$> i
-- tableAttr (LeftTB1 i ) = tableAttr<$> i
tableAttr (DelayedTB1 (Just tb)) = tableAttr tb
tableAttr (TB1 (m ,(Compose (Labeled _ (KV  n)))) ) =   concat  $ F.toList (nonRef <$> n)

nonRef :: (Ord f,Show k ,Show f,Ord k) => Compose (Labeled f ) (TB (Labeled f) ) k () -> [Compose (Labeled f ) (TB (Labeled f) ) k ()]
nonRef i@(Compose (Labeled _ (Attr _ _ ))) =[i]
nonRef i@(Compose (Unlabeled  (Attr _ _ ))) =[i]
nonRef (Compose (Unlabeled  ((FKT i  _ _ )))) = concat (nonRef <$> i)
nonRef (Compose (Labeled _ ((FKT i  _ _ )))) = concat (nonRef <$> i)
nonRef (Compose (Unlabeled (IT j k ))) = nonRef j
nonRef (Compose (Labeled _ (IT j k ))) = nonRef j
nonRef i = errorWithStackTrace (show i)



tableNonRef :: Ord k => TB2 k a -> TB3 Identity k a
tableNonRef (ArrayTB1 i) = ArrayTB1 $ tableNonRef <$> i
tableNonRef (LeftTB1 i ) = LeftTB1 $ tableNonRef <$> i
tableNonRef (DelayedTB1 i ) = DelayedTB1 $ tableNonRef <$> i
tableNonRef (TB1 (m,n)  )  = TB1 (m, mapComp (\(KV n)-> KV  (mapFromTBList $ fmap (Compose . Identity ) $ concat $ F.toList $  overComp nonRef <$> n)) n)
  where
    nonRef :: Ord k => TB Identity k a -> [(TB Identity ) k a]
    nonRef (Attr k v ) = [Attr k v]
    nonRef (FKT i _ _ ) = concat (overComp nonRef <$> i)
    nonRef it@(IT j k ) = [(IT  j (tableNonRef k )) ]

tableNonRefK :: Ord k => TB2 k Showable -> TB3 Identity k Showable
tableNonRefK   = tableNonRef

addDefault
  :: Functor g => Compose g (TB f) d a
     -> Compose g (TB f) d b
addDefault = mapComp def
  where
    def ((Attr k i)) = (Attr k (LeftTB1 Nothing))
    def ((IT  rel j )) = (IT  rel (LeftTB1 Nothing)  )

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
aattri (IT _  i ) =  recTB i
  where recTB (TB1 (_, i) ) =  concat $ fmap aattr (F.toList $ _kvvalues $ runIdentity $ getCompose i)
        recTB (ArrayTB1 i ) = concat $ fmap recTB i
        recTB (LeftTB1 i ) = concat $ F.toList $ fmap recTB i
        recTB (DelayedTB1 i ) = concat $ F.toList $ fmap recTB i



addToList  (InsertTB m) =  (m:)
addToList  (DeleteTB m ) =  L.delete m
addToList  (EditTB m n ) = (map (\e-> if  (e ==  n) then  mapTB1 (\i -> maybe i snd $ getCompose $  runIdentity $ getCompose $ findTB1 (\k -> keyattr k == keyattr i  ) m ) e  else e ))


mapComp :: (Functor t) => (f c a -> g d b) ->  Compose t f c a -> Compose t g d b
mapComp f =  Compose. fmap  f . getCompose

traComp :: (Applicative k ,Traversable t ,Functor t )=> (f c a -> k (g d b)) ->  Compose t f c a -> k (Compose t g d b)
traComp f =  fmap Compose. traverse f . getCompose

concatComp  =  Compose . concat . fmap getCompose

tableMeta t = KVMetadata (rawName t) (rawSchema t) (rawPK t) (rawDescription t) (uniqueConstraint t)(rawAttrs t) (rawDelayed t)

tbmap :: Ord k => Map (Set (Rel k) ) (Compose Identity  (TB Identity) k a) -> TB3 Identity k a
tbmap = TB1 . (KVMetadata "" ""  Set.empty [] [] Set.empty Set.empty,) . Compose . Identity . KV

tbmapPK :: Ord k => Set k -> Map (Set (Rel k) ) (Compose Identity  (TB Identity) k a) -> TB3 Identity k a
tbmapPK pk = TB1 . (KVMetadata "" ""  pk  [] [] Set.empty Set.empty,) . Compose . Identity . KV

tblist :: Ord k => [Compose Identity  (TB Identity) k a] -> TB3 Identity k a
tblist = tbmap . mapFromTBList

tblistPK :: Ord k => Set k -> [Compose Identity  (TB Identity) k a] -> TB3 Identity k a
tblistPK s = tbmapPK s . mapFromTBList

tblist' :: Table -> [Compose Identity  (TB Identity) Key a] -> TB3 Identity Key a
tblist' t  = TB1 . (tableMeta t, ) . Compose . Identity . KV . mapFromTBList


instance Ord a => Ord (Interval.Interval a ) where
  compare i j = compare (Interval.upperBound i )  (Interval.upperBound j)

instance Ord k => Monoid (KV f k a) where
  mempty = KV Map.empty
  mappend (KV i ) (KV j)   =    KV (Map.union i  j)

unKV = _kvvalues . unTB

makeLenses ''KV
makeLenses ''TB
makeLenses ''Rel

