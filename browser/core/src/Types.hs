{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TypeFamilies#-}
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

module Types  where

import Data.Ord
import qualified NonEmpty as Non
import NonEmpty (NonEmpty(..))
import Control.Lens.TH
import qualified Control.Lens as Le
import Data.Functor.Apply
import Utils
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


isSerial (KSerial _) = True
isSerial _ = False

isPrim (Primitive i) = True
isPrim i = False

isOptional (KOptional _) = True
isOptional _ = False

unkvlist :: KV f k a -> [f k a]
unkvlist = F.toList . _kvvalues

kvlist :: (Foldable f, Ord k )=> [Compose f (TB f ) k a] -> KV (Compose f (TB f )) k a
kvlist = KV. mapFromTBList

isArray :: KType i -> Bool
isArray (KArray _) = True
isArray (KOptional i) = isArray i
isArray _ = False

type PGType = (Text,Text)
type PGKey = FKey (KType PGPrim )
type PGRecord = (Text,Text)
type PGPrim =  Prim PGType PGRecord
type CorePrim = Prim KPrim (Text,Text)
type CoreKey = FKey (KType CorePrim)

unArray' (ArrayTB1 s) =  s
unArray' o  = Non.fromList [o] -- errorWithStackTrace $ "unArray' no pattern " <> show o

unArray (ArrayTB1 s) =  s
unArray o  = errorWithStackTrace $ "unArray no pattern " <> show o

unSOptional (LeftTB1 i) = i
unSOptional i = (Just i)-- traceShow ("unSOptional No Pattern Match SOptional-" <> show i) (Just i)

unSOptional' (LeftTB1 i ) = i
unSOptional' (SerialTB1 i )  = i
unSOptional' (DelayedTB1 i )  = i
unSOptional' i   = Just i

unSComposite (ArrayTB1 i) = i
unSComposite i = errorWithStackTrace ("unSComposite " <> show i)

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

isFunction :: SqlOperationK k -> Bool
isFunction (FunctionField _ _ _) = True
isFunction i = False

isRecRel (RecJoin _ _ ) =  True
isRecRel i = False

pathRel (Path _ rel  ) = rel
pathRelRef (Path ifk _  ) = ifk

pathRelRel :: Ord k => Path (Set k ) (SqlOperationK k) -> Set (Rel k)
pathRelRel (Path _ (FKJoinTable  rel   _ )  ) = Set.fromList rel
pathRelRel (Path r (FKInlineTable  _  )   ) = Set.map Inline r
pathRelRel (Path r (RecJoin l rel )   ) =  pathRelRel (Path r rel )
pathRelRel (Path r (FunctionField _ _ a ) ) =  Set.map Inline r <> (S.fromList $ relAccesGen <$> a)


pathRelRel' :: Ord k => Path (Set k ) (SqlOperationK k) -> MutRec [Set (Rel k )]
pathRelRel' (Path r (RecJoin l rel )   )
  | L.null (unMutRec l) =  MutRec [[pathRelRel (Path r rel )]]
  | otherwise = fmap ((pathRelRel (Path r rel ) :) . fmap (Set.fromList)) l



newtype Compose f g k a = Compose {getCompose :: f (g k a) } deriving (Functor,Foldable,Traversable,Ord,Eq,Show,Generic)

data Path a b
  = Path  a  b
  deriving(Eq,Ord,Show ,Functor)


newtype KV f k a
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

data Access a
  = IProd Bool [a]
  | ISum  [Access a]
  | Nested (Access a) (Access a)
  | Rec Int (Access a)
  | Point Int
  | Many [Access a]
  deriving(Show,Eq,Ord,Functor,Foldable,Traversable,Generic)

data BoolCollection a
 = AndColl [BoolCollection a]
 | OrColl [BoolCollection a]
 | PrimColl a
 deriving(Show,Eq,Ord,Functor,Foldable)

type AccessOp a= Either (FTB a, BinaryOperator) UnaryOperator

data UnaryOperator
  = IsNull
  | Not UnaryOperator
  deriving(Eq,Ord,Show)

renderUnary (Not i) = "not " <> renderUnary i
renderUnary IsNull = "null"
renderUnary i = errorWithStackTrace (show i)

renderBinary (Flip (Flip i)) = renderBinary i
renderBinary Contains  = "@>"
renderBinary (Flip Contains) = "<@"
renderBinary Equals = "="
renderBinary (Flip Equals )= "="
renderBinary IntersectOp = "&&"
renderBinary (Flip IntersectOp )= "&&"
renderBinary (AllOp op) = renderBinary op <> " all"
renderBinary (AnyOp op) = renderBinary op <> " any"
renderBinary (Flip (AllOp op)) = " all" <> renderBinary op
renderBinary (Flip (AnyOp op)) = " any" <> renderBinary op
renderBinary i = errorWithStackTrace (show i)

readBinaryOp :: T.Text -> BinaryOperator
readBinaryOp "=" = Equals
readBinaryOp "@>" = Contains
readBinaryOp "<@" = Flip Contains
readBinaryOp "&&" = IntersectOp
readBinaryOp "= all" = AllOp Equals
readBinaryOp "@> all" = AllOp Contains
readBinaryOp "<@ all" = AllOp (Flip Contains)
readBinaryOp "= any" = AnyOp Equals
readBinaryOp "@> any" = AnyOp Contains
readBinaryOp "<@ any" = AnyOp (Flip Contains)
readBinaryOp i = errorWithStackTrace (show i)


data BinaryOperator
  = AllOp BinaryOperator
  | Contains
  | Equals
  | IntersectOp
  | Flip BinaryOperator
  | AnyOp BinaryOperator
  deriving (Eq,Ord,Show,Generic)
instance Binary BinaryOperator

type WherePredicate = TBPredicate Key Showable

newtype TBPredicate k a
  = WherePredicate (BoolCollection (Access k ,AccessOp a ))
  deriving (Show,Eq,Ord)


kvfullname m = _kvschema m <> "." <> _kvname m
data KVMetadata k
  = KVMetadata
  { _kvname :: Text
  , _kvschema :: Text
  , _kvscopes  :: [k]
  , _kvpk :: [k]
  , _kvdesc :: [k]
  , _kvuniques :: [[k]]
  , _kvorder :: [(k,Order)]
  , _kvattrs :: [k]
  , _kvdelayed :: [k]
  , _kvrecrels :: [MutRec [[Rel k]]]
  }deriving(Functor,Foldable,Generic)

instance Eq (KVMetadata k) where
  i == j = _kvschema  i  == _kvschema j &&  _kvname i == _kvname j
instance Eq k => Ord (KVMetadata k) where
  compare  = comparing _kvschema  <> comparing _kvname

instance Show k => Show (KVMetadata k) where
  show k = T.unpack (_kvname k)

kvMetaFullName m = _kvschema m <> "." <> _kvname m

filterTB1 f = fmap (filterTB1' f)
filterTB1' f ((m ,i)) = (m , mapComp (filterKV f) i)
mapTB1  f (TB1 (m, i))  =  TB1 (m ,mapComp (mapKV f) i )
mapBothKV :: Ord b => (a -> b) -> (f a c -> g b d) -> KV f a c -> KV g b d
mapBothKV k f (KV  n) =  KV  (Map.mapKeys (S.map (fmap k )) $ fmap f n)

mapKV f (KV  n) =  KV  (fmap f n)

traverseKV f (KV  n) =  KV  <$> traverse f n
filterKV i (KV n) =  KV $ Map.filterWithKey (\k ->  i. snd) n
findKV i (KV  n) =  L.find (i . snd) $Map.toList  n
findTB1  i (TB1 (m, j) )  = mapComp (Compose . findKV i) j
-- findTB1  l (LeftTB1  j )  = join $ findTB1  l <$> j -- errorWithStackTrace (show m)

findTB1'  i (TB1 (m, j) )  = Map.lookup  i (_kvvalues $ runIdentity $ getCompose j  )
findTB1'  i (LeftTB1  j )  = join $ findTB1' i <$> j


mapTBF f (Attr i k) = (Attr i k )
mapTBF f (IT i k) = IT i ((mapFTBF f) k)
mapTBF f (FKT i  r k) = FKT  (mapKV (Compose .  fmap (mapTBF f) . f .   getCompose) i)   r  (mapFTBF f k)

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

type Key = CoreKey -- FKey (KType  (Prim (Text,Text) (Text,Text)))

data FKey a
    = Key
    { keyValue :: Text
    , keyTranslation ::  (Maybe Text)
    , keyModifier :: [FieldModifier]
    , keyPosition :: Int
    , keyStatic :: Maybe (FTB Showable)
    , keyFastUnique ::  Unique
    , _keyTypes ::  a
    }deriving(Functor,Generic)

instance (Functor f ,Bifunctor g)  => Bifunctor (Compose f g ) where
  first f  = Compose . fmap (first f) . getCompose
  second f = Compose . fmap (second f) . getCompose

keyType = _keyTypes

data Rel k
  = Inline
  {_relOri :: k
  }
  | Rel
  { _relOri :: k
  , _relOperator:: BinaryOperator
  , _relTip :: k
  }
  | RelAccess
  { _relOri :: k
  , _relAccess :: (Rel k)
  }
  deriving(Eq,Show,Ord,Functor,Foldable,Generic)


_relTarget (Rel _ _ i ) =  i
_relTarget (RelAccess _ i) = _relTarget i
_relTarget i = errorWithStackTrace (show i)

_relOrigin (Rel i _ _) = i
_relOrigin (Inline i) = i
_relOrigin (RelAccess _ i) = _relOrigin i
_relRoot  (Rel i _ _ ) = i
_relRoot  (Inline i  ) = i
_relRoot  (RelAccess i _ ) = i

instance Binary Sess.Session where
  put i = return ()
  get = error ""
instance Binary Order
instance Binary a => Binary (NonEmpty a) where
instance Binary a => Binary (KType a)
instance (Binary (f (g k a)) ) => Binary (Compose f g k a )
instance (Binary (f k a) ,Binary k ) => Binary (KV f k a)
instance Binary k => Binary (Rel k)
instance Binary a => Binary (Identity a)
instance (Binary (f (KV (Compose f (TB f)) g k)) , Binary (f (KV (Compose f (TB f)) g ())) , Binary (f (TB f g ())) ,Binary (f (TB f g k)), Binary k ,Binary g) => Binary (TB f g k )
instance Binary a => Binary (FTB a)
instance Binary k => Binary (KVMetadata k )
instance Binary k => Binary (Access k)
instance Binary Expr

instance Binary a => Binary (Interval.Extended a) where
  put (Interval.Finite a ) = B.put a
  get = Interval.Finite <$> B.get
instance Binary a => Binary ( Interval.Interval a)  where
  put (Interval.Interval i j ) = B.put i >> B.put j
  get = liftA2 Interval.Interval B.get B.get


instance Binary Position
instance Binary Bounding
instance Binary LineString
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



data TB f k a
  = Attr
    { _tbattrkey ::  k
    , _tbattr ::  FTB a
    }
  | Fun
    { _tbattrkey :: k
    , _fundata :: (Expr,[Access k])
    , _tbattr :: FTB a
    }
  | IT -- Inline Table
    { _tbattrkey ::  k
    , _fkttable ::   (FTB1 f  k a)
    }
  | FKT -- Foreign Table
    { _tbref ::  (KV (Compose f (TB f)) k a)
    , _fkrelation ::  [Rel k]
    , _fkttable ::   (FTB1 f  k a)
    }
  deriving(Functor,Foldable,Traversable,Generic)

deriving instance (Eq (f (TB f k a )), Eq (f (KV (Compose f (TB f)) k ())) ,Eq (f (TB f k () )) , Eq ( (FTB1 f  k a )) ,Eq a , Eq k ) => Eq (TB f k a)
deriving instance (Ord (f (TB f k a )), Ord (f (KV (Compose f (TB f)) k ())), Ord (f (TB f k () )) , Ord ( (FTB1 f  k a )) ,Ord a , Ord k ) => Ord (TB f k a)
deriving instance (Show (f (TB f k a )), Show (f (KV (Compose f (TB f)) k ())),Show (f (TB f k () )) , Show ( (FTB1 f k a )) ,Show (FTB a),Show a , Show k ) =>Show (TB f k a)

type TB1 a = TB2 Key a
type TB2 k a = TB3 Identity k a
type TB3 f k a = FTB1 f k a



filterKey' f ((m ,k) ) = (m,) . mapComp (\(KV kv) -> KV $ Map.filterWithKey f kv )  $  k
filterKey f = fmap f


newtype MutRec a = MutRec {unMutRec ::  [a] }deriving(Eq,Ord,Show,Functor,Foldable,Generic,Binary)

traFAttr :: (Traversable g ,Applicative f) => ( FTB a -> f (FTB a) ) -> TB g k a -> f (TB g k a)
traFAttr f (Attr i v)  = Attr i <$> f v
traFAttr f (IT i v)  = IT i <$> traverse (traFValue f) v
traFAttr f (FKT  i rel v)  = liftA2 (\a b -> FKT a rel b)  ((traverseKV (traComp (traFAttr f))) i) (traverse (traFValue f) v)

traFValue :: (Traversable g ,Applicative f) => ( FTB a -> f (FTB a) ) -> TB3Data g k a -> f (TB3Data g k a)
traFValue f (m ,k) =  fmap ((m,)). traComp (fmap KV . traverse (traComp (traFAttr f)) . _kvvalues )  $  k



mapFAttr f (Attr i v)  = (Attr i (f v))
mapFAttr f (IT i v)  = IT i (mapFValue f v)
mapFAttr f (FKT  i rel v)  = FKT (mapKV (mapComp (mapFAttr f) ) i) rel  (mapFValue f v)

mapFValue f = fmap (mapFValue' f)
mapFValue' f ((m ,k) ) = (m,) . mapComp (KV . fmap (mapComp (mapFAttr f)) . _kvvalues )  $  k

mapRecord  f (m ,k)  = (m,) . mapComp (fmap  f)  $  k

mapValue' f ((m ,k) ) = (m,) . mapComp (fmap  f)  $  k
mapValue f = fmap (mapValue' f)


mapTable f (kv,m) = (kv,mapComp (KV. fmap (mapComp (mapTableAttr f )) . _kvvalues )  m )

mapTableAttr  f (IT l j ) =  IT l (f  (mapTable f <$> j))
mapTableAttr  f (FKT l rel j ) =  FKT l rel (f  (mapTable f <$> j))
mapTableAttr f  i = i

mapKey' :: Ord b => Functor f => (a -> b) -> TB3Data f a c -> TB3Data f b c
mapKey f = fmap (mapKey' f)
mapKey' f ((m ,k) ) = (fmap f m,) . mapComp (firstKV f)  $  k



firstKV :: (Ord k ,Functor f) => (c -> k) -> KV (Compose f (TB f))c a -> KV (Compose f (TB f))k a
firstKV  f (KV m ) = KV . fmap (mapComp (firstTB f) ) . Map.mapKeys (Set.map (fmap f)) $ m
secondKV  f (KV m ) = KV . fmap (second f ) $ m

firstTB :: (Ord k, Functor f) => (c -> k) -> TB f c a -> TB f k a
firstTB f (Attr k i) = Attr (f k) i
firstTB f (Fun k i l ) = Fun (f k) (fmap (fmap f) <$> i) l
firstTB f (IT k i) = IT (f k) (fmap (mapKey' f) i)
firstTB f (FKT k  m  i) = FKT  (mapBothKV (f) (mapComp (firstTB f)) k)  (fmap f  <$> m) (fmap (mapKey' f) i)

data FTB a
  = TB1 a
  | LeftTB1   (Maybe (FTB a))
  | SerialTB1 (Maybe (FTB a))
  | IntervalTB1 (Interval.Interval (FTB a))
  | DelayedTB1 (Maybe (FTB a))
  | ArrayTB1  (NonEmpty (FTB a))
  deriving(Eq,Ord,Show,Functor,Foldable,Traversable,Generic)

instance Applicative FTB where
  pure = TB1
  TB1 i <*> TB1 j = TB1 $ i  j

  LeftTB1 i <*> LeftTB1 j = LeftTB1 $ liftA2 (<*>) i j
  i <*> LeftTB1 j = LeftTB1 $ fmap (i <*>)  j
  LeftTB1 i <*> j = LeftTB1 $ fmap (<*>j)  i

  DelayedTB1 i <*> DelayedTB1 j = DelayedTB1 $ liftA2 (<*>) i j
  i <*> DelayedTB1 j = DelayedTB1 $ fmap (i <*>)  j
  DelayedTB1 i <*> j = DelayedTB1 $ fmap (<*>j)  i

  SerialTB1 i <*> SerialTB1 j = SerialTB1 $ liftA2 (<*>) i j
  i <*> SerialTB1 j = SerialTB1 $ fmap (i <*>)  j
  SerialTB1 i <*> j = SerialTB1 $ fmap (<*>j)  i

  ArrayTB1 i <*> ArrayTB1 j = ArrayTB1 $ liftA2 (<*>) i j
  i <*> ArrayTB1 j = ArrayTB1 $ fmap (i <*>)  j
  ArrayTB1  i <*> j = ArrayTB1 $ fmap (<*>j)  i

deriving instance Functor Interval.Interval
deriving instance Foldable Interval.Interval
deriving instance Foldable Interval.Extended
deriving instance Traversable Interval.Interval
deriving instance Traversable Interval.Extended

type FTB1 f k a = FTB (KVMetadata k, Compose f (KV (Compose f (TB f))) k a)

data KPrim
   = PText
   | PBoolean
   | PAddress
   | PInt Int
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
   | PColor
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
   deriving(Eq,Ord,Functor,Generic,Foldable,Show)


showTy f (Primitive i ) = f i
showTy f (KArray i) = "{" <>  showTy f i <> "}"
showTy f (KOptional i) = showTy f i <> "*"
showTy f (KInterval i) = "(" <>  showTy f i <> ")"
showTy f (KSerial i) = showTy f i <> "?"
showTy f (KDelayed i) = showTy f i <> "-"
showTy f (KTable i) = "t"
showTy f i = errorWithStackTrace ("no ty for " <> show   i)


instance Eq (FKey a) where
   k == l = keyFastUnique k == keyFastUnique l

instance Ord (FKey a) where
   compare i j = compare (keyFastUnique i) (keyFastUnique j)

instance Show a => Show (FKey a)where
  show k = (T.unpack $ maybe (keyValue k) id (keyTranslation  k)) <> "::" <> (show $ hashUnique $ keyFastUnique k)

showKey k  =   maybe (keyValue k)  (\t -> keyValue k <> "-" <> t ) (keyTranslation k) <> "::" <> T.pack ( show $ hashUnique $ keyFastUnique k )<> "::" <> T.pack (show $ keyStatic k) <>  "::" <> T.pack (show (keyType k) <> "::" <> show (keyModifier k) <> "::" <> show (keyPosition k )  )

newtype Position = Position (Double,Double,Double) deriving(Eq,Ord,Typeable,Show,Read,Generic)

newtype Bounding = Bounding (Interval.Interval Position) deriving(Eq,Ord,Typeable,Show,Generic)

newtype LineString = LineString (Vector Position) deriving(Eq,Ord,Typeable,Show,Read,Generic)


data Showable
  = SText Text
  | SNumeric Int
  | SBoolean Bool
  | SDouble Double
  | STimestamp LocalTime
  | SPInterval DiffTime
  | SPosition Position
  | SBounding Bounding
  | SLineString LineString
  | SDate Day
  | SDayTime TimeOfDay
  | SBinary BS.ByteString
  | SDynamic  (FTB Showable)
  | SSession Sess.Session
  deriving(Ord,Eq,Show,Generic)

instance Eq Sess.Session where
   i==  j = True

instance Ord Sess.Session where
  compare i j = compare 1 2

data Expr
  = Value Int
  | Function Text [Expr]
  deriving(Eq,Ord,Show,Generic)

type SqlOperation = SqlOperationK Key
data SqlOperationK k
  = FKJoinTable [Rel k] (Text,Text)
  | RecJoin (MutRec [[Rel k ]])  (SqlOperationK k)
  | FKInlineTable (Text,Text)
  | FunctionField k Expr [Access k]
  deriving(Eq,Ord,Show,Functor)

fkTargetTable (FKJoinTable  r tn) = snd tn
fkTargetTable (FKInlineTable tn) = snd tn
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

mapTableK f (Raw  uni s tt tr de is rn  un ra rsc rp rd rf inv rat u ) = Raw uni s tt tr (S.map f de) is rn (fmap (S.map f) un) ra (map f rsc ) (map f rp) (fmap f rd) (S.map (mapPath f )  rf )(S.map (mapPath f )  inv) (S.map f rat) (mapTableK f <$> u)
  where mapPath f (Path i j ) = Path (S.map f i) (fmap f j)

instance Show Unique where
    show i = show (hashUnique i)
instance Eq (TableK k) where
  i == j = _tableUnique i == _tableUnique j
instance Ord (TableK k) where
  compare i j = compare (_tableUnique i) (_tableUnique j)

data TableK k
  =  Raw   { _tableUnique :: Unique
           ,_rawSchemaL :: Text
           , rawTableType :: TableType
           , rawTranslation :: Maybe Text
           , rawDelayed :: (Set k)
           , rawIsSum :: Bool
           , _rawNameL :: Text
           , uniqueConstraint :: [Set k]
           , rawAuthorization :: [Text]
           , _rawScope :: [k]
           , _rawPKL :: [k]
           , _rawDescriptionL :: [k]
           , _rawFKSL ::  (Set (Path (Set k) (SqlOperationK k )))
           , _rawInvFKS ::  (Set (Path (Set k) (SqlOperationK k)))
           , rawAttrs :: (Set k)
           , rawUnion :: [TableK k ]
           }
     | Union
          { origin :: TableK k
          , unionList :: [(TableK k)]
          }
     deriving(Show)

rawFKS = _rawFKSL

unRecRel (RecJoin _ l) = l
unRecRel l = l




rawPK  (Union i _ ) = _rawPKL i
rawPK  i  = _rawPKL i
rawDescription (Union i _ ) = _rawDescriptionL i
rawDescription  i  = _rawDescriptionL i
rawName (Union i _) = _rawNameL i
rawName i  = _rawNameL i
rawSchema (Union i _) = _rawSchemaL i
rawSchema i  = _rawSchemaL i

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
  toRational (SNumeric i )=  toRational i
  toRational (SDouble i )=  toRational i

instance RealFrac Showable where
  properFraction (SDouble i) = second SDouble $ properFraction i --toRational (SDouble i )=  toRational i
  properFraction (SNumeric j ) = (fromIntegral j,SNumeric 0)

instance Integral a => Integral (FTB a) where
  toInteger (TB1 i) = toInteger i
  quotRem (TB1 i ) (TB1 j ) = (\(l,m) -> (TB1 l , TB1 m)) $ quotRem i j

instance Integral Showable where
  toInteger (SNumeric i) = toInteger i
  quotRem (SNumeric i ) (SNumeric j ) = (\(l,m) -> (SNumeric l , SNumeric m)) $ quotRem i j


instance Num a => Num (FTB a) where
  i + j = liftA2 (+) i  j
  i - j = liftA2 (-) i j
  i * j = liftA2 (*) i  j
  abs i  = fmap abs i
  signum i  = signum <$> i
  fromInteger i  = TB1 (fromInteger i )

instance Num Showable where
    SNumeric i +  SNumeric j = SNumeric (i + j)
    SDouble i +  SDouble j = SDouble (i + j)
    SDouble i + SNumeric j = SDouble $ i +  fromIntegral j
    SNumeric j  + SDouble i = SDouble $ i +  fromIntegral j
    v + k = errorWithStackTrace (show (v,k))
    SNumeric i *  SNumeric j = SNumeric (i * j)
    SNumeric i *  SDouble j = SDouble (fromIntegral i * j)
    SDouble i *  SNumeric j = SDouble (i * fromIntegral j)
    SDouble i *  SDouble j = SDouble (i * j)
    i * j = errorWithStackTrace (show (i,j))
    fromInteger i = SDouble $ fromIntegral i
    negate (SNumeric i) = SNumeric $ negate i
    negate (SDouble i) = SDouble $ negate i
    negate i = errorWithStackTrace (show i)
    abs (SNumeric i) = SNumeric $ abs i
    abs (SDouble i) = SDouble $ abs i
    signum (SNumeric i) = SNumeric $ signum i
    signum (SDouble i) = SDouble $ signum i

instance Fractional a => Fractional (FTB a) where
  fromRational i = TB1 (fromRational i)
  recip i = fmap recip i

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

mapFromTBList :: (Foldable f ,Ord k )=> [Compose f (TB f ) k  a] -> Map (Set (Rel k) ) (Compose f ( TB f ) k  a)
mapFromTBList = Map.fromList . fmap (\i -> (Set.fromList (keyattr  i),i))

keyattr :: Foldable f => Compose f (TB f ) k  a -> [Rel k]
keyattr = keyattri . head . F.toList . getCompose


relAccesGen :: Access k -> Rel k
relAccesGen (IProd i [l] ) = Inline l
relAccesGen (Nested (IProd i [l]) m ) = RelAccess l (relAccesGen m)
relAccesGen (Many [l]) = relAccesGen l

keyattri :: Foldable f => TB f  k  a -> [Rel k]
keyattri (Attr i  _ ) = [Inline i]
keyattri (Fun i  l _ ) = [Inline i] <> (relAccesGen <$> snd l)
keyattri (FKT i  rel _ ) = rel
keyattri (IT i  _ ) =  [Inline i]

-- tableAttr :: (Traversable f ,Ord k) => TB3 f k () -> [Compose f (TB f) k ()]
-- tableAttr (ArrayTB1 i) = tableAttr <$> i
-- tableAttr (LeftTB1 i ) = tableAttr<$> i
tableAttr (DelayedTB1 (Just tb)) = tableAttr tb
tableAttr (TB1 (m ,(Compose (Labeled _ (KV  n)))) ) =   concat  $ F.toList (nonRef <$> n)
tableAttr (TB1 (m ,(Compose (Unlabeled (KV  n)))) ) =   concat  $ F.toList (nonRef <$> n)

nonRef :: (Ord f,Show k ,Show f,Ord k) => Compose (Labeled f ) (TB (Labeled f) ) k () -> [Compose (Labeled f ) (TB (Labeled f) ) k ()]
nonRef i@(Compose (Labeled _ (Fun _ _ _ ))) =[i]
nonRef i@(Compose (Unlabeled  (Fun _ _ _ ))) =[i]
nonRef i@(Compose (Labeled _ (Attr _ _ ))) =[i]
nonRef i@(Compose (Unlabeled  (Attr _ _ ))) =[i]
nonRef (Compose (Unlabeled  ((FKT i  _ _ )))) = concat (nonRef <$> unkvlist i)
nonRef (Compose (Labeled _ ((FKT i  _ _ )))) = concat (nonRef <$> unkvlist i)
nonRef j@(Compose (Unlabeled (IT k v ))) = [Compose (Labeled (label $ getCompose $ snd $ head $ F.toList v) (Attr k (TB1 ()))) ]
nonRef j@(Compose (Labeled l (IT k v ))) = [Compose (Labeled l (Attr k (TB1 ()))) ]

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
    nonRef (Fun k rel v ) = [Compose . return $ Fun k rel v]
    nonRef (Attr k v ) = [Compose . return $ Attr k v]
    nonRef (FKT i _ _ ) = tra
        where tra = concat ( fmap compJoin   . traComp  nonRef <$> unkvlist i)
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
        where tra = unkvlist i <> concat  (flattenNonRec r <$> (F.toList k))
    nonRef r (Compose (Unlabeled (FKT i _ k ))) = tra
        where tra = unkvlist i <> concat  (flattenNonRec r <$> (F.toList k))
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
        where tra = unkvlist i <> concat  (flattenRec r <$> (F.toList k))
    nonRef r (Compose (Unlabeled (FKT i _ k ))) = tra
        where tra = unkvlist i <> concat  (flattenRec r <$> (F.toList k))
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




tableNonRef2 :: Ord k => TB3Data (Labeled Text) k a -> TB3Data (Labeled Text) k a
tableNonRef2 (m,n)  = (m, mapComp (KV . rebuildTable . _kvvalues) n)
  where
    rebuildTable n =    Map.unions (nonRef . getCompose <$> F.toList n)
    -- nonRef :: Ord k => TB (Labeled Text) k a -> M.Map (Rel k) (TB (Labeled Text) k  a)
    nonRef :: Ord k => Labeled Text (TB (Labeled Text) k a) -> Map (Set (Rel k )) (Compose (Labeled Text ) (TB (Labeled Text)) k a)
    nonRef (Labeled _ (Fun i _ _ )) =Map.empty
    nonRef (Unlabeled (Fun i _ _ )) = Map.empty
    nonRef (Labeled _ (FKT i _ _ )) = _kvvalues i
    nonRef (Unlabeled (FKT i _ _ )) = _kvvalues i
    nonRef (Labeled t it@(IT j k )) = Map.singleton (S.singleton $ Inline j) (Compose $ Labeled t $ IT  j (tableNonRef2 <$> k ))
    nonRef (Unlabeled it@(IT j k )) = Map.singleton (S.singleton $ Inline j) (Compose $ Unlabeled $ IT  j (tableNonRef2 <$> k ))
    nonRef i@(Labeled t (Attr j _)) = Map.singleton (S.singleton $ Inline j) (Compose i)
    nonRef i@(Unlabeled (Attr j _)) = Map.singleton (S.singleton $ Inline j) (Compose i)



tableNonRef :: Ord k => TB2 k a -> TB2 k a
tableNonRef = fmap tableNonRef'

tableNonRef' :: Ord k => TBData k a -> TBData k a
tableNonRef' (m,n)  = (m, mapComp (KV . rebuildTable . _kvvalues) n)
  where
    rebuildTable n = mapFromTBList .  concat . F.toList $  traComp nonRef <$> n
    nonRef :: Ord k => TB Identity k a -> [(TB Identity ) k a]
    nonRef (FKT i _ _ ) = concat (overComp nonRef <$> unkvlist i)
    nonRef it@(IT j k ) = [(IT  j (tableNonRef k )) ]
    nonRef i = [i]

nonRefTB :: Ord k => TB Identity k a -> [(TB Identity ) k a]
nonRefTB (FKT i _ _ ) = concat (overComp nonRefTB <$> unkvlist i)
nonRefTB it@(IT j k ) = [(IT  j (tableNonRef k )) ]
nonRefTB i  = [i]


addDefault
  :: Functor g => Compose g (TB g) d a
     -> Compose g (TB g) d b
addDefault = mapComp def
  where
    def ((Attr k i)) = (Attr k (LeftTB1 Nothing))
    def ((Fun k i _)) = (Fun k i (LeftTB1 Nothing))
    def ((IT  rel j )) = (IT  rel (LeftTB1 Nothing)  )
    def ((FKT at rel j )) = (FKT (KV $ addDefault <$> _kvvalues at) rel (LeftTB1 Nothing)  )

kattr :: Compose Identity (TB Identity  ) k a -> [FTB a]
kattr = kattri . runIdentity . getCompose
kattri :: Column k a -> [FTB a]
kattri (Attr _ i ) = [i]
kattri (Fun _ _ i ) = [i]
kattri (FKT i  _ _ ) =  (L.concat $ kattr  <$> unkvlist i)
kattri (IT _  i ) =  recTB i
  where recTB (TB1 (m, i) ) =  L.concat $ fmap kattr (F.toList $ _kvvalues $ runIdentity $ getCompose i)
        recTB (ArrayTB1 i ) = L.concat $ F.toList $ fmap recTB i
        recTB (LeftTB1 i ) = L.concat $ F.toList $ fmap recTB i

aattr = aattri . runIdentity . getCompose
aattri (Attr k i ) = [(k,i)]
aattri (Fun k _ i ) = [(k,i)]
aattri (FKT i  _ _ ) =  (L.concat $ aattr  <$> unkvlist i)
aattri (IT _ _) = []





mapComp :: (Functor t) => (f c a -> g d b) ->  Compose t f c a -> Compose t g d b
mapComp f =  Compose. fmap  f . getCompose

traComp :: (Applicative k ,Traversable t ,Functor t )=> (f c a -> k (g d b)) ->  Compose t f c a -> k (Compose t g d b)
traComp f =  fmap Compose. traverse f . getCompose


tableMeta :: Ord k => TableK k -> KVMetadata k
tableMeta (Union s l ) =  tableMeta s
tableMeta t = KVMetadata (rawName t) (rawSchema t) (_rawScope t) (rawPK t) (rawDescription t) (fmap F.toList $ uniqueConstraint t) [] (F.toList $ rawAttrs t) (F.toList $ rawDelayed t) (paths' <> paths)
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

tblistM :: Ord k => KVMetadata k -> [Compose Identity  (TB Identity) k a] -> TBData k a
tblistM t  = (t, ) . Compose . Identity . KV . mapFromTBList

reclist' :: Ord k => TableK k  -> [Compose Identity  (TB Identity) k a] -> TBData k a
reclist' t  = (tableMeta t, ) . Compose . Identity . KV . mapFromTBList

kvempty  = KVMetadata "" ""  [] [] [] [] [] [] [] []

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

unTB1 :: Show a=> FTB a -> a
unTB1 i = fromMaybe (errorWithStackTrace ("unTB1" <> show i)) . headMay . F.toList $ i

-- Intersections and relations

keyAttr (Attr i _ ) = i
keyAttr (Fun i _ _ ) = i
keyAttr i = errorWithStackTrace $ "cant find keyattr " <> (show i)

unAttr (Attr _ i) = i
unAttr (Fun _ _ i) = i
unAttr i = errorWithStackTrace $ "cant find attr" <> (show i)

srange l m = IntervalTB1 $ Interval.interval (Interval.Finite l,True) (Interval.Finite m ,True)




makeLenses ''KV
makeLenses ''TB
makeLenses ''Rel
makeLenses ''FKey
makeLenses ''TableK

--
--- Attr Cons/Uncons
--
unIndexItens :: (Show (KType k),Show a) =>  Int -> Int -> Maybe (TB Identity  (FKey (KType k))  a ) -> Maybe (TB Identity  (FKey (KType k))  a )
unIndexItens ix o =  join . fmap (unIndex (ix+ o) )

unIndex :: (Show (KType k),Show a) => Int -> TB Identity (FKey (KType k)) a -> Maybe (TB Identity (FKey (KType k)) a )
unIndex o (Attr k (ArrayTB1 v)) = Attr (unKArray k) <$> Non.atMay v o
unIndex o (IT na (ArrayTB1 j))
  =  IT  na <$>  Non.atMay j o
unIndex o (FKT els rel (ArrayTB1 m)  ) = (\li mi ->  FKT  (kvlist $ nonl <> fmap (mapComp (firstTB unKArray) )li) (Le.over relOri (\i -> if isArray (keyType i) then unKArray i else i ) <$> rel) mi ) <$> (maybe (Just []) (Just .pure ) (join (traComp (traFAttr (indexArray o))  <$> l))) <*> (Non.atMay m o)
  where
    l = L.find (all (isArray.keyType) . fmap _relOrigin . keyattr)  (unkvlist els)
    nonl = L.filter (not .all (isArray.keyType) . fmap _relOrigin . keyattr) (unkvlist els)
    indexArray ix s =  Non.atMay (unArray s) ix
unIndex o i = errorWithStackTrace (show (o,i))

unLeftKey :: (Show k,Ord b,Show b) => TB Identity (FKey (KType k)) b -> TB Identity (FKey (KType k)) b
unLeftKey (Attr k v ) = (Attr (unKOptional k) v)
unLeftKey (IT na (LeftTB1 (Just tb1))) = IT na tb1
unLeftKey i@(IT na (TB1  _ )) = i
unLeftKey (FKT ilk rel  (LeftTB1 (Just tb1))) = (FKT (kvlist $ mapComp (firstTB unKOptional) <$> unkvlist ilk) (Le.over relOri unKOptional <$> rel) tb1)
unLeftKey i@(FKT ilk rel  (TB1  _ )) = i
unLeftKey i = errorWithStackTrace (show i)

unLeftItens  :: (Show k , Show a) => TB Identity  (FKey (KType k)) a -> Maybe (TB Identity  (FKey (KType k)) a )
unLeftItens = unLeftTB
  where
    unLeftTB (Attr k v)
      = Attr (unKOptional k) <$> unSOptional v
    unLeftTB (Fun k rel v)
      = Fun (unKOptional k) rel <$> unSOptional v
    unLeftTB (IT na (LeftTB1 l))
      = IT (unKOptional na) <$>  l
    unLeftTB i@(IT na (TB1 (_,l)))
      = Just i
    unLeftTB (FKT ifk rel  (LeftTB1 tb))
      = (\ik -> FKT (kvlist ik  ) (Le.over relOri unKOptional <$> rel))
          <$> traverse ( traComp (traFAttr unSOptional) . mapComp (firstTB unKOptional )  ) (unkvlist ifk)
          <*>  tb
    unLeftTB i@(FKT ifk rel  (TB1  _ )) = Just i
    unLeftTB i = errorWithStackTrace (show i)



attrOptional :: TB Identity (FKey (KType k))  Showable ->  (TB Identity  (FKey (KType k))  Showable)
attrOptional (Attr k v) =  Attr (kOptional k) (LeftTB1 . Just $ v)
attrOptional (Fun k rel v) =  Fun (kOptional k) rel (LeftTB1 . Just $ v)
attrOptional (FKT ifk rel  tb)  = FKT (mapKV tbOptional ifk) (Le.over relOri kOptional <$> rel) (LeftTB1 (Just tb))
  where tbOptional = mapComp (firstTB kOptional) . mapComp (mapFAttr (LeftTB1 . Just))
attrOptional (IT na j) = IT  na (LeftTB1 (Just j))

leftItens :: TB Identity (FKey (KType k)) a -> Maybe (TB Identity  (FKey (KType k)) Showable) -> Maybe (TB Identity  (FKey (KType k)) Showable)
leftItens tb@(Fun k  rel _ ) =  maybe emptyAttr (Just .attrOptional)
  where emptyAttr = Fun k rel <$> (showableDef (keyType k))
leftItens tb@(Attr k _ ) =  maybe emptyAttr (Just .attrOptional)
  where emptyAttr = Attr k <$> (showableDef (keyType k))
leftItens tb@(IT na _ ) =   Just . maybe  emptyIT attrOptional
  where emptyIT = IT  na  (LeftTB1 Nothing)
leftItens tb@(FKT ilk rel _) = Just . maybe  emptyFKT attrOptional
  where
      emptyFKT = FKT (mapKV (mapComp (mapFAttr (const (LeftTB1 Nothing)))) ilk) rel (LeftTB1 Nothing)

-- mapkvlist f =  kvlist . f . unkvlist


attrArray :: TB Identity Key b -> NonEmpty (TB Identity Key Showable) -> TB Identity Key Showable
attrArray back@(Attr  k _) oldItems  = (\tb -> Attr k (ArrayTB1 tb)) $ (\(Attr _ v) -> v) <$> oldItems
attrArray back@(FKT _ _ _) oldItems  = (\(lc,tb) ->  FKT (kvlist [Compose $ Identity $ Attr (kArray $ _relOrigin $  head $ keyattr (Non.head lc )) (ArrayTB1 $ head .  kattr  <$> lc)]) (_fkrelation back) (ArrayTB1 tb  ) )  $ Non.unzip $ (\(FKT lc rel tb ) -> (head $ F.toList $ _kvvalues lc , tb)) <$> oldItems
attrArray back@(IT _ _) oldItems  = (\tb ->  IT  (_tbattrkey back) (ArrayTB1 tb  ) )  $ (\(IT _ tb ) -> tb) <$> oldItems


keyOptional (k,v) = (kOptional k ,LeftTB1 $ Just v)

unKeyOptional (k  ,(LeftTB1 v) ) = fmap (unKOptional k,) v

kOptional = Le.over keyTypes KOptional
kArray = Le.over keyTypes KArray
kDelayed = Le.over keyTypes KDelayed

unKOptional (Key a  v c m n d (KOptional e)) = (Key a  v c m n d e )
unKOptional (Key a  v c m n d (KSerial e)) = (Key a  v c m n d e )
unKOptional (Key a  v c m n d (e@(Primitive _))) = (Key a  v c m n d e )
unKOptional i = errorWithStackTrace ("unKOptional" <> show i)

unKDelayed (Key v a  c m n d (KDelayed e)) = (Key v a  c m n d e )
unKDelayed i = errorWithStackTrace ("unKDelayed" <> show i)

unKArray (Key a v c d m n (KArray e)) = Key a v  c d  m n e
unKArray (Key a v c d m n e) = Key a  v c d  m n e

tableKeys (TB1  (_,k) ) = concat $ fmap (fmap _relOrigin.keyattr) (F.toList $ _kvvalues $  runIdentity $ getCompose $ k)
tableKeys (LeftTB1 (Just i)) = tableKeys i
tableKeys (ArrayTB1 (i :| _) ) = tableKeys i

recOverAttr :: Ord k => [Set(Rel k)] -> TB Identity k a -> (Map (Set (Rel k )) (Compose Identity (TB Identity) k a ) -> Map (Set (Rel k )) (Compose Identity (TB Identity) k a ))
recOverAttr (k:[]) attr = Map.insert k (_tb attr )
recOverAttr (k:xs) attr = Map.alter (fmap (mapComp (Le.over fkttable (fmap (fmap (mapComp (KV . recOverAttr xs attr . _kvvalues )))))))  k

recOverMAttr' :: [Set (Rel Key)] -> [[Set (Rel Key)]] -> Map (Set (Rel Key)) (Compose Identity (TB Identity ) Key b ) ->Map (Set (Rel Key)) (Compose Identity (TB Identity ) Key b )
recOverMAttr' tag tar  m =   foldr go m tar
  where
    go (k:[]) = Map.alter (fmap (mapComp (Le.over fkttable (fmap (fmap (mapComp (KV . recOverAttr tag  recv . _kvvalues ))))) )) k
      where recv = gt tag m
    go (k:xs) = Map.alter (fmap (mapComp (Le.over fkttable (fmap (fmap (mapComp (KV . go xs . _kvvalues )))) ))) k

    gt (k:[]) = unTB . justError "no key" . Map.lookup k
    gt (k:xs) = gt xs . _kvvalues . unTB . snd . head .F.toList. _fkttable . unTB  . justError "no key" . Map.lookup k

replaceRecRel :: Map (Set (Rel Key)) (Compose Identity (TB Identity ) Key b ) -> [MutRec [Set (Rel Key) ]] -> Map (Set (Rel Key)) (Compose Identity (TB Identity ) Key b )
replaceRecRel = foldr (\(MutRec l) v  -> foldr (\a -> recOverMAttr' a l )   v l)

unKOptionalAttr (Attr k i ) = Attr (unKOptional k) i
unKOptionalAttr (Fun k rel i ) = Fun (unKOptional k) rel i
unKOptionalAttr (IT  r (LeftTB1 (Just j))  ) = (\j-> IT   r j )    j
unKOptionalAttr (FKT i  l (LeftTB1 (Just j))  ) = FKT (fmap (mapComp (first unKOptional) ) i)  l j

unOptionalAttr (Attr k i ) = Attr (unKOptional k) <$> unSOptional i
unOptionalAttr (Fun k rel i ) = Fun (unKOptional k) rel <$> unSOptional i
unOptionalAttr (IT r (LeftTB1 j)  ) = (\j-> IT   r j ) <$>     j
unOptionalAttr (FKT i  l (LeftTB1 j)  ) = liftA2 (\i j -> FKT i  l j) (traverseKV ( traComp (traFAttr unSOptional) . (mapComp (firstTB unKOptional)) ) i)  j



tbUn :: (Functor f,Ord k) =>   Set k -> TB3 f k a ->  Compose f (KV  (Compose f (TB f ))) k a
tbUn un (TB1 (kv,item)) =  (\kv ->  mapComp (\(KV item)->  KV $ Map.filterWithKey (\k _ -> pred kv k ) $ item) item ) un
  where pred kv k = (S.isSubsetOf (S.map _relOrigin k) kv )


getPK (TB1 i) = getPKM i
getPKM (m, k) = Map.fromList $  concat $ F.toList (fmap aattr $ F.toList $ (Map.filterWithKey (\k v -> Set.isSubsetOf  (Set.map _relOrigin k)(Set.fromList $ _kvpk m)) (  _kvvalues (unTB k))))

getAttr'  (m, k) =  L.sortBy (comparing fst) (concat (fmap aattr $ F.toList $  (  _kvvalues (runIdentity $ getCompose k))))

getPKAttr (m, k) = traComp (concat . F.toList . (Map.filterWithKey (\k v -> Set.isSubsetOf  (Set.map _relOrigin k)(Set.fromList $ _kvpk m))   )) k
getAttr (m, k) = traComp (concat . F.toList) k


getUn un (m, k) =   concat (fmap aattr $ F.toList $ (Map.filterWithKey (\k v -> Set.isSubsetOf  (Set.map _relOrigin k) un ) (  _kvvalues (unTB k))))


inlineName (KOptional i) = inlineName i
inlineName (KArray a ) = inlineName a
inlineName (Primitive (RecordPrim (s, i)) ) = (s,i)

inlineFullName (KOptional i) = inlineFullName i
inlineFullName (KArray a ) = inlineFullName a
inlineFullName (Primitive (RecordPrim (s, i)) ) = s <> "." <> i

attrT :: (a,FTB b) -> Compose Identity (TB Identity) a b
attrT (i,j) = Compose . Identity $ Attr i j


-- notOptional :: k a -> G.TBIndex k a
notOptionalPK m =  justError "cant be empty " . traverse unSOptional'  $ m

tbPK :: (Functor f,Ord k)=>TB3 f k a -> Compose f (KV  (Compose f (TB f ))) k a
tbPK = tbFilter  (\kv k -> (S.isSubsetOf (S.map _relOrigin k) (S.fromList $ _kvpk kv ) ))

tbFilter :: (Functor f,Ord k) =>  ( KVMetadata k -> Set (Rel k) -> Bool) -> TB3 f k a ->  Compose f (KV  (Compose f (TB f ))) k a
tbFilter pred (TB1 i) = tbFilter' pred i
tbFilter pred (LeftTB1 (Just i)) = tbFilter pred i
tbFilter pred (ArrayTB1 (i :| _ )) = tbFilter pred i
tbFilter pred (DelayedTB1 (Just i)) = tbFilter pred i



tbFilter' :: (Functor f,Ord k) =>  ( KVMetadata k -> Set (Rel k) -> Bool) -> TB3Data f k a ->  Compose f (KV  (Compose f (TB f ))) k a
tbFilter' pred (kv,item) =  mapComp (\(KV item)->  KV $ Map.filterWithKey (\k _ -> pred kv k ) $ item) item

txt = TB1 . SText
