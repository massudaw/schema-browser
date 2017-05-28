{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE UndecidableInstances #-}

module Types.Common (
     module Types.Compose
    ,TB (..),TB2,TB3
    ,_fkttable
    ,mapFValue,mapFValue',mapFAttr,traFAttr,traFValue,mapValue,mapValue'
    ,keyAttr
    ,unAttr

    ,FTB (..)
    ,mapKV,findTB1,filterTB1',mapTB1,mapKey',mapKey,firstTB,mapBothKV,firstKV,secondKV,traverseKV,filterTB1,filterTB1'
    ,mapTable
    ,unTB1
    ,unSOptional ,unSOptional'
    ,unSSerial, unSDelayed
    ,unArray' , unArray

    ,KV(..)
    ,kvAttrs
    ,kvMetaFullName
    ,unKV
    ,kvlist
    ,unkvlist
    ,KVMetadata (..)
    ,mapFromTBList
    ,tblist
    ,tblistM
    ,kvempty

    ,Rel(..)
    ,_relOrigin  ,_relRoot  ,_relTarget,_relInputs,_relOutputs,iprodRef

    ,Expr (..) , Access(..)
    ,UnaryOperator(..)
    ,Constant(..)
    ,notNull
    ,keyRef
    ,BinaryOperator(..)
    ,renderUnary,readBinaryOp,renderBinary
    ,AccessOp
    ,MutRec(..)

    ,Order(..),showOrder
    ,Identity(..)
    ,_tb
    ,unTB
    ,overComp

    ,tableNonRef'
    ,keyattr
    ,kattri
    ,kattr
    ,aattr
    ,aattri
    ,relAccesGen
    ,keyattri
    ,filterRec
    ,joinNonRef'
    ,filterNonRec
    ,tableNonRef )   where

import Data.Ord
import Types.Compose
import Control.DeepSeq
import qualified NonEmpty as Non
import NonEmpty (NonEmpty(..))
import Utils
import Data.Bifunctor
import Safe
import Prelude hiding(head)
import Data.Maybe
import GHC.Generics
import Data.Binary (Binary)
import qualified Data.Binary as B
import Data.Functor.Identity
import Data.Binary.Orphans
import Data.Typeable
import Data.Vector(Vector)
import Data.Functor.Classes
import Data.Foldable (Foldable)
import qualified Data.Foldable as F
import qualified Data.Interval as Interval
import Data.Monoid hiding (Product)
import qualified Data.Text as T
import qualified Data.ByteString as BS
import GHC.Stack
import Data.Traversable(Traversable,traverse)
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


unkvlist :: KV f k a -> [f k a]
unkvlist = F.toList . _kvvalues

kvlist :: (Foldable f, Ord k )=> [Compose f (TB f ) k a] -> KV (Compose f (TB f )) k a
kvlist = KV. mapFromTBList

unArray' (ArrayTB1 s) =  s
unArray' o  = Non.fromList [o] -- errorWithStackTrace $ "unArray' no pattern " <> show o

unArray (ArrayTB1 s) =  s
unArray o  = errorWithStackTrace $ "unArray no pattern " <> show o

unSOptional (LeftTB1 i) = i
unSOptional i = (Just i)-- traceShow ("unSOptional No Pattern Match SOptional-" <> show i) (Just i)

unSOptional' (LeftTB1 i ) = i
unSOptional' i   = Just i


unSDelayed (LeftTB1 i) = i
unSDelayed i = traceShow ("unSDelayed No Pattern Match" <> show i) Nothing

unSSerial (LeftTB1 i) = i
unSSerial i = traceShow ("unSSerial No Pattern Match SSerial-" <> show i) Nothing







newtype KV f k a
  = KV {_kvvalues :: Map (Set (Rel k)) (f k a)  }deriving(Eq,Ord,Functor,Foldable,Traversable,Show,Generic)

instance Binary Order
instance NFData Order

showOrder Asc = "ASC"
showOrder Desc = "DESC"

data Order
  = Asc
  | Desc
  deriving(Eq,Ord,Show,Generic)


type Column k a = TB Identity k a
type TBData k a = (KVMetadata k,Compose Identity (KV (Compose Identity (TB Identity))) k a )
type TB3Data  f k a = (KVMetadata k,Compose f (KV (Compose f (TB f ))) k a )

keyRef k = IProd notNull k
iprodRef (IProd _ l) = l

data Access  a
  = IProd (Maybe UnaryOperator) a
  | ISum  [Access  a]
  | Nested [Access  a] (Access  a)
  | Rec Int (Access  a)
  | Point Int
  | Many [Access a]
  deriving(Show,Eq,Ord,Functor,Foldable,Traversable,Generic)

data BoolCollection a
 = AndColl [BoolCollection a]
 | OrColl [BoolCollection a]
 | PrimColl a
 deriving(Show,Eq,Ord,Functor,Foldable,Generic)

instance NFData a => NFData (BoolCollection a)

type AccessOp a= Either (FTB a, BinaryOperator) UnaryOperator

data Constant
  = CurrentTime
  | CurrentDate
  deriving(Eq,Ord,Show,Generic)

data UnaryOperator
  = IsNull
  | Not UnaryOperator
  | Range Bool UnaryOperator
  | BinaryConstant BinaryOperator Constant
  deriving(Eq,Ord,Show,Generic)

instance NFData UnaryOperator
instance Binary UnaryOperator
instance NFData Constant
instance Binary Constant

notNull = Just $ Not IsNull

renderUnary (Not i) = "not " <> renderUnary i
renderUnary IsNull = "null"
renderUnary (Range b i )= (if b then " upper" else " lower")
renderUnary i = errorWithStackTrace (show i)

renderBinary (Flip (Flip i)) = renderBinary i
renderBinary Contains  = "@>"
renderBinary (Flip Contains) = "<@"
renderBinary Equals = "="
renderBinary (Flip Equals )= "="
renderBinary (Flip (GreaterThan b)) = renderBinary( LowerThan b)
renderBinary (Flip (LowerThan b)) = renderBinary( GreaterThan b)
renderBinary (GreaterThan True )=  ">="
renderBinary (GreaterThan False)=  ">"
renderBinary (LowerThan False)=  "<"
renderBinary (LowerThan True)=  "<="
renderBinary (IntersectOp )= "&&"
renderBinary (Flip IntersectOp )= "&&"
renderBinary (AllOp op) = renderBinary op <> " all"
renderBinary (AnyOp op) = renderBinary op <> " any"
renderBinary (Flip (AllOp op)) = " all" <> renderBinary op
renderBinary (Flip (AnyOp op)) = " any" <> renderBinary op
-- Symetric Operators
renderBinary  (Flip i ) = renderBinary i
renderBinary i = errorWithStackTrace (show i)

readBinaryOp :: T.Text -> BinaryOperator
readBinaryOp "=" = Equals
readBinaryOp "@>" = Contains
readBinaryOp "<@" = Flip Contains
readBinaryOp "&&" = IntersectOp
readBinaryOp "any =" = Flip $ AnyOp Equals
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
  | GreaterThan Bool
  | LowerThan  Bool
  | IntersectOp
  | Flip BinaryOperator
  | AnyOp BinaryOperator
  deriving (Eq,Ord,Show,Generic)

instance Binary BinaryOperator
instance NFData BinaryOperator


instance Monoid (KVMetadata k ) where
  mempty = kvempty

kvAttrs m =  L.nub $ _kvattrs m <> _kvpk m <> _kvdesc m

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
  , _kvrefs :: [[Rel k]]
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
filterTB1' f (m ,i) = (m , mapComp (filterKV f) i)

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



-- Reference labeling
-- exchange label reference for values when labeled
-- inline values reference when unlabeled


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
  , _relAccess :: Rel k
  }
  | RelFun
  { _relOri :: k
  , _relReference :: [Rel k]
  }
  deriving(Eq,Show,Ord,Functor,Foldable,Generic)


_relTarget (Rel _ _ i ) =  i
_relTarget (RelAccess _ i) = _relTarget i
_relTarget i = errorWithStackTrace (show i)

_relOrigin (Rel i _ _) = i
_relOrigin (Inline i) = i
_relOrigin (RelAccess i _) = i
_relOrigin (RelFun i _) = i
_relRoot  (Rel i _ _ ) = i
_relRoot  (Inline i  ) = i
_relRoot  (RelAccess i _ ) = i
_relRoot  (RelFun i _ ) = i


_relInputs (Rel i _ _ ) = Just [i]
_relInputs (Inline i   ) = Nothing
_relInputs (RelAccess i _ ) = Just [i ]
_relInputs (RelFun  _ l) = Just $ fmap _relOrigin l

_relOutputs (Rel _ (Flip (AnyOp Equals)) _ ) = Nothing
_relOutputs (Rel _ IntersectOp  _ ) = Nothing
_relOutputs (Rel _ (Flip IntersectOp ) _ ) = Nothing
_relOutputs (Rel _ Contains _ ) = Nothing
_relOutputs (Rel _ (Flip Contains ) _ ) = Nothing
_relOutputs (Rel i (AnyOp Equals) _ ) = Just [i]
_relOutputs (Rel i  Equals _ ) = Just [i]
_relOutputs (Rel i  (Flip Equals ) _ ) = Just [i]
_relOutputs (Rel _  _ _ ) = Nothing
_relOutputs (Inline i ) = Just [i]
_relOutputs (RelAccess i _) = Nothing -- Just [i]
_relOutputs (RelFun i _) = Just [i]

instance (Binary (f k a) ,Binary k ) => Binary (KV f k a)
instance Binary k => Binary (Rel k)
instance NFData k => NFData (Rel k)
instance Binary a => Binary (Identity a)
instance (Binary (f (KV (Compose f (TB f)) g k)) , Binary (f (KV (Compose f (TB f)) g ())) , Binary (f (TB f g ())) ,Binary (f (TB f g k)), Binary k ,Binary g) => Binary (TB f g k )
instance Binary a => Binary (FTB a)
instance NFData a => NFData (FTB a)
instance Binary k => Binary (KVMetadata k )
instance NFData k => NFData (KVMetadata k )
instance (Binary k) => Binary (Access k )
instance (NFData k) => NFData (Access k )
instance Binary Expr
instance NFData Expr






data TB f k a
  = Attr
    { _tbattrkey :: !k
    , _tbattr :: !(FTB a)
    }
  | Fun
    { _tbattrkey :: ! k
    , _fundata :: ! (Expr,[Access k  ])
    , _tbattr :: ! (FTB a)
    }
  | IT -- Inline Table
    { _tbattrkey :: ! k
    , _ifkttable ::   ! (FTB1 f  k a)
    }
  | FKT -- Foreign Table
    { _tbref ::  ! (KV (Compose f (TB f)) k a)
    , _fkrelation :: ! [Rel k]
    , _ifkttable ::   ! (FTB1 f  k a)
    }
  deriving(Functor,Foldable,Traversable,Generic)

_fkttable (IT _  i) = i
_fkttable (FKT _ _ i) = i
_fkttable (Attr i _) = errorWithStackTrace "hit attr"
_fkttable (Fun i _ _) = errorWithStackTrace "hit fun"

deriving instance (Eq (f (TB f k a )), Eq (f (KV (Compose f (TB f)) k ())) ,Eq (f (TB f k () )) , Eq ( (FTB1 f  k a )) ,Eq a , Eq k ) => Eq (TB f k a)
deriving instance (Ord (f (TB f k a )), Ord (f (KV (Compose f (TB f)) k ())), Ord (f (TB f k () )) , Ord ( (FTB1 f  k a )) ,Ord a , Ord k ) => Ord (TB f k a)
deriving instance (Show (f (TB f k a )), Show (f (KV (Compose f (TB f)) k ())),Show (f (TB f k () )) , Show ( (FTB1 f k a )) ,Show (FTB a),Show a , Show k ) =>Show (TB f k a)

type TB2 k a = TB3 Identity k a

type TB3 f k a = FTB1 f k a



filterKey' f ((m ,k) ) = (m,) . mapComp (\(KV kv) -> KV $ Map.filterWithKey f kv )  $  k
filterKey f = fmap f


newtype MutRec a = MutRec {unMutRec ::  [a] }deriving(Eq,Ord,Show,Functor,Foldable,Generic,Binary,NFData)

traFAttr :: (Traversable g ,Applicative f) => ( FTB a -> f (FTB a) ) -> TB g k a -> f (TB g k a)
traFAttr f (Attr i v)  = Attr i <$> f v
traFAttr f (IT i v)  = IT i <$> traverse (traFValue f) v
traFAttr f (FKT  i rel v)  = liftA2 (\a b -> FKT a rel b)  ((traverseKV (traComp (traFAttr f))) i) (traverse (traFValue f) v)

traFValue :: (Traversable g ,Applicative f) => (FTB a -> f (FTB a) ) -> TB3Data g k a -> f (TB3Data g k a)
traFValue f (m ,k) =  fmap ((m,)). traComp (fmap KV . traverse (traComp (traFAttr f)) . _kvvalues )  $  k



mapFAttr f (Attr i v)  = (Attr i (f v))
mapFAttr f (IT i v)  = IT i (mapFValue f v)
mapFAttr f (FKT  i rel v)  = FKT (mapKV (mapComp (mapFAttr f) ) i) rel  (mapFValue f v)

mapFValue f = fmap (mapFValue' f)
mapFValue' f ((m ,k) ) = (m,) . mapComp (KV . fmap (mapComp (mapFAttr f)) . _kvvalues )  $  k


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
firstTB f (IT k i) = IT (f k) (mapKey f i)
firstTB f (FKT k  m  i) = FKT  (mapBothKV (f) (mapComp (firstTB f)) k)  (fmap f  <$> m) (mapKey f i)

data FTB a
  = TB1 ! a
  | LeftTB1  ! (Maybe (FTB a))
  | ArrayTB1  ! (NonEmpty (FTB a))
  | IntervalTB1 ! (Interval.Interval (FTB a))
  deriving(Eq,Ord,Show,Functor,Foldable,Traversable,Generic)

instance Applicative FTB where
  pure = TB1
  TB1 i <*> TB1 j = TB1 $ i  j

  LeftTB1 i <*> LeftTB1 j = LeftTB1 $ liftA2 (<*>) i j
  i <*> LeftTB1 j = LeftTB1 $ fmap (i <*>)  j
  LeftTB1 i <*> j = LeftTB1 $ fmap (<*>j)  i

  ArrayTB1 i <*> ArrayTB1 j = ArrayTB1 $ liftA2 (<*>) i j
  i <*> ArrayTB1 j = ArrayTB1 $ fmap (i <*>)  j
  ArrayTB1  i <*> j = ArrayTB1 $ fmap (<*>j)  i


type FTB1 f k a = FTB (KVMetadata k, Compose f (KV (Compose f (TB f))) k a)




data Expr
  = Value Int
  | Function Text [Expr]
  deriving(Eq,Ord,Show,Generic)



unTB :: Compose Identity f k b -> f k b
unTB = runIdentity . getCompose

_tb :: f k b -> Compose Identity f k b
_tb = Compose . Identity




-- Literals Instances

instance Enum a => Enum (FTB a) where
    toEnum = TB1 . toEnum
    fromEnum (TB1 i ) = fromEnum i


instance Real a => Real (FTB a) where
  toRational (TB1 i )=  toRational i


instance Integral a => Integral (FTB a) where
  toInteger (TB1 i) = toInteger i
  quotRem (TB1 i ) (TB1 j ) = (\(l,m) -> (TB1 l , TB1 m)) $ quotRem i j



instance Num a => Num (FTB a) where
  i + j = liftA2 (+) i  j
  i - j = liftA2 (-) i j
  i * j = liftA2 (*) i  j
  negate  = fmap negate
  abs   = fmap abs
  signum   = fmap signum
  fromInteger i  = TB1 (fromInteger i )

instance Fractional a => Fractional (FTB a) where
  fromRational i = TB1 (fromRational i)
  recip i = fmap recip i




overComp :: (f k b -> a ) -> Compose Identity f k b -> a
overComp f =  f . unTB


mapFromTBList :: (Foldable f ,Ord k )=> [Compose f (TB f ) k  a] -> Map (Set (Rel k) ) (Compose f ( TB f ) k  a)
mapFromTBList = Map.fromList . fmap (\i -> (Set.fromList (keyattr  i),i))

keyattr :: Foldable f => Compose f (TB f ) k  a -> [Rel k]
keyattr = keyattri . head . F.toList . getCompose


relAccesGen :: Access k -> Rel k
relAccesGen (IProd i l ) = Inline l
relAccesGen (Nested [IProd i l] m ) = RelAccess l (relAccesGen m)
relAccesGen (Many [l]) = relAccesGen l

keyattri :: Foldable f => TB f  k  a -> [Rel k]
keyattri (Attr i  _ ) = [Inline i]
keyattri (Fun i  l _ ) = [RelFun i (relAccesGen <$> snd l)]
keyattri (FKT i  rel _ ) = rel
keyattri (IT i  _ ) =  [Inline i]

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


kattr :: Compose Identity (TB Identity  ) k a -> [FTB a]
kattr = kattri . runIdentity . getCompose
kattri :: Column k a -> [FTB a]
kattri (Attr _ i ) = [i]
kattri (Fun _ _ i ) = [i]
kattri (FKT i  _ _ ) =  L.concat $ kattr  <$> unkvlist i
kattri (IT _  i ) =  recTB i
  where recTB (TB1 (m, i) ) =  L.concat $ fmap kattr (F.toList $ _kvvalues $ runIdentity $ getCompose i)
        recTB (ArrayTB1 i ) = L.concat $ F.toList $ fmap recTB i
        recTB (LeftTB1 i ) = L.concat $ F.toList $ fmap recTB i

aattr = aattri . unTB
aattri (Attr k i ) = [(k,i)]
aattri (Fun k _ i ) = [(k,i)]
aattri (FKT i  _ _ ) =  L.concat $ aattr  <$> unkvlist i
aattri (IT _ i) =  go i
  where
    go i = case i of
        -- TODO : Make a better representation for inline tables , to support product and sum tables properly
        TB1 i -> concat $ fmap maybeToList $ filter isJust $ fmap (traverse unSOptional') $ concat $ fmap aattr $ F.toList $ unkvlist (unTB $ snd i)
        LeftTB1 i ->   maybe [] go i
        i -> []




tblist :: Ord k => [Compose Identity  (TB Identity) k a] -> TBData k a
tblist = tblistM kvempty

tblistM :: Ord k => KVMetadata k -> [Compose Identity  (TB Identity) k a] -> TBData k a
tblistM t  = (t, ) . Compose . Identity . KV . mapFromTBList


kvempty  = KVMetadata "" ""  [] [] [] [] [] [] [] [] []

instance Ord a => Ord (Interval.Interval a ) where
  compare i j = compare (Interval.upperBound i )  (Interval.upperBound j)

instance Ord k => Monoid (KV f k a) where
  mempty = KV Map.empty
  mappend (KV i ) (KV j)   =    KV (Map.union i  j)


unKV
  :: Compose Identity (KV f) k a
     -> Map.Map (Set (Rel k)) (f k a)
unKV = _kvvalues . unTB


unTB1 :: Show a=> FTB a -> a
unTB1 i = fromMaybe (errorWithStackTrace ("unTB1" <> show i)) . headMay . F.toList $ i

-- Intersections and relations

keyAttr (Attr i _ ) = i
keyAttr (Fun i _ _ ) = i
keyAttr i = errorWithStackTrace $ "cant find keyattr " <> (show i)

unAttr (Attr _ i) = i
unAttr (Fun _ _ i) = i
unAttr i = errorWithStackTrace $ "cant find attr" <> (show i)



