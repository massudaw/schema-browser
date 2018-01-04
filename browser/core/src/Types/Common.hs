{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE OverloadedStrings #-}

module Types.Common (
     module Types.Compose
    ,TB (..),TB2,TB3
    ,_fkttable
    ,mapFValue,mapFValue',mapFAttr,traFAttr,traFValue,mapValue,mapValue'
    ,keyAttr
    ,unAttr
    ,Ring(..)
    ,FTB1
    ,SqlOperationTK(..)
    ,SqlOperationK(..)
    ,FTB (..)
    ,mapKV,findKV,findTB1,filterTB1',mapTB1,mapKey',mapKey,firstTB,mapBothKV,firstKV,secondKV,traverseKV,filterTB1
    ,mapTable
    ,atTBValue
    ,unTB1
    ,unSOptional ,unSOptional'
    ,unSSerial, unSDelayed
    ,unArray
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
    ,Union(..)
    ,notNull
    ,keyRef
    ,BinaryOperator(..)
    ,renderUnary,readBinaryOp,renderBinary
    ,AccessOp
    ,MutRec(..)
    ,Order(..),showOrder
    ,liftFK
    ,tableNonRef'
    ,keyattr
    ,kattri
    ,kattr
    ,aattr
    ,aattri
    ,relAccesGen
    ,keyattri
    ,tableNonRef )   where

import Data.Ord
import qualified Control.Lens as Le
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
import Data.Binary.Orphans
import Data.Binary (Binary(..))
import Data.Foldable (Foldable)
import qualified Data.Foldable as F
import qualified Data.Interval as Interval
import Data.Monoid hiding (Product)
import qualified Data.Text as T
import Data.Traversable(Traversable,traverse)
import Control.Monad
import Control.Applicative
import qualified Data.List as L
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Set as  S
import Data.Text (Text)
import Debug.Trace


unkvlist :: KV k a -> [TB k a]
unkvlist = F.toList . _kvvalues

kvlist :: Ord k => [TB k a] -> KV k a
kvlist = KV. mapFromTBList

unArray (ArrayTB1 s) =  s
unArray o  = error $ "unArray no pattern " <> show o

unSOptional (LeftTB1 i) = join $ unSOptional <$> i
unSOptional i = Just i

unSOptional' (LeftTB1 i ) = join $ unSOptional <$> i
unSOptional' i   = Just i


unSDelayed (LeftTB1 i) = i
unSDelayed i = traceShow ("unSDelayed No Pattern Match" <> show i) Nothing

unSSerial (LeftTB1 i) = i
unSSerial i = traceShow ("unSSerial No Pattern Match SSerial-" <> show i) Nothing


newtype KV k a
  = KV {_kvvalues :: Map (Set (Rel k)) (TB k a)  }deriving(Eq,Ord,Functor,Foldable,Traversable,Show,Generic)


instance Binary Order
instance NFData Order

showOrder Asc = "ASC"
showOrder Desc = "DESC"

data Order
  = Asc
  | Desc
  deriving(Eq,Ord,Show,Generic)

class Ring a where
  zero :: a
  one :: a
  mult :: a -> a -> a
  add :: a -> a -> a
  star :: a -> a

type Column k a = TB k a
type TBData k a = (KV k a )
type TB3Data  k a = (KV k a )

keyRef k = IProd notNull k
iprodRef (IProd _ l) = l

data Union a
  = Many [Union a]
  | ISum [Union a]
  | One a
  deriving(Show,Eq,Ord,Functor,Foldable,Traversable,Generic)

data Access  a
  = IProd (Maybe UnaryOperator) a
  | Nested [Access  a] (Union (Access  a))
  | Rec Int (Union (Access  a))
  | Point Int
  deriving(Show,Eq,Ord,Functor,Foldable,Traversable,Generic)

data BoolCollection a
 = AndColl [BoolCollection a]
 | OrColl [BoolCollection a]
 | PrimColl a
 deriving(Show,Eq,Ord,Functor,Foldable,Generic)

instance NFData a => NFData (BoolCollection a)

type AccessOp a = Either (FTB a, BinaryOperator) UnaryOperator

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
renderUnary i = error (show i)

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
renderBinary i = error (show i)

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
readBinaryOp i = error (show i)


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
  mappend _ = id

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
  , _kvjoins :: [SqlOperationK  k ]
  , _kvrecrels :: [MutRec [[Rel k]]]
  }deriving(Functor,Foldable,Generic)

type SqlOperationK = SqlOperationTK (Text,Text)

data SqlOperationTK t k
  = FKJoinTable [Rel k] t
  | RecJoin (MutRec [[Rel k ]])  (SqlOperationTK t k)
  | FKInlineTable k t
  | FunctionField k Expr [Access k]
  deriving(Eq,Ord,Show,Functor,Foldable,Generic)



instance Eq (KVMetadata k) where
  i == j = _kvschema  i  == _kvschema j &&  _kvname i == _kvname j
instance Eq k => Ord (KVMetadata k) where
  compare  = comparing _kvschema  <> comparing _kvname

instance Show k => Show (KVMetadata k) where
  show k = T.unpack (_kvname k)

kvMetaFullName m = _kvschema m <> "." <> _kvname m

filterTB1 f = fmap (filterTB1' f)
filterTB1' f (m ,i) = (m , (filterKV f) i)

mapTB1  f (TB1 (m, i))  =  TB1 (m ,(mapKV f) i )

mapBothKV :: Ord b => (a -> b) -> (TB a c -> TB b d) -> KV a c -> KV  b d
mapBothKV k f (KV  n) =  KV  (Map.mapKeys (S.map (fmap k )) $ fmap f n)

mapKV f (KV  n) =  KV  (fmap f n)

traverseKV f (KV  n) =  KV  <$> traverse f n

filterKV i (KV n) =  KV $ Map.filterWithKey (\k ->  i) n

findKV i (KV  n) =  L.find (i . snd) $Map.toList  n

findTB1  i (TB1  j )  = findKV i j
-- findTB1  l (LeftTB1  j )  = join $ findTB1  l <$> j -- error (show m)




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
_relTarget i = error (show i)

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

instance (Binary  a ,Binary k ) => Binary (KV  k a)
instance Binary k => Binary (Rel k)
instance NFData k => NFData (Rel k)
instance (Binary k ,Binary g) => Binary (TB g k )
instance Binary a => Binary (FTB a)
instance NFData a => NFData (FTB a)
instance Binary k => Binary (SqlOperationK k )
instance NFData k => NFData (SqlOperationK k )
instance Binary k => Binary (KVMetadata k )
instance NFData k => NFData (KVMetadata k )
instance (Binary k) => Binary (Access k )
instance (NFData k) => NFData (Access k )
instance (Binary k) => Binary (Union k )
instance (NFData k) => NFData (Union k )
instance Binary Expr
instance NFData Expr

data TB k a
  = Attr
    { _tbattrkey :: k
    , _tbattr :: FTB a
    }
  | Fun
    { _tbattrkey ::  k
    , _fundata ::  (Expr,[Access k  ])
    , _tbattr :: FTB a
    }
  | IT -- Inline Table
    { _tbattrkey ::  k
    , _ifkttable ::  FTB (KV k a)
    }
  | FKT -- Foreign Table
    { _tbref ::   KV k a
    , _fkrelation ::  [Rel k]
    , _ifkttable ::   FTB (KV k a)
    }
  deriving(Functor,Foldable,Traversable,Generic,Eq,Ord,Show)



_fkttable (IT _  i) = i
_fkttable (FKT _ _ i) = i
_fkttable (Attr i _) = error "hit attr"
_fkttable (Fun i _ _) = error "hit fun"


type TB2 k a = TB3 k a

type TB3 k a = FTB1 k a


filterKey' f ((m ,k) ) = (m,) . (\(KV kv) -> KV $ Map.filterWithKey f kv )  $  k
filterKey f = fmap f


newtype MutRec a = MutRec {unMutRec ::  [a] }deriving(Eq,Ord,Show,Functor,Foldable,Generic,Binary,NFData)

traFAttr :: (Applicative f) => ( FTB a -> f (FTB a) ) -> TB k a -> f (TB k a)
traFAttr f (Attr i v)  = Attr i <$> f v
traFAttr f (IT i v)  = IT i <$> traverse (traFValue f) v
traFAttr f (FKT  i rel v)  = liftA2 (\a b -> FKT a rel b)  ((traverseKV ((traFAttr f))) i) (traverse (traFValue f) v)

traFValue :: (Applicative f) => (FTB a -> f (FTB a) ) -> TBData k a -> f (TBData  k a)
traFValue f k =   fmap KV . traverse ((traFAttr f)) . _kvvalues   $  k

mapFAttr f (Attr i v)  = (Attr i (f v))
mapFAttr f (IT i v)  = IT i (mapFValue f v)
mapFAttr f (FKT  i rel v)  = FKT (mapKV ((mapFAttr f) ) i) rel  (mapFValue f v)

mapFValue f = fmap (mapFValue' f)
mapFValue' f k = KV . fmap ((mapFAttr f)) . _kvvalues   $  k


mapValue' f k =  fmap  f  $  k
mapValue f = fmap (mapValue' f)


mapTable f m = KV. fmap ((mapTableAttr f )) . _kvvalues  $   m

mapTableAttr  f (IT l j ) =  IT l (f  (mapTable f <$> j))
mapTableAttr  f (FKT l rel j ) =  FKT l rel (f  (mapTable f <$> j))
mapTableAttr f  i = i

mapKey' :: Ord b => (a -> b) -> TB3Data  a c -> TB3Data  b c
mapKey f = fmap (mapKey' f)
mapKey' f k = firstKV f  $  k

firstKV :: (Ord k ) => (c -> k) -> KV c a -> KV k a
firstKV  f (KV m ) = KV . fmap (firstTB f)  . Map.mapKeys (Set.map (fmap f)) $ m
secondKV  f (KV m ) = KV . fmap (fmap f ) $ m

firstTB :: (Ord k) => (c -> k) -> TB  c a -> TB  k a
firstTB f (Attr k i) = Attr (f k) i
firstTB f (Fun k i l ) = Fun (f k) (fmap (fmap f) <$> i) l
firstTB f (IT k i) = IT (f k) (mapKey f i)
firstTB f (FKT k  m  i) = FKT  (mapBothKV (f) ((firstTB f)) k)  (fmap f  <$> m) (mapKey f i)

data FTB a
  = TB1  a
  | LeftTB1  ! (Maybe (FTB a))
  | ArrayTB1  ! (NonEmpty (FTB a))
  | IntervalTB1  ! (Interval.Interval (FTB a))
  deriving(Eq,Ord,Show,Functor,Foldable,Traversable,Generic)


instance Monad FTB where
  TB1 i >>= j =  j i
  LeftTB1 o  >>= j =  LeftTB1 $ fmap (j =<<) o
  ArrayTB1 o  >>= j =  ArrayTB1 $ fmap (j =<<) o

instance Applicative FTB where
  pure = TB1
  TB1 i <*> TB1 j = TB1 $ i  j
  LeftTB1 i <*> LeftTB1 j = LeftTB1 $ liftA2 (<*>) i j
  ArrayTB1 i <*> ArrayTB1 j = ArrayTB1 $ Non.zipWith (<*>) i j

  i <*> LeftTB1 j = LeftTB1 $ fmap (i <*>)  j
  LeftTB1 i <*> j = LeftTB1 $ fmap (<*>j)  i

  i <*> ArrayTB1 j = ArrayTB1 $ fmap (i <*>)  j
  ArrayTB1  i <*> j = ArrayTB1 $ fmap (<*>j)  i

type FTB1 k a = FTB (KV k a)

data Expr
  = Value Int
  | Function Text [Expr]
  deriving(Eq,Ord,Show,Generic)



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

mapFromTBList :: Ord k => [TB k  a] -> Map (Set (Rel k) ) (TB k  a)
mapFromTBList = Map.fromList . fmap (\i -> (Set.fromList (keyattr  i),i))

keyattr :: TB k  a -> [Rel k]
keyattr = keyattri


relAccesGen :: Access k -> Rel k
relAccesGen (IProd i l ) = Inline l
relAccesGen (Nested [IProd i l] (Many [One m]) ) = RelAccess l (relAccesGen m)

keyattri :: TB  k  a -> [Rel k]
keyattri (Attr i  _ ) = [Inline i]
keyattri (Fun i  l _ ) = [RelFun i (relAccesGen <$> snd l)]
keyattri (FKT i  rel _ ) = rel
keyattri (IT i  _ ) =  [Inline i]

traTable f (KV i) = KV <$> f i

alterFTB :: Applicative f => (a -> f a ) -> FTB a -> f (FTB a)
alterFTB f (TB1 i ) = TB1 <$> f i
alterFTB f (ArrayTB1 i ) = ArrayTB1 <$> traverse (alterFTB f)  i
alterFTB f (LeftTB1 i ) = LeftTB1 <$> traverse (alterFTB f)  i
alterFTB f (IntervalTB1 i ) = IntervalTB1 <$> traverse (alterFTB f)  i

liftFK :: Ord k => Column k b-> FTB (Map k (FTB b) ,TBData k b)
liftFK (FKT l rel i ) = first (fmap TB1 ) <$> liftRel (F.toList $ _kvvalues l ) rel i

liftRel :: (Ord k) => [Column k b] -> [Rel k] -> FTB c -> FTB (Map k b ,c)
liftRel l rel f = liftA2 (,) (Map.fromList  <$> F.foldl' (flip merge ) (TB1 []) rels) f
  where rels = catMaybes $ findRel l <$> rel

recoverFK :: Ord k => [k] -> [Rel k]-> FTB (Map k (FTB s),TBData k s ) -> Column k s
recoverFK ori rel i =
  FKT (kvlist $ (fmap (\(i,j) -> Attr i (join j)) $  zip  (L.sort ori ). getZipList . sequenceA $ fmap ( ZipList . F.toList. fst) i)) rel   (fmap snd i)



merge :: FTB a -> FTB [a] -> FTB [a]
merge (LeftTB1 i ) (LeftTB1 j) = LeftTB1 $ merge <$> i <*> j
merge (ArrayTB1 i ) (ArrayTB1 j) = ArrayTB1 $ Non.zipWith merge i j
merge (TB1 i ) (TB1 j) = TB1 $ i:j
merge (LeftTB1 i) j = LeftTB1 $ (\i  -> merge i j) <$> i
merge i (LeftTB1 j) = LeftTB1 $ (\j  -> merge i j) <$> j
merge (ArrayTB1 i) j = ArrayTB1 $ (\i  -> merge i j) <$> i
merge i  (ArrayTB1 j) = ArrayTB1 $ (\j  -> merge i j) <$> j


findRel l (Rel k op j) =  do
  Attr k v <- L.find (\(Attr i v) -> i == k ) l
  return $ fmap (k,) v

atTBValue
  :: (Applicative f , Ord k ) =>
    [Access k]
     -> (FTB b -> f (FTB b))
     -> (FTB (TBData  k b ) -> f (FTB (TBData k b)))
     -> (FTB (Map k (FTB b),TBData k b) -> f (FTB (Map k (FTB b), TBData k b)))
     -> (TBData k b)
     -> f (TBData k b)
atTBValue l f g h v = traTable (Le.at key (traverse (modify ))) v
  where key = justError "cant find key" $ L.find (\i -> S.map _relOrigin  i == S.fromList (iprodRef <$> l) ) (Map.keys  (_kvvalues v))
        modify i = case i  of
          Attr k j -> Attr k <$> f j
          IT l  j -> IT l <$> g j
          t@(FKT l  i j) -> recoverFK  (concat $ fmap _relOrigin . keyattr <$> (unkvlist l )) i <$> h (liftFK t)


tableNonRef :: Ord k => TB2 k a -> TB2 k a
tableNonRef = fmap tableNonRef'


tableNonRef' :: Ord k => TBData k a -> TBData k a
tableNonRef' n  = (KV . rebuildTable . _kvvalues) n
  where
    rebuildTable n = mapFromTBList .  concat . F.toList $  nonRef <$> n
    nonRef :: Ord k => TB k a -> [(TB ) k a]
    nonRef (FKT i _ _ ) = concat (nonRef <$> unkvlist i)
    nonRef (IT j k ) = [(IT  j (tableNonRef k )) ]
    nonRef i = [i]


nonRefTB :: Ord k => TB k a -> [TB k a]
nonRefTB (FKT i _ _ ) = concat (nonRefTB <$> unkvlist i)
nonRefTB (IT j k ) = [(IT  j (tableNonRef k )) ]
nonRefTB i  = [i]


kattr :: TB k a -> [FTB a]
kattr = kattri
kattri :: Column k a -> [FTB a]
kattri (Attr _ i ) = [i]
kattri (Fun _ _ i ) = [i]
kattri (FKT i  _ _ ) =  L.concat $ kattr  <$> unkvlist i
kattri (IT _  i ) =  recTB i
  where recTB (TB1  i ) =  L.concat $ fmap kattr (F.toList $ _kvvalues $  i)
        recTB (ArrayTB1 i ) = L.concat $ F.toList $ fmap recTB i
        recTB (LeftTB1 i ) = L.concat $ F.toList $ fmap recTB i


aattr = aattri
aattri (Attr k i ) = [(k,i)]
aattri (Fun k _ i ) = [(k,i)]
aattri (FKT i  _ _ ) =  L.concat $ aattr  <$> unkvlist i
aattri (IT _ i) =  go i
  where
    go i = case i of
        -- TODO : Make a better representation for inline tables , to support product and sum tables properly
        TB1 i -> concat $ fmap maybeToList $ filter isJust $ fmap (traverse unSOptional') $ concat $ fmap aattr $ F.toList $ unkvlist i
        LeftTB1 i ->   maybe [] go i
        i -> []


tblist :: Ord k => [TB k a] -> TBData k a
tblist = tblistM

tblistM :: Ord k =>  [TB k a] -> TBData k a
tblistM   =   KV . mapFromTBList


kvempty  = KVMetadata "" ""  [] [] [] [] [] [] [] [] [] []

instance Ord a => Ord (Interval.Interval a ) where
  compare i j = compare (Interval.upperBound i )  (Interval.upperBound j)

instance Ord k => Monoid (KV  k a) where
  mempty = KV Map.empty
  mappend (KV i ) (KV j)   =    KV (Map.union i  j)


unKV
  :: KV k a
     -> Map.Map (Set (Rel k)) (TB k a)
unKV = _kvvalues


unTB1 :: FTB a -> a
unTB1 (TB1 i) =  i
unTB1 i = fromMaybe (error "unTB1: " ) . headMay . F.toList $ i

-- Intersections and relations

keyAttr (Attr i _ ) = i
keyAttr (Fun i _ _ ) = i
keyAttr i = error $ "cant find keyattr " <> (show i)

unAttr (Attr _ i) = i
unAttr (Fun _ _ i) = i
unAttr i = error $ "cant find attr" <> (show i)
