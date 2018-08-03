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
{-# LANGUAGE TemplateHaskell #-}

module Types.Common
  ( TB(..)
  , TBRef(..)
  , _fkttable
  , ifkttable
  , mapFValue
  , mapFAttr
  , replaceRecRel
  , traFAttr
  , traFValue
  , relSort
  , keyAttr
  , tbUn
  , unAttr
  , mapKV
  , findKV
  , mapKey'
  , mapKey
  , firstTB
  , mapBothKV
  , firstKV
  , secondKV
  , traverseKV
  , traverseKVWith
  , mergeKV
  , trazipWithKV
  , traTable
  , keyattr
  , liftFK
  , recoverFK
  , kvFind
  , kvFilter
  , kvFilterWith
  , kvNull
  , kvSingleton
  , kvSize
  -- ,recoverAttr', firstATB ,traFAValue,AValue(..),TBAttr
  , FTB(..)
  , unTB1
  , unSOptional
  , unSSerial
  , unSDelayed
  , addDefault
  , unArray
  , KV
  , TBData
  , unKV
  , kvlist
  , kvkeys
  , kvToMap
  , addAttr
  , alterKV
  , alterAtF
  , findFun
  , findFK
  , findFKAttr
  , findAttr
  , kvLookup
  , refLookup
  , recLookup
  , relLookup
  , attrLookup
  , unkvlist
  , sortedFields
  , kvmap
  , kattr
  , aattr
  , nonRefTB
  , tableNonRef
  , restrictTable
  , nonFK
  , Rel(..)
  , indexerRel
  , _relOrigin
  , _relTarget
  , _relInputs
  , _relOutputs
  , Expr
  , MutRec(..)
  , FExpr(..)
  , BinaryOperator(..)
  , readBinaryOp
  , renderRel
  , renderBinary
    -- ,valueattr
  ) where

import Control.Applicative
import qualified Data.Poset as P
import Control.DeepSeq
import Control.Monad
import Data.Binary (Binary(..))
import Data.Foldable (Foldable)
import qualified Data.Foldable as F
import Data.Functor.Identity
import qualified Data.Interval as Interval
import qualified Data.List as L
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Monoid hiding (Product)
import qualified Control.Lens as Le
import Control.Lens.TH
import Data.Ord
import Algebra.PartialOrd
import qualified Data.POMap.Lazy as PM
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Set as S
import qualified Data.Text as T
import Data.Text (Text)
import Data.Traversable (Traversable, traverse)
import Debug.Trace
import GHC.Generics
import qualified NonEmpty as Non
import Data.String
import NonEmpty (NonEmpty(..))
import Prelude hiding (head)
import Safe
import Utils


newtype KV k a
  = KV
  { _kvvalues :: PM.POMap (Set (Rel k)) (TB k a)
  } deriving (Eq, Ord, Functor, Foldable, Traversable, Show, Generic)

instance (PartialOrd k , Ord k , Ord v ) => Ord (PM.POMap k v) where
  compare i j = compare (PM.toList i) (PM.toList j)

relSort i = RelSort (inp i)  (out i) i
  where
    inp j = norm $ _relInputs <$> F.toList j
    out j = norm $ _relOutputs <$> F.toList j
    norm = S.fromList . concat . catMaybes

data RelSort k =
  RelSort (Set k) (Set k) (S.Set (Rel k))
  deriving (Eq, Ord,Show)

newtype MutRec a = MutRec
  { unMutRec :: [a]
  } deriving (Eq, Ord, Show, Functor, Foldable, Generic, Binary, NFData)


sortedFields
  :: Ord k
  => KV k a
  -> [(Set (Rel k) , TB k a)]
sortedFields =  PM.toList . _kvvalues

instance  Ord k => PartialOrd (RelSort k) where
  leq (RelSort inpi outi _ ) (RelSort inpj outj _) = (not (S.null outi ) && not (S.null inpj) && leq outi inpj)

-- To Topologically sort the elements we compare  both inputs and outputs for intersection if one matches we flip the
instance (Ord k, P.Poset k) => P.Poset (RelSort k) where
  compare (RelSort inpi outi i ) (RelSort inpj outj j) =
    case ( comp outi inpj
         , comp outj inpi
         , P.compare inpi inpj
         , P.compare outi outj)
            -- Reverse order
          of
      (_, P.LT, _, _) ->
        if S.size outj == L.length j
          then P.GT
          else P.EQ
            -- Right order
      (P.LT, _, _, _) -> P.LT
            -- No intersection  between elements sort by inputset
      (_, _, P.EQ, o) -> o
      (_, _, i, _) -> i
    where
      comp i j
        | S.null (S.intersection i j) = P.EQ
      comp i j
        | S.empty == i = P.EQ
      comp i j
        | S.empty == j = P.EQ
      comp i j = P.compare i j



kvlist :: Ord k => [TB k a] -> KV k a
kvlist = KV . mapFromTBList

kvToMap :: Ord k => KV k a -> Map.Map k (FTB a)
kvToMap = Map.mapKeys (_relOrigin . L.head .F.toList ) . fmap _tbattr . Map.fromList . PM.toList . _kvvalues

kvkeys :: Ord k => KV k a -> [Set (Rel k)]
kvkeys = PM.keys . _kvvalues

unkvlist :: KV k a -> [TB k a]
unkvlist = F.toList . _kvvalues

-- unkvlist = fmap (recoverAttr . first F.toList ) . Map.toList . _kvvalues
-- unkvmap = Map.fromList . fmap (\(i,j) -> (i, recoverAttr  (F.toList i,j))) . Map.toList . _kvvalues
kvmap :: Ord k => Map.Map (Set (Rel k)) (TB k a) -> KV k a
kvmap = KV . PM.fromList . Map.toList

-- kvmap = KV . fmap valueattr
unKV :: Ord k => KV k a -> Map.Map (Set (Rel k)) (AValue k a)
unKV = Map.fromList . PM.toList . _kvvalues

mapBothKV :: Ord b => (a -> b) -> (AValue a c -> AValue b d) -> KV a c -> KV b d
mapBothKV k f (KV n) = KV (PM.mapKeys (S.map (fmap k)) $ fmap f n)

mapKV f (KV n) = KV (fmap f n)

mergeKV (KV i ) (KV j) = KV $ PM.unionWith const i j
traverseKVWith
  :: Applicative f =>
    (Set (Rel k) -> TB k a1 -> f (TB k a2)) -> KV k a1 -> f (KV k a2)
traverseKVWith f (KV n) = KV <$> PM.traverseWithKey f n


traverseKV
  :: Applicative f =>
     (TB k a1 -> f (TB k a2)) -> KV k a1 -> f (KV k a2)
traverseKV f (KV n) = KV <$> traverse f n

trazipWithKV f (KV v1) (KV v2) = KV <$>  sequence (PM.intersectionWith f v1 v2)

filterKV :: (TB k a -> Bool) -> KV k a -> KV k a
filterKV i (KV n) = KV $ PM.filterWithKey (\k -> i) n

findKV :: (TB k a -> Bool) -> KV k a -> Maybe (Set (Rel k), TB k a)
findKV i (KV n) = L.find (i . snd) $ PM.toList n


type Column k a = TB k a

type TBData k a = KV k a

renderBinary (Flip (Flip i)) = renderBinary i
renderBinary Contains = "@>"
renderBinary (Flip Contains) = "<@"
renderBinary Equals = "="
renderBinary (Flip Equals) = "="
renderBinary (Flip (GreaterThan b)) = renderBinary (LowerThan b)
renderBinary (Flip (LowerThan b)) = renderBinary (GreaterThan b)
renderBinary (GreaterThan True) = ">="
renderBinary (GreaterThan False) = ">"
renderBinary (LowerThan False) = "<"
renderBinary (LowerThan True) = "<="
renderBinary (IntersectOp) = "&&"
renderBinary (Flip IntersectOp) = "&&"
renderBinary (AllOp op) = renderBinary op <> " all"
renderBinary (AnyOp op) = renderBinary op <> " any"
renderBinary (Flip (AllOp op)) = " all" <> renderBinary op
renderBinary (Flip (AnyOp op)) = " any" <> renderBinary op
-- Symetric Operators

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
  | LowerThan Bool
  | IntersectOp
  | Flip BinaryOperator
  | AnyOp BinaryOperator
  deriving (Eq, Ord, Show, Generic)

instance Binary BinaryOperator

instance NFData BinaryOperator

data Rel k
  = Inline { _relOri :: k }
  | Rel { _relAccess :: Rel k
        , _relOperator :: BinaryOperator
        , _relTip :: k }
  | RelAlias { _relOri :: k
             , _relReference :: [Rel k] }
  | RelAccess { _relReference :: [Rel k]
              , _relAccess :: Rel k }
  | RelFun { _relOri :: k
           , _relExpr :: Expr
           , _relReference :: [Rel k] }
  deriving (Eq, Show, Ord, Functor, Traversable, Foldable, Generic)

_relTarget (Rel _ _ i) = i
_relTarget (RelAccess _ i) = _relTarget i
_relTarget i = error (show i)

_relOrigin (Rel i _ _) = _relOrigin i
_relOrigin (Inline i) = i
_relOrigin (RelAccess _ i) = _relOrigin i
_relOrigin (RelFun i _ _) = i
_relOrigin (RelAlias i _) = i

-- TODO Fix Rel to store proper relaaccess
_relInputs (Rel i _ _) = Just [_relOrigin i]
_relInputs (Inline i) = Nothing
_relInputs (RelAccess i _) = Just $ concat (catMaybes $ _relInputs <$> i)
_relInputs (RelFun _ _ l) = Just $ fmap _relOrigin l
_relInputs (RelAlias i l) = Just $ fmap _relOrigin l

_relOutputs (Rel _ (Flip (AnyOp Equals)) _) = Nothing
_relOutputs (Rel _ IntersectOp _) = Nothing
_relOutputs (Rel _ (Flip IntersectOp) _) = Nothing
_relOutputs (Rel _ Contains _) = Nothing
_relOutputs (Rel _ (Flip Contains) _) = Nothing
_relOutputs (Rel i (AnyOp Equals) _) = _relOutputs i
_relOutputs (Rel i Equals _) =  _relOutputs i
_relOutputs (Rel i (Flip Equals) _) = _relOutputs i
_relOutputs (Rel _ _ _) = Nothing
_relOutputs (Inline i) = Just [i]
_relOutputs (RelAccess i _) = Nothing -- Just [i]
_relOutputs (RelFun i _ _) = Just [i]
_relOutputs (RelAlias i _) = Nothing

instance (PartialOrd k ,Binary k , Binary a) => Binary (PM.POMap k a) where
  get = PM.fromList <$> get
  put = put . PM.toList

instance (Ord k ,Binary a, Binary k) => Binary (KV k a)

instance Binary k => Binary (Rel k)

instance NFData k => NFData (Rel k)

instance (Ord g ,Binary k, Binary g) => Binary (TB g k)

instance Binary a => Binary (FTB a)

instance NFData a => NFData (FTB a)

type Expr = FExpr Text Text

data FExpr r k
  = Value Int
  | ConstantExpr k
  | Function r
             [FExpr r k]
  deriving (Eq, Ord, Show, Generic)

instance (Binary k, Binary j) => Binary (FExpr k j)

instance (NFData k, NFData j) => NFData (FExpr k j)

type TBAttr k v = ([Rel k], AValue k v)

type AValue k a = TB k a

recoverAttr' = id


{-

valueattr :: TB k a -> AValue k a
valueattr (Attr i j) = APrim j
valueattr (Fun _ _ v) = APrim v
valueattr (IT _ v) = ARef v
valueattr (FKT i  _ v) = ARel i v


-- instance (Binary  a ,Binary k ) => Binary (AValue k a)
data AValue k a
  = APrim {_aprim :: (FTB a) }
  | ARef {_aref :: (FTB (KV k a))}
  | ARel { _arel :: KV k a  , _aref :: (FTB (KV k a))}
  deriving(Eq,Ord,Functor,Foldable,Traversable,Show,Generic)

instance (Binary k ,Binary g) => Binary (AValue g k )

recoverAttr' :: Ord k => (Set.Set (Rel k), AValue k a) -> TB k a
recoverAttr' = recoverAttr . first F.toList
recoverAttr ::  Ord k => TBAttr k a -> TB k a
recoverAttr ([Inline i],APrim v) = Attr i v
recoverAttr ([RelFun i j k ] ,APrim v) = Fun i (j,accesRelGen' <$> k) v
recoverAttr ([Inline i] ,ARef v) = IT i v
recoverAttr (i,ARel l v) = FKT l  i v

splitAttr :: TB k a -> TBAttr k a
splitAttr  i = (keyattr i ,valueattr i)

traFAValue :: Applicative f => (FTB a -> f (FTB b)) -> AValue k a -> f (AValue k b)
traFAValue f (APrim v)  = APrim <$> f v
traFAValue f (ARef v)  = ARef <$> traverse (traFValue f) v
traFAValue f (ARel i v)  = liftA2 (\a b -> ARel a b)  (traFValue f i) (traverse (traFValue f) v)

traverseRef :: Applicative f => (FTB a -> f (FTB b)) -> AValue k a -> f (AValue k b)
traverseRef f (APrim v)  = APrim <$> f v
traverseRef f (ARef v)  = ARef <$> traverse (traFValue f) v
traverseRef f (ARel i v)  = liftA2 (\a b -> ARel a b)  (traFValue f i) (traverse (traFValue f) v)


mapFAValue :: (FTB a -> FTB a) -> AValue k a -> AValue k a
mapFAValue = traMap traFAValue

firstATB :: Ord k => (c -> k) -> AValue c a -> AValue k a
firstATB f (APrim i) = APrim i
firstATB f (ARef i) = ARef (mapKey f i)
firstATB f (ARel m  i) = ARel (mapKey' f m)  (mapKey f i)

-}
data TB k a
  = Attr -- Primitive Value
     { _tbattrkey :: k
     , _tbattr :: FTB a }
  | Fun -- Function Call
     { _tbattrkey :: k
     , _fundata :: (Expr, [Rel k])
     , _tbattr :: FTB a }
  | IT -- Inline Table
     { _tbattrkey :: k
     , _ifkttable :: FTB (KV k a) }
  | FKT -- Foreign Table
     { _tbref :: KV k a
     , _fkrelation :: [Rel k]
     , _ifkttable :: FTB (KV k a) }
  deriving (Functor, Foldable, Traversable, Generic, Eq, Ord, Show)

newtype TBRef k s = TBRef { unTBRef :: (KV k s,KV k s)}deriving(Show,Eq,Ord,Functor)

_fkttable (IT _ i) = i
_fkttable (FKT _ _ i) = i
_fkttable (Attr i _) = error "hit attr"
_fkttable (Fun i _ _) = error "hit fun"



traFAttr :: Applicative f => (FTB a -> f (FTB b)) -> TB k a -> f (TB k b)
traFAttr f (Attr i v) = Attr i <$> f v
traFAttr f (IT i v) = IT i <$> traverse (traFValue f) v
traFAttr f (FKT i rel v) =
  liftA2 (\a b -> FKT a rel b) (traFValue f i) (traverse (traFValue f) v)

traFValue :: Applicative f => (FTB a -> f (FTB b)) -> KV k a -> f (KV k b)
traFValue f k = traverseKV (traFAttr f) k

traMap g f = runIdentity . g (Identity . f)

mapFAttr :: (FTB a -> (FTB b)) -> TB k a -> (TB k b)
mapFAttr = traMap traFAttr

mapFValue f k = KV . fmap (traMap traFAttr f) . _kvvalues $ k

-- mapFValue f k = KV . fmap (traMap traFAValue f) . _kvvalues   $  k
mapKey' :: Ord b => (a -> b) -> KV a c -> KV b c
mapKey f = fmap (mapKey' f)

mapKey' f k = firstKV f $ k

firstKV :: Ord k => (c -> k) -> KV c a -> KV k a
-- firstKV  f (KV m ) = KV . fmap (firstATB f)  . Map.mapKeys (Set.map (fmap f)) $ m
firstKV f (KV m) = KV . fmap (firstTB f) . PM.mapKeys (Set.map (fmap f)) $ m

secondKV f (KV m) = KV . fmap (fmap f) $ m

firstTB :: Ord k => (c -> k) -> TB c a -> TB k a
firstTB f (Attr k i) = Attr (f k) i
firstTB f (Fun k i l) = Fun (f k) (fmap (fmap f) <$> i) l
firstTB f (IT k i) = IT (f k) (mapKey f i)
firstTB f (FKT k m i) = FKT (mapKey' f k) (fmap f <$> m) (mapKey f i)

data FTB a
  = TB1 !a
  | LeftTB1 !(Maybe (FTB a))
  | ArrayTB1 !(NonEmpty (FTB a))
  | IntervalTB1 !(Interval.Interval (FTB a))
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Generic)

instance Monad FTB where
  TB1 i >>= j = j i
  LeftTB1 o >>= j = LeftTB1 $ fmap (j =<<) o
  ArrayTB1 o >>= j = ArrayTB1 $ fmap (j =<<) o

instance Applicative FTB where
  pure = TB1
  TB1 i <*> TB1 j = TB1 $ i j
  LeftTB1 i <*> LeftTB1 j = LeftTB1 $ liftA2 (<*>) i j
  ArrayTB1 i <*> ArrayTB1 j = ArrayTB1 $ Non.zipWith (<*>) i j
  i <*> LeftTB1 j = LeftTB1 $ fmap (i <*>) j
  LeftTB1 i <*> j = LeftTB1 $ fmap (<*> j) i
  i <*> ArrayTB1 j = ArrayTB1 $ fmap (i <*>) j
  ArrayTB1 i <*> j = ArrayTB1 $ fmap (<*> j) i

-- Literals Instances
instance Enum a => Enum (FTB a) where
  toEnum = TB1 . toEnum
  fromEnum (TB1 i) = fromEnum i

instance Real a => Real (FTB a) where
  toRational (TB1 i) = toRational i

instance Integral a => Integral (FTB a) where
  toInteger (TB1 i) = toInteger i
  quotRem (TB1 i) (TB1 j) = (\(l, m) -> (TB1 l, TB1 m)) $ quotRem i j

instance Num a => Num (FTB a) where
  i + j = liftA2 (+) i j
  i - j = liftA2 (-) i j
  i * j = liftA2 (*) i j
  negate = fmap negate
  abs = fmap abs
  signum = fmap signum
  fromInteger i = TB1 (fromInteger i)

instance Fractional a => Fractional (FTB a) where
  fromRational = TB1 . fromRational
  recip = fmap recip

mapFromTBList :: Ord k => [TB k a] -> PM.POMap (Set (Rel k)) (AValue k a)
mapFromTBList = PM.fromList . fmap (\i -> (Set.fromList (keyattr i), i))

-- mapFromTBList = Map.fromList . fmap (\i -> (Set.fromList (keyattr  i),valueattr i))
keyattr :: TB k a -> [Rel k]
keyattr (Attr i _) = [Inline i]
keyattr (Fun i l _) = [RelFun i (fst l) (snd l)]
keyattr (FKT i rel _) = rel
keyattr (IT i _) = [Inline i]

traTable f (KV i) = KV <$> f i

alterFTB :: Applicative f => (a -> f a) -> FTB a -> f (FTB a)
alterFTB f (TB1 i) = TB1 <$> f i
alterFTB f (ArrayTB1 i) = ArrayTB1 <$> traverse (alterFTB f) i
alterFTB f (LeftTB1 i) = LeftTB1 <$> traverse (alterFTB f) i
alterFTB f (IntervalTB1 i) = IntervalTB1 <$> traverse (alterFTB f) i

liftFK :: Ord k => Column k b -> FTB (TBRef k b)
liftFK (FKT l rel i) = TBRef <$> liftRel (unkvlist l) rel i

liftRel ::
     (Ord k) => [Column k b] -> [Rel k] -> FTB (KV k b) -> FTB (KV k b, KV k b)
liftRel l rel f =
  merge
    (,)
    (kvlist [], )
    (, kvlist [])
    (kvlist <$> F.foldl' (flip (merge (:) id pure)) (TB1 []) rels)
    f
  where
    rels = catMaybes $ findRel l <$> rel

addDefault :: Ord d => TB d a -> TB d b
addDefault = def
  where
    def (Attr k i) = Attr k (LeftTB1 Nothing)
    def (Fun k i _) = Fun k i (LeftTB1 Nothing)
    def (IT rel j) = IT rel (LeftTB1 Nothing)
    def (FKT at rel j) =
      FKT (kvlist $ addDefault <$> unkvlist at) rel (LeftTB1 Nothing)


recoverFK :: Ord k => [k] -> [Rel k] -> FTB (TBRef k s) -> Column k s
recoverFK ori rel i
  -- FKT (kvlist . catMaybes $ (\k -> Attr k <$> (fmap join . traverse (fmap _aprim . Map.lookup (S.singleton $ Inline k). _kvvalues . fst ) $ i)) <$> ori )rel   (fmap snd i)
 =
  FKT
    (kvlist . catMaybes $
     (\k ->
        Attr k <$>
        (fmap join .
         traverse
           (fmap _tbattr . PM.lookup (S.singleton $ Inline k) . _kvvalues . fst.unTBRef) $
         i)) <$>
     ori)
    rel
    (fmap (snd .unTBRef ) i)

merge :: (a -> b -> c) -> (b -> c) -> (a -> c) -> FTB a -> FTB b -> FTB c
merge f g h (LeftTB1 i) (LeftTB1 j) =
  LeftTB1 $ (merge f g h <$> i <*> j) <|> (fmap h <$> i) <|> (fmap g <$> j)
merge f g h (ArrayTB1 i) (ArrayTB1 j) =
  ArrayTB1 $
  Non.fromList $
  F.toList (Non.zipWith (merge f g h) i j) <>
  (fmap g <$> (Non.drop (Non.length i) j)) <>
  (fmap h <$> (Non.drop (Non.length j) i))
merge f g h (TB1 i) (TB1 j) = TB1 $ f i j
merge f g h (LeftTB1 i) j = LeftTB1 $ (\i -> merge f g h i j) <$> i
merge f g h i (LeftTB1 j) = LeftTB1 $ (\j -> merge f g h i j) <$> j
merge f g h (ArrayTB1 i) j = ArrayTB1 $ (\i -> merge f g h i j) <$> i
merge f g h i (ArrayTB1 j) = ArrayTB1 $ (\j -> merge f g h i j) <$> j

instance IsString i => IsString (Rel i ) where
  fromString i = Inline (fromString i)

findRel l (Rel k op j) = do
  Attr k v <- L.find (\(Attr i v) -> i == _relOrigin k) l
  return $ fmap (Attr k . TB1) v


restrictTable :: Ord k => (TB k a  -> [TB k a]) -> KV k a -> KV k a
restrictTable f n =  (rebuildTable . unkvlist) n
  where
    rebuildTable n = kvlist . concat . F.toList $ f <$> n

tableNonRef :: Ord k => KV k a -> KV k a
tableNonRef = restrictTable  nonRefTB

nonFK :: Ord k => TB k a -> [TB k a]
nonFK (FKT i _ _) = concat (nonFK <$> _kvvalues i)
nonFK (IT j k) = [IT j (restrictTable nonFK <$> k)]
nonFK (Fun _ (_,l)  _) | L.any isRel l = []
  where isRel (RelAccess i _ ) = L.any isRel i
        isRel (Rel _ _ _) = True
        isRel _ = False
nonFK i = [i]

nonRefTB :: Ord k => TB k a -> [TB k a]
nonRefTB (FKT i _ _) = concat (nonRefTB <$> _kvvalues i)
nonRefTB (IT j k) = [IT j (restrictTable nonRefTB <$> k)]
nonRefTB (Fun _ _ _) = []
nonRefTB i = [i]

kattr :: Ord k => Column k a -> [FTB a]
kattr (Attr _ i) = [i]
kattr (Fun _ _ i) = [i]
kattr (FKT i _ _) = L.concat $ kattr <$> unkvlist i
kattr (IT _ i) = recTB i
  where
    recTB (TB1 i) = L.concat $ fmap kattr (unkvlist i)
    recTB (ArrayTB1 i) = L.concat $ F.toList $ fmap recTB i
    recTB (LeftTB1 i) = L.concat $ F.toList $ fmap recTB i

aattr :: Ord k => TB k a -> [(k, FTB a)]
aattr (Attr k i) = [(k, i)]
aattr (Fun k _ i) = [(k, i)]
aattr (FKT i _ _) = L.concat $ aattr <$> unkvlist i
aattr (IT _ i) = go i
  where
    go i =
      case i
        -- TODO : Make a better representation for inline tables , to support product and sum tables properly
            of
        TB1 i ->
          concat $
          fmap maybeToList $
          filter isJust $
          fmap (traverse unSOptional) $
          concat $ fmap aattr $ F.toList $ unkvlist i
        LeftTB1 i -> maybe [] go i
        i -> []

instance Ord a => Ord (Interval.Interval a) where
  compare i j = compare (Interval.upperBound i) (Interval.upperBound j)

instance Ord k => Semigroup (KV k a) where
  (KV i) <> (KV j) = KV (PM.union i j)

instance Ord k => Monoid (KV k a) where
  mempty = KV PM.empty


findFK :: (Show k, Ord k, Show a) => [k] -> (TBData k a) -> Maybe (TB k a)
findFK l v =
  fmap snd $
  L.find (\(i, v) -> isFK v && S.map _relOrigin i == (S.fromList l)) $
  PM.toList $ _kvvalues $ (v)
  where
    isRel (Rel _ _ _) = True
    isRel _ = False
    isFK i =
      case i of
        FKT _ _ _ -> True
        IT _ _ -> True
                   -- ARel _ _ -> True
                   -- ARef  _  -> True
        i -> False

-- findFK  l v =  fmap recoverAttr' $ L.find (\(i,v) -> isFK v && S.map _relOrigin i == (S.fromList l))  $ Map.toList $ _kvvalues $ v
findAttr :: (Show k, Ord k, Show a) => k -> (TBData k a) -> Maybe (TB k a)
findAttr l v = kvLookup (S.singleton . Inline $ l) v <|> findFun l v



addAttr :: Ord k => TB k v -> KV k v -> KV k v
addAttr v i = KV $ PM.insert (S.fromList $ keyattr v) v (_kvvalues i)

findFun :: (Show k, Ord k, Show a) => k -> (TBData k a) -> Maybe (TB k a)
findFun l v =
  fmap snd .
  L.find (((pure . Inline $ l) ==) . fmap mapFunctions . S.toList . fst) $
  PM.toList $ _kvvalues $ (v)
  where
    mapFunctions (RelFun i _ _) = Inline i
    mapFunctions j = j

-- findFun l v = fmap recoverAttr' . L.find (((pure . Inline $ l) == ).fmap mapFunctions . S.toList .fst) $ Map.toList $ _kvvalues $ v
findFKAttr :: (Show k, Ord k, Show a) => [k] -> (TBData k a) -> Maybe (TB k a)
findFKAttr l v =
  case L.find (\(k, v) -> not $ L.null $ L.intersect l (S.toList k)) $
       PM.toList $ PM.mapKeys (S.map (_relOrigin)) $ _kvvalues $ (v) of
    Just (k, FKT a _ _) ->
      L.find
        (\i -> not $ L.null $ L.intersect l $ fmap (_relOrigin) $ keyattr $ i)
        (F.toList $ _kvvalues $ a)
   -- Just (k,ARel a _ ) ->   L.find (\i -> not $ L.null $ L.intersect l $ fmap (_relOrigin) $ keyattr $ i ) (unkvlist a)
    Just (k, i) -> error (show l)
    Nothing -> Nothing


recLookup :: Ord k => Rel k -> TBData k v -> Maybe (FTB v)
recLookup p@(Inline l) v = _tbattr <$> kvLookup (S.singleton p) v
recLookup n@(RelAccess l nt) v =
  join $ fmap join . traverse (recLookup nt) <$> refLookup (S.fromList l) v

kvLookup :: Ord k => Set (Rel k) -> KV k a -> Maybe (TB k a)
-- kvLookup rel  (KV i) = Map.lookup rel i
kvLookup rel (KV i) = recoverAttr' <$> PM.lookup rel i

relLookup :: Ord k => Set (Rel k) -> KV k a -> Maybe (FTB (TBRef k a))
relLookup rel i = liftFK <$> kvLookup rel i

refLookup :: Ord k => Set (Rel k) -> KV k a -> Maybe (FTB (KV k a))
-- refLookup rel (KV i) = _aref <$> Map.lookup rel i
refLookup rel i = _fkttable <$> kvLookup rel i

attrLookup :: Ord k => Set (Rel k) -> KV k a -> Maybe (FTB a)
attrLookup rel i = _tbattr <$> kvLookup rel i

-- attrLookup rel (KV i) = _aprim <$> Map.lookup rel i
unTB1 :: FTB a -> a
unTB1 (TB1 i) = i
unTB1 i = fromMaybe (error "unTB1: ") . headMay . F.toList $ i

-- Intersections and relations
keyAttr (Attr i _) = i
keyAttr (Fun i _ _) = i
keyAttr i = error $ "cant find keyattr " <> (show i)

unAttr (Attr _ i) = i
unAttr (Fun _ _ i) = i
unAttr i = error $ "cant find attr" <> (show i)

unArray (ArrayTB1 s) = s
unArray o = error $ "unArray no pattern " <> show o

unSOptional (LeftTB1 i) = join $ unSOptional <$> i
unSOptional i = Just i

unSDelayed (LeftTB1 i) = i
unSDelayed i = traceShow ("unSDelayed No Pattern Match" <> show i) Nothing

unSSerial (LeftTB1 i) = i
unSSerial i =
  traceShow ("unSSerial No Pattern Match SSerial-" <> show i) Nothing

indexerRel :: Text -> Rel Text
indexerRel field =
  L.head $
  foldr
    (\i -> fmap (RelAccess (Inline <$> i) ))
    (Inline <$> last vec)
    (init vec)
  where
    vec = T.splitOn "," <$> T.splitOn ":" field

renderRel :: Show k => Rel k -> String
renderRel (Inline k) = show k
renderRel (RelFun k expr rel) = show k ++ " = " ++ renderFun expr rel
  where
    renderFun :: Show k => Expr -> [Rel k] -> String
    renderFun e ac = go e
      where
        go :: Expr -> String
        go (Function i e) =
          T.unpack i ++ "(" ++ L.intercalate "," (fmap go e) ++ ")"
        go (Value i) = renderRel $ justError "no value" $ ac `atMay` i
renderRel (RelAlias k rel) =
  show k ++ " = " ++ L.intercalate "," (renderRel <$> rel) ++ " as "
renderRel (RelAccess i l) =
  L.intercalate "," (renderRel <$> i) ++ "." ++ renderRel l
renderRel (Rel i Equals k)
  | show i == show k = show i
renderRel (Rel i op k) = show i <> renderBinary op <> show k


tbUn :: Ord k => Set k -> KV k a -> KV k a
tbUn un (KV item) = KV $ PM.filterWithKey (\k _ -> pred k) item
  where
    pred k = S.isSubsetOf (S.map _relOrigin k) un


makeLenses ''KV
makeLenses ''TB


recOverAttr ::
     Ord k
  => [Set (Rel k)]
  -> TB k a
  -> KV k a -> KV k a
recOverAttr (k:[]) attr = KV . PM.insert k attr . _kvvalues
recOverAttr (k:xs) attr =
  KV . PM.alter
    (fmap (Le.over ifkttable (fmap (recOverAttr xs attr ))))
    k . _kvvalues

recOverKV ::
     Ord k => [Set (Rel k )]
  -> [[Set (Rel k)]]
  -> KV k b
  -> KV k b
recOverKV tag tar (KV m) = KV $ foldr go m tar
  where
    go (k:[]) =
      PM.alter
        (fmap (Le.over ifkttable (fmap (recOverAttr tag recv )))) k
      where
        recv = gt tag m
    go (k:xs) =
      PM.alter
        (fmap (Le.over ifkttable (fmap (KV . go xs . _kvvalues))))
        k
    gt (k:[]) = justError "no key" . PM.lookup k
    gt (k:xs) =
      gt xs .
      _kvvalues .
      L.head . F.toList . _fkttable . justError "no key" . PM.lookup k

replaceRecRel ::
     Ord k => KV k b
  -> [MutRec [Set (Rel k)]]
  -> KV k b
replaceRecRel i = foldr (\(MutRec l) v -> foldr (\a -> recOverKV a l) v l) i

kvSingleton  :: Ord k => TB k a -> KV k a
kvSingleton i = KV $ PM.singleton (S.fromList $ keyattr i ) i

kvSize :: Ord k => KV k a ->  Int
kvSize (KV i) = PM.size i

kvNull :: Ord k => KV k a ->  Bool
kvNull (KV i) = PM.null i

kvFind :: Ord k =>  (Set (Rel k) -> Bool) -> KV k a ->  Maybe (TB k a)
kvFind pred (KV item) = safeHead . F.toList $ PM.filterWithKey (\k _ -> pred k ) item

kvFilter :: Ord k =>  (Set (Rel k) -> Bool) -> KV k a ->  KV k a
kvFilter pred (KV item) = KV $ PM.filterWithKey (\k _ -> pred k ) item

kvFilterWith :: Ord k =>  (Set (Rel k) -> TB k a -> Bool) -> KV k a ->  KV k a
kvFilterWith pred (KV item) = KV $ PM.filterWithKey pred item

alterKV k fun (KV i ) = KV <$> (PM.alterF fun k i)

alterAtF k fun i= alterKV k (traverse (Le.traverseOf ifkttable fun))  i
