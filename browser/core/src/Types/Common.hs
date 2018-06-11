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

module Types.Common
  ( TB(..)
  , TBRef(..)
  , _fkttable
  , mapFValue
  , mapFAttr
  , traFAttr
  , traFValue
  , keyAttr
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
  , traTable
  , keyattr
  , liftFK
  , recoverFK
  -- ,recoverAttr', firstATB ,traFAValue,AValue(..),TBAttr
  , FTB(..)
  , unTB1
  , unSOptional
  , unSSerial
  , unSDelayed
  , unArray
  , KV(..)
  , TBData
  , unKV
  , kvlist
  , kvLookup
  , refLookup
  , recLookup
  , relLookup
  , attrLookup
  , unkvlist
  , kvmap
  , kattr
  , aattr
  , tableKeys
  , nonRefTB
  , tableNonRef
  , Rel(..)
  , indexerRel
  , _relOrigin
  , _relRoot
  , _relTarget
  , _relInputs
  , _relOutputs
  , Expr
  , FExpr(..)
  , BinaryOperator(..)
  , readBinaryOp
  , renderRel
  , renderBinary
    -- ,valueattr
  ) where

import Control.Applicative
import Control.DeepSeq
import Control.Monad
import Data.Binary (Binary(..))
import Data.Binary.Orphans
import Data.Foldable (Foldable)
import qualified Data.Foldable as F
import Data.Functor.Identity
import qualified Data.Interval as Interval
import qualified Data.List as L
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Monoid hiding (Product)
import Data.Ord
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Set as S
import qualified Data.Text as T
import Data.Text (Text)
import Data.Traversable (Traversable, traverse)
import Debug.Trace
import GHC.Generics
import qualified NonEmpty as Non
import NonEmpty (NonEmpty(..))
import Prelude hiding (head)
import Safe
import Utils

newtype TBRef k s = TBRef { unTBRef :: (KV k s,KV k s)}deriving(Show,Eq,Ord,Functor)

newtype KV k a
  -- = KV { _kvvalues :: Map (Set (Rel k)) (AValue k a) }deriving(Eq,Ord,Functor,Foldable,Traversable,Show,Generic)
         = KV
  { _kvvalues :: Map (Set (Rel k)) (TB k a)
  } deriving (Eq, Ord, Functor, Foldable, Traversable, Show, Generic)

kvlist :: Ord k => [TB k a] -> KV k a
kvlist = KV . mapFromTBList

unkvlist :: Ord k => KV k a -> [TB k a]
unkvlist = F.toList . _kvvalues

-- unkvlist = fmap (recoverAttr . first F.toList ) . Map.toList . _kvvalues
-- unkvmap = Map.fromList . fmap (\(i,j) -> (i, recoverAttr  (F.toList i,j))) . Map.toList . _kvvalues
kvmap :: Map.Map (Set (Rel k)) (TB k a) -> KV k a
kvmap = KV

-- kvmap = KV . fmap valueattr
unKV :: KV k a -> Map.Map (Set (Rel k)) (AValue k a)
unKV = _kvvalues

mapBothKV :: Ord b => (a -> b) -> (AValue a c -> AValue b d) -> KV a c -> KV b d
mapBothKV k f (KV n) = KV (Map.mapKeys (S.map (fmap k)) $ fmap f n)

mapKV f (KV n) = KV (fmap f n)

traverseKV f (KV n) = KV <$> traverse f n

filterKV i (KV n) = KV $ Map.filterWithKey (\k -> i) n

findKV i (KV n) = L.find (i . snd) $ Map.toList n

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
renderBinary (Flip i) = renderBinary i
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
  | LowerThan Bool
  | IntersectOp
  | Flip BinaryOperator
  | AnyOp BinaryOperator
  deriving (Eq, Ord, Show, Generic)

instance Binary BinaryOperator

instance NFData BinaryOperator

-- Reference labeling
-- exchange label reference for values when labeled
-- inline values reference when unlabeled
data Rel k
  = Inline { _relOri :: k }
  | Rel { _relOri :: k
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

_relOrigin (Rel i _ _) = i
_relOrigin (Inline i) = i
_relOrigin (RelAccess _ i) = _relOrigin i
_relOrigin (RelFun i _ _) = i
_relOrigin (RelAlias i _) = i

_relRoot (Rel i _ _) = i
_relRoot (Inline i) = i
_relRoot (RelAccess _ i) = _relOrigin i
_relRoot (RelFun i _ _) = i
_relRoot (RelAlias i _) = i

_relInputs (Rel i _ _) = Just [i]
_relInputs (Inline i) = Nothing
_relInputs (RelAccess i _) = Just $ concat (catMaybes $ _relInputs <$> i)
_relInputs (RelFun _ _ l) = Just $ fmap _relOrigin l
_relInputs (RelAlias i l) = Just $ fmap _relOrigin l

_relOutputs (Rel _ (Flip (AnyOp Equals)) _) = Nothing
_relOutputs (Rel _ IntersectOp _) = Nothing
_relOutputs (Rel _ (Flip IntersectOp) _) = Nothing
_relOutputs (Rel _ Contains _) = Nothing
_relOutputs (Rel _ (Flip Contains) _) = Nothing
_relOutputs (Rel i (AnyOp Equals) _) = Just [i]
_relOutputs (Rel i Equals _) = Just [i]
_relOutputs (Rel i (Flip Equals) _) = Just [i]
_relOutputs (Rel _ _ _) = Nothing
_relOutputs (Inline i) = Just [i]
_relOutputs (RelAccess i _) = Nothing -- Just [i]
_relOutputs (RelFun i _ _) = Just [i]
_relOutputs (RelAlias i _) = Nothing

instance (Binary a, Binary k) => Binary (KV k a)

instance Binary k => Binary (Rel k)

instance NFData k => NFData (Rel k)

instance (Binary k, Binary g) => Binary (TB g k)

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
-- traFValue f k =  traverseKV (traFAValue f) k
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
firstKV f (KV m) = KV . fmap (firstTB f) . Map.mapKeys (Set.map (fmap f)) $ m

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
  fromRational i = TB1 (fromRational i)
  recip i = fmap recip i

mapFromTBList :: Ord k => [TB k a] -> Map (Set (Rel k)) (AValue k a)
mapFromTBList = Map.fromList . fmap (\i -> (Set.fromList (keyattr i), i))

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
           (fmap _tbattr . Map.lookup (S.singleton $ Inline k) . _kvvalues . fst.unTBRef) $
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

findRel l (Rel k op j) = do
  Attr k v <- L.find (\(Attr i v) -> i == k) l
  return $ fmap (Attr k . TB1) v

tableKeys k = concat $ fmap (fmap _relOrigin . keyattr) (unkvlist k)

tableNonRef :: Ord k => KV k a -> KV k a
tableNonRef n = (rebuildTable . unkvlist) n
  where
    rebuildTable n = kvlist . concat . F.toList $ nonRefTB <$> n

nonRefTB :: Ord k => TB k a -> [TB k a]
nonRefTB (FKT i _ _) = concat (nonRefTB <$> unkvlist i)
nonRefTB (IT j k) = [IT j (tableNonRef <$> k)]
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

instance Ord k => Monoid (KV k a) where
  mempty = KV Map.empty
  mappend (KV i) (KV j) = KV (Map.union i j)

recLookup :: Ord k => Rel k -> TBData k v -> Maybe (FTB v)
recLookup p@(Inline l) v = _tbattr <$> kvLookup (S.singleton p) v
recLookup n@(RelAccess l nt) v =
  join $ fmap join . traverse (recLookup nt) <$> refLookup (S.fromList l) v

kvLookup :: Ord k => Set (Rel k) -> KV k a -> Maybe (TB k a)
-- kvLookup rel  (KV i) = Map.lookup rel i
kvLookup rel (KV i) = recoverAttr' <$> Map.lookup rel i

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
    (\i j -> RelAccess (Inline <$> i) <$> j)
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
