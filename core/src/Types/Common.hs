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
  , TBF(..)
  , AValue(..)
  , FAValue(..)
  , RelSort(..)
  , TBRef(..)
  , FKV(..)
  , _fkttable
  , _tbattr
  , ifkttable
  , mapFValue
  , mapFAttr
  , simplifyRel
  , relComp
  , relAccessSafe
  , relCompS
  , relNormalize 
  , relNull
  , relUnComp
  , replaceRecRel
  , traFAttr
  , traFValue
  , relSort
  , relSortL
  , keyAttr
  , tbUn
  , unAttr
  , mapKV
  , mapKVMaybe
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
  , mergeKVWith
  , trazipWithKV
  , traTable
  , keyattr
  , recoverFK
  , kvFind
  , kvFilter
  , kvFilterWith
  , kvNull
  , kvNonEmpty
  , kvSingleton
  , kvSize
  , getAtt
  -- ,recoverAttr', firstATB ,traFAValue,AValue(..),TBAttr
  , FTB(..)
  , PathTID(..)
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
  ,kvMerge
  ,kvUnion
  , kvlistMerge
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
  , recLookupKV
  , refLookup
  , relAppend
  , recLookup'
  , recLookup
  , attrLookup
  , unkvlist
  , sortedFields
  , sortRels
  , sortValues
  , kvmap
  , aattr
  , nonRefTB
  , tableNonRef
  , restrictTable
  , nonFK
  , isRelAccess
  , Rel(..)
  , indexerRel
  , _relOrigin
  , _relTarget
  , _relInputs
  , _relOutputs
  , relOutputSet
  , Expr
  , MutRec(..)
  , FExpr(..)
  , BinaryOperator(..)
  , readBinaryOp
  , renderRel
  , renderBinary
  ) where

import Control.Applicative
import Control.Arrow
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
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Set as S
import qualified Data.Text as T
import Data.Graph
import Data.Text (Text)
import Data.Traversable (Traversable, traverse)
import Debug.Trace
import GHC.Generics
import qualified NonEmpty as Non
import Data.String
import NonEmpty (NonEmpty(..))
import Data.Sequence.NonEmpty (NonEmptySeq(..))
import qualified Data.Sequence.NonEmpty as NonS 
import Prelude hiding (head)
import Safe
import Utils

newtype FKV k f a
  = KV
  { _kvvalues :: Map (RelSort k) (FAValue k f a)
  } deriving (Functor, Foldable, Traversable, Generic)

type KV k a = FKV k FTB a

relSortL :: Ord k  =>  Rel k  -> RelSort k
relSortL = relSort 

originalRel (RelSort _ _  l) = l

relSortMap f (RelSort i j k) = RelSort  ( S.map  f i) (S.map f j) (fmap f k)

relSort i = RelSort (inp i)  (out i) i
  where
    inp j = norm $ _relInputs j
    out j = norm $ _relOutputs  j
    norm = maybe S.empty S.fromList 

instance Eq k => Eq (RelSort k ) where
  (RelSort _ _ i) ==  (RelSort _ _ j ) = i == j 

instance Ord k => Ord (RelSort k ) where
  compare  (RelSort _ _ i) (RelSort _ _ j ) = compare i j 

data RelSort k =
  RelSort (Set k) (Set k) (Rel k)
  deriving (Generic)

instance Show k => Show (RelSort k) where
  show (RelSort _ _ i )= renderRel  i

    

newtype MutRec a = MutRec
  { unMutRec :: [a]
  } deriving (Eq, Ord, Show, Functor, Foldable, Generic, Binary, NFData)

sortRels
  :: (Show k,Ord k) =>
  [Rel k]  -> [Rel k]
sortRels = fmap relComp . fst .topSortRels . fmap (S.fromList . relUnComp) -- fmap (originalRel) .P.sortBy (P.comparing id) . fmap relSort

simplifyRel (RelAccess i l ) = simplifyRel l
simplifyRel (RelComposite l ) = relComp $ fmap simplifyRel $ filter (not . S.null . relOutputSet ) l
simplifyRel (Rel i _ j ) = i
-- simplifyRel (NInline _ i) = Inline i
simplifyRel i = i 


sortedFields
  :: (Show a,Show k,Ord k)
  => FKV k f a
  -> [(Rel k , TBF k f a)]
sortedFields (KV map)=  (\i -> (i,) . recoverAttr . (i,) . justError"noField" $  Map.lookup  (relSort i) map ) <$>  srels
  where srels = sortRels (originalRel <$> Map.keys map)

sortValues :: (Ord k ,Show v,Show k) => (v -> Rel k ) -> [v] -> [v]
sortValues f  v =  (\i -> justError ("noField" ++ show (i,Map.keys fieldMap )) $ Map.lookup i fieldMap )  <$>  srels
  where srels = sortRels (fst <$> map)
        fieldMap = Map.fromList map 
        map  = fmap (\i -> (f i ,i)) v



isInline (Inline i ) = True
isInline _ = False

instance  Ord k => PartialOrd (RelSort k) where
  leq (RelSort inpi outi i ) (RelSort inpj outj j)
      | isInline i && isInline j = i <= j
      | isInline i &&  not (isInline j) = True
      | isInline j &&  not (isInline j) = False
  leq (RelSort inpi outi i ) (RelSort inpj outj j)
    =  li || i == j  -- || if not (li || lo) then (not (S.null outj) && not (S.null outi) && S.toList outi < S.toList outj) else False
    where li = not (S.null outi) && not (S.null inpj) && leq outi inpj
          -- lo = not (S.null inpi) && not (S.null outj) && leq inpi outj

-- To Topologically sort the elements we compare  both inputs and outputs for intersection if one matches we flip the
instance (Ord k, P.Poset k) => P.Poset (RelSort k) where
  compare (RelSort inpi outi i ) (RelSort inpj outj j) =
    case (  inline i j
         , comp outi inpj
         , comp outj inpi
         , P.compare inpi inpj
         , P.compare outi outj)
            -- Reverse order
          of
      (p, i, j, k, l) -> p <> i <> flipO j  <> k <> l
    where
      flipO P.GT = P.LT
      flipO P.LT = P.GT
      flipO i = i

      inline i j
        -- | F.all isInline i && F.all isInline j = P.compare i j
        | isInline i && not (isInline j) = P.LT
        | isInline j && not (isInline i) = P.GT
        | otherwise = P.EQ
      comp i j
        | S.null (S.intersection i j) = P.EQ
      comp i j
        | S.empty == i = P.EQ
      comp i j
        | S.empty == j = P.EQ
      comp i j = P.compare i j

testMap =  originalRel <$> [(relSortL (Inline 3)),(relSortL (Inline 1)),(relSortL (Inline 2)),(relSortL (relComp [Output (Inline 4),Rel (RelAccess (Inline (3 :: Int)) (Inline 3)) (Flip Contains) (Inline 4)])), (relSortL (Inline 4)),relSortL (Rel (Inline 3) Contains (Inline 5))]

topSortRels :: (Show k,Ord k) => [Set (Rel k)] ->  ([Set (Rel k)],[Int])
topSortRels l = ((l!!) <$> sorted,sorted)
  where
    edgeList = concat $ concat $ deps
    sorted = topSort (buildG (0,L.length l - 1 ) edgeList)
    edges = zip  l [0..]
    outputMap = Map.fromListWith (<>) $ fmap pure . first outputs <$> edges
    deps = findDeps <$> edges
    outputs i = S.fromList $ concat $ catMaybes $ _relOutputs <$> S.toList i
    findDeps (l,ix) = findDep ix <$> S.toList l
    findDep ix (RelAccess l _)
      = maybe [] (fmap (,ix) )$ Map.lookup (outputs $ S.singleton l) outputMap
    findDep ix rel@(Rel r _ _)
      | not (isRelAccess r) && isNothing (_relOutputs rel) = maybe [] (fmap (,ix)) $ Map.lookup (outputs (S.singleton r)) outputMap
    findDep ix (Rel r _ _) = findDep ix r
    findDep ix (RelFun _ _ l) = concat $ findDep ix . fix <$> l
      where fix (Inline i) =  (RelAccess (Inline i) (Inline i))
            fix i = i
    findDep ix (Inline i) = [(ix,ix)]
    findDep ix (Output (RelAccess i _ ) ) = maybe [] (fmap (ix,)) $ Map.lookup (outputs $ S.singleton i) outputMap
    findDep ix (Output i) = maybe [] (fmap (ix,)) $ Map.lookup (outputs $ S.singleton i) outputMap
    findDep ix c = []


kvlist,kvlistMerge :: (Applicative f, Ord k )=> [TBF k f a] -> FKV k f a
kvlist = KV . mapFromTBList

kvlistMerge = KV .mapFromTBListMerge

kvMerge :: (Applicative f, Ord k )=> FKV k f a -> FKV k f a -> FKV k f a
kvMerge i j = kvlistMerge (unkvlist i ++ unkvlist j ) 

kvUnion :: (Applicative f, Ord k )=> [FKV k f a] -> FKV k f a
kvUnion i = kvlistMerge (concat $ unkvlist <$> i  ) 

kvToMap :: Ord k => KV k a -> Map.Map (Rel k) (FTB a)
kvToMap = fmap _aprim . Map.fromList .fmap (first originalRel).  Map.toList . _kvvalues

kvkeys :: Ord k => FKV k f a -> [Rel k]
kvkeys = fmap originalRel . Map.keys . _kvvalues

unkvlist :: Ord k => FKV k f a -> [TBF k f a]
unkvlist = fmap (recoverAttr . first originalRel). Map.toList . _kvvalues


kvmap :: Ord k => Map.Map (Rel k) (TBF k f a) -> FKV k f a
kvmap = KV . Map.fromList . fmap (first relSort . fmap valueattr). Map.toList

unKV :: Ord k => FKV k f a -> Map.Map (Rel k) (TBF k f a)
unKV =  Map.fromList . fmap (\i ->  (originalRel (fst i),) . recoverAttr . first originalRel $ i ) . Map.toList . _kvvalues

mapBothKV :: (Ord a,Ord b) => (a -> b) -> (TBF a f c -> TBF b f d) -> FKV a f c -> FKV b f d
mapBothKV k f (KV n) = KV (Map.mapKeys (relSortMap k) $ Map.mapWithKey (\k ->  valueattr . f . recoverAttr . (originalRel k ,) )  n)

mapKV f (KV n) = KV (Map.mapWithKey (\k ->  valueattr . f . recoverAttr . (originalRel k ,) ) n)

mapKVMaybe  f (KV n) = KV (runIdentity $ Map.traverseMaybeWithKey (\k ->  Identity . fmap valueattr . f . recoverAttr . (originalRel k ,) ) n)

mergeKV (KV i ) (KV j) = KV $ Map.unionWith const i j

mergeKVWith
  :: (Show k,Show v,Ord k) =>
     (FAValue k f a -> FAValue k f a -> v)
     -> (FAValue k f a -> v) -> FKV k f a -> FKV k f a -> [(Rel k, v)]
mergeKVWith diff create (KV v ) (KV o) = first originalRel <$> (Map.toList (Map.intersectionWith  diff v o) <> created)
  where created = fmap (fmap create) $  filter (not . flip Set.member (S.fromList $ Map.keys v). fst ) (Map.toList o) 

traverseKVWith
  :: (Ord k ,Applicative f)
    => (Rel k -> AValue k a1 -> f (AValue k a2)) 
    -> KV k a1 
    -> f (KV k a2)
traverseKVWith f (KV n) = KV <$> Map.traverseWithKey (\i -> f (originalRel i) )  n

traverseKV
  :: (Ord k ,Applicative g,Applicative f)
    => (TBF k g a1 -> f (TBF k l a2)) 
    -> FKV k g a1 
    -> f (FKV k  l a2)
traverseKV f (KV n) = KV . fmap valueattr <$> traverse f (Map.mapWithKey (curry (recoverAttr . first originalRel )) n ) 


trazipWithKV f (KV v1) (KV v2) = KV <$>  sequence (Map.intersectionWithKey (\k i j -> valueattr <$> f (conv k i) (conv k j) )  v1 v2)
  where conv = curry (recoverAttr . first originalRel )

filterKV ::Ord k =>  (TB k a -> Bool) -> KV k a -> KV k a
filterKV i (KV n) = KV $ Map.filterWithKey (curry ( i . recoverAttr . first originalRel) ) n

findKV :: Ord k => (TB k a -> Bool) -> KV k a -> Maybe (Rel k, TB k a)
findKV i (KV n) = fmap (\i -> (originalRel (fst i) , ). recoverAttr.  first originalRel $ i ) . L.find (i .recoverAttr . first originalRel ) $ Map.toList n


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
  | NInline 
          { _relTable :: String 
          , _relOri :: k }
  | Output { _relAccess :: Rel k }
  | Rel { _relAccess :: Rel k
        , _relOperator :: BinaryOperator
        , _relTip :: Rel k  }
  | RelComposite [Rel k]
  | RelAccess { _relAccess :: Rel k
              , _relTip :: Rel k }
  | RelFun { _relAccess :: Rel k
           , _relExpr :: Expr
           , _relReference :: [Rel k] }
  deriving (Eq, Show, Ord, Functor, Traversable, Foldable, Generic)

relAccessSafe (Rel i _ _)  = i 
relAccessSafe (RelAccess i _ ) = i 
relAccessSafe (RelFun i _ _ ) = i 
relAccessSafe (Output i ) = i
relAccessSafe i@(Inline _ ) = i
relAccessSafe i = error $ "failed relAccess on " ++ show (i)

_relTarget (Rel _ _ i) = i
-- _relTarget (RelComposite i ) = _relTarget <$> i
_relTarget (RelAccess _ i) = _relTarget i
_relTarget i = error (show i)

relNull (RelComposite []) = True
relNull i = False

relCompS :: Ord a => Foldable f => f (Rel a) -> Rel a
relCompS  i 
  | F.length i > 1 = RelComposite $ F.toList  i
  | otherwise = fromMaybe (RelComposite []) $ safeHead (F.toList i )


relComp :: Ord a => Foldable f => f (Rel a) -> Rel a
relComp  i 
  | F.length i > 1 = RelComposite $ L.sort $ F.toList  i
  | otherwise = fromMaybe (RelComposite []) $ safeHead (F.toList i )

relUnComp (RelComposite l) = l 
relUnComp i = [i]

relNormalize l 
  = ((\ (i, j) -> RelAccess i (relComp (relNormalize j)))  <$> groupSplit2 _relAccess relRef (filter isRelAccess l) ) <> filter (not .isRelAccess) l
    where isRelAccess (RelAccess _ _) = True
          isRelAccess _ = False
          relRef (RelAccess _ ref) = ref

_relOrigin (Rel i _ _) = _relOrigin i
_relOrigin (RelComposite i ) = case simplifyRel (relComp i) of
                                 RelComposite i -> error "origin needs to be unique"
                                 i -> _relOrigin i
_relOrigin (Inline i) = i
_relOrigin (NInline _ i ) = i
_relOrigin (Output i) = _relOrigin i
_relOrigin (RelAccess _ i) = _relOrigin i
_relOrigin (RelFun i _ _) = _relOrigin i


-- TODO Fix Rel to store proper relaaccess
_relInputs (Rel i _ _) = _relInputs i
_relInputs (Inline i) = Just [i]
_relInputs (Output i) = Nothing
_relInputs (RelAccess i _) = _relOutputs i
_relInputs (RelFun _ _ l) =  _relOutputs (relComp l )
_relInputs (RelComposite l ) = nonEmpty $ concat $ catMaybes $ fmap _relInputs l

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
_relOutputs (NInline _ i) = Just [i]
_relOutputs (Output i) = _relOutputs i
_relOutputs (RelAccess i _) = Nothing -- Just [i]
_relOutputs (RelFun i _ _) = _relOutputs i
_relOutputs (RelComposite l ) = nonEmpty $ concat $ catMaybes $ fmap _relOutputs l

relOutputSet :: Ord k => Rel k -> Set k 
relOutputSet  = maybe S.empty S.fromList . _relOutputs 



instance Binary k => Binary (RelSort k )
instance NFData k => NFData (RelSort k )
instance (Ord a,Ord k ,Binary a, Binary k) => Binary (KV k a)

instance Binary k => Binary (Rel k)

instance NFData k => NFData (Rel k)

instance (Ord k,Ord g ,Binary k, Binary g) => Binary (TB g k)

instance Binary a => Binary (FTB a)

instance NFData a => NFData (FTB a)

type Expr = FExpr Text Text

data FExpr r k
  = Value Int
  | ConstantExpr k
  | Function r [FExpr r k]
  deriving (Eq, Ord, Show, Generic,Functor,Foldable,Traversable)

instance (Binary k, Binary j) => Binary (FExpr k j)

instance (NFData k, NFData j) => NFData (FExpr k j)

type TBAttr k f v = (Rel k, FAValue k f v)


type AValue k a = FAValue k FTB a

data FAValue k f a
  = APrim {_aprim :: f a }
  | ARef {_aref :: f (FKV k f a)}
  | ARel { _arel :: FKV k f a  , _aref :: (f (FKV k f a))}
  deriving(Functor,Foldable,Traversable,Generic)

recoverAttr ::  Ord k => TBAttr k f a -> TBF k f a
recoverAttr (Inline i,APrim v) = Attr i v
recoverAttr (RelFun (Inline i) j k  ,APrim v) = Fun i (j,k) v
recoverAttr (Inline i ,ARef v) = IT i v
recoverAttr (i,ARel l v) = FKT l  (relUnComp i) v

valueattr :: TBF k f a -> FAValue k f a
valueattr (Attr i j) = APrim j
valueattr (Fun _ _ v) = APrim v
valueattr (IT _ v) = ARef v
valueattr (FKT i  _ v) = ARel i v


instance (Ord g,Ord k,Binary k ,Binary g) => Binary (AValue g k )
instance (NFData k ,NFData g) => NFData (AValue g k )

instance (NFData k, NFData a) => NFData (KV k a)

instance (NFData k, NFData a) => NFData (TB k a)

{-
-- instance (Binary  a ,Binary k ) => Binary (AValue k a)
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

_tbattr (Attr _ v ) = v
_tbattr (Fun _ _ v) = v
_tbattr i = error "not a attr"


data TBF k f a
  = Attr -- Primitive Value
     { _tbattrkey :: k
     , _tbattrvalue :: f a }
  | Fun -- Function Call
     { _tbattrkey :: k
     , _fundata :: (Expr, [Rel k])
     , _tbattrvalue :: f a }
  | IT -- Inline Table
     { _tbattrkey :: k
     , _ifkttable :: f (FKV k f a) }
  | FKT -- Foreign Table
     { _tbref :: FKV k f a
     , _fkrelation :: [Rel k]
     , _ifkttable :: f (FKV k f a) }
  deriving (Functor, Foldable, Traversable, Generic )

type TB k a = TBF k FTB a

newtype TBRef k s = TBRef { unTBRef :: (KV k s,KV k s)}deriving(Functor)

_fkttable (IT _ i) = i
_fkttable (FKT _ _ i) = i
_fkttable (Attr i _) = error "hit attr"
_fkttable (Fun i _ _) = error "hit fun"



traFAttr :: (Ord k ,Applicative f) => (FTB a -> f (FTB b)) -> TB k a -> f (TB k b)
traFAttr f (Attr i v) = Attr i <$> f v
traFAttr f (IT i v) = IT i <$> traverse (traFValue f) v
traFAttr f (FKT i rel v) =
  liftA2 (\a b -> FKT a rel b) (traFValue f i) (traverse (traFValue f) v)

traFValue :: (Ord k ,Applicative f) => (FTB a -> f (FTB b)) -> KV k a -> f (KV k b)
traFValue f k = traverseKV (traFAttr f) k

traMap g f = runIdentity . g (Identity . f)

mapFAttr :: Ord k => (FTB a -> (FTB b)) -> TB k a -> (TB k b)
mapFAttr = traMap traFAttr


mapFValue :: Ord k => (FTB a1 -> FTB a2) -> KV k a1 -> KV k a2
mapFValue f k = KV . fmap (valueattr . traMap traFAttr f). Map.mapWithKey (curry (recoverAttr . first originalRel )) . _kvvalues $ k



mapKey',firstKV :: (Functor f, Ord c,Ord k) => (c -> k) -> FKV c f a -> FKV k f a
firstKV f (KV m) = KV . Map.mapKeys (relSortMap f). Map.mapWithKey (curry (valueattr . firstTB f. recoverAttr . first originalRel))   $ m
mapKey' = firstKV 
mapKey f = fmap (mapKey' f)

secondKV f (KV m) = KV . fmap (fmap f) $ m

firstTB :: (Functor f,Ord c,Ord k) => (c -> k) -> TBF c f a -> TBF k f a
firstTB f (Attr k i) = Attr (f k) i
firstTB f (Fun k i l) = Fun (f k) (fmap (fmap f) <$> i) l
firstTB f (IT k i) = IT (f k) (mapKey f i)
firstTB f (FKT k m i) = FKT (mapKey' f k) (fmap f <$> m) (mapKey f i)

data FTB a
  = TB1 !a
  | LeftTB1 !(Maybe (FTB a))
  | ArrayTB1 !(NonEmptySeq (FTB a))
  | IntervalTB1 !(Interval.Interval (FTB a))
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Generic)


data PathTID
  = PIdIdx Int
  | PIdOpt
  | PIdTraverse
  | PIdInter Bool
  | PIdAtom
  deriving (Eq,Ord,Show,Generic)



instance Monad FTB where
  TB1 i >>= j = j i
  LeftTB1 o >>= j = LeftTB1 $ fmap (j =<<) o
  ArrayTB1 o >>= j = ArrayTB1 $ fmap (j =<<) o

instance Applicative FTB where
  pure = TB1
  TB1 i <*> TB1 j = TB1 $ i j
  LeftTB1 i <*> LeftTB1 j = LeftTB1 $ liftA2 (<*>) i j
  ArrayTB1 i <*> ArrayTB1 j = ArrayTB1 $ NonS.zipWith (<*>) i j
  i <*> LeftTB1 j = LeftTB1 $ fmap (i <*>) j
  LeftTB1 i <*> j = LeftTB1 $ fmap (<*> j) i
  i <*> ArrayTB1 j = ArrayTB1 $ fmap (i <*>) j
  ArrayTB1 i <*> j = ArrayTB1 $ fmap (<*> j) i

-- Literals Instances
instance Enum a => Enum (FTB a) where
  toEnum = TB1 . toEnum
  fromEnum (TB1 i) = fromEnum i

instance Floating a => Floating (FTB a) where
  (TB1 i) ** TB1 j  = TB1 (i ** j)


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

mapFromTBList :: Ord k => [TBF k f a] -> Map (RelSort k) (FAValue k f a)
mapFromTBList = Map.fromList . fmap (\i -> (relSort $ keyattr i, valueattr i))

mapFromTBListMerge :: (Applicative f, Ord k) => [TBF k f a] -> Map (RelSort k) (FAValue k f a)
mapFromTBListMerge = Map.fromListWith mergeAttr . fmap (\i -> (relSort $ keyattr i, valueattr i))

mergeAttr (APrim _) a@(APrim _) =  a
mergeAttr (ARef j)  (ARef  m) =  ARef $ (\ j m -> KV $ mapFromTBListMerge (unkvlist j ++ unkvlist m)) <$> j <*> m
mergeAttr (ARel i j)  (ARel  l m) =  ARel (KV $ mapFromTBListMerge (unkvlist i ++ unkvlist l)) $ (\ j m -> KV $ mapFromTBListMerge (unkvlist j ++ unkvlist m)) <$> j <*> m


keyattr :: Ord k => TBF k f a -> Rel k
keyattr (Attr i _) = Inline i
keyattr (Fun i l _) = RelFun (Inline i) (fst l) (snd l)
keyattr (FKT i rel _) = relComp rel
keyattr (IT i _) = Inline i

traTable f (KV i) = KV <$> f i

alterFTB :: Applicative f => (a -> f a) -> FTB a -> f (FTB a)
alterFTB f (TB1 i) = TB1 <$> f i
alterFTB f (ArrayTB1 i) = ArrayTB1 <$> traverse (alterFTB f) i
alterFTB f (LeftTB1 i) = LeftTB1 <$> traverse (alterFTB f) i
alterFTB f (IntervalTB1 i) = IntervalTB1 <$> traverse (alterFTB f) i



addDefault :: Ord d => TB d a -> TB d b
addDefault = def
  where
    def (Attr k i) = Attr k (LeftTB1 Nothing)
    def (Fun k i _) = Fun k i (LeftTB1 Nothing)
    def (IT rel j) = IT rel (LeftTB1 Nothing)
    def (FKT at rel j) =
      FKT (kvlist $ addDefault <$> unkvlist at) rel (LeftTB1 Nothing)


recoverFK :: (Show s,Show k ,Ord k) => [Rel k] -> [Rel k] -> FTB (TBRef k s) -> Column k s
--recoverFK i l j | traceShow (i,l,j ) False = undefined
recoverFK ori rel i
 =
  FKT
    (kvlist . catMaybes $
     (\k ->
        Attr (_relOrigin k) <$>
        (fmap join .
         traverse
           (fmap _tbattr . kvLookup k . fst.unTBRef) $
         i)) <$>
     ori)
    rel
    (fmap (snd .unTBRef ) i)

instance IsString (Rel Text) where
  fromString i = 
    case T.break (=='.') (T.pack i) of
      (i,l) | T.null l ->  Inline i
      (t,v) -> NInline  (T.unpack t) (fromString $ T.unpack $ T.tail v)


instance IsString (Rel String ) where
  fromString i = 
    case L.break (=='.') i of
      (i,[]) ->  Inline i
      (t,_:v) -> NInline  t v


restrictTable :: (Applicative f , Ord k) => (TBF k f a  -> [TBF k f a]) -> FKV k f a -> FKV k f a
restrictTable f n =  (rebuildTable . unkvlist) n
  where
    rebuildTable n = kvlist . concat . F.toList $ f <$> n

tableNonRef :: (Applicative f ,Ord k) => FKV k f a -> FKV k f a
tableNonRef = restrictTable nonRefTB

isRelAccess (RelAccess i _ ) = isRelAccess i
isRelAccess (RelComposite i ) = L.any isRelAccess i
isRelAccess (Rel _ _ _) = True
isRelAccess _ = False

nonFK :: (Applicative f, Ord k) => TBF k f a -> [TBF k f a]
nonFK (FKT i _ _) = concat (nonFK <$> unkvlist i)
nonFK (IT j k) = [IT j (restrictTable nonFK <$> k)]
nonFK (Fun _ (_,l)  _) | L.any isRelAccess  l = []
nonFK i = [i]

nonRefTB :: (Applicative f,Ord k) => TBF k f a -> [TBF k f a]
nonRefTB (FKT i _ _) = concat (nonRefTB <$> unkvlist i)
nonRefTB (IT j k) = [IT j (restrictTable nonRefTB <$> k)]
nonRefTB (Fun _ _ _) = []
nonRefTB i = [i]


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
          concatMap maybeToList $
          filter isJust $
          fmap (traverse unSOptional) $
          concat $ fmap aattr $ F.toList $ unkvlist i
        LeftTB1 i -> maybe [] go i
        i -> []

instance Ord a => Ord (Interval.Interval a) where
  compare i j = compare (Interval.upperBound i) (Interval.upperBound j)

instance Ord k => Semigroup (FKV k f a) where
  (KV i) <> (KV j) = KV (Map.union i j)

instance Ord k => Monoid (FKV k f a) where
  mempty = KV Map.empty
  mappend = (<>)


findFK :: (Show k, Ord k, Show a) => [k] -> (TBData k a) -> Maybe (TB k a)
findFK l v =
  fmap (recoverAttr . first originalRel) $
    L.find (\(RelSort _ _ i, v) -> isFK v && relOutputSet i == (S.fromList l)) $
  Map.toList $ _kvvalues $ v
  where
    isRel (Rel _ _ _) = True
    isRel _ = False
    isFK i =
      case i of
       ARel _ _ -> True
       ARef  _  -> True
       i -> False

findAttr :: (Show k, Ord k, Show a) => k -> (FKV k f a) -> Maybe (TBF k f a)
findAttr l v = kvLookup ( Inline  l) v <|> findFun l v


addAttr :: Ord k => TB k v -> KV k v -> KV k v
addAttr v (KV i) = KV $ Map.insert (relSort $ keyattr v) (valueattr v) i

findFun :: (Show k, Ord k, Show a) => k -> (FKV k f a) -> Maybe (TBF k f a)
findFun l v =
  fmap (recoverAttr .first originalRel ).
  L.find (((Inline  l) ==) . mapFunctions  . originalRel . fst) $
  Map.toList $ _kvvalues $ (v)
  where
    mapFunctions (RelFun i _ _) = i
    mapFunctions j = j

findFKAttr :: (Show k, Ord k, Show a) => [k] -> (TBData k a) -> Maybe (TB k a)
findFKAttr l v =
  case L.find (\(k, v) -> not $ L.null $ L.intersect l k) $
       Map.toList $ Map.mapKeys (fmap _relOrigin. relUnComp . originalRel) $ _kvvalues $ (v) of
    Just (k,ARel a _ ) ->   L.find (\i -> not $ Set.null $ Set.intersection (S.fromList l) $ relOutputSet $ keyattr $ i ) (unkvlist a)
    Just (k, i) -> error (show l)
    Nothing -> Nothing


relAppend  (RelAccess i j ) v  = RelAccess i (relAppend j v )
relAppend  i j = RelAccess i j  

recLookup' :: Ord k => Rel k -> TBData k v -> [FTB v]
recLookup' p@(Inline l) v = maybeToList $ _tbattr <$> kvLookup p v
recLookup' n@(RelAccess l nt) v =
  join $ fmap join . traverse (recLookup' nt) <$> maybeToList (refLookup l v)
recLookup' p@(RelComposite i) v = join $ maybeToList $ nonEmpty (join $ traverse (flip recLookup' v ) i)  <|> fmap (explodeAttr) (kvLookup p v)
  where explodeAttr (Attr i v ) = [v]
        explodeAttr (FKT i _ _ ) = join $ explodeAttr <$> unkvlist i 
recLookup' p@(Rel i _ _) v = maybeToList $ _tbattr <$> kvLookup i  v 

recLookupKV :: (Traversable f, Show k ,Ord k,Monad f) => Rel k -> FKV k f v -> Maybe (f (TBF k f v))
-- recLookupKV i j | traceShow (i,kvkeys j )  False = undefined
recLookupKV n@(RelAccess l nt) v =
  join $ fmap join . traverse (recLookupKV nt) <$> refLookup  l v
recLookupKV p@(RelComposite i) v = return <$> kvLookup p  v 
recLookupKV p@(Rel _ _ _) v = return <$> kvLookup p  v 
recLookupKV p@(Inline l) v = return <$> kvLookup p v


recLookup :: Ord k => Rel k -> TBData k v -> Maybe (FTB v)
recLookup p@(Inline l) v = _tbattr <$> kvLookup p v
recLookup n@(RelAccess l nt) v =
  join $ fmap join . traverse (recLookup nt) <$> refLookup l v
recLookup p@(RelComposite i) v = _tbattr <$> kvLookup p  v 
recLookup p@(Rel i _ _) v = _tbattr <$> kvLookup i  v 

kvLookup :: Ord k => Rel k -> FKV k f a -> Maybe (TBF k f a)
kvLookup rel (KV i) = recoverAttr . (rel,) <$> Map.lookup (relSort $ rel) i


refLookup :: Ord k => Rel k -> FKV k f a -> Maybe (f (FKV k f a))
refLookup rel i = _fkttable <$> kvLookup rel i

attrLookup :: Ord k => Rel k -> KV k a -> Maybe (FTB a)
attrLookup rel i = _tbattr <$> kvLookup rel i

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

-- TODO: Remove special case for atoms
unArray i@(TB1 _) = NonS.fromList $ [i]
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
    (\i -> fmap (RelAccess (relComp $ Inline <$> i) ))
    (Inline <$> last vec)
    (init vec)
  where
    vec = T.splitOn "," <$> T.splitOn ":" field

onTable = NInline 

renderRel :: Show k => Rel k -> String
renderRel (Inline k) = show k
renderRel (NInline t k) = show t <> "." <> show k
renderRel (Output k) = renderRel k ++ "="
renderRel (RelFun k expr rel) = renderRel k ++ " = " ++ renderFun expr rel
  where
    renderFun :: Show k => Expr -> [Rel k] -> String
    renderFun e ac = go e
      where
        go :: Expr -> String
        go (Function i e) =
          T.unpack i ++ "(" ++ L.intercalate "," (fmap go e) ++ ")"
        go (Value i) = renderRel $ justError "no value" $ ac `atMay` i
renderRel (RelComposite l ) =  "(" <> L.intercalate ","  (renderRel <$> l) <> ")"
renderRel (RelAccess i l) =
  renderRel i ++ ". " ++ renderRel l
renderRel (Rel i Equals k)
  | show i == show k = "[" <> renderRel i <> "]"
renderRel (Rel i op k) = "[" <> renderRel i <> " " <> renderBinary op <> " "<> renderRel k <> "]"


makeLenses ''FKV
makeLenses ''TBF
makeLenses ''FAValue

deriving instance (Show a , Show k) => Show (KV k a) 
deriving instance (Show a , Show k) => Show (TB k a) 
deriving instance (Show a , Show k) => Show (TBRef k a) 
deriving instance (Show a , Show k) => Show (AValue k a) 

deriving instance (Ord a , Ord k) => Ord (KV k a) 
deriving instance (Ord a , Ord k) => Ord (TB k a) 
deriving instance (Ord a , Ord k) => Ord (TBRef k a) 
deriving instance (Ord a , Ord k) => Ord (AValue k a) 


deriving instance (Eq a , Eq k) => Eq (KV k a) 
deriving instance (Eq a , Eq k) => Eq (TB k a) 
deriving instance (Eq a , Eq k) => Eq (TBRef k a) 
deriving instance (Eq a , Eq k) => Eq (AValue k a) 


recurseOverAttr ::
     Ord k
  => [(Rel k)]
  -> AValue k a
  -> KV k a -> KV k a
recurseOverAttr (k:[]) attr = KV . Map.insert (relSort k) attr . _kvvalues
recurseOverAttr (k:xs) attr =
  KV . Map.alter
    (fmap (Le.over aref (fmap (recurseOverAttr xs attr ))))
    (relSort (k)) . _kvvalues

recOverKV ::
     Ord k => [(Rel k )]
  -> [[(Rel k)]]
  -> KV k b
  -> KV k b
recOverKV tag tar (KV m) = KV $ foldr go m tar
  where
    go (k:[]) =
      Map.alter
        (fmap (Le.over aref (fmap (recurseOverAttr tag recv )))) (relSort $ k)
      where
        recv = gt tag m
    go (k:xs) =
      Map.alter
        (fmap (Le.over aref (fmap (KV . go xs . _kvvalues))))
        (relSort $ k)
    gt (k:[]) = justError "no key" . Map.lookup (relSort $ k)
    gt (k:xs) =
      gt xs .
      _kvvalues .
        L.head . F.toList . _aref . justError "no key" . Map.lookup (relSort $ k)

replaceRecRel ::
     Ord k => KV k b
  -> [MutRec [(Rel k)]]
  -> KV k b
replaceRecRel i = foldr (\(MutRec l) v -> foldr (\a -> recOverKV a l) v l) i

kvSingleton  :: Ord k => TB k a -> KV k a
kvSingleton i = KV $ Map.singleton (relSort $ keyattr i ) (valueattr i)

kvSize :: Ord k => FKV k f a ->  Int
kvSize (KV i) = Map.size i

kvNonEmpty :: Ord k => KV k a ->  Maybe (KV k a)
kvNonEmpty i = if kvNull i then Nothing else Just i

kvNull :: Ord k => FKV k f a ->  Bool
kvNull (KV i) = Map.null i

kvFind :: Ord k =>  (Rel k -> Bool) -> FKV k f a ->  Maybe (TBF k f a)
kvFind pred (KV item) = fmap (recoverAttr .first originalRel).  safeHead . Map.toList $ Map.filterWithKey (\k _ -> pred (originalRel k) ) item

kvFilter :: Ord k =>  (Rel k -> Bool) -> FKV k f a ->  FKV k f a
kvFilter pred = kvFilterWith (\i _ -> pred i)

kvFilterWith :: Ord k =>  (Rel k -> TBF k f a -> Bool) -> FKV k f a ->  FKV k f a
kvFilterWith pred (KV item) = KV $ Map.filterWithKey (\i -> pred (originalRel i) . recoverAttr . (originalRel i,) ) item

tbUn :: Ord k => Set (Rel k) -> KV k a -> KV k a
tbUn un = kvFilter pred where
    pred k = S.isSubsetOf (relOutputSet k) (S.unions (relOutputSet <$> S.toList un))

getAtt :: Ord a1 => Set a1 -> KV a1 a2 -> [TB a1 a2]
getAtt i k  = filter ((`S.isSubsetOf` i) . relOutputSet  . keyattr ) . unkvlist  $ k


alterAtF
  :: (Ord k, Applicative f) =>
     Rel k
     -> (FTB (KV k a) -> f (FTB (KV k a))) -> KV k a -> f (KV k a)
alterAtF k fun i= alterKV k (traverse (Le.traverseOf ifkttable fun))  i

alterKV
  :: (Functor f, Ord k) =>
     Rel k
     -> (Maybe (TB k a) -> f (Maybe (TB k a))) -> KV k a -> f (KV k a)
alterKV k fun (KV i ) = KV <$> (Map.alterF (\ i -> fmap (fmap valueattr) $ fun (recoverAttr .(k,) <$> i)) (relSort k) i)

