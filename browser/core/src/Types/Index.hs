{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies#-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE GeneralizedNewtypeDeriving#-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Types.Index
  (Range(..), Positive(..),Affine (..),Predicate(..),DiffShowable(..),TBIndex(..) , toList ,lookup ,fromList ,fromList',filter ,filter'
  ,getIndex ,getBounds,getUnique,notOptional,notOptionalM,tbpred,tbpredM
  ,unFin
  ,Node(..)
  ,indexParam
  ,keys
  ,queryCheck
  ,PathIndex(..)
  ,AttributePath(..)
  ,mapAttributePath
  ,indexPred
  ,checkPred
  ,checkPredIdx
  ,checkPredId
  ,cinterval
  ,PathTID(..)
  ,splitIndex
  ,splitPred
  ,splitIndexPKB
  ,splitIndexPK
  ,module G ) where

import qualified Data.Vector as V
import Data.Maybe
import Unsafe.Coerce
import qualified Data.Sequence as S
import Safe
import Control.Monad
import Control.Arrow (first)
import Data.Functor.Identity
import Step.Host
import Control.Applicative
import qualified NonEmpty as Non
import Data.Either
import Data.GiST.BTree hiding(Equals,Contains)
import Data.GiST.GiST as G
import Data.Tuple (swap)
import Data.Binary
import Control.DeepSeq
import Data.Semigroup
import GHC.Generics
import Types
import Utils
import Data.Time
import Data.Ord
import Data.Foldable (foldl')
import Data.Char
import qualified Data.Foldable as F
import Data.Functor.Apply
import Prelude hiding(head,lookup,filter)
import qualified Data.Interval as Interval
import Data.Interval (Interval,interval,lowerBound',upperBound',lowerBound,upperBound)
import qualified Data.ExtendedReal as ER
import qualified Data.Text as T
import GHC.Stack
import Debug.Trace
import qualified Data.List as L
import qualified Data.Set as Set
import qualified Data.List as L
import Data.Map (Map)
import qualified Data.Map.Strict as M



--- Row Level Predicate
instance (Binary a)  => Binary (TBIndex a)
instance (NFData a)  => NFData (TBIndex a)

cinterval ::Ord a=> a -> a -> Interval a
cinterval i j = ER.Finite i Interval.<=..<= ER.Finite j


getUnique :: Ord k => [k] -> TBData k a -> TBIndex  a
getUnique ks v = Idex .  fmap snd . L.sortBy (comparing ((`L.elemIndex` ks).fst)) .  getUn (Set.fromList ks) $ v

getIndex :: Ord k => KVMetadata k -> TBData k a -> TBIndex  a
getIndex m v = Idex .  fmap snd . L.sortBy (comparing ((`L.elemIndex` (_kvpk m)).fst)) .  getPKL m $ v

getBounds :: (Ord k, Ord a) => KVMetadata k -> [TBData k a] -> Maybe [Interval (FTB a)]
getBounds m [] = Nothing
getBounds m ls = Just $ zipWith  (\i j -> (ER.Finite i,True) `interval` (ER.Finite j,False)) l u
  where Idex l = getIndex m (head ls)
        Idex u = getIndex m (last ls)

notOptionalM :: TBIndex  a -> Maybe (TBIndex a)
notOptionalM (Idex m) = fmap Idex   . join . fmap nonEmpty . traverse unSOptional'  $ m


notOptional :: Show a => TBIndex  a -> TBIndex  a
notOptional m = justError ("cant be empty " <> show m) . notOptionalM $ m

tbpredM :: Ord k => KVMetadata k -> TBData k a -> Maybe (TBIndex a)
tbpredM m = notOptionalM . getIndex m

tbpred :: (Show a, Ord k) => KVMetadata k -> TBData k a -> TBIndex a
tbpred m = notOptional . getIndex m

instance (Show a,Affine a) => Affine (ER.Extended a ) where
  type Tangent (ER.Extended a) = ER.Extended (Tangent  a)
  subtraction (ER.Finite i) (ER.Finite j) = ER.Finite $ subtraction i j
  subtraction (ER.NegInf ) i = ER.NegInf
  subtraction (ER.PosInf ) i = ER.PosInf
  subtraction i  (ER.PosInf ) = ER.NegInf
  subtraction i  (ER.NegInf) = ER.PosInf
  subtraction i j = errorWithStackTrace (show (i,j))

notNeg (DSPosition l)
  | otherwise = DSPosition l
notNeg (DSText l)
  | L.null dp || headS dp < 0 = def
  | otherwise = DSText l
  where dp =  dropWhile (==0) l
        def = DSText []
notNeg (DSDouble l)
  | l < 0 = DSDouble 0
  | otherwise = DSDouble l
notNeg (DSInt l)
  | l < 0 = DSInt 0
  | otherwise =  DSInt l
notNeg (DSDays l )
  | l < 0 = DSDays 0
  | otherwise =  DSDays l
notNeg (DSDiffTime l )
  | l < 0 = DSDiffTime 0
  | otherwise =  DSDiffTime l
notNeg i= errorWithStackTrace (show i)


instance Semigroup a => Semigroup (ER.Extended a ) where
  (ER.Finite i ) <>  (ER.Finite j) = ER.Finite (i <> j)
  ER.NegInf  <>  j = ER.NegInf
  j <> ER.NegInf  = ER.NegInf
  i <>  ER.PosInf = ER.PosInf
  ER.PosInf <> _= ER.PosInf
  {-# INLINE (<>) #-}

instance Semigroup DiffPosition where
  DiffPosition2D (x,y) <> DiffPosition2D (i,j)  = DiffPosition2D (x + i , y + j)
  DiffPosition3D (x,y,z) <> DiffPosition3D (i,j,k)  = DiffPosition3D (x + i , y + j,z+ k)
  a <> b = errorWithStackTrace (show (a,b))

instance Semigroup DiffShowable where
  (<>) = appendDShowable
    where
      appendDShowable :: DiffShowable -> DiffShowable -> DiffShowable
      appendDShowable (DSInt l ) (DSInt j) =  DSInt $ l + j
      appendDShowable (DSText l ) (DSText j) =  DSText $ zipWith (+) l j <> L.drop (L.length j) l <> L.drop (L.length l ) j
      appendDShowable (DSDouble l ) (DSDouble j) =  DSDouble$ l + j
      appendDShowable (DSDays l ) (DSDays j) =  DSDays $ l + j
      appendDShowable (DSDiffTime l ) (DSDiffTime j) =  DSDiffTime $ l + j
      appendDShowable (DSPosition x ) (DSPosition y ) =  DSPosition $ x <> y
      appendDShowable a b = errorWithStackTrace ("append " <> show (a,b))
      {-# INLINE appendDShowable #-}
  {-# INLINE (<>) #-}


headS [] = errorWithStackTrace "no head"
headS i = head i

class Affine f where
  type Tangent f
  subtraction :: f -> f -> Tangent f

class Positive f where
  notneg :: f -> f


instance Affine String where
  type Tangent String = [Int]
  subtraction i j = diffStr i j
    where
      diffStr :: String -> String -> [Int]
      diffStr (a:as) (b:bs) = (ord b - ord a) : diffStr as bs
      diffStr bs [] = ord <$> bs
      diffStr [] bs = ord <$> bs
      diffStr [] [] = []
  {-# INLINE subtraction #-}

splitIndexPK :: Eq k => BoolCollection (Access k ,AccessOp Showable) -> [k] -> Maybe (BoolCollection (Access k , AccessOp Showable))
splitIndexPK (OrColl l ) pk  = if F.all (isNothing .snd) al then Nothing else Just $ OrColl $ fmap (\(i,j) -> fromMaybe i j) al
    where
      al = (\l -> (l,splitIndexPK  l pk ) )<$> l
splitIndexPK (AndColl l ) pk  = fmap AndColl $ nonEmpty $ catMaybes $ (\i -> splitIndexPK  i pk ) <$> l
splitIndexPK (PrimColl (p@(IProd _ i),op) ) pk  = if elem i  pk  then Just (PrimColl (p,op)) else Nothing
-- splitIndexPK (PrimColl (p@(IProd _ l),op) ) pk  = Nothing --errorWithStackTrace (show (l,op,pk))
splitIndexPK i  pk  = Nothing -- errorWithStackTrace (show (i,pk))

splitIndexPKB :: Eq k => BoolCollection (Access k ,AccessOp Showable) -> [k] -> Maybe (BoolCollection (Access k , AccessOp Showable))
splitIndexPKB  (OrColl l ) pk  = if F.all (isNothing .snd) al then Nothing else Just $ OrColl $ fmap (\(i,j) -> fromMaybe i j) al
    where
      al = (\l -> (l,splitIndexPKB  l pk ) )<$> l
splitIndexPKB  (AndColl l ) pk  = fmap AndColl $ nonEmpty $ catMaybes $ (\i -> splitIndexPKB  i pk ) <$> l
splitIndexPKB  (PrimColl (p@(IProd _ i),op) ) pk  = if not (elem i  pk)  then Just (PrimColl (p,op)) else Nothing
splitIndexPKB  i  pk  = Just i



instance Monoid (TBIndex a) where
  mempty  = Idex []

splitIndex :: (Eq k ,Show k) => BoolCollection (Access k ,AccessOp Showable) -> [k] -> TBIndex Showable -> Maybe (BoolCollection (Access k, AccessOp Showable))
splitIndex (AndColl l ) pk f = if F.all (isNothing .snd) al then Nothing else Just $ AndColl $ fmap (\(i,j) -> fromMaybe i j) al
    where
      al = (\l -> (l,splitIndex  l pk f) )<$> l
splitIndex (OrColl l ) pk f = fmap OrColl $ nonEmpty $ catMaybes $ (\i -> splitIndex  i pk f) <$> l
splitIndex (PrimColl (p@(IProd _ i),op) ) pk (Idex v ) = maybe (Just (PrimColl (p,op))) (splitPred (PrimColl (p,op))) ((v !!) <$>  (L.elemIndex i pk ))
splitIndex i  k j = Just i

splitPred :: (Eq k ,Show k) => BoolCollection (Access k,AccessOp Showable) ->  FTB Showable -> Maybe (BoolCollection (Access k,AccessOp Showable)  )
splitPred (PrimColl (prod ,Left (a@(TB1 _ ) ,op))) (ArrayTB1 b ) = if elem a  b then Nothing else Just (PrimColl (prod , Left (a,op)))
splitPred (PrimColl (prod ,Left (a@(TB1 _ ) ,op))) (IntervalTB1 b ) = if Interval.member a  b then Nothing else Just (PrimColl (prod , Left (a,op)))
splitPred (PrimColl (prod ,Left (a@(TB1 _ ) ,op))) b@(TB1  _ ) = if a  == b then Nothing else Just (PrimColl (prod , Left (a,op)))
splitPred (PrimColl (prod ,Left ((IntervalTB1 a ) ,op))) i@(TB1  _ ) = (\i -> if F.length i == 1 then head . F.toList $ i else OrColl (F.toList i) ). fmap (PrimColl. (prod,). Left . (,op).IntervalTB1) <$> Interval.split i a
splitPred (PrimColl (prod ,Left (i@(IntervalTB1 u) ,op))) (IntervalTB1 a ) =(\i -> if F.length i == 1 then head . F.toList $ i else OrColl (F.toList i) ). fmap (PrimColl .(prod,). Left . (,op).IntervalTB1) <$>  Interval.difference u a
splitPred (PrimColl (prod ,Left ((ArrayTB1 l ) ,Flip (AnyOp op)))) a  = OrColl <$> nonEmpty (catMaybes $ fmap (\i -> splitPred (PrimColl (prod,Left (i,op))) a) $ F.toList l)
splitPred p@(PrimColl (prod,Right i)) _ =  Just p
splitPred a e = errorWithStackTrace (show (a,e))

instance Affine Position where
  type Tangent Position = DiffPosition
  subtraction ((Position (x,y,z)) ) ((Position (a,b,c))) = DiffPosition3D (a-x,b-y,c-z)
  subtraction ((Position2D (x,y)) ) ((Position2D (a,b))) = DiffPosition2D (a-x,b-y)

instance Affine Int where
  type Tangent Int = Int
  subtraction = (-)


instance Affine Showable where
  type Tangent Showable = DiffShowable
  subtraction = diffS
    where
      diffS :: Showable -> Showable -> DiffShowable
      diffS (SNumeric t) (SNumeric o) = DSInt $ subtraction o t
      diffS (SText t) (SText o) = DSText $ subtraction (T.unpack o) (T.unpack t)
      diffS (SDouble t) (SDouble o) = DSDouble $ o -t
      diffS (STime (STimestamp i )) (STime (STimestamp j)) = DSDiffTime (diffUTCTime j i)
      diffS (STime (SDate i )) (STime (SDate j)) = DSDays (diffDays j i)
      diffS (SGeo(SPosition s )) (SGeo(SPosition b)) = DSPosition $ subtraction s b
      diffS a b  = errorWithStackTrace (show (a,b))
      {-# INLINE diffS #-}
  {-# INLINE subtraction #-}

instance Positive DiffShowable where
  notneg = notNeg

transEither
  :: (Either (Node (FTB b)) (FTB b) -> Either (Node (FTB b)) (FTB b) -> Bool)
  -> Either (Node (TBIndex b)) (TBIndex b)
  -> Either (Node (TBIndex b)) (TBIndex b)
  -> Bool
transEither f  i j  =
    case (i,j) of
        (Right (Idex i) ,Right (Idex j)) -> co (Right <$> i) (Right <$> j)
        (Left (TBIndexNode i) ,Left (TBIndexNode j)) -> co (Left <$> i) (Left <$> j)
        (Right (Idex i) ,Left (TBIndexNode j)) -> co  (Right <$> i) (Left<$> j)
        (Left (TBIndexNode i) ,Right (Idex j)) -> co (Left <$> i) (Right <$> j)
    where co i j =  F.foldl' (&&) True (zipWith f i j)
{-# INLINE transEither #-}


instance Predicates (FTB v) => Predicates (TBIndex v ) where
  type (Penalty (TBIndex v)) = [Penalty (FTB v)]
  type Query (TBIndex v) = (TBPredicate Int v)
  data Node (TBIndex v) = TBIndexNode [Node (FTB v)] deriving (Eq,Ord,Show)
  consistent = transEither consistent
  {-# INLINE consistent #-}

  -- This limit to 100 the number of index fields to avoid infinite lists
  origin = TBIndexNode (replicate 100 G.origin)
  match (WherePredicate a)  (Right (Idex v)) = go a
    where
      -- Index the field and if not found return true to row filtering pass
      go (AndColl l) = F.all go l
      go (OrColl l ) = F.any go  l
      go (PrimColl (IProd _ i,op)) = maybe True (match op .Right)  (v `atMay` i)
  match (WherePredicate a)  (Left (TBIndexNode v)) = go a
    where
      -- Index the field and if not found return true to row filtering pass
      go (AndColl l) = F.all go l
      go (OrColl l ) = F.any go  l
      go (PrimColl (IProd _ i,op)) = maybe True (match op . node )  (v `atMay` i)
      node :: Node (FTB v) -> Either (Node (FTB v )) (FTB v)
      node i = Left i


  bound (Idex i) =  TBIndexNode $ bound <$> i
  merge (TBIndexNode i) (TBIndexNode j) = TBIndexNode $ zipWith merge i j
  penalty (TBIndexNode i ) (TBIndexNode j) = zipWith penalty i j
  {-# INLINE penalty #-}

projIdex (Idex v) = F.toList v

instance (Predicates (TBIndex  a )  ) => Monoid (G.GiST (TBIndex  a)  b) where
  mempty = G.empty
  mappend i j
    | G.size i < G.size j = ins  j (getEntries i )
    | otherwise  = ins  i (getEntries j )
    where ins = foldl' (\j i -> G.insertL i indexParam j)




indexParam :: (Int,Int)
indexParam = (10,20)

-- Attr List Predicate


checkPredId v (WherePredicate l) = checkPredIdx  v l
checkPredIdx v (AndColl i ) = fmap concat $ allMaybes $ fmap (checkPredIdx v)i
checkPredIdx v (OrColl i ) = fmap concat $ nonEmpty $ catMaybes $   fmap (checkPredIdx v) i
checkPredIdx v (PrimColl i) = fmap pure (indexPredIx i v)

checkPred v (WherePredicate l) = checkPred' v l
checkPred' v (AndColl i ) = F.all  (checkPred' v)i
checkPred' v (OrColl i ) = F.any (checkPred' v) i
checkPred' v (PrimColl i) = indexPred i v

type ShowableConstr  a = (Fractional a ,Range a,ConstantGen (FTB a ),Affine a,Positive (Tangent a),Semigroup (Tangent a),Ord (Tangent a),Ord a )


data PathIndex  a b
  = ManyPath (Non.NonEmpty (PathIndex a b))
  | NestedPath a (PathIndex a b)
  | TipPath b
  deriving(Eq,Ord,Show,Functor)

mapAttributePath :: (a -> b) -> AttributePath a i -> AttributePath b i
mapAttributePath f (PathAttr k l) = PathAttr (f k ) l
mapAttributePath f (PathInline k l ) = PathInline (f k) (fmap (mapAttributePath f ) l)
mapAttributePath f (PathForeign k l ) = PathForeign (fmap f <$> k) (fmap (mapAttributePath f ) l)

data AttributePath  k b
  = PathAttr k (PathIndex PathTID b)
  | PathInline k (PathIndex PathTID  (AttributePath k b))
  | PathForeign [Rel k ] (PathIndex PathTID (AttributePath k b))
  deriving(Eq,Ord,Show,Functor)

data PathTID
  = PIdIdx Int
  | PIdOpt
  | PIdInter Bool
  | PIdAtom
  deriving (Eq,Ord,Show)



indexPredIx :: (Show k ,ShowableConstr a , Show a,Ord k) => (Access k ,AccessOp a) -> TBData k a-> Maybe (AttributePath k ())
-- indexPredIx (Many i,eq) a= traverse (\i -> indexPredIx (i,eq) a) i
indexPredIx (n@(Nested [(IProd _ key)] (Many[One nt]) ) ,eq) r
  = case  indexField n r of
    Nothing -> Nothing
    Just i ->  fmap (PathInline key) $ recPred $ indexPredIx (nt , eq ) <$> _fkttable  i
  where
    recPred (TB1 i ) = TipPath <$> i
    recPred (LeftTB1 i) = fmap (NestedPath PIdOpt )$  join $ traverse recPred i
    recPred (ArrayTB1 i) = fmap ManyPath  $ Non.nonEmpty $ catMaybes $ F.toList $ Non.imap (\ix i -> fmap (NestedPath (PIdIdx ix )) $ recPred i ) i
    recPred i = errorWithStackTrace (show i)
indexPredIx (a@(IProd _ key),eq) r =
  case indexField a r of
    Nothing ->  Nothing
    Just (Attr _ rv) ->
      fmap (PathAttr key) $ recPred eq rv
  where
    recPred eq (TB1 i ) = if match eq (Right (TB1 i)) then  Just (TipPath ()) else Nothing
    recPred eq (LeftTB1 i) = fmap (NestedPath PIdOpt )$  join $ traverse (recPred eq )i
    recPred eq (ArrayTB1 i) = fmap ManyPath . Non.nonEmpty $ catMaybes $ F.toList $ Non.imap (\ix i -> fmap (NestedPath (PIdIdx ix )) $ recPred eq i  ) i
indexPredIx i v= errorWithStackTrace (show (i,v))



indexPred :: (Show k ,ShowableConstr a , Show a,Ord k) => (Access k ,AccessOp a) -> TBData k a-> Bool
-- indexPred (Many i,eq) a= all (\i -> indexPred (i,eq) a) i
indexPred (n@(Nested k (Many[One nt]) ) ,eq) r
  = case  indexField n r of
    Nothing ->False
    Just i  ->recPred $ indexPred (nt , eq) <$> _fkttable  i
  where
    recPred (TB1 i ) = i
    recPred (LeftTB1 i) = maybe False recPred i
    recPred (ArrayTB1 i) = any recPred i
    recPred i = errorWithStackTrace (show i)
indexPred (a@(IProd _ _),eq) r =
  case indexField a r of
    Nothing -> False
    Just (Fun _ _ rv) ->
      case eq of
        i -> match eq (Right rv)
    Just (Attr _ rv) ->
      case eq of
        i -> match eq (Right rv)
    Just (IT _ rv) ->
      case eq of
        Right (Not IsNull ) -> isJust $ unSOptional' rv
        Right IsNull -> isNothing $ unSOptional' rv
        i -> errorWithStackTrace (show i)
    Just (FKT _ _ rv) ->
      case eq of
        Right (Not IsNull)  -> isJust $ unSOptional' rv
        Right IsNull -> isNothing $ unSOptional' rv
        i -> errorWithStackTrace (show i)
indexPred i v= errorWithStackTrace (show (i,v))



queryCheck :: (Show k,Ord k) => (WherePredicateK k ,[k])-> G.GiST (TBIndex Showable) (TBData k Showable) -> G.GiST (TBIndex  Showable) (TBData k Showable)
queryCheck pred@(WherePredicate b ,pk) = t1
  where t1 = fromList' . maybe id (\pred -> L.filter (flip checkPred (WherePredicate pred) . leafValue )) notPK . maybe G.getEntries (\p -> G.queryL (mapPredicate (\i -> justError ("no predicate " ++ show (i,pk)) $ L.elemIndex i pk)  $ WherePredicate p)) (splitIndexPK b pk)
        notPK = splitIndexPKB b pk


-- Atomic Predicate


data DiffPosition
  = DiffPosition3D (Double,Double,Double)
  | DiffPosition2D (Double,Double)
  deriving(Eq,Ord ,Show)

data DiffShowable
  = DSText [Int]
  | DSDouble Double
  | DSPosition DiffPosition
  | DSInt Int
  | DSDiffTime NominalDiffTime
  | DSDays Integer
  deriving(Eq,Ord,Show)


class Range v where
  pureR :: v -> Interval  v
  appendR :: v -> v -> Interval v


instance (Ord v ,Range v) => Range (FTB v ) where
  pureR (TB1 i)  =  fmap TB1 $ pureR i
  pureR (ArrayTB1 (is Non.:| xs)) = F.foldl' appendRI  (pureR is) (fmap pureR xs)
  pureR (IntervalTB1 is) =  is
  pureR (LeftTB1 is) =  maybe Interval.empty  pureR is
  {-# INLINE pureR #-}
  appendR (TB1 i ) (TB1 j) = fmap TB1 $ appendR i j
  {-# INLINE appendR#-}


instance Range Showable where
  pureR  i = i `cinterval` i
  {-# INLINE pureR #-}
  appendR !(SGeo (SPosition i)) !(SGeo (SPosition j)) =  fmap (SGeo . SPosition )  $ mergeP i j
    where
      mergeP !(Position2D (i,j)) !(Position2D (l,m))=  Position2D (min i l , min j m) `cinterval` Position2D (max i l , max j m)
      mergeP (Position(i,j,k)) (Position (l,m,n))=  Position (min i l , min j m,min k n) `cinterval` Position (max i l , max j m,max k n)
      {-# INLINE mergeP #-}
  appendR i j = min i j  `cinterval` max i j
  {-# INLINE appendR #-}


appendRI :: (Ord v ,Range v) => Interval v -> Interval v -> Interval v
appendRI ! i  ! j  = maybe (min (lowerBound' j) (lowerBound' i )) lowerBound' (liftA2 appendR (unFin $ fst $ lowerBound' i ) (unFin $ fst $ lowerBound' j)) `interval`  (maybe (max (upperBound' i) (upperBound' j))upperBound' (liftA2 appendR (unFin $ fst $ upperBound' i ) (unFin $ fst $ upperBound' j)) )
{-# INLINE appendRI #-}

instance (Range v,ConstantGen (FTB v) , Positive (Tangent v), Semigroup (Tangent v),Ord (Tangent v),Ord v,Show v , Affine v ) => Predicates (FTB v) where
  data Node (FTB v) = FTBNode (Interval.Interval v) deriving (Eq,Ord,Show)
  type Penalty (FTB v) = ER.Extended (Tangent v)
  type Query (FTB v) = AccessOp v
  consistent (Left (FTBNode i) ) (Left (FTBNode j)) = not . Interval.null $  j `Interval.intersection` i
  consistent (Right i ) (Left (FTBNode j)) = consrl i j
      where
        consrl (TB1 j)  i  = j `Interval.member` i
        consrl (IntervalTB1 i) j = not $ Interval.null $  j `Interval.intersection` (fmap unTB1 i)
        consrl (LeftTB1 i) j = fromMaybe True $ (flip consrl j ) <$>  i
        consrl (ArrayTB1 i)  j  = F.any (flip consrl j) i
  consistent (Left i ) (Right j) = consistent (Right j) (Left i)
  consistent (Right i) (Right j) = cons i j
      where
        cons (TB1 i)  (TB1 j)  = i == j
        cons (IntervalTB1 i) (IntervalTB1 j) = not $ Interval.null $  j `Interval.intersection` i
        cons j@(TB1 _)  (IntervalTB1 i)  = j `Interval.member` i
        cons (IntervalTB1 i) j@(TB1 _)  = j `Interval.member` i
        cons (ArrayTB1 i)  (ArrayTB1 j)   = not $ Set.null $ Set.intersection (Set.fromList (F.toList i) ) (Set.fromList  (F.toList j))
        cons (ArrayTB1 i)  j  = F.any (flip cons j) i
        cons i  (ArrayTB1 j ) = F.any (cons i) j
        cons (LeftTB1 i) (LeftTB1 j ) = fromMaybe True $ liftA2 cons j  i
        cons (LeftTB1 i) j = fromMaybe True $ (flip cons j ) <$>  i
        cons i (LeftTB1 j) = fromMaybe True $(cons i ) <$>  j
        cons i j  = errorWithStackTrace (show ("rr",i,j))
  match i (Left (FTBNode j)) = mal i  j
    where
      mal (Left (v))  j  = ma  v  j
        where
          ma ((TB1 i) ,op)  j  = i `Interval.member` j
          ma (LeftTB1 j ,v)   i   = fromMaybe False ((\a -> ma (a,v) i) <$> j)
          ma (ArrayTB1 i,Flip (AnyOp o))  j  = F.any (\i -> ma (i,o)  j ) i
          ma (IntervalTB1 j ,Flip Contains) (i)  = fmap unTB1 j `Interval.isSubsetOf` i
          ma (IntervalTB1 j ,IntersectOp) (i)  = not $ Interval.null $ fmap unTB1 j `Interval.intersection` i
          ma (IntervalTB1 j ,_) (i)  = not $ Interval.null $ fmap unTB1 j `Interval.intersection` i
          ma (j ,IntersectOp ) (i)  = not $ Interval.null $ unFTB (bound j) `Interval.intersection` i
          ma (j ,Flip o ) (i)  = ma (j,o) i
          ma  i j =errorWithStackTrace (show (i,j))
          unFTB (FTBNode i ) = i
      mal (Right v) j = ma v j
        where
          ma (Not i) j = not $ ma i   j
          ma IsNull j = False
          ma (BinaryConstant op e )  v  = mal (Left (generate e,op))  v
          ma (Range b pred)  j   = match  (Right  pred) $ Right $ LeftTB1 $ fmap TB1 $ unFin $ if b then upperBound j else lowerBound j
          ma i j =errorWithStackTrace (show (i,j))
      mal i j = errorWithStackTrace $ show (i,j)
  match i (Right j) = mar i j
    where
      mar (Left v)  j  = ma  v  j
        where
          -- ma v a j | traceShow (v,a,j) False = undefined
          ma  (v,Flip (Flip op)) j  = ma (v,op)   j
          ma  v (LeftTB1 j) = fromMaybe False (ma v  <$> j)
          ma  (LeftTB1 j ,v) i = fromMaybe False ((\a -> ma (a,v) i) <$> j)
          ma  (TB1 i, GreaterThan True )  (TB1 j)   = i >= j
          ma  (TB1 i, (Flip (GreaterThan True) ))  (TB1 j)   = i <= j
          ma  (TB1 i, GreaterThan False )  (TB1 j)   = i < j
          ma  (TB1 i, (Flip (GreaterThan False) ))  (TB1 j)   = i > j
          ma  (TB1 i,Flip (LowerThan True ))   (TB1 j)   = i >= j
          ma  (TB1 i,(LowerThan True ))   (TB1 j)   = i <= j
          ma  (TB1 i,_)   (TB1 j)   = i == j
          ma  ((ArrayTB1 i) ,Flip Contains )   ((ArrayTB1 j)  ) = Set.fromList (F.toList i) `Set.isSubsetOf` Set.fromList  (F.toList j)
          ma  ((ArrayTB1 j),Contains )   ((ArrayTB1 i)  ) = Set.fromList (F.toList i) `Set.isSubsetOf` Set.fromList  (F.toList j)
          ma (j,AnyOp o )  (ArrayTB1 i) = F.any (ma (j,o)  )  i
          ma (j,Flip (AnyOp o) )  (ArrayTB1 i) = F.any (ma (j,o)  )  i
          ma (ArrayTB1 i,Flip (AnyOp o))  j  = F.any (\i -> ma (i,o)  j ) i
          ma (i@(TB1 _) ,op)  (IntervalTB1 j)  = i `Interval.member` j
          ma (IntervalTB1 i ,op)  j@(TB1 _)  = j `Interval.member` i
          ma (IntervalTB1 i ,Contains) (IntervalTB1 j)  = j `Interval.isSubsetOf` i
          ma (IntervalTB1 j ,Flip Contains) (IntervalTB1 i)  = j `Interval.isSubsetOf` i
          ma (IntervalTB1 j ,IntersectOp) (IntervalTB1 i)  = not $ Interval.null $ j `Interval.intersection` i
          ma (j ,IntersectOp) (i)  = not $ Interval.null $ unFTB (bound j ) `Interval.intersection` unFTB (bound i)
          ma (j ,Contains) (i)  = not $ Interval.null $ unFTB (bound j ) `Interval.intersection` unFTB (bound i)
          ma (j ,(Flip op)) i = ma (j, op)  i
          ma i  j =  errorWithStackTrace ("no mar left = " <> show (snd i ,fst i,j))
          unFTB (FTBNode i ) = i
      mar (Right i ) j =ma i j
        where
          ma  (Not i) j  = not $ ma i   j
          ma  IsNull  (LeftTB1 j)   = maybe True (ma IsNull) j
          ma  IsNull  j   = False
          ma  (BinaryConstant op e )  v  = mar (Left (generate e,op))  v
          ma  (Range b pred)  (IntervalTB1 j)   = ma  pred $ LeftTB1 $ unFin $ if b then upperBound j else lowerBound j
          ma i  j = errorWithStackTrace ("no mar right =" ++ show (i ,j))
  match x  z = errorWithStackTrace ("no match = " <> show (x,z))

  origin  = FTBNode Interval.empty
  bound i =  FTBNode $ fmap unTB1 $ pureR i
  {-# INLINE bound #-}
  merge (FTBNode i) (FTBNode j) = FTBNode $ appendRI i j
  {-# INLINE merge #-}
  penalty ((FTBNode i))  ((FTBNode  j))
    = (fmap notneg $ subtraction (fst (lowerBound' j  )) (fst $ lowerBound' i))
    <> (fmap notneg $ subtraction (fst $ upperBound' i  ) (fst $ upperBound' j))
  {-# INLINE penalty #-}

-- Higher Level operations
fromList pred = foldl'  acc G.empty
  where
    acc !m v = G.insert (v,pred v ) indexParam m

-- Higher Level operations
fromList' :: Predicates p => [LeafEntry p a ] -> GiST p a
fromList' = foldl'  acc G.empty
  where
    acc !m v = G.insertL v indexParam m

lookup pk  = safeHead . G.search pk

keys :: GiST p a -> [p]
keys = fmap (\(_,_,k)-> k) . getEntries

toList = getData

filter f = foldl' (\m i -> G.insertL i indexParam m) G.empty  . L.filter (f .leafValue) . getEntries
filter' f = foldl' (\m i -> G.insert i indexParam m) G.empty  . L.filter (f .fst )

