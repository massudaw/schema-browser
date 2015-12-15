{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies#-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}

module Types.Index
  (TBIndex(..) ) where

import Types
import Utils
import Data.Time
import Data.Maybe
import Data.Ord
import Data.Char
import qualified Data.Foldable as F
import Data.Functor.Apply
import Prelude hiding(head)
import Data.GiST.GiST as G
import qualified Data.Interval as Interval
import Data.Interval (interval,lowerBound',upperBound')
import qualified Data.ExtendedReal as ER
import Data.Monoid hiding (Product)
import qualified Data.Text as T
import GHC.Stack
import qualified Data.List as L
import qualified Data.Set as Set

import Data.Traversable(traverse)
import Debug.Trace

data TBIndex a
  = Idex (Set.Set Key) a
  deriving(Eq,Show,Ord,Functor)

projUn u v = justError ("cant be optional" <> show (u,getUn u v))  . (traverse (traverse unSOptional')) . getUn u $ v

instance Predicates TBIndex (TBData Key Showable) where
  type (Penalty (TBData Key Showable) ) = Penalty [FTB Showable]
  consistent (Idex i j) (NodeEntry (_,Idex l m  )) = consistent (SPred $ fmap snd $ projUn i  $ j  ) (NodeEntry (undefined,SPred $ fmap snd $ projUn l $ m))
  consistent (Idex i j) (LeafEntry (_,Idex l m  )) = consistent (SPred $ fmap snd $ projUn i  $ j  ) (LeafEntry (undefined,SPred $ fmap snd $ projUn l $ m))
  union l  = Idex i (tblist $ fmap (_tb . uncurry Attr) $  zipWith (,) kf projL)
    where Idex i v = head l
          proj a = projUn i a
          kf = fmap fst (proj v)
          SPred projL = union $ fmap (SPred . fmap snd . proj .(\(Idex _ a) -> a)) l

  penalty i j = penalty (projIdex i ) (projIdex j)
  pickSplit = pickSplitG

projIdex (Idex i v) = SPred $ fmap snd $ projUn i v



instance  Predicates Predicate [FTB Showable] where
  type Penalty [FTB Showable] = [DiffShowable]
  consistent (SPred l ) (NodeEntry (v,SPred i)) =  all id $ zipWith consistent (SPred <$> l) (NodeEntry  . (undefined,) . SPred <$> i)
  consistent (SPred l ) (LeafEntry (v,SPred i)) =  all id $ zipWith consistent (SPred <$> l) (LeafEntry . (undefined,) . SPred <$> i)
  union l = SPred $ fmap (\i -> (\(SPred i) -> i) $ union i )$ L.transpose $ fmap (\(SPred i) -> fmap SPred i ) l
  penalty (SPred p1) (SPred p2) = zipWith penalty (fmap SPred p1 ) (fmap SPred p2)
  pickSplit = pickSplitG

data DiffShowable
  = DSText [Int]
  | DSDouble Double
  | DSInt Int
  | DSDiffTime NominalDiffTime
  | DSDays Integer
  deriving(Eq,Ord,Show)

diffStr [] [] = []
diffStr bs [] = ord <$> bs
diffStr [] bs = ord <$> bs
diffStr (a:as) (b:bs) = (ord b - ord a) : diffStr as bs

diffS (SText t) (SText o) = DSText $ diffStr (T.unpack o) (T.unpack t)
diffS (SDouble t) (SDouble o) = DSDouble $ o -t
diffS (SNumeric t) (SNumeric o) = DSInt $ o -t
diffS (STimestamp i ) (STimestamp j) = DSDiffTime (diffUTCTime (localTimeToUTC utc j) (localTimeToUTC utc  i))
diffS (SDate i ) (SDate j) = DSDays (diffDays j i)
diffS a b  = errorWithStackTrace (show (a,b))


appendDShowable (DSText l ) (DSText j) =  DSText $ zipWith (+) l j <> L.drop (L.length j) l <> L.drop (L.length l ) j
appendDShowable (DSDouble l ) (DSDouble j) =  DSDouble$ l + j
appendDShowable (DSInt l ) (DSInt j) =  DSInt $ l + j
appendDShowable (DSDays l ) (DSDays j) =  DSDays $ l + j
appendDShowable (DSDiffTime l ) (DSDiffTime j) =  DSDiffTime $ l + j
appendDShowable a b = errorWithStackTrace (show (a,b))


instance Predicates Predicate (FTB Showable) where
  type Penalty (FTB Showable) = DiffShowable
  consistent (SPred j@(TB1 _) )  (NodeEntry (_,SPred (IntervalTB1 i) )) = j `Interval.member` i
  consistent (SPred j@(TB1 _) )  (LeafEntry (_,SPred (IntervalTB1 i) )) = j `Interval.member` i
  consistent (SPred (IntervalTB1 i) ) (NodeEntry (_,SPred (IntervalTB1 j)  )) = not $ Interval.null $ i `Interval.intersection` j
  consistent (SPred (IntervalTB1 i) ) (LeafEntry (_,SPred (IntervalTB1 j) )) = j `Interval.isSubsetOf` i
  consistent (SPred (IntervalTB1 i) ) (LeafEntry (_,SPred j@(TB1 _) )) = j `Interval.member` i
  consistent (SPred (ArrayTB1 i) ) (NodeEntry (_,SPred (ArrayTB1 j)  )) = Set.fromList (F.toList i) `Set.isSubsetOf` Set.fromList  (F.toList j)
  consistent (SPred (ArrayTB1 i) ) (LeafEntry (_,SPred (ArrayTB1 j)  )) = Set.fromList (F.toList i) `Set.isSubsetOf` Set.fromList  (F.toList j)
  consistent (SPred (ArrayTB1 i) ) (NodeEntry (_,SPred j  )) = all (\i -> consistent   ( SPred i) (NodeEntry (undefined,SPred j))) i
  consistent (SPred (ArrayTB1 i) ) (LeafEntry (_,SPred j@(TB1 _)  )) = elem  j i
  consistent (SPred i@(TB1 _) ) (LeafEntry (_,SPred (ArrayTB1 j)  )) = elem  i j
  consistent (SPred (LeftTB1 i) ) (LeafEntry (_,SPred j  )) = maybe False (\i -> consistent (SPred i ) (LeafEntry (undefined,SPred j))) i
  consistent (SPred (SerialTB1 i) ) (LeafEntry (_,SPred j  )) = maybe False (\i -> consistent (SPred i ) (LeafEntry (undefined,SPred j))) i
  consistent (SPred j ) (LeafEntry (_,SPred (LeftTB1 i)  )) = maybe False (\i -> consistent (SPred i ) (LeafEntry (undefined,SPred j))) i
  consistent (SPred j ) (LeafEntry (_,SPred (SerialTB1 i)  )) = maybe False (\i -> consistent (SPred i ) (LeafEntry (undefined,SPred j))) i
  consistent (SPred i@(TB1 _ ) ) (NodeEntry (_,SPred (ArrayTB1 j))) = elem  i j
  consistent (SPred (TB1 i) ) (LeafEntry (_,SPred (TB1 j) )) = i == j
  consistent (SPred (TB1 i) ) (NodeEntry (_,SPred (TB1 j) )) = i == j
  consistent i (NodeEntry (_,j))  = errorWithStackTrace (show ("Node",i,j))
  consistent i (LeafEntry (_,j))  = errorWithStackTrace (show ("Leaf",i,j))

  union  l = SPred (IntervalTB1 (minimum (minP <$> l)  `interval` maximum (maxP <$> l)))
  pickSplit = pickSplitG
  penalty p1 p2 =  (notNeg $ (unFin $ fst $ minP p2) `diffS` (unFin $ fst $ minP p1)) `appendDShowable`  (notNeg $ (unFin $ fst $ maxP p1) `diffS` (unFin $ fst $ maxP p2))

notNeg (DSText l)
  | L.null dp = DSText []
  | head dp < 0 = DSText []
  | otherwise = DSText dp
  where dp =  dropWhile (==0) l
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
notNeg i = errorWithStackTrace (show i)

inter a b = IntervalTB1 $ (ER.Finite a,True) `interval` (ER.Finite b,True)

unFin (Interval.Finite (TB1 i) ) = i
unFin o = errorWithStackTrace (show o)

minP (SPred (IntervalTB1 i) ) = lowerBound' i
minP (SPred i@(TB1 _) ) = (ER.Finite $ i,True)
minP (SPred (ArrayTB1 i) ) = (ER.Finite $  L.minimum i,True)
minP i = errorWithStackTrace (show i)

maxP (SPred (IntervalTB1 i) ) = upperBound' i
maxP (SPred i@(TB1 _) ) = (ER.Finite $ i,True)
maxP (SPred (ArrayTB1 i) ) = (ER.Finite $  L.maximum i,True)
maxP i = errorWithStackTrace (show i)


greatestPenalty :: (Ord (f b) ,Predicates f b ) => Entry f b -> [Entry f b] -> (Penalty b , Entry f b, Entry f b)
greatestPenalty e es = L.maximumBy (comparing (\(p,_,_) -> p)) [(penalty (entryPredicate e) (entryPredicate e1), e, e1) | e1 <- es]

-- | Implementation of the linear split algorithm taking the minimal fill factor into account
linearSplit :: (Ord (f b),Predicates f b ) => [Entry f b] -> [Entry f b] ->
    [Entry f b] -> Int -> ([Entry f b], [Entry f b])
linearSplit es1 es2 [] _ = (es1,es2)
linearSplit es1 es2 (e:es) max
    |length es1 == max  = (es1,es2 ++ (e:es))
    |length es2 == max  = (es1 ++ (e:es), es2)
    |otherwise          = if penalty (entryPredicate e) (union $ map entryPredicate es1) >
                            penalty (entryPredicate e) (union $ map entryPredicate es2)
                            then linearSplit es1 (e:es2) es max
                            else linearSplit (e:es1) es2 es max

pickSplitG
  :: (Predicates f b, Ord (f b)) =>
     [Entry f b] -> ([Entry f b], [Entry f b])
pickSplitG es = linearSplit [e1] [e2] [e | e <- L.sortBy (comparing entryPred)  es, entryPred e /= entryPred e1, entryPred e/= entryPred e2] $ (length es + 1) `div` 2
        -- A tuple containing the two most disparate entries in the list their corresponding penalty penalty
        where (_, e1, e2) = L.maximumBy (comparing (\(a,_,_) -> a)) [greatestPenalty e es | e <- es]

entryPred (NodeEntry (_,p)) = p
entryPred (LeafEntry (_,p)) = p

