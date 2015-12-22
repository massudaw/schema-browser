{-# LANGUAGE TypeFamilies#-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Types.Index
  (TBIndex(..) , toList ,lookup ,fromList ,filter ,module G ) where

import Data.GiST.RTree (pickSplitG)
import Data.Semigroup
import Types
import Utils
import Data.Time
import Data.Ord
import Data.Foldable (foldl')
import Data.Char
import qualified Data.Foldable as F
import Data.Functor.Apply
import Prelude hiding(head,lookup,filter)
import Data.GiST.GiST as G
import qualified Data.Interval as Interval
import Data.Interval (interval,lowerBound',upperBound',lowerBound,upperBound)
import qualified Data.ExtendedReal as ER
import qualified Data.Text as T
import GHC.Stack
import Debug.Trace
import qualified Data.List as L
import qualified Data.Set as Set
import Data.GiST.BTree



--- Row Level Predicate
newtype TBIndex k a
  = Idex [(k,FTB a)]
  deriving(Eq,Show,Ord,Functor)

instance Semigroup DiffShowable where
  (<>) = appendDShowable
    where
      appendDShowable :: DiffShowable -> DiffShowable -> DiffShowable
      appendDShowable (DSText l ) (DSText j) =  DSText $ zipWith (+) l j <> L.drop (L.length j) l <> L.drop (L.length l ) j
      appendDShowable (DSDouble l ) (DSDouble j) =  DSDouble$ l + j
      appendDShowable (DSInt l ) (DSInt j) =  DSInt $ l + j
      appendDShowable (DSDays l ) (DSDays j) =  DSDays $ l + j
      appendDShowable (DSDiffTime l ) (DSDiffTime j) =  DSDiffTime $ l + j
      appendDShowable a b = errorWithStackTrace (show (a,b))


class Affine f where
  type Tangent f
  subtraction :: f -> f -> Tangent f
  addition :: f -> Tangent f -> f

instance Affine String where
  type Tangent String = [Int]
  subtraction = diffStr
    where
      diffStr :: String -> String -> [Int]
      diffStr [] [] = []
      diffStr bs [] = ord <$> bs
      diffStr [] bs = ord <$> bs
      diffStr (a:as) (b:bs) = (ord b - ord a) : diffStr as bs
  addition = addStr
    where
      addStr [] [] = []
      addStr (a:as) []  = a : addStr as []
      addStr [] (b:bs) = chr b : addStr [] bs
      addStr (a:as) (b:bs) = chr (ord a + b) : addStr as bs


instance Affine Showable where
  type Tangent Showable = DiffShowable
  subtraction = diffS
    where
      diffS :: Showable -> Showable -> DiffShowable
      diffS (SText t) (SText o) = DSText $ subtraction (T.unpack o) (T.unpack t)
      diffS (SDouble t) (SDouble o) = DSDouble $ o -t
      diffS (SNumeric t) (SNumeric o) = DSInt $ o -t
      diffS (STimestamp i ) (STimestamp j) = DSDiffTime (diffUTCTime (localTimeToUTC utc j) (localTimeToUTC utc  i))
      diffS (SDate i ) (SDate j) = DSDays (diffDays j i)
      diffS a b  = errorWithStackTrace (show (a,b))
  addition (SText v) (DSText t) = SText $ T.pack $ addition (T.unpack v) t
  addition (SNumeric v) (DSInt t) = SNumeric  $ v + t
  addition (SDouble v) (DSDouble t) = SDouble $ v + t
  addition (STimestamp  v) (DSDiffTime t) = STimestamp $ utcToLocalTime utc $ addUTCTime t (localTimeToUTC utc v)
  addition (SDate v) (DSDays t) = SDate $ addDays t v
  addition i j = errorWithStackTrace (show (i,j))

instance Predicates (TBIndex Key Showable) where
  type (Penalty (TBIndex Key Showable)) = Penalty ([FTB Showable])
  consistent (Idex j) (Idex  m ) = consistent (fmap snd $  j) (fmap snd $ m)
  union l  = Idex (zipWith (,) kf projL)
    where Idex  v = head l
          kf = fmap fst v
          projL = union $ fmap (fmap snd . (\(Idex  a) -> a)) l

  penalty i j = penalty (projIdex i ) (projIdex j)
  pickSplit = pickSplitG

projIdex (Idex v) = fmap snd $ v

instance (Predicates (TBIndex k a )  ) => Monoid (G.GiST (TBIndex k a)  b) where
  mempty = G.empty
  mappend i j
    | G.size i < G.size j = ins  j (getEntries i )
    | otherwise  = ins  i (getEntries j )
    where ins = foldl' (\j i -> G.insert i (3,6) j)


-- Attr List Predicate
instance  Predicates [FTB Showable] where
  type Penalty ([FTB Showable] ) = [DiffShowable]
  consistent (l ) (i) =  all id $ zipWith consistent (l) (i)
  union l = fmap (\i ->  union i )$ L.transpose $  l
  penalty (p1) (p2) = zipWith penalty p1  p2
  pickSplit = pickSplitG



-- Atomic Predicate

data DiffFTB a
  = DiffInterval (DiffFTB a,DiffFTB a)
  | DiffArray [DiffFTB a]
  deriving(Eq,Ord,Show)

instance Affine a => Affine (ER.Extended a) where
  type Tangent (ER.Extended a) = Tangent a
  subtraction (ER.Finite i) (ER.Finite j)=  subtraction i j
  addition (ER.Finite i) j =  ER.Finite (addition i j)

instance (Fractional (DiffFTB (Tangent a)) ,Affine a ,Ord a) => Affine (FTB a) where
  type Tangent (FTB a) = DiffFTB (Tangent a)
  subtraction = intervalSub
  addition = intervalAdd

data DiffShowable
  = DSText [Int]
  | DSDouble Double
  | DSInt Int
  | DSDiffTime NominalDiffTime
  | DSDays Integer
  deriving(Eq,Ord,Show)


instance Predicates (FTB Showable) where
  type Penalty (FTB Showable) = DiffShowable
  consistent (j@(TB1 _) )  ((IntervalTB1 i) ) = j `Interval.member` i
  consistent (i@(TB1 _) ) ((ArrayTB1 j)) = F.elem  i j
  consistent ((TB1 i) ) ((TB1 j) ) = i == j
  consistent ((IntervalTB1 i) ) ((IntervalTB1 j) ) = not $ Interval.null $  j `Interval.intersection` i
  -- consistent ((IntervalTB1 i) ) ((IntervalTB1 j)) = i `Interval.isSubsetOf` j
  consistent ((IntervalTB1 i) ) (j@(TB1 _) ) = j `Interval.member` i
  -- consistent ((ArrayTB1 i) ) ((ArrayTB1 j)  ) = not $ Set.null $ Set.fromList (F.toList i) `Set.intersection` Set.fromList  (F.toList j)
  consistent ((ArrayTB1 i) ) ((ArrayTB1 j)  ) = Set.fromList (F.toList i) `Set.isSubsetOf` Set.fromList  (F.toList j)
  consistent ((ArrayTB1 i) ) (j@(TB1 _)) = F.elem  j i
  consistent ((ArrayTB1 i) ) (j  ) = F.all (\i -> consistent   ( i) (j)) i
  consistent i j  = errorWithStackTrace (show (i,j))
  union  l = (IntervalTB1 (minimum (minP <$> l)  `interval` maximum (maxP <$> l)))
  pickSplit = pickSplitG
  penalty p1 p2 =  (notNeg $ (unFin $ fst $ minP p2) `subtraction`  (unFin $ fst $ minP p1)) <>  (notNeg $ (unFin $ fst $ maxP p1) `subtraction` (unFin $ fst $ maxP p2))

intervalAdd (IntervalTB1 i ) (DiffInterval (off,wid))
  = IntervalTB1 $ (lowerBound i `addition` off,True) `Interval.interval` (upperBound i `addition` wid,True)

intervalSub (IntervalTB1 i) (IntervalTB1 j)
  = DiffInterval (center j `subtraction` center i ,width j - width i)
  where
    center i = Interval.lowerBound i  `addition` ((width i)/2)
    width i = Interval.upperBound i `subtraction` Interval.lowerBound i


notNeg (DSText l)
  | L.null dp || head dp < 0 = def
  | otherwise = DSText l
  where dp =  dropWhile (==0) l
        def = DSText (replicate (L.length l) 0)
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


unFin (Interval.Finite (TB1 i) ) = i
unFin o = errorWithStackTrace (show o)

minP ((IntervalTB1 i) ) = lowerBound' i
minP (i@(TB1 _) ) = (ER.Finite $ i,True)
minP ((ArrayTB1 i) ) = minP$   F.minimum i
minP i = errorWithStackTrace (show i)

maxP ((IntervalTB1 i) ) = upperBound' i
maxP (i@(TB1 _) ) = (ER.Finite $ i,True)
maxP ((ArrayTB1 i) ) =   maxP $  F.maximum i
maxP i = errorWithStackTrace (show i)





-- Higher Level operations
fromList pred = foldl'  acc G.empty
  where
    acc !m v = G.insert (v,pred v ) (3,6) m

lookup pk  = safeHead . G.search pk

toList = getData

filter f = foldl' (\m i -> G.insert i (3,6) m) G.empty  . L.filter (f .fst ) . getEntries

