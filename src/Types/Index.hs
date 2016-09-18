{-# LANGUAGE TypeFamilies#-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Types.Index
  (Affine (..),Predicate(..),DiffShowable(..),TBIndex(..) , toList ,lookup ,fromList ,filter ,filter',mapKeys ,getIndex ,pickSplitG ,minP,maxP,unFin,module G ) where

import Data.Maybe
import Data.Functor.Identity
import Step.Host
import Control.Applicative
import Data.GiST.RTree (pickSplitG)
import Data.Tuple (swap)
import Data.Binary
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
import Data.GiST.GiST as G
import Data.GiST.BTree (Predicate(..))
import qualified Data.Interval as Interval
import Data.Interval (interval,lowerBound',upperBound',lowerBound,upperBound)
import qualified Data.ExtendedReal as ER
import qualified Data.Text as T
import GHC.Stack
import Debug.Trace
import qualified Data.List as L
import qualified Data.Set as Set
import Data.GiST.BTree
import Data.Map (Map)
import qualified Data.Map as M



--- Row Level Predicate
newtype TBIndex k a
  = Idex (Map k (FTB a))
  deriving(Eq,Show,Ord,Functor,Generic)

instance (Binary a, Binary k)  => Binary (TBIndex  k a)

mapKeys f (Idex i ) = Idex $ M.mapKeys f i
getIndex :: Ord k => TBData k a -> TBIndex k a
getIndex = Idex . getPKM

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

instance Predicates (WherePredicate,Predicate Int) where
  type Penalty (WherePredicate ,Predicate Int)= ([DiffShowable],Int)
  type Query (WherePredicate ,Predicate Int)= (WherePredicate ,Predicate Int)
  consistent (c1,i) (c2,j) = consistent c1 c2 && consistent i j
  penalty (c1,i) (c2,j) = (penalty c1 c2 ,penalty i j)
  match  (c1,i) (c2,j) = match c1 c2 && match i j
  union i  = (union (fst <$> i), union (snd <$> i))
  pickSplit = pickSplitG

instance Predicates WherePredicate where
  type Penalty WherePredicate = [DiffShowable]
  type Query WherePredicate = WherePredicate
  consistent (WherePredicate c1) (WherePredicate c2)  = F.all id $ M.mergeWithKey (\_ i j -> Just $ consistent (snd i) (snd j)) (const False <$>) (const False <$>) (M.fromList $fmap projKey  $ F.toList c1) (M.fromList $ fmap projKey $ F.toList c2)
    where projKey (a,b,c) =  (a,(b,c))

  match (WherePredicate c1) (WherePredicate c2)  = F.all id $ M.mergeWithKey (\_ i j -> Just $ match (swap i) (snd j)) (const False <$>) (const False <$>) (M.fromList $fmap projKey  $ F.toList c1) (M.fromList $ fmap projKey $ F.toList c2)
    where projKey (a,b,c) =  (a,(b,c))

  penalty (WherePredicate c1) (WherePredicate c2) =F.toList $ M.mergeWithKey (\_ i j -> Just $ penalty  (snd i) (snd j) ) (fmap (loga .unFin . fst .minP. (\(a,c) -> c))) (fmap (loga . unFin . fst . minP. (\(a,c) -> c))) (M.fromList $fmap projKey  $ F.toList c1) (M.fromList $ fmap projKey $ F.toList c2)
    where projKey (a,b,c) =  (a,(b,c))
  pickSplit = pickSplitG
  union l = WherePredicate $ AndColl $ fmap (\(k,(a,b))-> PrimColl(k,a,b))$ M.toList $ foldl1 ( M.mergeWithKey (\_ i j -> Just $ pairunion [i,j]) (fmap id) (fmap id) ) ((\(WherePredicate pr ) -> M.fromList .fmap projKey  . F.toList $ pr)<$> l)
    where projKey (a,b,c) =  (a,(b,c))
          pairunion i = (head $ fst <$> i,union $ snd <$> i)



class Affine f where
  type Tangent f
  loga :: f -> Tangent f
  expa :: Tangent f -> f
  subtraction :: f -> f -> Tangent f
  addition :: f -> Tangent f -> f

instance Affine String where
  type Tangent String = [Int]
  loga = fmap ord
  expa = fmap chr
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
  loga (SText t) =  DSText $ loga (T.unpack t)
  loga (SDouble t) =  DSDouble $ t
  loga (SNumeric t) =  DSInt $ t
  loga (SDate t) =  DSDays  (diffDays  t (ModifiedJulianDay 0))
  loga (STimestamp t) =  DSDiffTime (diffUTCTime (localTimeToUTC utc t) (UTCTime (ModifiedJulianDay 0) 0))
  loga i = errorWithStackTrace (show i)
  expa (DSText t) =  SText $ T.pack $ expa t
  expa (DSDouble t) =  SDouble $ t
  expa (DSInt t) =  SNumeric $ t
  expa (DSDays t) =  SDate $ addDays t (ModifiedJulianDay 0)
  expa (DSDiffTime t) =  STimestamp $ utcToLocalTime utc $ addUTCTime  t (UTCTime (ModifiedJulianDay 0) 0)
  expa i = errorWithStackTrace (show i)
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
  type (Penalty (TBIndex Key Showable)) = Penalty (Map Key (FTB Showable))
  type Query (TBIndex Key Showable) = TBPredicate Key Showable
  consistent (Idex j) (Idex  m )
     = consistent j m
  match (WherePredicate l)  (Idex v) =  match (WherePredicate l) v
  union l  = Idex   projL
    where
          projL = union  (fmap (\(Idex i) -> i)l)

  penalty (Idex i ) (Idex j) = penalty i j
  pickSplit = pickSplitG

projIdex (Idex v) = F.toList v

instance (Predicates (TBIndex k a )  ) => Monoid (G.GiST (TBIndex k a)  b) where
  mempty = G.empty
  mappend i j
    | G.size i < G.size j = ins  j (getEntries i )
    | otherwise  = ins  i (getEntries j )
    where ins = foldl' (\j i -> G.insert i (3,6) j)


-- Attr List Predicate
instance  Predicates (Map Key (FTB Showable)) where
  type Penalty (Map Key (FTB Showable )) = Map Key DiffShowable
  type Query (Map Key (FTB Showable )) = TBPredicate Key Showable
  match (WherePredicate a )  v=  go a
    where
      go (AndColl l) = F.all go l
      go (OrColl l ) = F.any go  l
      -- Index the field and if not found return true to row filtering pass
      go (PrimColl (i,op,c)) = maybe True (match (c,op)) (fmap _tbattr $ indexField i (undefined,Compose $Identity $ KV (M.mapKeys (Set.singleton .Inline) $ M.mapWithKey (\k v -> Compose $ Identity $ Attr k v) v)) )
  consistent l i =  if M.null b then False else  F.all id b
    where
      b =  M.intersectionWith consistent (M.mapKeys keyValue l) (M.mapKeys keyValue i)
  union l = foldl1 (M.intersectionWith (\i j -> union [i,j]) ) l
  penalty p1 p2 = M.mergeWithKey (\_ i j -> Just $penalty i j ) (fmap (loga .unFin . fst .minP)) (fmap (loga . unFin . fst . minP))  p1 p2
  pickSplit = pickSplitG



-- Atomic Predicate

data DiffFTB a
  = DiffInterval (DiffFTB a,DiffFTB a)
  -- | DiffArray [DiffFTB a]
  deriving(Eq,Ord,Show)

instance Affine a => Affine (ER.Extended a) where
  type Tangent (ER.Extended a) = Tangent a
  subtraction (ER.Finite i) (ER.Finite j)=  subtraction i j
  subtraction i j=  errorWithStackTrace " no subtraction"
  addition (ER.Finite i) j =  ER.Finite (addition i j)
  addition i j=  errorWithStackTrace " no subtraction"

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
  type Query (FTB Showable) = (FTB Showable , T.Text)
  consistent (LeftTB1 Nothing) (LeftTB1 Nothing)     = True
  consistent (LeftTB1 (Just i)) (LeftTB1 (Just j) )    = consistent j  i
  consistent (LeftTB1 (Just i)) j     = consistent j  i
  consistent i (LeftTB1 (Just j))     = consistent i  j
  consistent (j@(TB1 _) )  (LeftTB1 (Just i))  = consistent j  i
  consistent (j@(TB1 _) )  (SerialTB1 (Just i))  = consistent j  i
  consistent (j@(TB1 _) )  ((IntervalTB1 i) ) = j `Interval.member` i
  consistent (i@(TB1 _) ) ((ArrayTB1 j)) = F.elem  i j
  consistent ((TB1 i) ) ((TB1 j) ) = i == j
  consistent ((IntervalTB1 i) ) ((IntervalTB1 j) ) = not $ Interval.null $  j `Interval.intersection` i
  -- consistent ((IntervalTB1 i) ) ((IntervalTB1 j)) = i `Interval.isSubsetOf` j
  consistent ((IntervalTB1 i) ) (j@(TB1 _) ) = j `Interval.member` i
  -- consistent ((ArrayTB1 i) ) ((ArrayTB1 j)  ) = not $ Set.null $ Set.fromList (F.toList i) `Set.intersection` Set.fromList  (F.toList j)
  consistent ((ArrayTB1 i) ) ((ArrayTB1 j)  ) = Set.fromList (F.toList i) `Set.isSubsetOf` Set.fromList  (F.toList j)
  consistent ((ArrayTB1 i) ) (j@(TB1 _)) = F.elem  j i
  consistent ((ArrayTB1 i) ) (j  ) = F.all (\i -> consistent i j) i
  consistent   ((SerialTB1 (Just i)) ) (j@(TB1 _) )= consistent i j
  consistent i j  = errorWithStackTrace (show (i,j))

  match  (_,"is not null")  j   = True
  match  (_,"is null")  j   = False
  match  (_,"is null")  (LeftTB1 j)   = isNothing j
  match  v  (LeftTB1 j)   = fromMaybe False (match v <$> j)
  match  (LeftTB1 j ,v)  i   = fromMaybe False ((\a -> match (a,v) i) <$> j)
  match  (LeftTB1 i,"=")  (LeftTB1 j)   = fromMaybe False $ liftA2 match ((,"=") <$> i) j
  match  ((ArrayTB1 j) ,"IN") i  = F.elem i j
  match  (TB1 i,"=") (TB1 j)   = i == j
  match  ((ArrayTB1 i) ,"<@") ((ArrayTB1 j)  ) = Set.fromList (F.toList i) `Set.isSubsetOf` Set.fromList  (F.toList j)
  match  ((ArrayTB1 j) ,"IN") ((ArrayTB1 i)  ) = Set.fromList (F.toList i) `Set.isSubsetOf` Set.fromList  (F.toList j)
  match  ((ArrayTB1 j),"@>" ) ((ArrayTB1 i)  ) = Set.fromList (F.toList i) `Set.isSubsetOf` Set.fromList  (F.toList j)
  match (j@(TB1 _),"<@") (ArrayTB1 i) = F.elem j i
  match (j@(TB1 _),"=")(ArrayTB1 i) = F.elem j i
  match ((ArrayTB1 i) ,"@>") j@(TB1 _)   = F.elem j i
  match ((ArrayTB1 i) ,"=")j@(TB1 _)   = F.elem j i
  match ((ArrayTB1 i) ,"@>") j   = F.all (\i -> match (i,"@>") j) i
  match (IntervalTB1 i ,"<@") j@(TB1 _)  = j `Interval.member` i
  match (j@(TB1 _ ),"@>") (IntervalTB1 i)  = j `Interval.member` i
  match (j@(TB1 _ ),"=")(IntervalTB1 i)  = j `Interval.member` i
  match (IntervalTB1 i ,"<@") (IntervalTB1 j)  = j `Interval.isSubsetOf` i
  match (IntervalTB1 j ,"@>") (IntervalTB1 i)  = j `Interval.isSubsetOf` i
  match (IntervalTB1 j ,"&&") (IntervalTB1 i)  = not $ Interval.null $ j `Interval.intersection` i
  match i j = errorWithStackTrace ("no match = " <> show (i,j))

  union  l
    | mi == ma = justError "cant be inf" $unFinite $ fst $ mi
    | otherwise =  IntervalTB1 (  mi `interval` ma )
    where mi = minimum (minP <$> l)
          ma = maximum (maxP <$> l)

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
        def = DSText [] -- (replicate (L.length l) 0)
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

minP (LeftTB1 (Just i) ) = minP i
minP ((IntervalTB1 i) ) = lowerBound' i
minP (i@(TB1 _) ) = (ER.Finite $ i,True)
minP ((ArrayTB1 i) ) = minP$   F.minimum i
minP i = errorWithStackTrace (show i)

maxP (LeftTB1 (Just i) ) = minP i
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
filter' f = foldl' (\m i -> G.insert i (3,6) m) G.empty  . L.filter (f .fst )

