{-# LANGUAGE TypeFamilies#-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Types.Index
  (Affine (..),Predicate(..),DiffShowable(..),TBIndex(..) , toList ,lookup ,fromList ,filter ,filter',mapKeys ,getIndex ,pickSplitG ,minP,maxP,unFin,queryCheck,indexPred,checkPred,module G ) where

import Data.Maybe
import Control.Arrow (first)
import Data.Functor.Identity
import Step.Host
import Control.Applicative
import Data.Either
import Data.GiST.RTree (pickSplitG)
import Data.GiST.BTree hiding(Equals,Contains)
import Data.GiST.GiST as G
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
import qualified Data.Interval as Interval
import Data.Interval (interval,lowerBound',upperBound',lowerBound,upperBound)
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
      appendDShowable (DSPosition (x,y,z) ) (DSPosition (a,b,c)) =  DSPosition $ (x+a,y+b,z+c)
      appendDShowable a b = errorWithStackTrace (show (a,b))

instance (Predicates (Predicate a),Ord a) => Predicates (WherePredicate,Predicate a ) where
  type Penalty (WherePredicate ,Predicate a)= ([DiffShowable],Penalty (Predicate a))
  type Query (WherePredicate ,Predicate a)= (WherePredicate ,Query (Predicate a) )
  consistent (c1,i) (c2,j) = consistent c1 c2 && consistent i j
  penalty (c1,i) (c2,j) = (penalty c1 c2 ,penalty i j)
  match  (c1,i) e (c2,j) = match c1 e c2 && match i e j
  union i  = (union (fst <$> i), union (snd <$> i))
  pickSplit = pickSplitG

instance Predicates WherePredicate where
  type Penalty WherePredicate = [DiffShowable]
  type Query WherePredicate = WherePredicate
  consistent (WherePredicate c1) (WherePredicate c2)  = F.all id $ M.mergeWithKey (\_ i j -> Just $ cons i j) (const False <$>) (const False <$>) (M.fromList $F.toList c1) (M.fromList $ F.toList c2)
    where
      cons (Left i ) (Left j ) =consistent (fst i) (fst j)
      cons (Right i ) (Left j ) =False
      cons (Left i ) (Right j ) =False
      cons (Right i ) (Right j ) = i == j

  match (WherePredicate c1) e (WherePredicate c2)  = F.all id $ M.mergeWithKey (\_ i j -> Just $ either (match i e.fst) (const False) j  ) (const False <$>) (const False <$>) (M.fromList $ F.toList c1) (M.fromList $  F.toList c2)

  penalty (WherePredicate c1) (WherePredicate c2) =F.toList $ M.intersectionWithKey (\_ i j -> cons i j )  (M.fromList $ F.toList c1) (M.fromList $  F.toList c2)
    where
      cons (Left i ) (Left j ) =penalty (fst i) (fst j)
      cons (Right i ) (Left j ) = DSInt 1
      cons (Left i ) (Right j ) = DSInt (-1)
      cons (Right i ) (Right j ) = DSInt $ if i == j then 0 else 1
  pickSplit = pickSplitG
  union l = WherePredicate $ AndColl $ fmap (\(k,a)-> PrimColl(k,a))$ M.toList $ foldl ( M.mergeWithKey (\_ i j -> Just $ pairunion [i,j]) (fmap id) (fmap id) ) M.empty ((\(WherePredicate pr ) -> M.fromList .F.toList $ pr)<$> l)
    where
      pairunion i = Left $ (union  $ fmap fst (lefts i),headS $ fmap snd (lefts i ))


headS [] = errorWithStackTrace "no head"
headS i = head i

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
  loga (SPosition (Position t)) =  DSPosition t
  loga i = errorWithStackTrace (show i)
  expa (DSText t) =  SText $ T.pack $ expa t
  expa (DSDouble t) =  SDouble $ t
  expa (DSInt t) =  SNumeric $ t
  expa (DSDays t) =  SDate $ addDays t (ModifiedJulianDay 0)
  expa (DSDiffTime t) =  STimestamp $ utcToLocalTime utc $ addUTCTime  t (UTCTime (ModifiedJulianDay 0) 0)
  expa (DSPosition t) =  SPosition $ Position t
  expa i = errorWithStackTrace (show i)
  subtraction = diffS
    where
      diffS :: Showable -> Showable -> DiffShowable
      diffS (SText t) (SText o) = DSText $ subtraction (T.unpack o) (T.unpack t)
      diffS (SDouble t) (SDouble o) = DSDouble $ o -t
      diffS (SNumeric t) (SNumeric o) = DSInt $ o -t
      diffS (STimestamp i ) (STimestamp j) = DSDiffTime (diffUTCTime (localTimeToUTC utc j) (localTimeToUTC utc  i))
      diffS (SDate i ) (SDate j) = DSDays (diffDays j i)
      diffS (SPosition (Position (x,y,z)) ) (SPosition (Position (a,b,c))) = DSPosition (a-x,b-y,c-z)
      diffS a b  = errorWithStackTrace (show (a,b))
  addition (SText v) (DSText t) = SText $ T.pack $ addition (T.unpack v) t
  addition (SNumeric v) (DSInt t) = SNumeric  $ v + t
  addition (SDouble v) (DSDouble t) = SDouble $ v + t
  addition (STimestamp  v) (DSDiffTime t) = STimestamp $ utcToLocalTime utc $ addUTCTime t (localTimeToUTC utc v)
  addition (SDate v) (DSDays t) = SDate $ addDays t v
  addition (SPosition (Position (x,y,z)) ) (DSPosition (a,b,c)) = SPosition $ Position (a+x,b+y,c+z)
  addition i j = errorWithStackTrace (show (i,j))

instance Predicates (TBIndex Key Showable) where
  type (Penalty (TBIndex Key Showable)) = Penalty (Map Key (FTB Showable))
  type Query (TBIndex Key Showable) = TBPredicate Key Showable
  consistent (Idex j) (Idex  m )
     = consistent j m
  match (WherePredicate l)  e (Idex v) =  match (WherePredicate l) e v
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
  match (WherePredicate a ) e  v=  go a
    where
      -- Index the field and if not found return true to row filtering pass
      go (AndColl l) = F.all go l
      go (OrColl l ) = F.any go  l
      go (PrimColl (i,op)) = maybe True (\i -> match op e  i) (fmap _tbattr $ indexField i (errorWithStackTrace "no meta",Compose $Identity $ KV (M.mapKeys (Set.singleton .Inline) $ M.mapWithKey (\k v -> Compose $ Identity $ Attr k v) v)) )
  consistent l i =  if M.null b then False else  F.all id b
    where
      b =  M.intersectionWith consistent (M.mapKeys keyValue l) (M.mapKeys keyValue i)
  union l = foldl1 (M.intersectionWith (\i j -> union [i,j]) ) l
  penalty p1 p2 = M.mergeWithKey (\_ i j -> Just $penalty i j ) (fmap (loga .unFin . fst .minP)) (fmap (loga . unFin . fst . minP))  p1 p2
  pickSplit = pickSplitG


checkPred v (WherePredicate l) = checkPred' v l

checkPred' v (AndColl i ) = F.all  (checkPred' v)i
checkPred' v (OrColl i ) = F.any (checkPred' v) i
checkPred' v (PrimColl i) = indexPred i v

indexPred :: (Access Key ,AccessOp Showable ) -> TBData Key Showable -> Bool
indexPred (Many i,eq) a= all (\i -> indexPred (i,eq) a) i
indexPred (n@(Nested k nt ) ,eq) r
  = case  indexField n r of
    Nothing -> errorWithStackTrace ("cant find attr" <> show (n,nt))
    Just i ->  recPred $ indexPred (nt , eq ) <$> _fkttable  i
  where
    recPred (SerialTB1 i) = maybe False recPred i
    recPred (LeftTB1 i) = maybe False recPred i
    recPred (TB1 i ) = i
    recPred (ArrayTB1 i) = all recPred (F.toList i)
    recPred i = errorWithStackTrace (show i)
indexPred (a@(IProd _ _),eq) r =
  case indexField a r of
    Nothing ->  errorWithStackTrace ("cant find attr" <> show (a,eq,r))
    Just (Fun _ _ rv) ->
      case eq of
        i -> match eq Exact rv
    Just (Attr _ rv) ->
      case eq of
        i -> match eq Exact rv
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


queryCheck :: WherePredicate -> G.GiST (TBIndex Key Showable) (TBData Key Showable) -> G.GiST (TBIndex Key Showable) (TBData Key Showable)
queryCheck pred = t1
  where t1 = filter' (flip checkPred pred) . G.query pred

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
  | DSPosition (Double,Double,Double)
  | DSInt Int
  | DSDiffTime NominalDiffTime
  | DSDays Integer
  deriving(Eq,Ord,Show)


instance Predicates (FTB Showable) where
  type Penalty (FTB Showable) = DiffShowable
  type Query (FTB Showable) = AccessOp Showable
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
  consistent ((IntervalTB1 i) ) (j@(TB1 _) ) = j `Interval.member` i
  consistent (ArrayTB1 i)  ((ArrayTB1 j)  ) = Set.fromList (F.toList i) `Set.isSubsetOf` Set.fromList  (F.toList j)
  consistent (ArrayTB1 i)  (j@(TB1 _)) = F.elem  j i
  consistent (ArrayTB1 i)  (j  ) = F.all (\i -> consistent i j) i
  consistent (SerialTB1 (Just i)) j@(TB1 _) = consistent i j
  consistent i j  = errorWithStackTrace (show (i,j))

  match  (Right (Not i) ) c  j   = not $ match (Right i ) c j
  match  (Right IsNull) _   (LeftTB1 j)   = isNothing j
  match  (Right IsNull) _   j   = False
  match (Left v) a j  = ma  v a j
    where
      -- ma v a j | traceShow (v,a,j) False = undefined
      ma  v  a  (LeftTB1 j)   = fromMaybe False (ma v a <$> j)
      ma  v  a  (SerialTB1 j)   = fromMaybe False (ma v a <$> j)
      ma  v  a  (DelayedTB1 j)   = fromMaybe False (ma v a <$> j)
      ma  (LeftTB1 j ,v) e  i   = fromMaybe False ((\a -> ma (a,v) e i) <$> j)
      ma  (LeftTB1 i,Equals) e   (LeftTB1 j)   = fromMaybe False $ liftA2 (\a b -> ma (a,Equals) e b) i j
      ma  (TB1 i,_) _  (TB1 j)   = i == j
      ma  ((ArrayTB1 i) ,Flip Contains ) _  ((ArrayTB1 j)  ) = Set.fromList (F.toList i) `Set.isSubsetOf` Set.fromList  (F.toList j)
      ma  ((ArrayTB1 j),Contains ) _  ((ArrayTB1 i)  ) = Set.fromList (F.toList i) `Set.isSubsetOf` Set.fromList  (F.toList j)
      ma (j@(TB1 _),AnyOp o ) p  (ArrayTB1 i) = F.any (ma (j,o) p )  i
      ma (ArrayTB1 i,Flip (AnyOp o)) p j  = F.any (\i -> ma (i,o) p j ) i
      ma (i@(TB1 _) ,op) p (IntervalTB1 j)  = i `Interval.member` j
      ma (IntervalTB1 i ,op) p j@(TB1 _)  = j `Interval.member` i
     {- ma ((ArrayTB1 i) ,"@>") _ j@(TB1 _)   = F.elem j i
      ma ((ArrayTB1 i) ,"=") _ j@(TB1 _)   = F.elem j i
      ma  ((ArrayTB1 j) ,"IN") p  i  = F.any (\el -> ma (el,"=") p i ) j
      ma  ((ArrayTB1 j) ,"ANY") p  i  = F.any (\el -> ma (el,"=") p i ) j
      ma  ((ArrayTB1 j) ,"FIN") p  i  = F.any (\el -> ma (el,"=") p  i ) j
      ma ((ArrayTB1 i) ,"@>") e j   = F.all (\i -> ma (i,"@>") e j) i
      ma (IntervalTB1 i ,"<@") _ j@(TB1 _)  = j `Interval.member` i
      ma (IntervalTB1 i ,"@>") _ j@(TB1 _)  = j `Interval.member` i
      ma (IntervalTB1 i ,"FIN")_ j@(TB1 _)  = j `Interval.member` i
      ma (IntervalTB1 i ,"IN") _ j@(TB1 _)  = j `Interval.member` i
      ma (IntervalTB1 i ,"=") _ j@(TB1 _)  = j `Interval.member` i
      ma (j@(TB1 _ ),"IN") _ (IntervalTB1 i)  = j `Interval.member` i
      ma (j@(TB1 _ ),"FIN")_ (IntervalTB1 i)  = j `Interval.member` i
      ma (j@(TB1 _ ),"<@") _ (IntervalTB1 i)  = j `Interval.member` i
      ma (j@(TB1 _ ),"@>") _ (IntervalTB1 i)  = j `Interval.member` i
      ma (j@(TB1 _ ),"=") _ (IntervalTB1 i)  = j `Interval.member` i
-}
      ma (IntervalTB1 i ,Contains) Exact (IntervalTB1 j)  = j `Interval.isSubsetOf` i
      ma (IntervalTB1 j ,Flip Contains) Exact (IntervalTB1 i)  = j `Interval.isSubsetOf` i
      ma (IntervalTB1 j ,IntersectOp) _  (IntervalTB1 i)  = not $ Interval.null $ j `Interval.intersection` i
      ma (IntervalTB1 i ,_) Intersect (IntervalTB1 j)  = not $ Interval.null $ j `Interval.intersection` i
      ma i e j = errorWithStackTrace ("no ma = " <> show (i,e,j))
  match x y z = errorWithStackTrace ("no match = " <> show (x,y,z))

  union  l
    | otherwise =  IntervalTB1 ( mi `interval` ma )
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


notNeg (DSPosition l)
  | otherwise = DSPosition l
notNeg (DSText l)
  | L.null dp || headS dp < 0 = def
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
notNeg i= errorWithStackTrace (show i)


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

