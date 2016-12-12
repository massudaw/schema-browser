{-# LANGUAGE TypeFamilies#-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Types.Index
  (Affine (..),Predicate(..),DiffShowable(..),TBIndex(..) , toList ,lookup ,fromList ,filter ,filter'
  ,getIndex ,getUnique,notOptional,tbpred
  ,minP,maxP,unFin,queryCheck,indexPred,checkPred,splitIndex,splitPred,splitIndexPK,module G ) where

import Data.Maybe
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
instance (Binary a)  => Binary (TBIndex a)
instance (NFData a)  => NFData (TBIndex a)


getUnique :: Ord k => [k] -> TBData k a -> TBIndex  a
getUnique ks (m,v) = Idex .  fmap snd . L.sortBy (comparing ((`L.elemIndex` ks).fst)) .  getUn (Set.fromList ks) $ (m,v)

getIndex :: Ord k => TBData k a -> TBIndex  a
getIndex (m,v) = Idex .  fmap snd . L.sortBy (comparing ((`L.elemIndex` (_kvpk m)).fst)) .  getPKL $ (m,v)

notOptional :: TBIndex  a -> TBIndex  a
notOptional (Idex m) = Idex   . justError "cant be empty " . traverse unSOptional'  $ m

tbpred :: Ord k => TBData k a -> TBIndex a
tbpred = notOptional . getIndex


instance (Num a , Num (Tangent a) ,Fractional a ,Affine a) => Affine (ER.Extended a ) where
  type Tangent (ER.Extended a) = ER.Extended (Tangent  a)
  loga (ER.Finite i) = ER.Finite $ loga i
  loga ER.PosInf = ER.PosInf
  loga ER.NegInf = ER.NegInf
  expa (ER.Finite i) = ER.Finite $ expa  i
  expa ER.PosInf = ER.PosInf
  expa ER.NegInf = ER.PosInf
  subtraction (ER.Finite i) (ER.Finite j) = ER.Finite $ subtraction i j
  subtraction (ER.PosInf ) (ER.PosInf ) = ER.Finite 0
  subtraction (ER.PosInf ) (ER.NegInf ) = ER.PosInf
  subtraction (ER.NegInf ) (ER.PosInf ) = ER.NegInf
  subtraction (ER.NegInf ) (ER.NegInf ) = ER.Finite 0
  addition (ER.Finite i) (ER.Finite j) = ER.Finite $ addition i j
  addition ER.NegInf  ER.NegInf = ER.NegInf
  addition ER.PosInf ER.NegInf = ER.Finite 0
  addition ER.NegInf ER.PosInf = ER.Finite 0
  addition ER.PosInf ER.PosInf = ER.PosInf

instance Semigroup a => Semigroup (ER.Extended a ) where
  (ER.Finite i ) <>  (ER.Finite j) = ER.Finite (i <> j)
  ER.NegInf  <>  j = ER.NegInf
  j <> ER.NegInf  = ER.NegInf
  i <>  ER.PosInf = ER.PosInf
  ER.PosInf <> _= ER.PosInf

instance Semigroup DiffPosition where
  DiffPosition2D (x,y) <> DiffPosition2D (i,j)  = DiffPosition2D (x + i , y + j)
  DiffPosition3D (x,y,z) <> DiffPosition3D (i,j,k)  = DiffPosition3D (x + i , y + j,z+ k)
  a <> b = errorWithStackTrace (show (a,b))

instance Semigroup DiffShowable where
  (<>) = appendDShowable
    where
      appendDShowable :: DiffShowable -> DiffShowable -> DiffShowable
      appendDShowable (DSText l ) (DSText j) =  DSText $ zipWith (+) l j <> L.drop (L.length j) l <> L.drop (L.length l ) j
      appendDShowable (DSDouble l ) (DSDouble j) =  DSDouble$ l + j
      appendDShowable (DSInt l ) (DSInt j) =  DSInt $ l + j
      appendDShowable (DSDays l ) (DSDays j) =  DSDays $ l + j
      appendDShowable (DSDiffTime l ) (DSDiffTime j) =  DSDiffTime $ l + j
      appendDShowable (DSPosition x ) (DSPosition y ) =  DSPosition $ x <> y
      appendDShowable a b = errorWithStackTrace ("append " <> show (a,b))


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
  subtraction i j = diffStr i j
    where
      diffStr :: String -> String -> [Int]
      diffStr (a:as) (b:bs) = (ord b - ord a) : diffStr as bs
      diffStr bs [] = ord <$> bs
      diffStr [] bs = ord <$> bs
      diffStr [] [] = []
  {-# INLINE subtraction #-}
  addition  i j = addStr  i j
    where
      addStr (a:as) (b:bs) = chr (ord a + b) : addStr as bs
      addStr (a:as) []  = a : addStr as []
      addStr [] (b:bs) = chr b : addStr [] bs
      addStr [] [] = []
  {-# INLINE addition #-}

splitIndexPK :: Eq k => BoolCollection (Access k ,AccessOp Showable) -> [k] -> Maybe (BoolCollection (Access k , AccessOp Showable))
splitIndexPK (OrColl l ) pk  = if F.all (isNothing .snd) al then Nothing else Just $ OrColl $ fmap (\(i,j) -> fromMaybe i j) al
    where
      al = (\l -> (l,splitIndexPK  l pk ) )<$> l
splitIndexPK (AndColl l ) pk  = fmap AndColl $ nonEmpty $ catMaybes $ (\i -> splitIndexPK  i pk ) <$> l
splitIndexPK (PrimColl (p@(IProd _ [i]),op) ) pk  = if elem i  pk  then Just (PrimColl (p,op)) else Nothing
splitIndexPK (PrimColl (p@(IProd _ l),op) ) pk  = Nothing --errorWithStackTrace (show (l,op,pk))
splitIndexPK i  pk  = Nothing -- errorWithStackTrace (show (i,pk))


instance Monoid (TBIndex a) where
  mempty  = Idex []

splitIndex :: (Eq k ,Show k) => BoolCollection (Access k ,AccessOp Showable) -> [k] -> TBIndex Showable -> Maybe (BoolCollection (Access k, AccessOp Showable))
splitIndex (AndColl l ) pk f = if F.all (isNothing .snd) al then Nothing else Just $ AndColl $ fmap (\(i,j) -> fromMaybe i j) al
    where
      al = (\l -> (l,splitIndex  l pk f) )<$> l
splitIndex (OrColl l ) pk f = fmap OrColl $ nonEmpty $ catMaybes $ (\i -> splitIndex  i pk f) <$> l
splitIndex (PrimColl (p@(IProd _ [i]),op) ) pk (Idex v ) = maybe (Just (PrimColl (p,op))) (splitPred (PrimColl (p,op))) ((v !!) <$>  (L.elemIndex i pk ))
splitIndex i  k j = Just i

splitPred :: (Eq k ,Show k) => BoolCollection (Access k,AccessOp Showable) ->  FTB Showable -> Maybe (BoolCollection (Access k,AccessOp Showable)  )
splitPred (PrimColl (prod ,Left (a@(TB1 _ ) ,op))) (ArrayTB1 b ) = if elem a  b then Nothing else Just (PrimColl (prod , Left (a,op)))
splitPred (PrimColl (prod ,Left (a@(TB1 _ ) ,op))) (IntervalTB1 b ) = if Interval.member a  b then Nothing else Just (PrimColl (prod , Left (a,op)))
splitPred (PrimColl (prod ,Left (a@(TB1 _ ) ,op))) b@(TB1  _ ) = if a  == b then Nothing else Just (PrimColl (prod , Left (a,op)))
splitPred (PrimColl (prod ,Left ((IntervalTB1 a ) ,op))) i@(TB1  _ ) = (\i -> if F.length i == 1 then head . F.toList $ i else OrColl (F.toList i) ). fmap (PrimColl. (prod,). Left . (,op).IntervalTB1) <$> Interval.split i a
splitPred (PrimColl (prod ,Left (i@(IntervalTB1 u) ,op))) (IntervalTB1 a ) =(\i -> if F.length i == 1 then head . F.toList $ i else OrColl (F.toList i) ). fmap (PrimColl .(prod,). Left . (,op).IntervalTB1) <$>  Interval.difference u a
splitPred (PrimColl (prod ,Left ((ArrayTB1 l ) ,Flip (AnyOp op)))) a  = OrColl <$> nonEmpty (catMaybes $ fmap (\i -> splitPred (PrimColl (prod,Left (i,op))) a) $ F.toList l)
-- splitPred (AndColl l) e = fmap AndColl $ nonEmpty $ catMaybes $ (flip splitPred e)<$> l
-- splitPred (OrColl l) e = fmap OrColl $ nonEmpty $ catMaybes $ (flip splitPred e) <$> l
splitPred p@(PrimColl (prod,Right i)) _ =  Just p
splitPred a e = errorWithStackTrace (show (a,e))

instance Affine Position where
  type Tangent Position = DiffPosition
  subtraction ((Position (x,y,z)) ) ((Position (a,b,c))) = DiffPosition3D (a-x,b-y,c-z)
  subtraction ((Position2D (x,y)) ) ((Position2D (a,b))) = DiffPosition2D (a-x,b-y)
  addition ((Position (x,y,z)) ) ((DiffPosition3D (a,b,c))) = Position (a+x,b+y,c+z)
  addition ((Position2D (x,y)) ) ((DiffPosition2D (a,b))) = Position2D (a+x,b+y)
  expa ((DiffPosition3D t)) =  Position t
  expa ((DiffPosition2D t)) =  Position2D t
  loga ((Position t)) =  (DiffPosition3D t)
  loga ((Position2D t)) =  (DiffPosition2D t)

instance Affine Showable where
  type Tangent Showable = DiffShowable
  loga (SText t) =  DSText $ loga (T.unpack t)
  loga (SDouble t) =  DSDouble $ t
  loga (SNumeric t) =  DSInt $ t
  loga (SDate t) =  DSDays  (diffDays  t (ModifiedJulianDay 0))
  loga (STimestamp t) =  DSDiffTime (diffUTCTime (localTimeToUTC utc t) (UTCTime (ModifiedJulianDay 0) 0))
  loga (SGeo (SPosition t)) =  DSPosition (loga t)
  loga i = errorWithStackTrace (show i)
  expa (DSText t) =  SText $ T.pack $ expa t
  expa (DSDouble t) =  SDouble $ t
  expa (DSInt t) =  SNumeric $ t
  expa (DSDays t) =  SDate $ addDays t (ModifiedJulianDay 0)
  expa (DSDiffTime t) =  STimestamp $ utcToLocalTime utc $ addUTCTime  t (UTCTime (ModifiedJulianDay 0) 0)
  expa (DSPosition t) =  SGeo $ SPosition (expa t)
  expa i = errorWithStackTrace (show i)
  subtraction = diffS
    where
      diffS :: Showable -> Showable -> DiffShowable
      diffS (SText t) (SText o) = DSText $ subtraction (T.unpack o) (T.unpack t)
      diffS (SDouble t) (SDouble o) = DSDouble $ o -t
      diffS (SNumeric t) (SNumeric o) = DSInt $ o -t
      diffS (STimestamp i ) (STimestamp j) = DSDiffTime (diffUTCTime (localTimeToUTC utc j) (localTimeToUTC utc  i))
      diffS (SDate i ) (SDate j) = DSDays (diffDays j i)
      diffS (SGeo(SPosition s )) (SGeo(SPosition b)) = DSPosition $ subtraction s b
      diffS a b  = errorWithStackTrace (show (a,b))
  {-# INLINE subtraction #-}
  addition (SText v) (DSText t) = SText $ T.pack $ addition (T.unpack v) t
  addition (SNumeric v) (DSInt t) = SNumeric  $ v + t
  addition (SDouble v) (DSDouble t) = SDouble $ v + t
  addition (STimestamp  v) (DSDiffTime t) = STimestamp $ utcToLocalTime utc $ addUTCTime t (localTimeToUTC utc v)
  addition (SDate v) (DSDays t) = SDate $ addDays t v
  addition (SGeo(SPosition  v )) (DSPosition t ) = SGeo(SPosition $ addition v t)
  addition i j = errorWithStackTrace (show (i,j))
  {-# INLINE addition #-}

instance Predicates (TBIndex Showable) where
  type (Penalty (TBIndex Showable)) = [ER.Extended DiffShowable]
  type Query (TBIndex Showable) = (TBPredicate Int Showable)
  consistent (Idex l) (Idex  i )
    =  if null b then False else  F.all id b
    where
      b =  zipWith consistent l i

  match (WherePredicate a)  e (Idex v) = go a
    where
      -- Index the field and if not found return true to row filtering pass
      go (AndColl l) = F.all go l
      go (OrColl l ) = F.any go  l
      go (PrimColl (IProd _ [i],op)) = maybe (traceShow i True) (match op e)  ( v `atMay` i)

  union l
    | L.null l = Idex []
    | otherwise = F.foldl1 (\(Idex l) (Idex s) -> Idex $ zipWith (\i j -> union [i,j]) l s) l

  penalty (Idex p1 ) (Idex p2) = zipWith (\i j -> penalty i j ) p1 p2 -- (fmap (maybe ER.PosInf (ER.Finite .loga) .unFin . fst .minP)) (fmap (maybe ER.PosInf (ER.Finite .loga ). unFin . fst . minP))  p1 p2

projIdex (Idex v) = F.toList v

instance (Predicates (TBIndex  a )  ) => Monoid (G.GiST (TBIndex  a)  b) where
  mempty = G.empty
  mappend i j
    | G.size i < G.size j = ins  j (getEntries i )
    | otherwise  = ins  i (getEntries j )
    where ins = foldl' (\j i -> G.insert i (3,6) j)


-- Attr List Predicate

{-
instance  Predicates (Map k (FTB Showable)) where
  type Penalty (Map k (FTB Showable )) = Map k (ER.Extended DiffShowable)
  type Query (Map k (FTB Showable )) = TBPredicate k Showable
  match (WherePredicate a ) e  v=  go a
    where
      -- Index the field and if not found return true to row filtering pass
      go (AndColl l) = F.all go l
      go (OrColl l ) = F.any go  l
      go (PrimColl (i,op)) = maybe True (\i -> match op e  i) (fmap _tbattr $ indexField i (errorWithStackTrace "no meta",Compose $Identity $ KV (M.mapKeys (Set.singleton .Inline) $ M.mapWithKey (\k v -> Compose $ Identity $ Attr k v) v)) )
  consistent l i =  if M.null b then False else  F.all id b
    where
      b =  M.intersectionWith consistent (l) (i)
  union l
    | L.null l = M.empty
    | otherwise = foldl1 (M.intersectionWith (\i j -> union [i,j]) ) l
  penalty p1 p2 = M.mergeWithKey (\_ i j -> Just $penalty i j ) (fmap (maybe ER.PosInf (ER.Finite .loga) .unFin . fst .minP)) (fmap (maybe ER.PosInf (ER.Finite .loga ). unFin . fst . minP))  p1 p2
-}

checkPred v (WherePredicate l) = checkPred' v l

checkPred' v (AndColl i ) = F.all  (checkPred' v)i
checkPred' v (OrColl i ) = F.any (checkPred' v) i
checkPred' v (PrimColl i) = indexPred i v

indexPred :: (Show k ,Ord k) => (Access k ,AccessOp Showable ) -> TBData k Showable -> Bool
indexPred (Many i,eq) a= all (\i -> indexPred (i,eq) a) i
indexPred (n@(Nested k nt ) ,eq) r
  = case  indexField n r of
    Nothing -> False
    Just i ->  recPred $ indexPred (nt , eq ) <$> _fkttable  i
  where
    recPred (SerialTB1 i) = maybe False recPred i
    recPred (LeftTB1 i) = maybe False recPred i
    recPred (TB1 i ) = i
    recPred (ArrayTB1 i) = any recPred (F.toList i)
    recPred i = errorWithStackTrace (show i)
indexPred (a@(IProd _ _),eq) r =
  case indexField a r of
    Nothing ->  False
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
        i -> traceShow (a,eq,r) $errorWithStackTrace (show i)
    Just (FKT _ _ rv) ->
      case eq of
        Right (Not IsNull)  -> isJust $ unSOptional' rv
        Right IsNull -> isNothing $ unSOptional' rv
        i -> traceShow (a,eq,r) $errorWithStackTrace (show i)
indexPred i v= errorWithStackTrace (show (i,v))


queryCheck :: (Show k,Ord k) => (WherePredicateK k ,[k])-> G.GiST (TBIndex Showable) (TBData k Showable) -> G.GiST (TBIndex  Showable) (TBData k Showable)
queryCheck pred@(WherePredicate b ,pk) = t1
  where t1 = filter' (flip checkPred (fst pred)) . maybe G.getEntries (\p -> G.query (mapPredicate (\i -> justError "no predicate" $ L.elemIndex i pk)  $ WherePredicate p)) (splitIndexPK b pk)

-- Atomic Predicate

data DiffFTB a
  = DiffInterval (DiffFTB a,DiffFTB a)
  -- | DiffArray [DiffFTB a]
  deriving(Eq,Ord,Show)

data DiffPosition
  = DiffPosition3D (Double,Double,Double)
  | DiffPosition2D (Double,Double)
  deriving(Eq,Ord,Show)

data DiffShowable
  = DSText [Int]
  | DSDouble Double
  | DSPosition DiffPosition
  | DSInt Int
  | DSDiffTime NominalDiffTime
  | DSDays Integer
  deriving(Eq,Ord,Show)


instance Predicates (FTB Showable) where
  type Penalty (FTB Showable) = ER.Extended DiffShowable
  type Query (FTB Showable) = AccessOp Showable
  consistent (TB1 i)  (TB1 j)  = i == j
  consistent (IntervalTB1 i) (IntervalTB1 j) = not $ Interval.null $  j `Interval.intersection` i
  consistent j@(TB1 _)  (IntervalTB1 i)  = j `Interval.member` i
  consistent (IntervalTB1 i) j@(TB1 _)  = j `Interval.member` i
  consistent (ArrayTB1 i)  (ArrayTB1 j)   = not $ Set.null $ Set.intersection (Set.fromList (F.toList i) ) (Set.fromList  (F.toList j))
  consistent (ArrayTB1 i)  j  = F.any (flip consistent j) i
  consistent i  (ArrayTB1 j ) = F.any (consistent i) j

  consistent (SerialTB1 i) (SerialTB1 j ) = fromMaybe True $ liftA2 consistent j  i
  consistent (SerialTB1 i) j = fromMaybe True $ (flip consistent j ) <$>  i
  consistent j (SerialTB1 i)  = fromMaybe True $ (consistent j ) <$>  i
  consistent (LeftTB1 i) (LeftTB1 j ) = fromMaybe True $ liftA2 consistent j  i
  consistent (LeftTB1 i) j = fromMaybe True $ (flip consistent j ) <$>  i
  consistent i (LeftTB1 j) = fromMaybe True $(consistent i ) <$>  j
  consistent i j  = errorWithStackTrace (show (i,j))

  match  (Right (Not i) ) c  j   = not $ match (Right i ) c j
  match  (Right IsNull) _   (LeftTB1 j)   = isNothing j
  match  (Right IsNull) _   j   = False
  match  (Right (BinaryConstant op e )) i v  = match (Left (generateConstant e,op)) i v
  match  (Right (Range b pred)) i  (IntervalTB1 j)   = match  (Right $ pred) i $ LeftTB1 $ fmap TB1 $ unFin $ if b then upperBound j else lowerBound j
  match (Left v) a j  = ma  v a j
    where
      -- ma v a j | traceShow (v,a,j) False = undefined
      ma  (v,Flip (Flip op))  a  j   = ma (v,op)  a j
      ma  v  a  (LeftTB1 j)   = fromMaybe False (ma v a <$> j)
      ma  v  a  (SerialTB1 j)   = fromMaybe False (ma v a <$> j)
      ma  v  a  (DelayedTB1 j)   = fromMaybe False (ma v a <$> j)
      ma  (LeftTB1 j ,v) e  i   = fromMaybe False ((\a -> ma (a,v) e i) <$> j)
      ma  (LeftTB1 i,Equals) e   (LeftTB1 j)   = fromMaybe False $ liftA2 (\a b -> ma (a,Equals) e b) i j
      ma  (TB1 i,_) _  (TB1 j)   = i == j
      ma  ((ArrayTB1 i) ,Flip Contains ) _  ((ArrayTB1 j)  ) = Set.fromList (F.toList i) `Set.isSubsetOf` Set.fromList  (F.toList j)
      ma  ((ArrayTB1 j),Contains ) _  ((ArrayTB1 i)  ) = Set.fromList (F.toList i) `Set.isSubsetOf` Set.fromList  (F.toList j)
      ma (j,AnyOp o ) p  (ArrayTB1 i) = F.any (ma (j,o) p )  i
      ma (j,Flip (AnyOp o) ) p  (ArrayTB1 i) = F.any (ma (j,o) p )  i
      ma (ArrayTB1 i,Flip (AnyOp o)) p j  = F.any (\i -> ma (i,o) p j ) i
      ma (i@(TB1 _) ,op) p (IntervalTB1 j)  = i `Interval.member` j
      ma (IntervalTB1 i ,op) p j@(TB1 _)  = j `Interval.member` i
      ma (IntervalTB1 i ,Contains) Exact (IntervalTB1 j)  = j `Interval.isSubsetOf` i
      ma (IntervalTB1 j ,Flip Contains) Exact (IntervalTB1 i)  = j `Interval.isSubsetOf` i
      ma (IntervalTB1 j ,IntersectOp) _  (IntervalTB1 i)  = not $ Interval.null $ j `Interval.intersection` i
      ma (IntervalTB1 i ,_) Intersect (IntervalTB1 j)  = not $ Interval.null $ j `Interval.intersection` i
      ma i e j = traceShow (i,e,j) $ errorWithStackTrace ("no ma = " <> show (i,e,j))
  match x y z = errorWithStackTrace ("no match = " <> show (x,y,z))

  union  l
    | otherwise =  IntervalTB1 ( mi `interval` ma )
    where mi = minimum (minP <$> l)
          ma = maximum (maxP <$> l)


  penalty p1 p2 =  (maybe ER.PosInf ER.Finite $ fmap notNeg $ liftA2 subtraction (unFin $ fst $ minP p2) (unFin $ fst $ minP p1)) <>  (maybe ER.PosInf ER.Finite $ fmap notNeg $ liftA2 subtraction (unFin $ fst $ maxP p1)  (unFin $ fst $ maxP p2))



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


unFin (Interval.Finite (TB1 i) ) = Just i
unFin o = Nothing -- errorWithStackTrace (show o)

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


