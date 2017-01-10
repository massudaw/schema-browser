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
  (Affine (..),Predicate(..),DiffShowable(..),TBIndex(..) , toList ,lookup ,fromList ,filter ,filter'
  ,Number(..)
  ,getIndex ,getBounds,getUnique,notOptional,tbpred
--  ,insertRefl,deleteRefl,searchRefl
-- ,buildGistConsistent
-- ,ReifiedGist(..)
  ,minP,maxP,unFin,queryCheck,indexPred,checkPred,splitIndex,splitPred,splitIndexPK,module G ) where

import Data.Reflection
import qualified Data.Vector as V
import Data.Proxy      -- from tagged
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



getUnique :: Ord k => [k] -> TBData k a -> TBIndex  a
getUnique ks (m,v) = Idex .  fmap snd . L.sortBy (comparing ((`L.elemIndex` ks).fst)) .  getUn (Set.fromList ks) $ (m,v)

getIndex :: Ord k => TBData k a -> TBIndex  a
getIndex (m,v) = Idex .  fmap snd . L.sortBy (comparing ((`L.elemIndex` (_kvpk m)).fst)) .  getPKL $ (m,v)

getBounds :: (Ord k, Ord a) => [TBData k a] -> Maybe [Interval (FTB a)]
getBounds [] = Nothing
getBounds ls = Just $ zipWith  (\i j -> (ER.Finite i,True) `interval` (ER.Finite j,False)) l u
  where Idex l = getIndex (head ls)
        Idex u = getIndex (last ls)

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
  loga :: f -> Tangent f
  expa :: Tangent f -> f
  subtraction :: f -> f -> Tangent f
  addition :: f -> Tangent f -> f

class Positive f where
  notneg :: f -> f


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

instance Affine Int where
  type Tangent Int = Int
  loga  = id
  expa = id
  subtraction = (-)
  addition = (+)


instance Affine Showable where
  type Tangent Showable = DiffShowable
  loga (SNumeric t) =  DSInt $ loga t
  loga (SText t) =  DSText $ loga (T.unpack t)
  loga (SDouble t) =  DSDouble $ t
  loga (SDate t) =  DSDays  (diffDays  t (ModifiedJulianDay 0))
  loga (STimestamp t) =  DSDiffTime (diffUTCTime (localTimeToUTC utc t) (UTCTime (ModifiedJulianDay 0) 0))
  loga (SGeo (SPosition t)) =  DSPosition (loga t)
  loga i = errorWithStackTrace (show i)
  expa (DSInt t) =  SNumeric $ expa t
  expa (DSText t) =  SText $ T.pack $ expa t
  expa (DSDouble t) =  SDouble $ t
  expa (DSDays t) =  SDate $ addDays t (ModifiedJulianDay 0)
  expa (DSDiffTime t) =  STimestamp $ utcToLocalTime utc $ addUTCTime  t (UTCTime (ModifiedJulianDay 0) 0)
  expa (DSPosition t) =  SGeo $ SPosition (expa t)
  expa i = errorWithStackTrace (show i)
  subtraction = diffS
    where
      diffS :: Showable -> Showable -> DiffShowable
      diffS (SNumeric t) (SNumeric o) = DSInt $ subtraction o t
      diffS (SText t) (SText o) = DSText $ subtraction (T.unpack o) (T.unpack t)
      diffS (SDouble t) (SDouble o) = DSDouble $ o -t
      diffS (STimestamp i ) (STimestamp j) = DSDiffTime (diffUTCTime (localTimeToUTC utc j) (localTimeToUTC utc  i))
      diffS (SDate i ) (SDate j) = DSDays (diffDays j i)
      diffS (SGeo(SPosition s )) (SGeo(SPosition b)) = DSPosition $ subtraction s b
      diffS a b  = errorWithStackTrace (show (a,b))
      {-# INLINE diffS #-}
  {-# INLINE subtraction #-}
  addition (SNumeric v) (DSInt t) = SNumeric  $ addition v  t
  addition (SText v) (DSText t) = SText $ T.pack $ addition (T.unpack v) t
  addition (SDouble v) (DSDouble t) = SDouble $ v + t
  addition (STimestamp  v) (DSDiffTime t) = STimestamp $ utcToLocalTime utc $ addUTCTime t (localTimeToUTC utc v)
  addition (SDate v) (DSDays t) = SDate $ addDays t v
  addition (SGeo(SPosition  v )) (DSPosition t ) = SGeo(SPosition $ addition v t)
  addition i j = errorWithStackTrace (show (i,j))
  {-# INLINE addition #-}

instance Positive DiffShowable where
  notneg = notNeg

transEither
  :: (Either a (FTB b) -> Either a (FTB b) -> c)
  -> Either [a] (TBIndex b)
  -> Either [a] (TBIndex b)
  -> [c]
transEither f  i j  =
    case (i,j) of
        (Right (Idex i) ,Right (Idex j)) -> co (Right <$> i) (Right <$> j)
        (Left (i) ,Left (j)) -> co (Left <$> i) (Left <$> j)
        (Right (Idex i) ,Left (j)) -> co  (Right <$> i) (Left <$> j)
        (Left (i) ,Right (Idex j)) -> co (Left <$> i) (Right <$> j)
  where co l i =  zipWith f l i
{-# INLINE transEither #-}

instance ( Predicates (FTB v)) => Predicates (TBIndex v ) where
  type (Penalty (TBIndex v)) = [Penalty (FTB v)]
  type Query (TBIndex v) = (TBPredicate Int v)
  type Node (TBIndex v) = [Node (FTB v)]
  consistent i j = (\b -> if null b then False else  F.all id b) $ transEither consistent i j

  match (WherePredicate a)  (Right (Idex v)) = go a
    where
      -- Index the field and if not found return true to row filtering pass
      go (AndColl l) = F.all go l
      go (OrColl l ) = F.any go  l
      go (PrimColl (IProd _ [i],op)) = maybe True (match op .Right)  (v `atMay` i)
  match (WherePredicate a)  (Left v) = go a
    where
      -- Index the field and if not found return true to row filtering pass
      go (AndColl l) = F.all go l
      go (OrColl l ) = F.any go  l
      go (PrimColl (IProd _ [i],op)) = maybe True (match op . node )  (v `atMay` i)
      node :: Node (FTB v) -> Either (Node (FTB v )) (FTB v)
      node i = Left i


  bound (Right (Idex i)) =  fmap (bound .Right)i
  bound (Left i) =   i
  merge = transEither merge

  penalty = transEither penalty
  {-# INLINE penalty #-}

projIdex (Idex v) = F.toList v

instance (Predicates (TBIndex  a )  ) => Monoid (G.GiST (TBIndex  a)  b) where
  mempty = G.empty
  mappend i j
    | G.size i < G.size j = ins  j (getEntries i )
    | otherwise  = ins  i (getEntries j )
    where ins = foldl' (\j i -> G.insert i (3,6) j)


-- Attr List Predicate


checkPred v (WherePredicate l) = checkPred' v l

checkPred' v (AndColl i ) = F.all  (checkPred' v)i
checkPred' v (OrColl i ) = F.any (checkPred' v) i
checkPred' v (PrimColl i) = indexPred i v

type ShowableConstr  a = (ConstantGen (FTB a ),Affine a,Positive (Tangent a),Semigroup (Tangent a),Ord (Tangent a),Ord a )
indexPred :: (Show k ,ShowableConstr a , Show a,Ord k) => (Access k ,AccessOp a) -> TBData k a-> Bool
indexPred (Many i,eq) a= all (\i -> indexPred (i,eq) a) i
indexPred (n@(Nested k nt ) ,eq) r
  = case  indexField n r of
    Nothing -> False
    Just i ->  recPred $ indexPred (nt , eq ) <$> _fkttable  i
  where
    recPred (TB1 i ) = i
    recPred (LeftTB1 i) = maybe False recPred i
    recPred (ArrayTB1 i) = any recPred (F.toList i)
    recPred (DelayedTB1 i) = maybe False recPred i
    recPred (SerialTB1 i) = maybe False recPred i
    recPred i = errorWithStackTrace (show i)
indexPred (a@(IProd _ _),eq) r =
  case indexField a r of
    Nothing ->  False
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
  where t1 = filter' (flip checkPred (fst pred)) . maybe G.getEntries (\p -> G.query (mapPredicate (\i -> justError "no predicate" $ L.elemIndex i pk)  $ WherePredicate p)) (splitIndexPK b pk)

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

instance Predicates Showable where
  type Node Showable = Showable
  type Penalty Showable = DiffShowable
  type Query Showable = Showable
  penalty (Right (SNumeric i)) (Right (SNumeric j)) = DSInt $ i -  j
  penalty (Right (SDouble i)) (Right  (SDouble j)) = DSDouble $ i  - j
  -- penalty (Left i) (Right  (SDouble j)) = DSDouble $ i  - j


instance (ConstantGen (FTB v) , Positive (Tangent v), Semigroup (Tangent v),Ord (Tangent v),Ord v,Show v , Affine v ) => Predicates (FTB v) where
  type Node (FTB v) = Interval.Interval (FTB v)
  type Penalty (FTB v) = ER.Extended (Tangent v)
  type Query (FTB v) = AccessOp v
  consistent (Left i ) (Left j) = not . Interval.null $  j `Interval.intersection` i
  consistent (Right i ) (Left j) = cons i j
      where
        cons j@(TB1 _)  i  = j `Interval.member` i
        cons (LeftTB1 i) j = fromMaybe True $ (flip cons j ) <$>  i
        cons (ArrayTB1 i)  j  = F.any (flip cons j) i
        cons (IntervalTB1 i) j = not $ Interval.null $  j `Interval.intersection` i
        cons (SerialTB1 i) j = fromMaybe True $ (flip cons j ) <$>  i
        cons (DelayedTB1 i) j = fromMaybe True $ (flip cons j ) <$>  i
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
        cons (SerialTB1 i) (SerialTB1 j ) = fromMaybe True $ liftA2 cons j  i
        cons (SerialTB1 i) j = fromMaybe True $ (flip cons j ) <$>  i
        cons j (SerialTB1 i)  = fromMaybe True $ (cons j ) <$>  i
        cons i (LeftTB1 j) = fromMaybe True $(cons i ) <$>  j
        cons i j  = errorWithStackTrace (show (i,j))
  consistent  i j  = errorWithStackTrace (show (i,j))

  match i (Left j) = mar i  j
    where
      mar (Left v)  j  = ma  v  j
        where
          ma (i@(TB1 _) ,op)  j  = i `Interval.member` j
          ma (DelayedTB1 j ,v)   i   = fromMaybe False ((\a -> ma (a,v) i) <$> j)
          ma (SerialTB1 j ,v)   i   = fromMaybe False ((\a -> ma (a,v) i) <$> j)
          ma (LeftTB1 j ,v)   i   = fromMaybe False ((\a -> ma (a,v) i) <$> j)
          ma (ArrayTB1 i,Flip (AnyOp o))  j  = F.any (\i -> ma (i,o)  j ) i
          ma (IntervalTB1 i ,Contains) j = j `Interval.isSubsetOf` i
          ma (IntervalTB1 j ,Flip Contains) (i)  = j `Interval.isSubsetOf` i
          ma (IntervalTB1 j ,IntersectOp) (i)  = not $ Interval.null $ j `Interval.intersection` i
          ma  i j =errorWithStackTrace (show (i,j))
      mar (Right v) j = ma v j
        where
          ma  (Not i)   j   = not $ ma i   j
          ma  IsNull    j   = False
          ma  (BinaryConstant op e )  v  = mar (Left (generate e,op))  v
          ma  (Range b pred)  j   = match  (Right  pred) $ Right $ LeftTB1 $ fmap TB1 $ unFin $ if b then upperBound j else lowerBound j
          ma  i j =errorWithStackTrace (show (i,j))
      mar i j = errorWithStackTrace $ show (i,j)
  match i (Right j) = mar i j
    where
      mar (Left v)  j  = ma  v  j
        where
          -- ma v a j | traceShow (v,a,j) False = undefined
          ma  (v,Flip (Flip op)) j  = ma (v,op)   j
          ma  v (LeftTB1 j) = fromMaybe False (ma v  <$> j)
          ma  v (SerialTB1 j) = fromMaybe False (ma v  <$> j)
          ma  v (DelayedTB1 j) = fromMaybe False (ma v  <$> j)
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
          ma i  j =  errorWithStackTrace ("no ma = " <> show (i,j))
      mar (Right i ) j =ma i j
        where
          ma  (Not i) j  = not $ ma i   j
          ma  IsNull  (LeftTB1 j)   = isNothing j
          ma  IsNull   j   = False
          ma  (BinaryConstant op e )  v  = mar (Left (generate e,op))  v
          ma  (Range b pred)  (IntervalTB1 j)   = ma  pred $ LeftTB1 $ fmap TB1 $ unFin $ if b then upperBound j else lowerBound j
          ma i  j = errorWithStackTrace ("no ma =" ++ show (i,j))
  match x  z = errorWithStackTrace ("no match = " <> show (x,z))

  bound (Right i) =  (ER.Finite i,True) `interval` (ER.Finite i,True)
  bound (Left i) =  i
  {-# INLINE bound #-}
  merge (Left i ) (Left j)  =  min (lowerBound' i) (lowerBound' j) `interval` max (upperBound' j) (upperBound' i)
  merge (Right i ) (Left j)  =  min (minP i)   (lowerBound' j) `interval` max (maxP i) (upperBound' j)
  merge (Left j ) (Right i)  =  min (minP i)   (lowerBound' j) `interval` max (maxP i) (upperBound' j)
  merge (Right i ) (Right j) =  (min (minP i) (minP j)) `interval` (max (maxP i) (maxP j) )
  {-# INLINE merge #-}
  penalty (Left i)  (Left j)
    = (maybe ER.PosInf ER.Finite $ fmap notneg $ liftA2 subtraction (unFin (fst $ lowerBound' j  )) (unFin (fst $ lowerBound' i)))
    <> (maybe ER.PosInf ER.Finite $ fmap notneg $ liftA2 subtraction (unFin (fst $ upperBound' i  )) (unFin (fst $ upperBound' j)))
  penalty (Right i  ) (Left j)
    = (maybe ER.PosInf ER.Finite $ fmap notneg $ liftA2 subtraction (unFin (fst $ lowerBound' j  )) (unFin (fst $ minP i)))
    <> (maybe ER.PosInf ER.Finite $ fmap notneg $ liftA2 subtraction (unFin (fst $ maxP i  )) (unFin (fst $ upperBound' j)))
  penalty (Right p1) (Right p2) =  (maybe ER.PosInf ER.Finite $ fmap notneg $ liftA2 subtraction (unFin $ fst $ minP p2) (unFin $ fst $ minP p1)) <>  (maybe ER.PosInf ER.Finite $ fmap notneg $ liftA2 subtraction (unFin $ fst $ maxP p1)  (unFin $ fst $ maxP p2))
  penalty (Left i  ) (Right j)
    = (maybe ER.PosInf ER.Finite $ fmap notneg $ liftA2 subtraction  (unFin (fst $ minP j)) (unFin (fst $ lowerBound' i  )))
    <> (maybe ER.PosInf ER.Finite $ fmap notneg $ liftA2 subtraction  (unFin (fst $ upperBound' i)) (unFin (fst $ maxP j  )))
  {-# INLINE penalty #-}


newtype Number a = Number a deriving (Num,Eq,Ord,Generic)

instance NFData a => NFData (Number a)

instance (NFData a,Ord a ,Num a) => Predicates (Number a) where
  type Penalty (Number a) = ER.Extended (Number a)
  type Node (Number a) = Interval (Number a)
  consistent (Right i) (Right j) = i == j
  consistent (Left i) (Right j) =  Interval.member j  i
  consistent (Right i) (Left j) =  Interval.member i j
  consistent (Left i) (Left j) =  not $ Interval.null $ Interval.intersection i j
  penalty (Right i) (Right j)
    = ER.Finite (i - j)
  penalty (Left i) (Left j)
    = (maybe ER.PosInf (ER.Finite . max 0) $ liftA2 (-) (unFin' (fst $ lowerBound' j  )) (unFin' (fst $ lowerBound' i)))
    +  (maybe ER.NegInf (ER.Finite . max 0) $ liftA2 (-) (unFin' (fst $ upperBound' i  )) (unFin' (fst $ upperBound' i)))
  penalty (Left i) (Right j)
    = (maybe ER.PosInf (ER.Finite . max 0) $ liftA2 (-) (Just j) (unFin' (fst $ lowerBound' i)))
    +  (maybe ER.NegInf (ER.Finite . max 0) $ liftA2 (-) (unFin' (fst $ upperBound' i  )) (Just j))
  penalty  (Right j) (Left i)
    = (maybe ER.PosInf (ER.Finite . max 0) $ liftA2 (-) (unFin' (fst $ lowerBound' i)) (Just j))
    +  (maybe ER.NegInf (ER.Finite . max 0) $ liftA2 (-) (Just j) (unFin' (fst $ upperBound' i  )))

  bound (Right i) =  (ER.Finite i,True) `interval` (ER.Finite i,True)
  bound (Left i) = i
  {-# INLINE bound #-}
  merge (Left i ) (Left j)  =  min (lowerBound' i) (lowerBound' j) `interval` max (upperBound' j) (upperBound' i)
  merge (Right i ) (Left j)  =  min (ER.Finite i,True)   (lowerBound' j) `interval` max (ER.Finite i , True)  (upperBound' j)
  merge (Left j ) (Right i)  =  min (ER.Finite i,True)   (lowerBound' j) `interval` max (ER.Finite i , True)  (upperBound' j)
  merge (Right i ) (Right j) =  (ER.Finite $ min i j ,True ) `interval` (ER.Finite $ max i j , True)
  {-# INLINE merge #-}


unFin' (Interval.Finite i) = Just i
unFin' i = Nothing



unFin (Interval.Finite (TB1 i) ) = Just i
unFin o = Nothing -- errorWithStackTrace (show o)



minP ((IntervalTB1 i) ) = lowerBound' i
minP (i@(TB1 _) ) = (ER.Finite $ i,True)
minP (LeftTB1 (Just i) ) = minP i
minP (ArrayTB1 i) = minP$   F.minimum i
minP i = errorWithStackTrace (show i)

maxP ((IntervalTB1 i) ) = upperBound' i
maxP (i@(TB1 _) ) = (ER.Finite $ i,True)
maxP (LeftTB1 (Just i) ) = minP i
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

