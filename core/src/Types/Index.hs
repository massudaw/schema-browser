{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Types.Index
  ( Range(..)
  , Positive(..)
  , Affine(..)
  , Predicate(..)
  , DiffShowable(..)
  , IndexConstr
  , toList
  , lookup
  , fromList
  , fromList'
  , filter
  , filter'
  , getIndex
  , getBounds
  , getUnique
  , getUniqueM
  , notOptional
  , notOptionalM
  , tbpred
  , tbpredM
  , unFin
  , Node(..)
  , indexParam
  , keys
  , queryCheck
  , getOp
  , PathIndex(..)
  , AttributePath(..)
  , mapAttributePath
  , indexPred
  , indexFTB
  , recFTB
  , checkPred
  , checkPredId
  , projectIndex
  , filterIndex
  , filterRows
  , cinterval
  , PathTID(..)
  , splitIndexPKB
  , alterWith
  , splitIndexPK
  , module G
  ) where

import Control.Applicative
import Control.DeepSeq
import Control.Monad
import Data.Binary
import GHC.Generics
import Data.Char
import Data.Either
import qualified Data.ExtendedReal as ER
import Data.Foldable (foldl')
import Control.Arrow (first)
import qualified Data.Foldable as F
import Data.GiST.BTree hiding (Contains, Equals)
import Data.GiST.GiST as G
import qualified Data.Interval as Interval
import Data.Interval
       (Interval, interval, lowerBound, lowerBound', upperBound,
        upperBound')
import qualified Data.List as L
import qualified Data.Map.Strict as M
import Data.Maybe
import Data.Ord
import Data.Semigroup
import qualified Data.Set as Set
import qualified Data.Text as T
import Data.Time
import qualified NonEmpty as Non
import qualified Data.Sequence.NonEmpty as NonS
import Prelude hiding (filter, lookup)
import Safe
import Debug.Trace
import qualified Data.Sequence as S
-- import Step.Host
import Types.Common
import Types.Primitive
import Step.Common
import Utils

--- Row Level Predicate

cinterval ::Ord a=> a -> a -> Interval a
cinterval i j = ER.Finite i Interval.<=..<= ER.Finite j

uinterval ::Ord a=> ER.Extended a -> ER.Extended a -> Interval a
uinterval i j = i Interval.<=..<= j

getUnique :: (NFData a , Show k ,Ord k) => [Rel k] -> TBData k a -> TBIndex  a
getUnique ks = Idex . fmap snd . L.sortBy (comparing ((pkIndexM  ks).simplifyRel . fst)) .  getUn  (Set.fromList ks) 

getUniqueM :: (NFData a , Show k, Ord k) => [Rel k] -> TBData k a -> Maybe (TBIndex a)
getUniqueM un = notOptionalM . getUnique  un

getIndex :: (NFData a , Show k ,Ord k ) => KVMetadata k -> TBData k a -> TBIndex  a
getIndex m  = getUnique  (_kvpk m) 

getBounds :: (NFData a , Show k,Ord k, Ord a) => KVMetadata k -> [TBData k a] -> Interval (TBIndex a)
getBounds m [] = (ER.NegInf,False) `interval` (ER.PosInf,False)
getBounds m ls = (ER.Finite i,True) `interval` (ER.Finite j,False)
  where i = getIndex m (head ls)
        j = getIndex m (last ls)

notOptionalM :: TBIndex a -> Maybe (TBIndex a)
notOptionalM (Idex m) =
  fmap Idex . join . fmap nonEmpty . traverse unSOptional $ m

notOptional :: Show a => TBIndex a -> TBIndex a
notOptional m = justError ("cant be empty " <> show m) . notOptionalM $ m

tbpredM :: (NFData a , Show k, Ord k) => KVMetadata k -> TBData k a -> Maybe (TBIndex a)
tbpredM m = notOptionalM . getUnique  (_kvpk m)

tbpred :: (NFData a , Show k, Show a, Ord k) => KVMetadata k -> TBData k a -> TBIndex a
tbpred m = notOptional . getIndex m

instance Affine a => Affine [a] where
  type Tangent [a] = [Tangent  a]
  subtraction = zipWith subtraction

instance Affine a => Affine (ER.Extended a ) where
  type Tangent (ER.Extended a) = ER.Extended (Tangent  a)
  subtraction (ER.Finite i) (ER.Finite j) = ER.Finite $ subtraction i j
  subtraction ER.NegInf  i = ER.NegInf
  subtraction ER.PosInf  i = ER.PosInf
  subtraction i  ER.PosInf  = ER.NegInf
  subtraction i  ER.NegInf = ER.PosInf
  subtraction i j = error "could not match"

notNeg (DSPosition l)
  | otherwise = DSPosition l
notNeg (DSText l)
  | L.null dp || head dp < 0 = def
  | otherwise = DSText l
  where
    dp = dropWhile (== 0) l
    def = DSText []
notNeg (DSDouble l)
  | l < 0 = DSDouble 0
  | otherwise = DSDouble l
notNeg (DSInt l)
  | l < 0 = DSInt 0
  | otherwise = DSInt l
notNeg (DSDays l)
  | l < 0 = DSDays 0
  | otherwise = DSDays l
notNeg (DSDiffTime l)
  | l < 0 = DSDiffTime 0
  | otherwise = DSDiffTime l
notNeg i = error (show i)

instance Semigroup a => Semigroup (ER.Extended a) where
  (ER.Finite i) <> (ER.Finite j) = ER.Finite (i <> j)
  ER.NegInf <> j = ER.NegInf
  j <> ER.NegInf = ER.NegInf
  i <> ER.PosInf = ER.PosInf
  ER.PosInf <> _ = ER.PosInf

instance Semigroup DiffPosition where
  DiffPosition2D (x, y) <> DiffPosition2D (i, j) = DiffPosition2D (x + i, y + j)
  DiffPosition3D (x, y, z) <> DiffPosition3D (i, j, k) =
    DiffPosition3D (x + i, y + j, z + k)
  a <> b = error ("differror: " ++ show (a, b))

instance Semigroup DiffShowable where
  (<>) = appendDShowable
    where
      appendDShowable :: DiffShowable -> DiffShowable -> DiffShowable
      appendDShowable (DSInt l) (DSInt j) = DSInt $ l + j
      appendDShowable (DSText l) (DSText j) =
        DSText $
        zipWith (+) l j <> L.drop (L.length j) l <> L.drop (L.length l) j
      appendDShowable (DSDouble l) (DSDouble j) = DSDouble $ l + j
      appendDShowable (DSDays l) (DSDays j) = DSDays $ l + j
      appendDShowable (DSDiffTime l) (DSDiffTime j) = DSDiffTime $ l + j
      appendDShowable (DSPosition x) (DSPosition y) = DSPosition $ x <> y
      appendDShowable a b = error ("append " <> show (a, b))

class Affine f where
  type Tangent f
  subtraction :: f -> f -> Tangent f

class Positive f where
  notneg :: f -> f

newtype DiffString =
  DiffString String

instance Affine DiffString where
  type Tangent DiffString = [Int]
  subtraction (DiffString i) (DiffString j) = diffStr i j
    where
      diffStr :: String -> String -> [Int]
      diffStr (a:as) (b:bs) = (ord b - ord a) : diffStr as bs
      diffStr bs [] = ord <$> bs
      diffStr [] bs = ord <$> bs
      diffStr [] [] = []

instance Affine Position where
  type Tangent Position = DiffPosition
  subtraction (Position  x y z ) (Position  a b c ) = DiffPosition3D (a-x,b-y,c-z)
  subtraction (Position2D  x y ) (Position2D  a b ) = DiffPosition2D (a-x,b-y)

instance Affine Int where
  type Tangent Int = Int
  subtraction = (-)


instance Affine Showable where
  type Tangent Showable = DiffShowable
  subtraction = diffS
    where
      diffS :: Showable -> Showable -> DiffShowable
      diffS (SNumeric t) (SNumeric o) = DSInt $ subtraction o t
      diffS (SText t) (SText o) = DSText $ subtraction (DiffString $ T.unpack o) (DiffString $T.unpack t)
      diffS (SDouble t) (SDouble o) = DSDouble $ o -t
      diffS (STime (STimestamp i )) (STime (STimestamp j)) = DSDiffTime (diffUTCTime j i)
      diffS (STime (SDate i )) (STime (SDate j)) = DSDays (diffDays j i)
      diffS (SGeo(SPosition s )) (SGeo(SPosition b)) = DSPosition $ subtraction s b
      diffS a b  = error (show ("Diffs",a,b))

instance Positive DiffShowable where
  notneg = notNeg


instance (Show v,Affine v ,Range v, Positive (Tangent v), Semigroup (Tangent v),Ord v, Ord (Tangent v),Predicates (FTB v)) => Predicates (TBIndex v ) where
  type (Penalty (TBIndex v)) = ER.Extended [Tangent v]
  type Query (TBIndex v) = (TBPredicate Int v)
  data Node (TBIndex v) = TBIndexNode {unTBIndexNode :: Interval [v] } deriving (Eq,Ord,Show)
  consistent i j =
      case (i,j) of
        (Right (Idex i) ,Right (Idex j)) -> F.foldl' (&&) True (zipWith (\i j -> consistent (Right i) (Right j)) i j)
        (Left (TBIndexNode i) ,Left (TBIndexNode j)) -> not $ Interval.null $ i `Interval.intersection` j
        (Right i@(Idex _ ) ,Left (TBIndexNode j)) ->not $ Interval.null $ unTBIndexNode (bound i) `Interval.intersection` j
        (Left (TBIndexNode i) ,Right j@(Idex _)) -> not $ Interval.null $ unTBIndexNode (bound j) `Interval.intersection` i

  -- This limit to 100 the number of index fields to avoid infinite lists
  origin = TBIndexNode Interval.empty
  bound (Idex i) =  TBIndexNode  $ (maybe ER.NegInf ER.Finite $ traverse ( unFin . fst . lowerBound') v ) `uinterval` (maybe ER.PosInf ER.Finite $ traverse (unFin . fst .upperBound') v)
    where v = fmap unTB1 . pureR <$> i
  match (WherePredicate a)  (Right (Idex v)) =  if L.null v then  False else go a
    where
      -- Index the field and if not found return true to row filtering pass
      go (AndColl l) = F.all go l
      go (OrColl l ) = F.any go l
      go (PrimColl (ix@(Inline i),op)) = match (justError ("cant find " ++ show i) $ M.lookup ix $ M.fromList op) (Right  $ fromMaybe (error $ "no index" ++ show (v,a,i))  $ atMay v  i)
  match (WherePredicate a)  (Left (TBIndexNode v)) = F.all id $ fst $ go a ([],[] `cinterval`  [])
    where
      -- Index the field and if not found return true to row filtering pass

      access (PrimColl (Inline  i,_) )  = i
      access (AndColl l) = minimum $ fmap  access l
      access (OrColl l) = minimum $ fmap  access l
      access i = error (show i)

      go :: BoolCollection
                (Rel Int, [(Rel Int,Either (FTB v, BinaryOperator) UnaryOperator)])
              -> ([Bool], Interval [v]) -> ([Bool], Interval [v])
      go (AndColl l) prev = (fmap (all id) bl ,last il)
        where (bl,il) = unzip $ scanl (flip go) prev (L.sortBy (comparing access) l)
      go (OrColl l ) prev = (fmap (any id) bl , foldl Interval.hull  Interval.empty il)
        where (bl,il) = unzip $ flip go prev <$> (L.sortBy (comparing access)l)
      go (PrimColl (irel@(Inline  i),ops)) (b,prev)
        = case  getOp irel ops of
            Left (f,op) ->
                let
                  efields =  mergeInterval (liftA2 (\i j -> i ++ [j]) ) prev (fmap unTB1 $ pureR f )
                in (b ++ [not $ Interval.null $ Interval.intersection  efields (fmap (take (i+1)) v)] ,efields)
            j -> (b,prev)


  -- bound (Idex i) =  TBIndexNode $ (i,True) `Interval.interval` (i,True)
  --merge (TBIndexNode i) (TBIndexNode j) = TBIndexNode $ appendRA i j
  merge (TBIndexNode i) (TBIndexNode j) = TBIndexNode $ Interval.hull i j
  penalty (TBIndexNode i ) (TBIndexNode j)
    = (fmap (fmap notneg) $ subtraction (fst (lowerBound' j  )) (fst $ lowerBound' i))
    <> (fmap (fmap notneg) $ subtraction (fst $ upperBound' i  ) (fst $ upperBound' j))

mergeInterval f i j =  (f (lowerBound i)  (lowerBound j),True) `interval` (f (upperBound i) (upperBound j),True)

projIdex (Idex v) = F.toList v

instance Applicative ER.Extended where
  pure  = ER.Finite
  ER.Finite i <*>  ER.Finite j = ER.Finite $ i j
  i <*> ER.PosInf = ER.PosInf
  i <*> ER.NegInf = ER.NegInf
  ER.PosInf <*> i = ER.PosInf
  ER.NegInf<*> i = ER.NegInf


instance Predicates (TBIndex  a )  => Semigroup (G.GiST (TBIndex  a)  b) where
  i <> j
    | G.size i < G.size j = ins  j (getEntries i )
    | otherwise  = ins  i (getEntries j )
    where ins = foldl' (\j i -> G.insertL i indexParam j)


instance Predicates (TBIndex  a )  => Monoid (G.GiST (TBIndex  a)  b) where
  mempty = G.empty

indexParam :: (Int,Int)
indexParam = (4,8)

-- Attr List Predicate


type IndexConstr k a = (Ord k, Ord a, Ord (Tangent a), Show a, Show k,
      Semigroup (Tangent a), Positive (Tangent a), Affine a,
       Range a, Fractional a)

checkPredId
  :: (Ord k, Ord a, Ord (Tangent a), Show a, Show k,
      Semigroup (Tangent a), Positive (Tangent a), Affine a,
       Range a, Fractional a) =>
     KV k a
     -> TBPredicate k a -> Maybe [AttributePath k ()]
checkPredId v (WherePredicate l) = checkPredIdx  v l
  where
    checkPredIdx v (AndColl i ) = fmap (L.nub . foldr1 (\ i j -> concat $ [unifyPaths a b | a <-i , b <- j ])) $ allMaybes $ checkPredIdx v <$> i
    checkPredIdx v (OrColl i ) = fmap concat $ nonEmpty $ catMaybes $ checkPredIdx v <$>  i
    checkPredIdx v (PrimColl i) = fmap pure (indexPredIx i v)

-- When we search for two independent paths inside an AND predicate we later need to 
-- intersect both branches filtering only identical paths this does not happen in the predicate
-- evaluation because we are just reducing to a Bool 
tryAll :: Eq a => (a -> a -> [a]) ->  Union  a -> Union a -> [Union a]
tryAll f (Many i ) (Many j ) =  Many <$>  [f a b | a <- i , b <- j ]

unifyPaths :: (Show k, Eq k) => AttributePath k () -> AttributePath k () -> [AttributePath k ()]
unifyPaths (PathInline i j ) (PathInline k l ) | i == k = PathInline i <$> unifyPathsIndex (tryAll unifyPaths) j l 
unifyPaths (PathForeign i j ) (PathForeign k l ) | i == k = PathForeign i  <$> unifyPathsIndex (tryAll unifyPaths) j l 
unifyPaths i@(PathAttr k _ ) j@(PathAttr l _ ) | k == l = [i]
unifyPaths i@(PathAttr _ _ ) j@(PathAttr _ _ ) = [i,j]
unifyPaths _ _ = [] 

unifyPathsIndex :: (Eq a, Eq b) => (a -> a -> [a]) -> PathIndex b a -> PathIndex b a -> [PathIndex b a]
unifyPathsIndex f (ManyPath i)  (ManyPath l ) = catMaybes . fmap (fmap ManyPath . Non.nonEmpty ) $ [ unifyPathsIndex f a b | a <- F.toList i , b <- F.toList l ]
unifyPathsIndex f (NestedPath i j ) (NestedPath k l ) | i == k = NestedPath i <$> unifyPathsIndex f j l 
unifyPathsIndex f (TipPath i ) (TipPath j )  = TipPath <$> f i j 
unifyPathsIndex f i j = [] 


checkPred
  :: (Ord k, Ord a, Ord (Tangent a), Show a, Show k,
      Semigroup (Tangent a), Positive (Tangent a), Affine a,
       Range a, Fractional a) =>
     KV k a -> TBPredicate k a -> Bool
checkPred v (WherePredicate l) = checkPred' v l
  where
    checkPred' v (AndColl i ) = F.all (checkPred' v) i
    checkPred' v (OrColl i ) = maybe False (F.any (checkPred' v)) (nonEmpty i)
    checkPred' v (PrimColl i) = indexPred i v

type ShowableConstr  a = (Fractional a ,Range a,Affine a,Positive (Tangent a),Semigroup (Tangent a),Ord (Tangent a),Ord a )


data PathIndex  a b
  = ManyPath (Non.NonEmpty (PathIndex a b))
  | NestedPath a (PathIndex a b)
  | TipPath b
  deriving(Eq,Ord,Show,Functor,Generic)

mapAttributePath :: (a -> b) -> AttributePath a i -> AttributePath b i
mapAttributePath f (PathAttr k l) = PathAttr (f k ) l
mapAttributePath f (PathInline k l ) = PathInline (f k) (fmap (fmap (mapAttributePath f ) )l)
mapAttributePath f (PathForeign k l ) = PathForeign (fmap f <$> k) (fmap (fmap (mapAttributePath f ) )l)

data AttributePath  k b
  = PathAttr k (PathIndex PathTID b)
  | PathInline k (PathIndex PathTID  (Union (AttributePath k b)))
  | PathForeign [Rel k ] (PathIndex PathTID (Union (AttributePath k b)))
  deriving(Eq,Ord,Show,Functor,Generic)

recFTB f i = fmap (Many . pure) <$>  recFTB  i
  where 
    recFTB (TB1 i ) = TipPath <$> f i
    recFTB (LeftTB1 i) = fmap (NestedPath PIdOpt )$  join $ traverse recFTB i
    recFTB (ArrayTB1 i) = fmap ManyPath  $ Non.nonEmpty $ catMaybes $ F.toList $ NonS.imap (\ix i -> fmap (NestedPath (PIdIdx ix )) $ recFTB i ) i
    recFTB i = error (show ("IndexPredIx",i))

indexFTB  
  :: (Show k ,Show a,Ord k) 
  => [Rel k ] 
  -> (Rel k -> TBData k a -> Maybe (AttributePath k v )) 
  -> Rel k 
  -> TBData k a 
  -> Maybe (AttributePath k v) 
-- indexFTB t _ (RelAccess k n) v | 
--  (if (isNothing $ kvLookup k v ) 
--    then (trace ("indexFTB: " <>  (L.intercalate "." $ renderRel <$> reverse t)<> " | " <> renderRel k <> " | " <> renderRel n <>  (L.replicate 100 '=') <> show (kvLookup k v) <> (L.replicate 100 '=')<>  show ( renderRel <$> kvkeys v)<> (L.replicate 100 '=') )) else id ) False = undefined
indexFTB t f (RelAccess (Inline key) nt)  r 
 = do 
   i <- refLookup (Inline key) r 
   PathInline key <$> recFTB (indexFTB (Inline key : t) f nt) i
indexFTB t f n@(RelAccess nk nt )  r
 = do
    i <- relLookup nk r 
    PathForeign (relUnComp nk)  <$> recFTB allRefs i
  where
    allRefs (TBRef (i,v)) 
      =  case nt of 
        Rel _ _ _ -> indexFTB (nk : t) f nt i 
        i -> indexFTB (nk :t) f nt v 
indexFTB t f a  r
  =  f a r

indexPredIx :: (Show k ,ShowableConstr a , Show a,Ord k) => (Rel k ,[(Rel k ,(AccessOp a))]) -> TBData k a-> Maybe (AttributePath k ()) 
indexPredIx  (r,eqs) v
  =  indexFTB [] (indexInline eqs) r v

indexInline :: forall a k .(Show k ,ShowableConstr a , Show a,Ord k) => [(Rel k ,(AccessOp a))] -> Rel k -> TBData k a -> Maybe (AttributePath k ())
-- indexInline i j k | traceShow (i,j) False = undefined
  {-indexInline eqs key 
  | L.any isRel rels = 
    where rels = relUnComp key-}
indexInline eqs ik@(Inline key) r = fmap (PathAttr key) . recPred (snd eq)  =<< attrLookup ik (tableNonRef r)
  where
    Just (k,Left eq) = L.find ((==ik).fst) eqs
    recPred eq (LeftTB1 i) = fmap (NestedPath PIdOpt )$  join $ traverse (recPred eq) i
    recPred (Flip (AnyOp eq)) (ArrayTB1 i) = fmap ManyPath  . Non.nonEmpty . catMaybes . F.toList $ NonS.imap (\ix i -> fmap (NestedPath (PIdIdx ix )) $ recPred eq i ) i
    recPred op i = {-traceShow (ik , i, op,fst eq) $-} if match (Left (fst eq,op)) (Right i) then  Just (TipPath ()) else Nothing
indexInline eqs rel r 
  | L.all isRel (relUnComp rel) = fmap (PathForeign (relUnComp rel)) . recPred gop  =<< relLookup rel r 
  | otherwise = Nothing
  where
    gop = foldl1 mergeOp (_relOperator <$> relUnComp rel)
    mergeOp e (Flip (AnyOp n )) = Flip (AnyOp (mergeOp e n))
    mergeOp Equals Equals = Equals

    isRel (Rel _ _ _ ) = True
    isRel _ = False
    recPred eq (LeftTB1 i) = fmap (NestedPath PIdOpt )$  join $ traverse (recPred eq) i
    recPred (Flip (AnyOp eq)) (ArrayTB1 i) = fmap ManyPath  . Non.nonEmpty . catMaybes . F.toList $ NonS.imap (\ix i -> fmap (NestedPath (PIdIdx ix )) $ recPred eq i ) i
    recPred op (TB1 (TBRef (v,_))) =  TipPath . Many <$> allMaybes ( checkAttr v <$> relUnComp rel)
        where 
          checkAttr v (Rel i j k ) = {-traceShow (rel,i, op,fst eq) $ -} if match (Left (fst eq,op)) (Right (justError "no attr" $ attrLookup i v)) then  Just (PathAttr (_relOrigin i )(TipPath ())) else Nothing
              where Just (k,Left eq) = L.find ((==i).fst) eqs


indexPred :: (Show k ,ShowableConstr a , Show a,Ord k) => (Rel k ,[(Rel k,AccessOp a)]) -> TBData k a-> Bool
indexPred (n@(RelAccess k nt ) ,eq) r
  = case refLookup k r of
    Nothing -> False
    Just i  -> recPred $ indexPred (nt , eq) <$> i
  where
    recPred (TB1 i ) = i
    recPred (LeftTB1 i) = maybe False recPred i
    recPred (ArrayTB1 i) = any recPred i
    recPred i = error (show ("RecPred",i))
indexPred ((Rel key _ _ ),eqs) r = indexPred (key ,eqs) r
indexPred (RelComposite l , eqs) r = 
  fromMaybe False $ (recPred matchRel <$> relLookup (relComp l )  r ) <|> (  matchInline <$> kvLookup (_relAccess $ simplifyRel (relComp l)) (tableNonRef r))  
  where
    isRel (Rel _ _ _ ) = True
    isRel _ = False
    matchRel (TBRef (rv, _)) = L.any (\(Rel i _ _) -> indexPred  (i,eqs) rv) (L.filter (\i -> (isRel i) && (not . Set.null . relOutputSet  $ i )) l)
    matchInline (Attr _ v)  = match  eq (Right v) 
      where eq = getOp (_relAccess $ simplifyRel (relComp l)) eqs
    recPred f (TB1  i ) =  f i 
    recPred f (LeftTB1 i) = maybe False (recPred f ) i
    recPred f (ArrayTB1 i) = any (recPred f) i
    recPred f i = error (show ("RecPred",i))

indexPred (a@(Inline key),eqs) r =
  case attrLookup a (tableNonRef r) of
    Just rv ->
      match eq (Right rv)
    Nothing -> False
  where
    eq = getOp a eqs
indexPred i v= error (show (i,v))


getOp  key eqs = maybe (error (" no op" ++ show (key,eqs)) ) snd $  L.find ((==key).fst) eqs

queryCheck :: (Show k,Ord k) => (WherePredicateK k ,[Rel k])-> G.GiST (TBIndex Showable) (TBData k Showable) -> G.GiST (TBIndex  Showable) (TBData k Showable)
queryCheck (WherePredicate b ,pk)
  = case (notPK,isPK) of
      (Just i ,Just l ) ->fromList' . filterIndex i . projectIndex pk l
      (Nothing,Just l ) ->fromList' . projectIndex pk l
      (Just i ,Nothing) ->fromList' . filterIndex i . G.getEntries
      (Nothing,Nothing) ->id
 where
   notPK = fmap WherePredicate $ splitIndexPKB b pk
   isPK = fmap WherePredicate $ splitIndexPK b pk

projectIndex :: (Show k,Ord k) => [Rel k ] -> WherePredicateK k -> G.GiST (TBIndex Showable) a ->  [(a, Node (TBIndex Showable), TBIndex Showable)]
projectIndex pk l g =  G.queryL pred g
  where simplifyPred (WherePredicate l ) = WherePredicate $ fmap (first simplifyRel) l
        pred = mapPredicate (Inline . justError ("no predicate: " ++ (show (pk,l))) . pkIndexM pk .simplifyRel ) (simplifyPred l)

filterIndex l =  L.filter (flip checkPred l . leafValue)
filterRows l =  L.filter (flip checkPred l )

pkIndexM :: (Show a, Ord a) => [Rel a] -> Rel a -> Maybe Int
pkIndexM pk i =   L.elemIndex i (simplifyRel <$> pk)

-- Atomic Predicate

class Range v where
  pureR :: v -> Interval  v
  appendR :: v -> v -> Interval v


instance (Ord v ,Range v) => Range (FTB v ) where
  pureR (TB1 i)  =  fmap TB1 $ pureR i
  pureR (ArrayTB1 xs) =  F.foldl1 appendRI  inters
      where inters = pureR <$> xs
  pureR (IntervalTB1 is) =  is
  pureR (LeftTB1 is) =  maybe Interval.empty  pureR is
  appendR (TB1 i ) (TB1 j) = fmap TB1 $ appendR i j


instance Range Showable where
  pureR i = i `cinterval` i
  appendR (SGeo (SPosition i)) (SGeo (SPosition j)) =
    fmap (SGeo . SPosition) $ mergeP i j
    where
      mergeP (Position2D  i  j ) (Position2D  l  m ) =
        Position2D (min i l)  (min j m) `cinterval` Position2D (max i l)(max j m)
      mergeP (Position  i  j  k) (Position  l  m  n) =
        Position (min i l)(min j m)(min k n) `cinterval`
        Position (max i l)(max j m)(max k n)
  appendR i j = min i j `cinterval` max i j

 
upperRI , lowerRI:: (Ord v, Range v) => [ (Interval v)] -> (ER.Extended   v)
upperRI i  =
  maybe (ER.NegInf ) ER.Finite $ L.foldl1'  (\ i j -> join $ unFin . fst . lowerBound' <$> liftA2 appendR i j ) 
   (unFin . fst . lowerBound' <$> i)
lowerRI i  =
  maybe (ER.NegInf ) ER.Finite $ L.foldl1'  (\ i j -> join $ unFin . fst . upperBound' <$> liftA2 appendR i j ) 
   (unFin . fst . upperBound' <$> i)
    
   


appendRI :: (Ord v, Range v) => Interval v -> Interval v -> Interval v
appendRI i j =
  maybe  (ER.NegInf,True)
    lowerBound'
    (liftA2 appendR (unFin $ fst $ lowerBound' i) (unFin $ fst $ lowerBound' j)) `interval`
  maybe
     (ER.PosInf,True)
     upperBound'
     (liftA2 appendR (unFin $ fst $ upperBound' i) (unFin $ fst $ upperBound' j))

instance ( Range v
         , Positive (Tangent v)
         , Semigroup (Tangent v)
         , Ord (Tangent v)
         , Ord v
         , Show v
         , Affine v
         ) =>
         Predicates (FTB v) where
  data Node (FTB v) = FTBNode { unFTBNode :: Interval.Interval v}
                  deriving (Eq, Ord, Show)
  type Penalty (FTB v) = ER.Extended (Tangent v)
  type Query (FTB v) = AccessOp v
  consistent (Left (FTBNode i)) (Left (FTBNode j)) =
    not . Interval.null $ j `Interval.intersection` i
  consistent (Right i) (Left (FTBNode j)) = consrl i j
    where
      consrl (TB1 j) i = j `Interval.member` i
      consrl (IntervalTB1 i) j =
        not $ Interval.null $ j `Interval.intersection` (fmap unTB1 i)
      consrl (LeftTB1 i) j = fromMaybe True $ (flip consrl j) <$> i
      consrl (ArrayTB1 i) j = F.any (flip consrl j) i
  consistent (Left i) (Right j) = consistent (Right j) (Left i)
  consistent (Right i) (Right j) = cons i j
    where
      cons (TB1 i) (TB1 j) = {-# SCC "tt" #-}i == j
      cons j@(TB1 _) (IntervalTB1 i) = {-# SCC "ti" #-}j `Interval.member` i
      cons (IntervalTB1 i) j@(TB1 _) = {-# SCC "it" #-}j `Interval.member` i
      cons (IntervalTB1 i) (IntervalTB1 j) = {-# SCC "ii" #-}
        not $ Interval.null $ j `Interval.intersection` i
      cons (LeftTB1 i) (LeftTB1 j) = {-# SCC "ll" #-} fromMaybe True $ liftA2 cons j i
      cons (LeftTB1 i) j ={-# SCC "l_" #-}  maybe True (`cons` j) i
      cons i (LeftTB1 j) ={-# SCC "_l" #-} maybe True (cons i) j
      cons (ArrayTB1 i)  j@(TB1 _ ) = {-# SCC "a_" #-}  F.any (`cons` j) i
      cons i@(TB1 _ ) (ArrayTB1 j) = {-# SCC "_a" #-} F.any (cons i) j
      cons i j = i == j 
      cons i j = error (show ("rr", i, j))
  match i (Left (FTBNode j)) = mal i j
    where
      mal (Left v) j = ma v j
        where
          ma (TB1 i, op) j = i `Interval.member` j
          ma (LeftTB1 j, v) i = fromMaybe False ((\a -> ma (a, v) i) <$> j)
          ma (ArrayTB1 i, Flip (AnyOp o)) j = F.any (\i -> ma (i, o) j) i
          ma (IntervalTB1 j, _) (i) =
            not $ Interval.null $ fmap unTB1 j `Interval.intersection` i
          ma (j, IntersectOp) (i) =
            not $ Interval.null $ unFTB (bound j) `Interval.intersection` i
          ma (j, Flip o) (i) = ma (j, o) i
          ma i j = error (show (i, j))
          unFTB (FTBNode i) = i
      mal (Right v) j = ma v j
        where
          ma (Not i) j = not $ ma i j
          ma IsNull j = False
          ma Exists j = True
          ma (Range b pred) j =
            match (Right pred) $
            Right $
            LeftTB1 $
            fmap TB1 $
            unFin $
            if b
              then upperBound j
              else lowerBound j
          ma i j = error (show (i, j))
      mal i j = error $ show (i, j)
  match i (Right j) = mar i j
    where
      mar (Left v) j = ma v j
          -- ma v a j | traceShow (v,a,j) False = undefined
        where
          ma (v, Flip (Flip op)) j = ma (v, op) j
          ma v (LeftTB1 j) = fromMaybe False (ma v <$> j)
          ma (LeftTB1 j, v) i = fromMaybe False ((\a -> ma (a, v) i) <$> j)
          ma (TB1 i, GreaterThan True) (TB1 j) = i >= j
          ma (TB1 i, (Flip (GreaterThan True))) (TB1 j) = i <= j
          ma (TB1 i, GreaterThan False) (TB1 j) = i < j
          ma (TB1 i, (Flip (GreaterThan False))) (TB1 j) = i > j
          ma (TB1 i, Flip (LowerThan True)) (TB1 j) = i >= j
          ma (TB1 i, (LowerThan True)) (TB1 j) = i <= j
          ma (TB1 i, _) (TB1 j) = i == j
          ma ((ArrayTB1 i), Flip Contains) ((ArrayTB1 j)) =
            Set.fromList (F.toList i) `Set.isSubsetOf` Set.fromList (F.toList j)
          ma ((ArrayTB1 j), Contains) ((ArrayTB1 i)) =
            Set.fromList (F.toList i) `Set.isSubsetOf` Set.fromList (F.toList j)
          ma (j, AnyOp o) (ArrayTB1 i) = F.any (ma (j, o)) i
          ma (j, Flip (AnyOp o)) (ArrayTB1 i) = F.any (ma (j, o)) i
          ma (ArrayTB1 i , Equals) (ArrayTB1 j ) = i ==  j 
          ma (ArrayTB1 i, Flip (AnyOp o)) j = F.any (\i -> ma (i, o) j) i
          ma (i@(TB1 _), op) (IntervalTB1 j) = i `Interval.member` j
          ma (IntervalTB1 i, op) j@(TB1 _) = j `Interval.member` i
          ma (IntervalTB1 i, Equals) (IntervalTB1 j) =
            j == i
          ma (IntervalTB1 i, Contains) (IntervalTB1 j) =
            j `Interval.isSubsetOf` i
          ma (IntervalTB1 j, Flip Contains) (IntervalTB1 i) =
            j `Interval.isSubsetOf` i
          ma (IntervalTB1 j, IntersectOp) (IntervalTB1 i) =
            not $ Interval.null $ j `Interval.intersection` i
          ma (j, IntersectOp) (i) =
            not $
            Interval.null $
            unFTB (bound j) `Interval.intersection` unFTB (bound i)
          ma (j, Contains) (i) =
            not $
            Interval.null $
            unFTB (bound j) `Interval.intersection` unFTB (bound i)
          ma (j, (Flip op)) i = ma (j, op) i
          ma i j = error ("no mar left = " <> show (snd i, fst i, j))
          unFTB (FTBNode i) = i
      mar (Right i) j = ma i j
        where
          ma (Not i) j = not $ ma i j
          ma Exists j = True
          ma IsNull (LeftTB1 j) = maybe True (ma IsNull) j
          ma IsNull j = False
          ma (Range b pred) (IntervalTB1 j) =
            ma pred $
            LeftTB1 $
            unFin $
            if b
              then upperBound j
              else lowerBound j
          ma i j = error ("no mar right =" ++ show (i, j))
  match x z = error ("no match = " <> show (x, z))
  origin = FTBNode Interval.empty
  bound i = FTBNode $ fmap unTB1 $ pureR i
  merge (FTBNode i) (FTBNode j) = FTBNode $ Interval.hull i j
  penalty ((FTBNode i)) ((FTBNode j)) =
    (fmap notneg $ subtraction (fst (lowerBound' j)) (fst $ lowerBound' i)) <>
    (fmap notneg $ subtraction (fst $ upperBound' i) (fst $ upperBound' j))

alterWith f k v
  = case lookup k v of
      Just i -> G.insert (f (Just i) ,k) indexParam (G.delete k indexParam v)
      Nothing -> G.insert (f Nothing ,k) indexParam v

-- Higher Level operations
fromList pred = foldl' acc G.empty
  where
    acc !m v = G.insert (v, pred v) indexParam m

-- Higher Level operations
fromList' :: Predicates p => [LeafEntry p a] -> GiST p a
fromList' = foldl' acc G.empty
  where
    acc !m v = G.insertL v indexParam m

lookup pk = safeHead . G.search pk

keys :: GiST p a -> [p]
keys = fmap (\(_, _, k) -> k) . getEntries

toList = getData

filter f =
  foldl' (\m i -> G.insertL i indexParam m) G.empty .
  L.filter (f . leafValue) . getEntries

filter' f =
  foldl' (\m i -> G.insert i indexParam m) G.empty . L.filter (f . fst)
