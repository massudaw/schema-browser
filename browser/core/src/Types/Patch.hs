{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}

module Types.Patch
  (
  -- Class Patch Interface
  Compact (..)
  ,Patch(..)
  -- Patch Data Types and to be moved methods
  ,patchSet

  ,editor
  --,recoverEdit
  ,recoverEditChange
  ,Editor(..)
  ,filterDiff
  ,isDiff
  ,pattrKey
  ,isKeep
  ,isDelete
  ,patchEditor
  ,joinEditor
  ,indexFilterP
  ,indexFilterPatch
  ,G.tbpred
  --
  ,patchfkt
  ,unAtom
  ,unIndexItensP
  ,unLeftItensP
  --
  ,PathFTB(..)
  ,PathTID(..)
  ,upperPatch,lowerPatch
  ,PathAttr(..),TBIdx,firstPatch,firstPatchRow,PatchConstr
  ,RowPatch(..))where


-- import Warshal
import Types
import qualified Types.Index as G
import Types.Index (PathTID(..))
import Control.DeepSeq
import Data.Tuple
import qualified Control.Lens as Le
import Control.Monad.Reader
import Data.Semigroup hiding (diff)
import qualified NonEmpty as Non
import NonEmpty (NonEmpty)
import Data.Bifunctor
import Data.Maybe
import GHC.Generics
import Data.Either
import Data.Binary (Binary(..))
import Data.Ord
import Utils
import Data.Traversable(traverse,sequenceA)
import Data.Foldable (Foldable)
import qualified Data.Foldable as F
import qualified Data.Interval as Interval
import Data.Interval (Extended(..))
import Data.Interval (interval,lowerBound',upperBound')
import Data.Monoid hiding ((<>),Product)

import GHC.Stack
import Debug.Trace

import GHC.Exts
import Control.Applicative
import qualified Data.List as L
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set

import Prelude hiding(head)

filterDiff  = fmap (\(Diff i ) -> i) . filter isDiff

instance Applicative PathFTB where
  pure = PAtom
  POpt i <*> POpt j = POpt $ liftA2 (<*>) i j
  PIdx ixi i <*> PIdx ix j | ixi == ix= PIdx ix $ liftA2 (<*>) i j
  PatchSet i <*> PatchSet j = PatchSet $ Non.zipWith (<*>) i j
  PAtom i <*> PAtom j = PAtom $ i  j

  PIdx ix i <*> j = PIdx ix  $ (<*> j) <$>  i
  i <*> PIdx ix j = PIdx ix  $ (i <*> ) <$>  j
  i <*> POpt j = POpt $ fmap (i <*>)  j
  POpt i <*> j = POpt $ fmap (<*>j)  i
  PatchSet i <*> j = PatchSet $ fmap (<*> j ) i
  i <*> PatchSet j = PatchSet $ fmap (i <*>  ) j

data Editor  a
  = Diff ! a
  | Delete
  | Keep
  deriving(Eq,Ord,Functor,Show)


data PathFTB a
  = PAtom a
  | POpt (Maybe (PathFTB a))
  | PIdx Int (Maybe (PathFTB a))
  | PInter Bool (Extended (PathFTB a),Bool)
  | PatchSet (Non.NonEmpty (PathFTB a))
  deriving(Show,Eq,Ord,Functor,Generic,Foldable,Traversable)



isDiff (Diff _) = True
isDiff i = False
isKeep Keep = True
isKeep i = False
isDelete Delete = True
isDelete i = False

joinEditor (Diff i ) = i
joinEditor Keep  = Keep
joinEditor Delete = Delete

data RowPatch k a
  = CreateRow (TBData k a)
  | PatchRow (TBIdx k a)
  | DropRow (TBData k a)
  deriving(Show,Eq,Ord,Functor,Generic)

instance (NFData k ,NFData a )=> NFData (RowPatch k a)
instance (Binary k ,Binary a) => Binary (RowPatch k a)

type TBIdx k a = (KVMetadata k, G.TBIndex a ,[PathAttr k a])
patchEditor i
  | L.length i == 0 = Keep
  | L.length i == 1 = maybe Keep Diff $ safeHead i
  | otherwise = Diff $ PatchSet (Non.fromList$ concat $ normalize <$> i)
      where normalize (PatchSet i) = concat $ fmap normalize i
            normalize i = [i]

indexFilterP (WherePredicate p) v = go p
  where
    go (AndColl l)  = F.all go l
    go (OrColl l ) = F.any  go l
    go (PrimColl l ) = indexFilterPatch l v

indexFilterPatch :: (Show k,Ord k) => (Access k ,Either (FTB Showable,BinaryOperator) UnaryOperator) -> TBIdx k Showable -> Bool
indexFilterPatch ((IProd _ l) ,op)  (_,_,lo) =
  case L.find ((Set.singleton (Inline l) == ).pattrKey) lo of
    Just i ->
      case i of
        PAttr k f -> G.match op (Right $ (create f :: FTB Showable))
        i -> True
    Nothing -> True
indexFilterPatch ((Nested l n) ,op)  (_,_,lo) =
  case L.find ((Set.fromList (iprodRef <$> l) == ).Set.map _relOrigin . pattrKey) lo of
    Just i ->
      case i of
        PInline k f -> L.any (indexFilterPatchU (n,op)) f
        PFK _  _ f -> L.any (indexFilterPatchU (n,op)) f
        i -> True
    Nothing -> True
indexFilterPatch i o= errorWithStackTrace (show (i,o))

indexFilterPatchU :: (Show k,Ord k) => (Union (Access k) ,Either (FTB Showable,BinaryOperator) UnaryOperator) -> TBIdx k Showable -> Bool
indexFilterPatchU (Many [One n],op) o = indexFilterPatch (n,op) o

unIndexItensP :: (Show (KType k),Show a) =>  Int -> Int -> PathAttr (FKey (KType k)) a -> Maybe (PathAttr (FKey (KType k) ) a )
unIndexItensP ix o =  unIndexP (ix+ o)
  where
    unIndexF o (PIdx ix v) = if o == ix  then v else Nothing
    unIndexF o (PatchSet l ) =  PatchSet  <$> Non.nonEmpty ( catMaybes (unIndexF o <$> F.toList l))
    unIndexF o i = errorWithStackTrace ("unIndexF error" ++ show (o,i))
    unIndexP :: (Show (KType k),Show a) => Int -> PathAttr (FKey (KType k)) a -> Maybe (PathAttr (FKey (KType k) ) a )
    unIndexP o (PAttr  k v) =  PAttr k <$> unIndexF o v
    unIndexP o (PInline k v) = PInline k <$> unIndexF o v
    unIndexP o (PFK rel els  v) = (\mi li ->  PFK  (Le.over relOri (\i -> if isArray (keyType i) then unKArray i else i ) <$> rel) mi  li) <$> (traverse (unIndexP o) els) <*> unIndexF o v
    unIndexP o i = errorWithStackTrace ("unIndexP error" ++ show (o,i))

unSOptionalP (PatchSet l ) =  PatchSet  <$> Non.nonEmpty ( catMaybes (unSOptionalP <$> F.toList l))
unSOptionalP (POpt i ) = i
unSOptionalP i = Just i

unLeftItensP  :: (Show k , Show a) => PathAttr (FKey (KType k)) a -> Maybe (PathAttr (FKey (KType k)) a )
unLeftItensP = unLeftTB
  where

    unLeftTB (PAttr k (PatchSet l)) = PAttr (unKOptional k) . PatchSet  <$> Non.nonEmpty ( catMaybes (unSOptionalP <$> F.toList l))
    unLeftTB (PAttr k v)
      = PAttr (unKOptional k) <$> unSOptionalP v
    unLeftTB (PFun k rel v)
      = PFun (unKOptional k) rel <$> unSOptionalP v
    unLeftTB (PInline na l)
      = PInline (unKOptional na) <$>  unSOptionalP l
    unLeftTB (PFK rel ifk  tb)
      = (\ik -> PFK  (Le.over relOri unKOptional <$> rel) ik   )
          <$> traverse unLeftTB ifk
          <*>  unSOptionalP tb
    unLeftTB i = errorWithStackTrace (show i)



-- recoverEditChange  i j | traceShow (i,j) False = undefined
recoverEditChange (Just i) Keep = Just i
recoverEditChange (Just i) Delete = Nothing
recoverEditChange  (Just i)(Diff j ) =  applyIfChange i j
recoverEditChange  Nothing (Diff j ) = createIfChange j
recoverEditChange  Nothing Keep = Nothing
recoverEditChange  Nothing Delete = Nothing
recoverEditChange  _ _ = errorWithStackTrace "no edit"



-- editor  i j | traceShow (i,j) False = undefined
editor (Just i) Nothing = Delete
editor (Just i) (Just j) = maybe Keep Diff df
    where df = diff i j
editor Nothing (Just j) = Diff (patch j)
editor Nothing Nothing = Keep

upperPatch = PInter False
lowerPatch = PInter True


class Patch f where
  type Index f
  diff :: f -> f -> Maybe (Index f)
  apply :: f -> Index f -> f
  apply i  = justError "no apply" . applyIfChange i
  applyIfChange :: f -> Index f -> Maybe f
  create :: Index f -> f
  create = justError "no create" . createIfChange
  createIfChange :: Index f -> Maybe f
  patch  :: f -> Index f

data PatchIndex a = PatchIndex Int (Maybe a)

instance Patch a => Patch (NonEmpty a) where
  type Index (NonEmpty a)  = PatchIndex (Index a)
  applyIfChange j (PatchIndex i (Just a)) = Just $ Non.imap (\ix -> if ix == i then flip apply a else id ) j
  applyIfChange j (PatchIndex i Nothing ) =  Non.nonEmpty $ Non.take i j <> Non.drop (i+1) j
  createIfChange (PatchIndex i a ) = join $ fmap (fmap pure.createIfChange) a


class Compact f where
  compact :: [f] -> [f]


instance (Show (Index a),Ord (Index a),PatchConstr k a) => Compact (PathAttr k a) where
  compact = compactAttr

instance PatchConstr k a => Patch (TB k a)  where
  type Index (TB k a) =  PathAttr k (Index a)
  diff = diffAttr
  applyIfChange = applyAttrChange
  createIfChange = createAttrChange
  patch = patchAttr

instance  PatchConstr k a => Patch (TBData k a)  where
  type Index (TBData k a) =  TBIdx k (Index a)
  diff = difftable
  applyIfChange = applyRecordChange
  createIfChange = createTB1
  patch = patchTB1

instance PatchConstr k a => Compact (TBIdx k a) where
  compact = compactTB1

instance (Ord a,Show a,Patch a) => Patch (FTB a ) where
  type Index (FTB a) =  PathFTB (Index a)
  diff = diffFTB patch diff
  applyIfChange = applyFTBM createIfChange applyIfChange
  createIfChange = createFTBM createIfChange
  patch = patchFTB patch

instance Monoid Showable where
  mempty = error "no empty showable"
  mappend i j = j

instance Patch ()  where
  type Index () = ()
  patch = id
instance Patch Showable  where
  type Index Showable = Showable
  diff  = diffPrim
  apply _ i = i
  applyIfChange _ = Just
  createIfChange = Just
  create = id
  patch = id


type PatchConstr k a = (Eq (Index a),Patch a , Ord a , Show a,Show k , Ord k)



data PathAttr k a
  = PAttr k (PathFTB a)
  | PFun k (Expr ,[Access k]) (PathFTB a)
  | PInline k (PathFTB  (TBIdx k a))
  | PFK [Rel k] [PathAttr k a]  (PathFTB (TBIdx k a))
  deriving(Eq,Ord,Show,Functor,Generic)

patchfkt (PFK _ _  k) = k
patchfkt (PInline  _ k) = k
patchfkt i = errorWithStackTrace (show i)

unAtom (PatchSet (PAtom l Non.:| _ ) ) =  l
unAtom (PAtom i ) = i
unAtom i =errorWithStackTrace (show   i)

instance (Binary k ,Binary a) => Binary (PathAttr k a)
instance (NFData k ,NFData a) => NFData (PathAttr k a)


instance (NFData k ) => NFData (PathFTB k )
instance (Binary k ) => Binary (PathFTB k )

firstPatchRow :: (Ord a ,Ord k , Ord (Index a), Ord j ) => (k -> j ) -> RowPatch k a -> RowPatch j a
firstPatchRow f (CreateRow i ) = CreateRow $ mapKey' f i
firstPatchRow f (DropRow i ) = DropRow $ mapKey' f i
firstPatchRow f (PatchRow i ) = PatchRow $ firstPatch f i

firstPatch :: (Ord a ,Ord k , Ord (Index a), Ord j ) => (k -> j ) -> TBIdx k a -> TBIdx j a
firstPatch f (i,j,k) = (fmap f i , j ,fmap (firstPatchAttr f) k)

firstPatchAttr :: (Ord k , Ord j ,Ord a ,Ord (Index a)) => (k -> j ) -> PathAttr k a -> PathAttr j a
firstPatchAttr f (PAttr k a) = PAttr (f k) a
firstPatchAttr f (PFun k rel a) = PFun (f k) (fmap (fmap f ) <$> rel ) a
firstPatchAttr f (PInline k a) = PInline (f k) (fmap (firstPatch f) a)
firstPatchAttr f (PFK rel k   b ) = PFK (fmap (fmap f) rel)  (fmap (firstPatchAttr f) k)  (fmap (firstPatch f) $ b)



compactTB1 :: (Ord a , Show a, Ord b ,Show b) => [TBIdx a b] -> [TBIdx a b ]
compactTB1 i = fmap (\((i,j),p)-> (i,j,concat p)) $  groupSplit2 (\(i,j,_) -> (i,j))  (\(_,_,p) -> p) i

compactAttr :: (Ord a , Show a, Ord b ,Show b,Ord (Index b) ,Show (Index b)) => [PathAttr a b ] -> [PathAttr a b ]
compactAttr  i =  fmap recover .  groupSplit2 projectors pathProj $ i
  where
    pathProj (PAttr i j)  = Right (Right j)
    pathProj (PFun i rel j)  = Right (Right j)
    pathProj (PInline i j)  = Left j
    pathProj (PFK i p  j)  = Right (Left p)
    projectors (PAttr i j ) =  Left (Right i)
    projectors (PFun i r j ) =  Left (Left (i,r))
    projectors (PInline i j) = Left (Right i)
    projectors (PFK i _  j) = Right (i,j)
    recover (Left (Right i),j) = justError "cant compact" $ (fmap (PAttr i) $ compactPatches $ rights $ rights j) <|>  (fmap (PInline i ) $ compactPatches $lefts j)
    recover (Left (Left (i,r)),j) = PFun i r (justError "cant comapct pattr" $ compactPatches $ rights $ rights j)
    recover (Right (i,j) ,l) = PFK i (compactAttr $ concat $ lefts $ rights l)  j
    recover i  = errorWithStackTrace $ "no item" <> (show i)



compactPatches :: (Ord a ,Show a)=> [PathFTB  a] -> Maybe (PathFTB  a)
compactPatches [] = Nothing
compactPatches i = patchSet . fmap recover .  groupSplit2 projectors pathProj . concat . fmap expandPSet $ i
  where
    pathProj (PIdx _ i) = i
    pathProj (POpt  i) = i
    pathProj p@(PInter _ i) = Just p
    pathProj i@(PAtom _  ) = Just i
    -- pathProj i = errorWithStackTrace (show i)
    projectors (PIdx i _ ) = PIdIdx i
    projectors (POpt _  ) = PIdOpt
    projectors (PInter b _  ) = PIdInter b
    projectors (PAtom _  ) =  PIdAtom
    -- projectors i = errorWithStackTrace (show i)
    recover (PIdIdx i, j ) = PIdx i (compact j)
    recover (PIdOpt , j ) = POpt (compact j)
    recover (PIdInter i ,  j ) = justError "no patch inter" $ patchSet (catMaybes j)
    recover (PIdAtom , j ) = justError "can't be empty " $ patchSet (catMaybes j)
    -- recover i = errorWithStackTrace (show i)
    compact j = compactPatches $ catMaybes j



expandPSet (PatchSet l ) =  F.toList l
expandPSet p = [p]

groupSplit2 :: Ord b => (a -> b) -> (a -> c ) -> [a] -> [(b ,[c])]
groupSplit2 f g = fmap (\i-> (f $ justError "cant group" $ safeHead i , g <$> i)) . groupWith f



instance (NFData k ,NFData a) => NFData (KV  k a) where

instance (NFData k ,NFData a ) => NFData (TB k a) where


patchTB1 :: PatchConstr k a => TBData k  a -> TBIdx k  (Index a)
patchTB1 (m, k)  = (m  ,fmap patch $G.getIndex (m,k) ,  F.toList $ patchAttr   <$> (unKV k))

difftable
  ::  (PatchConstr k a  , Show a,Show k ) => TBData k a -> TBData k a
     -> Maybe (Index (TBData k a ))
difftable old@(m, v) (n, o) = if L.null attrs then Nothing else Just  (m,   fmap patch  $ G.getIndex old , attrs)
    where attrs = catMaybes $ F.toList  $ Map.mergeWithKey (\_ i j -> Just $ diffAttr (i) (j)) (const Map.empty ) (fmap (Just. patchAttr  ) ) (unKV v) (unKV $  o)

diffTB1 :: (PatchConstr k a ) =>  TB2 k a -> TB2  k  a -> Maybe (PathFTB   (Index (TBData k a )) )
diffTB1 = diffFTB patchTB1  difftable



travPath f p (PatchSet i) = F.foldl' f p i
travPath f p i = f p i



applyTB1
  :: PatchConstr k a =>
    FTB (TBData k a ) -> PathFTB   (TBIdx k (Index a) ) -> FTB (TBData k a )
applyTB1 = apply -- create applyRecord

createTB1
  :: PatchConstr d a =>
    (TBIdx d (Index a) ) ->
      Maybe (TBData d a)
createTB1 (m ,s ,k)  = (m ,).  KV . mapFromTBList  <$>  nonEmpty ( catMaybes $ fmap (createIfChange) k)


pattrKey (PAttr s _ ) = Set.singleton $ Inline s
pattrKey (PFun s l _ ) = Set.singleton $ RelFun s (relAccesGen <$> snd l)
pattrKey (PInline s _ ) = Set.singleton $ Inline s
pattrKey (PFK s _  _ ) = Set.fromList s


applyRecordChange
   :: PatchConstr d a =>
    TBData d a
     -> TBIdx d (Index a)
     -> Maybe (TBData d a)
applyRecordChange t@(m, v) (_,_, k) =
  {-| _kvname m == _kvname m2 && idx == fmap patch (G.getIndex t) =-} (m ,) <$> ref v
    -- | otherwise = createIfChange (m2,idx,k)
  where
    ref (KV v) =  KV <$>  fmap add (Map.traverseWithKey (\key -> (\vi -> maybe (Just vi) (F.foldl'  (\i j ->  edit j =<< i ) (Just vi)) (nonEmpty $ filter ((key ==).pattrKey )k) )) v)
    add v = foldr (\p v -> Map.insert (pattrKey p) (create p) v) v $  filter (isNothing . flip Map.lookup  v.pattrKey) k
    edit  k v = applyAttrChange  v k


patchSet i
  | L.length i == 0 = Nothing
  | L.length i == 1 = safeHead i
  | otherwise = Just $ PatchSet (Non.fromList $ concat $ normalize <$> i)
      where normalize (PatchSet i) = concat $ fmap normalize i
            normalize i = [i]


applyAttrChange :: PatchConstr k a  => TB k a -> PathAttr k (Index a) -> Maybe (TB k a)
applyAttrChange (Attr k i) (PAttr _ p)  = Attr k <$> (applyIfChange i p)
applyAttrChange (Fun k rel i) (PFun _ _ p)  = Fun k rel <$> (applyIfChange i p)
applyAttrChange (FKT k rel  i) (PFK _ p  b )  =  (\i -> FKT i rel  ) <$> ref <*> applyIfChange i b
  where
    ref =  fmap KV$  Map.traverseWithKey (\key vi ->  F.foldl'  (\i j ->  edit j =<< i ) (Just vi) (filter ((==key) . pattrKey ) p) ) (_kvvalues k)
    edit k v = (flip applyAttrChange k ) v

applyAttrChange (IT k i) (PInline _   p)  = IT k <$> (applyIfChange i p)



diffAttr :: PatchConstr k a  => TB k a -> TB k a -> Maybe (PathAttr k  (Index a))
diffAttr (Attr k i) (Attr l m ) = fmap (PAttr k) (diffShowable i m)
diffAttr (Fun k rel i) (Fun l rel2 m ) = fmap (PFun k rel ) (diffShowable i m)
diffAttr (IT k i) (IT _ l) = fmap (PInline k  ) (diffTB1 i l)
diffAttr (FKT  k _ i) (FKT m rel b) = PFK rel   <$> (Just $ catMaybes $ F.toList $ Map.intersectionWith (\i j -> diffAttr (i) (j)) (_kvvalues k) (_kvvalues m)  ) <*> diff i b

patchAttr :: PatchConstr k a  => TB k a -> PathAttr k (Index a)
patchAttr a@(Attr k v) = PAttr k  (patchFTB patch   v)
patchAttr a@(Fun k rel v) = PFun k  rel (patchFTB patch v)
patchAttr a@(IT k v) = PInline k (patchFTB patchTB1 v)
patchAttr a@(FKT k rel v) = PFK rel (patchAttr  <$> unkvlist k) (patch v)

createAttrChange :: PatchConstr k a  => PathAttr k (Index a) -> Maybe (TB k a)
createAttrChange (PAttr  k s  ) = Attr k <$> createIfChange s
createAttrChange (PFun k rel s  ) = Fun k rel <$> createIfChange s
createAttrChange (PInline k s ) = IT k <$> createIfChange s
createAttrChange (PFK rel k  b ) = flip FKT rel <$> (kvlist  <$> traverse createAttrChange  k) <*> createIfChange b





diffShowable ::  (Show a,Ord a ,Patch a ) => FTB a -> FTB a -> Maybe (PathFTB (Index a))
diffShowable = diffFTB patch diff

applyShowable ::  (Show a,Ord a ,Patch a ) => FTB a ->  PathFTB   (Index a)  -> FTB a
applyShowable = apply

createShowable :: (Show a,Ord a ,Patch a)=>  PathFTB (Index a) -> FTB a
createShowable = create


diffPrim :: (Eq a ,a ~ Index a) => a -> a -> Maybe (Index a)
diffPrim i j
  | i == j = Nothing
  | otherwise = Just  j


-- FTB

patchFTB :: Show a => (a -> Index a) -> FTB a -> PathFTB   (Index a)
patchFTB p (LeftTB1 j )  = POpt (patchFTB p <$> j)
patchFTB p (ArrayTB1 j )  = justError ("empty array in arraytb1 patchftb" <> show j)$  patchSet   $ zipWith (\i m ->  PIdx i  (Just m) ) [0..]  (F.toList $ patchFTB p <$> j)
patchFTB p (IntervalTB1 j ) =  justError ("no patch for" <> show j) $ patchSet  [PInter True $ (first (fmap (patchFTB p )) $ Interval.lowerBound' j) , PInter False $ (first (fmap (patchFTB p )) $ Interval.upperBound' j)]
patchFTB p (TB1 j) = PAtom $ p j

diffOpt :: (Ord a,Show a) => (a -> Index a ) -> (a -> a -> Maybe (Index a)) ->  Maybe (FTB a) -> Maybe (FTB a) -> Maybe (Maybe (PathFTB    (Index a)))
diffOpt p d i j
    | isJust i && isJust j = sequenceA $ liftA2 (diffFTB  p d ) i j
    | isJust i && isNothing j = Just  Nothing
    | isNothing i && isJust j = Just  (patchFTB p <$> j)
    | isNothing i && isNothing j =  Nothing

diffFTB :: (Ord a,Show a) => (a -> Index a) -> (a -> a -> Maybe (Index a) ) ->  FTB a -> FTB a -> Maybe (PathFTB (Index a))
diffFTB p d (LeftTB1 i) (LeftTB1 j) = POpt <$> diffOpt p d i j
diffFTB p d (ArrayTB1 i) (ArrayTB1 j) =
    patchSet $  catMaybes $ zipWith (\i -> fmap (PIdx  i)  ) ( [0..]) (F.toList  (Non.zipWith (\i j ->fmap Just $ diffFTB p d i j ) i j)  <> (const (Just  Nothing) <$> Non.drop (Non.length j  ) i ) <> (Just . Just . patchFTB p <$> Non.drop (Non.length i  ) j ))
diffFTB p d (IntervalTB1 i) (IntervalTB1 j)
  | i == j = Nothing
  | otherwise =  patchSet $  catMaybes   [match True (lowerBound' i ) (lowerBound' j) ,match False (upperBound' i ) (upperBound' j) ]
    where match f i j = fmap (PInter f . (,snd $  j)) (maybe (if snd j == snd i then Nothing  else Just $ patchFTB p <$> (fst $ j))  Just $ diffExtended (fst $  i) (fst $  j) )
          diffExtended (Finite i ) (Finite j) = fmap Finite $ diffFTB p d i j
          diffExtended _ (Finite i) = Just $ Finite $ patchFTB p  i
          diffExtended _   i = Nothing

diffFTB p d (TB1 i) (TB1  j) = fmap PAtom $ d i j
diffFTB p d  i j = errorWithStackTrace ("diffError" <> show (i,j))



applyFTBM
  :: (Ord a,Show a) =>
  (Index a  -> Maybe a) -> (a -> Index a -> Maybe a) -> FTB a -> PathFTB (Index a) -> Maybe (FTB a)
applyFTBM pr a (LeftTB1 i ) op@(POpt o) = Just $ LeftTB1 $ (join  (applyFTBM pr a <$> i <*> o)) <|> join (createFTBM pr <$> o)
applyFTBM pr a (ArrayTB1 i ) (PIdx ix o) = case o of
                      Nothing -> fmap ArrayTB1 . Non.nonEmpty $ (Non.take ix   i) ++ (Non.drop (ix+1) i)
                      Just p -> if ix <=  Non.length i - 1
                                then fmap ArrayTB1 $ sequenceA $ Non.imap (\i v -> if i == ix then applyFTBM pr a v p else Just v )  i
                                else if ix == Non.length i
                                      then (\p -> ArrayTB1 $ i <> pure p) <$> createFTBM pr p
                                      else Nothing -- errorWithStackTrace $ "ix bigger than next elem"
applyFTBM pr a (IntervalTB1 i) (PInter b (p,l))
  =  IntervalTB1 <$>  if b
                    then (flip interval) (upperBound' i)     <$> firstT (mapExtended p) (lowerBound' i)
                    else interval (lowerBound' i) <$> firstT (mapExtended  p ) (upperBound' i)
  where
    mapExtended p (Interval.Finite i) = traverse (applyFTBM pr a i)  p
    mapExtended p _ = traverse (createFTBM pr ) p
applyFTBM pr a (TB1 i) (PAtom p)  =  fmap TB1 $ a i p
applyFTBM pr a  b (PatchSet l ) = F.foldl' (\i l -> (\i -> applyFTBM pr a i l ) =<< i ) (Just b) l
applyFTBM pr _ a b = error ("applyFTB: " <> show (a,fmap pr b) )

checkInterM :: (Show a,Ord a) => (Index a  -> Maybe  a) -> PathFTB (Index a) -> Interval.Interval (FTB a)-> Maybe (Interval.Interval (FTB a))
checkInterM p (PInter b o) inter = if fst (lowerBound' inter) == Interval.PosInf || fst (upperBound' inter) == Interval.NegInf then Nothing else Just inter

createFTBM :: (Show a,Ord a) => (Index a  -> Maybe  a) -> PathFTB (Index a) -> Maybe (FTB a)
createFTBM p (POpt i ) = Just $ LeftTB1 (join $ createFTBM p <$> i)
createFTBM p (PIdx ix o ) = ArrayTB1 . pure <$>  join (createFTBM p <$> o)
createFTBM p (PInter b o ) = IntervalTB1 <$> join (checkInterM p (PInter b o)  <$> inter)
  where inter = if b then flip interval  (Interval.PosInf,False) <$> firstT (traverse ( createFTBM p) ) o else  interval  (Interval.NegInf,False) <$>  ( firstT (traverse (createFTBM p)) o)
createFTBM p (PAtom i )  = fmap TB1 $ p i
createFTBM p (PatchSet l) = F.foldl1 (<>) (createFTBM p <$> l)

firstT f (i,j) = (,j) <$> f i


instance Ord a => Semigroup (FTB a) where
  LeftTB1 i<> LeftTB1 j = LeftTB1 j
  IntervalTB1 i <> IntervalTB1 j = IntervalTB1 ( i `Interval.intersection` j)
  ArrayTB1 i <> ArrayTB1 j = ArrayTB1 (i <>  j)
  TB1 i <> TB1 j = TB1 j

instance Monad PathFTB where
  PAtom i >>= j = j i
  PIdx ix i >>= j = PIdx ix $ (j =<<)  <$> i
  POpt i >>= j = POpt $ (j =<<)  <$> i
  PatchSet i >>= j = PatchSet $ (j =<<) <$> i


