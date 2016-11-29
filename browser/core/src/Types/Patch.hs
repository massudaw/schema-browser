{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor #-}
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
  ,recoverEdit
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
  ,upperPatch,lowerPatch
  ,PathAttr(..),TBIdx,firstPatch,PatchConstr)where


-- import Warshal
import Types
import qualified Types.Index as G
import Control.DeepSeq
import Data.Tuple
import qualified Control.Lens as Le
import Control.Monad.Reader
import Data.Semigroup hiding (diff)
import qualified NonEmpty as Non
import Data.Bifunctor
import Data.Maybe
import GHC.Generics
import Data.Either
import Data.Binary (Binary(..))
import Data.Ord
import Data.Functor.Identity
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

isDiff i@(Diff _) = True
isDiff i = False
isKeep i@(Keep) = True
isKeep i = False
isDelete  i@(Delete) = True
isDelete i = False

joinEditor (Diff i ) = i
joinEditor Keep  = Keep
joinEditor Delete = Delete

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

indexFilterPatch :: (Access Key,Either (FTB Showable,BinaryOperator) UnaryOperator) -> TBIdx Key Showable -> Bool
indexFilterPatch ((IProd _ l) ,op)  (_,_,lo) =
  case L.find ((Set.fromList (fmap Inline l) == ).pattrKey) lo of
    Just i ->
      case i of
        PAttr k f -> G.match op G.Exact (create f :: FTB Showable)
        i -> True
    Nothing -> True
indexFilterPatch ((Nested (IProd _  l) n) ,op)  (_,_,lo) =
  case L.find ((Set.fromList l == ).Set.map _relOrigin . pattrKey) lo of
    Just i ->
      case i of
        PInline k f -> L.any (indexFilterPatch (n,op)) f
        PFK _ _ _ f -> L.any (indexFilterPatch (n,op)) f
        i -> True
    Nothing -> True
indexFilterPatch (Many [n],op) o = indexFilterPatch (n,op) o
indexFilterPatch i o= errorWithStackTrace (show (i,o))

unIndexItensP :: (Show (KType k),Show a) =>  Int -> Int -> Maybe (PathAttr (FKey (KType k)) a) -> Maybe (PathAttr (FKey (KType k) ) a )
unIndexItensP ix o =  join . fmap (unIndexP (ix+ o) )
  where
    unIndexF o (PIdx ix v) = if o == ix  then v else Nothing
    unIndexF o (PatchSet l ) =  PatchSet . Non.fromList <$> nonEmpty ( catMaybes (unIndexF o <$> F.toList l))
    unIndexF o i = errorWithStackTrace (show (o,i))
    unIndexP :: (Show (KType k),Show a) => Int -> PathAttr (FKey (KType k)) a -> Maybe (PathAttr (FKey (KType k) ) a )
    unIndexP o (PAttr  k v) =  PAttr k <$> unIndexF o v
    unIndexP o (PInline k v) = PInline k <$> unIndexF o v
    unIndexP o (PFK rel els m v) = (\mi li ->  PFK  (Le.over relOri (\i -> if isArray (keyType i) then unKArray i else i ) <$> rel) mi m li) <$> (traverse (unIndexP o) els) <*> unIndexF o v
    unIndexP o i = errorWithStackTrace (show (o,i))

unSOptionalP (PatchSet l ) =  PatchSet . Non.fromList <$> nonEmpty ( catMaybes (unSOptionalP <$> F.toList l))
unSOptionalP (POpt i ) = i
unSOptionalP i = Just i

unLeftItensP  :: (Show k , Show a) => PathAttr (FKey (KType k)) a -> Maybe (PathAttr (FKey (KType k)) a )
unLeftItensP = unLeftTB
  where

    unLeftTB (PAttr k (PatchSet l)) = PAttr (unKOptional k) . PatchSet . Non.fromList <$> nonEmpty ( catMaybes (unSOptionalP <$> F.toList l))
    unLeftTB (PAttr k v)
      = PAttr (unKOptional k) <$> unSOptionalP v
    unLeftTB (PFun k rel v)
      = PFun (unKOptional k) rel <$> unSOptionalP v
    unLeftTB (PInline na l)
      = PInline (unKOptional na) <$>  unSOptionalP l
    unLeftTB (PFK rel ifk m tb)
      = (\ik -> PFK  (Le.over relOri unKOptional <$> rel) ik   m)
          <$> traverse unLeftTB ifk
          <*>  unSOptionalP tb
    unLeftTB i = errorWithStackTrace (show i)





recoverEdit (Just i) Keep = Just i
recoverEdit (Just i) Delete = Nothing
recoverEdit (Just i)(Diff j ) = Just $ apply i j
recoverEdit Nothing (Diff j ) = Just $ create j
recoverEdit Nothing Keep = Nothing
recoverEdit Nothing Delete = Nothing
recoverEdit _ _ = errorWithStackTrace "no edit"


editor (Just i) Nothing = Delete
editor (Just i) (Just j) = maybe Keep Diff df
    where df = diff i j
editor Nothing (Just j) = Diff (patch j)
editor Nothing Nothing = Keep

data Editor  a
  = Diff a
  | Delete
  | Keep
  deriving(Eq,Ord,Functor,Show)

instance Applicative Editor where
  pure = Diff
  Diff a <*> Diff b = Diff $ a  b
  Delete <*> i = Delete
  i <*> Delete  = Delete
  Keep <*> i = Keep
  i <*> Keep = Keep



data PathFTB   a
  = POpt (Maybe (PathFTB a))
  | PDelayed (Maybe (PathFTB a))
  | PSerial (Maybe (PathFTB a))
  | PIdx Int (Maybe (PathFTB a))
  | PInter Bool (Extended (PathFTB a),Bool)
  | PatchSet (Non.NonEmpty (PathFTB a))
  | PAtom a
  deriving(Show,Eq,Ord,Functor,Generic,Foldable)

upperPatch = PInter False
lowerPatch = PInter True

newtype FBPatch p
  =  FBPatch (p ,p)
  deriving (Show,Eq,Ord)


class Patch f where
  type Index f
  diff :: f -> f -> Maybe (Index f)
  apply :: f -> Index f -> f
  applyIfChange :: f -> Index f -> Maybe f
  create :: Index f -> f
  patch  :: f -> Index f

class Compact f where
  compact :: [f] -> [f]

instance (G.Predicates (G.TBIndex   a) , PatchConstr k a) => Patch (G.GiST (G.TBIndex  a ) (TBData k a)) where
  type Index (G.GiST (G.TBIndex  a ) (TBData k a)  ) = RowPatch k (Index a)
  apply = applyGiST
  applyIfChange = applyGiSTChange
  -- diff = diffGiST


instance (Show (Index a),Ord (Index a),PatchConstr k a) => Compact (PathAttr k a) where
  compact = compactAttr

instance PatchConstr k a => Patch (TB Identity k a)  where
  type Index (TB Identity k a) =  PathAttr k (Index a)
  diff = diffAttr
  apply = applyAttr
  applyIfChange = applyAttrChange
  create = createAttr
  patch = patchAttr

instance  PatchConstr k a => Patch (TBData k a)  where
  type Index (TBData k a) =  TBIdx k (Index a)
  diff = difftable
  apply = applyRecord
  applyIfChange = applyRecordChange
  create = createTB1
  patch = patchTB1

instance PatchConstr k a => Compact (TBIdx k a) where
  compact = compactTB1

instance (Ord a,Show a,Patch a) => Patch (FTB a ) where
  type Index (FTB a) =  PathFTB (Index a)
  diff = diffFTB patch diff
  apply = applyFTB create apply
  create = createFTB create
  patch = patchFTB patch


instance Patch Showable  where
  type Index Showable = Showable
  diff  = diffPrim
  apply _ i = i
  applyIfChange i j = if i == j then Nothing else Just j
  create = id
  patch = id


type PatchConstr k a = (Eq (Index a),Patch a , Ord a , Show a,Show k , Ord k)

type TBIdx  k a = (KVMetadata k, G.TBIndex   a ,[PathAttr k a])
type RowPatch k a = TBIdx k a -- (KVMetadata k, TBData k a ,[PathAttr k a])


data PathAttr k a
  = PAttr k (PathFTB a)
  | PFun k (Expr ,[Access k]) (PathFTB a)
  | PInline k (PathFTB  (TBIdx k a))
  | PFK [Rel k] [PathAttr k a] (KVMetadata k) (PathFTB (TBIdx k a))
  deriving(Eq,Ord,Show,Functor,Generic)

patchfkt (PFK _ _ _ k) = k
patchfkt (PInline  _ k) = k
patchfkt i = errorWithStackTrace (show i)

unAtom (PatchSet (PAtom l Non.:| _ ) ) =  l
unAtom (PAtom i ) = i
unAtom i =errorWithStackTrace (show   i)

instance (Binary k ,Binary a) => Binary (PathAttr k a)
instance (NFData k ,NFData a) => NFData (PathAttr k a)


instance (NFData k ) => NFData (PathFTB k )
instance (Binary k ) => Binary (PathFTB k )

data PathTID
  = PIdIdx Int
  | PIdOpt
  | PIdSerial
  | PIdDelayed
  | PIdInter Bool
  | PIdAtom
  deriving (Eq,Ord,Show)


firstPatch :: (Ord a ,Ord k , Ord (Index a), Ord j ) => (k -> j ) -> TBIdx k a -> TBIdx j a
firstPatch f (i,j,k) = (fmap f i , G.mapKeys f j ,fmap (firstPatchAttr f) k)

firstPatchAttr :: (Ord k , Ord j ,Ord a ,Ord (Index a)) => (k -> j ) -> PathAttr k a -> PathAttr j a
firstPatchAttr f (PAttr k a) = PAttr (f k) a
firstPatchAttr f (PFun k rel a) = PFun (f k) (fmap (fmap f ) <$> rel ) a
firstPatchAttr f (PInline k a) = PInline (f k) (fmap (firstPatch f) a)
firstPatchAttr f (PFK rel k a  b ) = PFK (fmap (fmap f) rel)  (fmap (firstPatchAttr f) k) (fmap f a) (fmap (firstPatch f) $ b)


compactionLaw t l = diffTB1 t (foldl applyTB1 t l ) == compactPatches l

compactTB1 :: (Ord a , Show a, Ord b ,Show b) => [TBIdx a b] -> [TBIdx a b ]
compactTB1 i = fmap (\((i,j),p)-> (i,j,concat p)) $  groupSplit2 (\(i,j,_) -> (i,j))  (\(_,_,p) -> p) i

compactAttr :: (Ord a , Show a, Ord b ,Show b,Ord (Index b) ,Show (Index b)) => [PathAttr a b ] -> [PathAttr a b ]
compactAttr  i =  fmap recover .  groupSplit2 projectors pathProj $ i
  where
    pathProj (PAttr i j)  = Right (Right j)
    pathProj (PFun i rel j)  = Right (Right j)
    pathProj (PInline i j)  = Left j
    pathProj (PFK i p _ j)  = Right (Left p)
    projectors (PAttr i j ) =  Left (Right i)
    projectors (PFun i r j ) =  Left (Left (i,r))
    projectors (PInline i j) = Left (Right i)
    projectors (PFK i _ m j) = Right (i,m,j)
    recover (Left (Right i),j) = justError "cant compact" $ (fmap (PAttr i) $ compactPatches $ rights $ rights j) <|>  (fmap (PInline i ) $ compactPatches $lefts j)
    recover (Left (Left (i,r)),j) = PFun i r (justError "cant comapct pattr" $ compactPatches $ rights $ rights j)
    recover (Right (i,m,j) ,l) = PFK i (compactAttr $ concat $ lefts $ rights l) m j
    recover i  = errorWithStackTrace $ "no item" <> (show i)



compactPatches :: (Ord a ,Show a)=> [PathFTB  a] -> Maybe (PathFTB  a)
compactPatches [] = Nothing
compactPatches i = patchSet . fmap recover .  groupSplit2 projectors pathProj . concat . fmap expandPSet $ i
  where
    pathProj (PIdx _ i) = i
    pathProj (POpt  i) = i
    pathProj (PSerial i) = i
    pathProj (PDelayed i) = i
    pathProj p@(PInter _ i) = Just p
    pathProj i@(PAtom _  ) = Just i
    -- pathProj i = errorWithStackTrace (show i)
    projectors (PIdx i _ ) = PIdIdx i
    projectors (POpt _  ) = PIdOpt
    projectors (PSerial _  ) = PIdSerial
    projectors (PDelayed _  ) = PIdDelayed
    projectors (PInter b _  ) = PIdInter b
    projectors (PAtom _  ) =  PIdAtom
    -- projectors i = errorWithStackTrace (show i)
    recover (PIdIdx i, j ) = PIdx i  (compact j)
    recover (PIdOpt , j ) = POpt  (compact j)
    recover (PIdSerial , j ) = PSerial (compact j)
    recover (PIdDelayed , j ) = PDelayed (compact j)
    recover (PIdInter i ,  j ) = justError "no patch inter" $ patchSet (catMaybes j)
    recover (PIdAtom , j ) = justError "can't be empty " $ patchSet (catMaybes j)
    -- recover i = errorWithStackTrace (show i)
    compact j = compactPatches $ catMaybes j



expandPSet (PatchSet l ) =  F.toList l
expandPSet p = [p]

groupSplit2 :: Ord b => (a -> b) -> (a -> c ) -> [a] -> [(b ,[c])]
groupSplit2 f g = fmap (\i-> (f $ justError "cant group" $ safeHead i , g <$> i)) . groupWith f

applyGiSTChange
  ::  (G.Predicates (G.TBIndex   a) , PatchConstr k a)  => G.GiST (G.TBIndex  a ) (TBData k a) -> RowPatch k (Index a) -> Maybe (G.GiST (G.TBIndex  a ) (TBData k a))
applyGiSTChange l patom@(m,i, []) = Just $ G.delete (create <$> G.notOptional i) (3,6)  l
applyGiSTChange l patom@(m,ipa, p) =  case G.lookup (G.notOptional i) l  of
                  Just v ->
                        do
                          let val =  applyIfChange v patom
                          el <- if isNothing val then trace "no change" val else val
                          let pkel = G.getIndex el
                          Just $ G.insert (el,G.tbpred  el) (3,6) . G.delete (G.notOptional i)  (3,6) $ l
                  Nothing -> let
                      el = createTB1  patom
                   in Just $ G.insert (el,G.tbpred  el) (3,6)  l
   where
         i = fmap create  ipa


applyGiST
  ::  (G.Predicates (G.TBIndex   a) , PatchConstr k a)  => G.GiST (G.TBIndex  a ) (TBData k a) -> RowPatch k (Index a) -> G.GiST (G.TBIndex  a ) (TBData k a)
applyGiST l patom@(m,i, []) = G.delete (create <$> G.notOptional i) (3,6)  l
applyGiST l patom@(m,ipa, p) =  case G.lookup (G.notOptional i) l  of
                  Just v ->  let
                           el = applyRecord  v patom
                           pkel = G.tbpred el
                        in if  pkel == i
                              then G.update (G.notOptional i) (flip applyRecord patom) l
                              else G.insert (el,G.tbpred  el) (3,6) . G.delete (G.notOptional i)  (3,6) $ l
                  Nothing -> let
                      el = createTB1  patom
                      in G.insert (el,G.tbpred  el) (3,6)  l
    where
          i = fmap create  ipa

patchTB1 :: PatchConstr k a => TBData k  a -> TBIdx k  (Index a)
patchTB1 (m, k)  = (m  ,fmap patch $G.getIndex (m,k) ,  F.toList $ patchAttr  . unTB <$> (unKV k))

difftable
  ::  (PatchConstr k a  , Show a,Show k ) => TBData k a -> TBData k a
     -> Maybe (Index (TBData k a ))
difftable old@(m, v) (n, o) = if L.null attrs then Nothing else Just  (m,   fmap patch  $ G.getIndex old , attrs)
    where attrs = catMaybes $ F.toList  $ Map.mergeWithKey (\_ i j -> Just $ diffAttr (unTB  i) (unTB j)) (const Map.empty ) (fmap (Just. patchAttr . unTB) ) (unKV v) (unKV $  o)

diffTB1 :: (PatchConstr k a ) =>  TB2 k a -> TB2  k  a -> Maybe (PathFTB   (Index (TBData k a )) )
diffTB1 = diffFTB patchTB1  difftable



travPath f p (PatchSet i) = foldl f p i
travPath f p i = f p i

diffTable l l2 =   catMaybes $ F.toList $ Map.intersectionWith (\i j -> diffTB1 i j) (mkMap l) (mkMap l2)
  where mkMap = Map.fromList . fmap (\i -> (getPK i,i))


applyTB1
  :: PatchConstr k a =>
       FTB1 Identity k a -> PathFTB   (TBIdx k (Index a) ) -> FTB1 Identity k a
applyTB1 = applyFTB createTB1 applyRecord

createTB1
  :: PatchConstr d a =>
     (Index (TBData d a )) ->
     (KVMetadata d , Compose Identity  (KV (Compose Identity  (TB Identity))) d a)
createTB1 (m ,s ,k)  = (m , _tb .KV . mapFromTBList . fmap (_tb . createAttr) $  k)


pattrKey (PAttr s _ ) = Set.singleton $ Inline s
pattrKey (PFun s _ _ ) = Set.singleton $ Inline s
pattrKey (PInline s _ ) = Set.singleton $ Inline s
pattrKey (PFK s _ _ _ ) = Set.fromList s


applyRecordChange
   :: PatchConstr d a =>
    TBData d a
     -> TBIdx d (Index a)
     -> Maybe (TBData d a)
applyRecordChange t@((m, v)) (_ ,_  , k)  = fmap ((m ,)  ) $  traComp  (foldedit k) ( v)
  where
    foldedit k v0 =  fmap KV $ foldr  edit (Just $ _kvvalues v0) k
    edit  p m = Map.insert (pattrKey p) <$> maybe (Just $ _tb $ createAttr p) (traComp (flip applyIfChange p)) attr  <*> m
      where attr = join $ Map.lookup (pattrKey p)  <$> m



applyRecord
   :: PatchConstr d a =>
    TBData d a
     -> TBIdx d (Index a)
     -> TBData d a
applyRecord t@((m, v)) (m2 ,p  , k)
  | _kvname m == _kvname m2 && p == fmap patch (G.getIndex t) = (m ,mapComp (KV . flip (foldr (\p m -> Map.alter (\v -> Just $ maybe (_tb $ createAttr p) (mapComp (flip applyAttr p )) v   ) (pattrKey p) m)) k  . _kvvalues ) v)
  | otherwise = create (m2,p,k)
  where edit  v k =  mapComp (flip applyAttr k ) v

patchSet i
  | L.length i == 0 = Nothing
  | L.length i == 1 = safeHead i
  | otherwise = Just $ PatchSet (Non.fromList $ concat $ normalize <$> i)
      where normalize (PatchSet i) = concat $ fmap normalize i
            normalize i = [i]


applyAttrChange :: PatchConstr k a  => TB Identity k a -> PathAttr k (Index a) -> Maybe (TB Identity k a)
applyAttrChange (Attr k i) (PAttr _ p)  = Attr k <$> (applyIfChange i p)
applyAttrChange (Fun k rel i) (PFun _ _ p)  = Fun k rel <$> (applyIfChange i p)
applyAttrChange (FKT k rel  i) (PFK _ p _ b )  =  (\i -> FKT i rel  (create b)) <$> foldedit p k
  where
    foldedit k v0 =  fmap KV $ foldr  edit (Just $ _kvvalues v0) k
    edit  p m = Map.insert (pattrKey p) <$> maybe (Just $ _tb $ createAttr p) (traComp (flip applyIfChange p)) attr  <*> m
      where attr = join $ Map.lookup (pattrKey p)  <$> m

applyAttrChange (IT k i) (PInline _   p)  = IT k <$> (applyIfChange i p)


applyAttr :: PatchConstr k a  => TB Identity k a -> PathAttr k (Index a) -> TB Identity k a
applyAttr (Attr k i) (PAttr _ p)  = Attr k (applyShowable i p)
applyAttr (Fun k rel i) (PFun _ _ p)  = Fun k rel (applyShowable i p)
applyAttr (FKT k rel  i) (PFK _ p _ b )  =  FKT ref  rel  (apply  i b)
  where
              ref =  KV$  Map.mapWithKey (\key vi -> foldl  (\i j ->  edit key j i ) vi p ) (mapFromTBList (concat $ traComp nonRefTB <$>  unkvlist k))
              edit  key  k@(PAttr  s _) v = if (_relOrigin $ justError "no key" $ safeHead $ F.toList $ key) == s then  mapComp (flip applyAttr k ) v else v
applyAttr (IT k i) (PInline _   p)  = IT k (applyTB1 i p)

-- applyAttr i j = errorWithStackTrace ("applyAttr: " <> show (i,j))



diffAttr :: PatchConstr k a  => TB Identity k a -> TB Identity k a -> Maybe (PathAttr k  (Index a))
diffAttr (Attr k i) (Attr l m ) = fmap (PAttr k) (diffShowable i m)
diffAttr (Fun k rel i) (Fun l rel2 m ) = fmap (PFun k rel ) (diffShowable i m)
diffAttr (IT k i) (IT _ l) = fmap (PInline k  ) (diffTB1 i l)
diffAttr (FKT  k _ i) (FKT m rel b) = (\l m -> Just (PFK rel l m  (patch b))) (catMaybes $ F.toList $ Map.intersectionWith (\i j -> diffAttr (unTB i) (unTB j)) (_kvvalues k) (_kvvalues m)  ) kvempty

patchAttr :: PatchConstr k a  => TB Identity k a -> PathAttr k (Index a)
patchAttr a@(Attr k v) = PAttr k  (patchFTB patch   v)
patchAttr a@(Fun k rel v) = PFun k  rel (patchFTB patch v)
patchAttr a@(IT k v) = PInline k (patchFTB patchTB1 v)
patchAttr a@(FKT k rel v) = PFK rel (patchAttr . unTB <$> unkvlist k) kvempty (patch v)

-- createAttr (PatchSet l) = concat $ fmap createAttr l
createAttr :: PatchConstr k a  => PathAttr k (Index a) -> TB Identity k a
createAttr (PAttr  k s  ) = Attr k  (createShowable s)
createAttr (PFun k rel s  ) = Fun k  rel (createShowable s)
createAttr (PInline k s ) = IT k (createFTB createTB1 s)
createAttr (PFK rel k s b ) = FKT (kvlist $ _tb . createAttr <$> k) rel  (createFTB  createTB1   b)




diffShowable ::  (Show a,Ord a ,Patch a ) => FTB a -> FTB a -> Maybe (PathFTB (Index a))
diffShowable = diffFTB patch diff

applyShowable ::  (Show a,Ord a ,Patch a ) => FTB a ->  PathFTB   (Index a)  -> FTB a
applyShowable = applyFTB create apply

createShowable :: (Show a,Ord a ,Patch a)=>  PathFTB (Index a) -> FTB a
createShowable = createFTB create


diffPrim :: (Eq a ,a ~ Index a) => a -> a -> Maybe (Index a)
diffPrim i j
  | i == j = Nothing
  | otherwise = Just  j


-- FTB

patchFTB :: Show a => (a -> Index a) -> FTB a -> PathFTB   (Index a)
patchFTB p (LeftTB1 j )  = POpt (patchFTB p <$> j)
patchFTB p (ArrayTB1 j )  = justError ("empty array in arraytb1 patchftb" <> show j)$  patchSet   $ zipWith (\i m ->  PIdx i  (Just m) ) [0..]  (F.toList $ patchFTB p <$> j)
patchFTB p (DelayedTB1 j ) = PDelayed (patchFTB p <$> j)
patchFTB p (SerialTB1 j ) = PSerial (patchFTB p <$> j)
patchFTB p (IntervalTB1 j ) =  justError ("no patch for" <> show j) $ patchSet  [PInter True $ (first (fmap (patchFTB p )) $ Interval.lowerBound' j) , PInter False $ (first (fmap (patchFTB p )) $ Interval.upperBound' j)]
patchFTB p (TB1 j) = PAtom $ p j

diffOpt :: (Ord a,Show a) => (a -> Index a ) -> (a -> a -> Maybe (Index a)) ->  Maybe (FTB a) -> Maybe (FTB a) -> Maybe (Maybe (PathFTB    (Index a)))
diffOpt p d i j
    | isJust i && isJust j = sequenceA $ liftA2 (diffFTB  p d ) i j
    | isJust i && isNothing j = Just $ Nothing
    | isNothing i && isJust j = Just $ (patchFTB p <$> j)
    | i /= j = ( liftA2 (diffFTB p d ) i j )
    | otherwise = Nothing

diffFTB :: (Ord a,Show a) => (a -> Index a) -> (a -> a -> Maybe (Index a) ) ->  FTB a -> FTB a -> Maybe (PathFTB (Index a))
diffFTB p d (LeftTB1 i) (LeftTB1 j) = POpt <$> diffOpt p d i j
diffFTB p d (ArrayTB1 i) (ArrayTB1 j) =
    patchSet $  catMaybes $ zipWith (\i -> fmap (PIdx  i)  ) ( [0..]) (F.toList  (Non.zipWith (\i j ->fmap Just $ diffFTB p d i j ) i j)  <> (const (Just  Nothing) <$> Non.drop (Non.length j  ) i ) <> (Just . Just . patchFTB p <$> Non.drop (Non.length i  ) j ))
diffFTB p d (SerialTB1 i) (SerialTB1 j) = fmap PSerial $ diffOpt p d i j
diffFTB p d (DelayedTB1 i) (DelayedTB1 j) = fmap PDelayed $ diffOpt p d i j
diffFTB p d (IntervalTB1 i) (IntervalTB1 j)
  | i == j = Nothing
  | otherwise =  patchSet $  catMaybes   [match True (lowerBound' i ) (lowerBound' j) ,match False (upperBound' i ) (upperBound' j) ]
    where match f i j = fmap (PInter f . (,snd $  j)) (maybe (if snd j == snd i then Nothing  else Just $ patchFTB p <$> (fst $ j))  Just $ diffExtended (fst $  i) (fst $  j) )
          -- diffExtended :: Extended (FTB a) -> Extended (FTB a) -> Maybe (Extended (PathFTB (Index a)))
          diffExtended (Finite i ) (Finite j) = fmap Finite $ diffFTB p d i j
          diffExtended _ (Finite i) = Just $ Finite $ patchFTB p  i
          diffExtended _   i = Nothing

diffFTB p d (TB1 i) (TB1  j) = fmap PAtom $ d i j
diffFTB p d  i j = errorWithStackTrace ("diffError" <> show (i,j))


instance Applicative Interval.Extended where
  pure i = Interval.Finite i
  (Interval.Finite i) <*> (Interval.Finite j) =  Interval.Finite $ i j


applyOpt
  :: (Show a,Ord a) =>
     (Index a -> a)
     -> (a -> Index a  -> a)-> Maybe (FTB a) -> Maybe (PathFTB (Index a)) ->  (Maybe (FTB a))
applyOpt  pr a i  o = case i of
                      Nothing -> case o of
                            Nothing -> Nothing
                            Just j -> createFTB pr <$> o
                      Just _ -> applyFTB pr a <$> i <*> o

applyFTB
  :: (Ord a,Show a) =>
  (Index a  -> a) -> (a -> Index a -> a) -> FTB a -> PathFTB (Index a) -> FTB a
applyFTB pr a (LeftTB1 i ) op@(POpt o) = LeftTB1 $ applyOpt pr a i o
applyFTB pr a (ArrayTB1 i ) (PIdx ix o) = case o of
                      Nothing -> ArrayTB1 $ Non.fromList $ Non.take ix   i
                      Just p -> if ix <=  Non.length i - 1
                                then ArrayTB1 $ Non.imap (\i v -> if i == ix then applyFTB pr a v p else v )  i
                                else if ix == Non.length i
                                      then ArrayTB1 $ i <> pure (createFTB pr p)
                                      else errorWithStackTrace $ "ix bigger than next elem"
applyFTB pr a (SerialTB1 i ) (PSerial o) = SerialTB1 $  applyOpt pr a i o
applyFTB pr a (DelayedTB1 i ) (PDelayed o) = DelayedTB1 $  applyOpt pr a i o
applyFTB pr a (IntervalTB1 i) (PInter b (p,l))
  = IntervalTB1 $  if b
        then interval (second (const l) $ first (mapExtended p) (lowerBound' i))    (upperBound' i)
        else interval (lowerBound' i) (second (const l) $ first (mapExtended  p ) (upperBound' i))
  where
    mapExtended p (Interval.Finite i) = applyFTB pr a i <$> p
    mapExtended p _ = createFTB pr  <$> p
applyFTB pr a (TB1 i) (PAtom p)  =  TB1 $ a i p
applyFTB pr a  b (PatchSet l ) = foldl (applyFTB pr a ) b l
applyFTB _ _ a b = errorWithStackTrace ("applyFTB: " )

checkInter :: (Show a,Ord a) => (Index a  ->  a) -> PathFTB (Index a) -> Interval.Interval (FTB a)-> Interval.Interval (FTB a)
checkInter p (PInter b o) inter = if fst (lowerBound' inter) == Interval.PosInf || fst (upperBound' inter) == Interval.NegInf then errorWithStackTrace ("invalid interval" <> (show $ (b,createFTB p <$> (fst o)))) else inter

createFTB :: (Show a,Ord a) => (Index a  ->  a) -> PathFTB (Index a) -> FTB a
createFTB p (POpt i ) = LeftTB1 (createFTB p <$> i)
createFTB p (PSerial i ) = SerialTB1 (createFTB p <$> i)
createFTB p (PDelayed i ) = DelayedTB1 (createFTB p <$> i)
createFTB p (PIdx ix o ) = ArrayTB1 (fromJust  $  pure . createFTB p <$> o)
createFTB p (PInter b o ) = IntervalTB1 $ checkInter p (PInter b o) inter
  where inter = if b then interval (first (fmap ( createFTB p) ) o) (Interval.PosInf,False) else  interval  (Interval.NegInf,False) ( first (fmap (createFTB p)) o)
createFTB p (PAtom i )  = TB1 $ p i
createFTB p (PatchSet l)
  | L.null l= errorWithStackTrace "no patch"
  | otherwise = foldl1 mappend (createFTB p <$> l)


instance (Ord a )=> Monoid (FTB a) where
 mempty = LeftTB1 Nothing
 mappend (LeftTB1 i) (LeftTB1 j) = LeftTB1 (j)
 mappend (IntervalTB1 i) (IntervalTB1 j) = IntervalTB1 ( i `Interval.intersection` j)
 mappend (ArrayTB1 i) (ArrayTB1 j) = ArrayTB1 (i <>  j)
 mappend (DelayedTB1 i) (DelayedTB1 j) = DelayedTB1 (j)
 mappend (SerialTB1 i) (SerialTB1 j) = SerialTB1 (j)
 mappend (TB1 i) (TB1 j) = TB1 j

imap f = map (uncurry f) . zip [0..]

