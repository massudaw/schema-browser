{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor #-}
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

module Patch where

-- import Warshal
import Types
import Data.Functor.Apply
import Data.Bifunctor
import Data.Maybe
import GHC.Generics
import Data.Either
import Data.Binary (Binary)
import Data.Functor.Identity
import Utils
import Data.Traversable(sequenceA)
import Data.Vector(Vector)
import qualified Data.Vector as Vector
import Data.Functor.Classes
import Data.Foldable (Foldable)
import qualified Data.Foldable as F
import qualified Data.Interval as Interval
import Data.Interval (lowerBound,upperBound,(<..<))
import Data.Monoid hiding (Product)

import qualified Data.Text.Lazy as T
import qualified Data.ByteString as BS


import GHC.Stack

import Data.Traversable(Traversable)
import Database.PostgreSQL.Simple.Time

import Debug.Trace
import Data.Time
import Data.Time.Clock.POSIX
import Control.Monad
import GHC.Exts
import Control.Applicative
import qualified Data.List as L
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Control.Monad.State
import Data.Text.Lazy(Text)

import Data.Unique


{-
t1 =  tblistPK (Set.singleton "id")  [Compose $ Identity $ Attr "id" (TB1 (SNumeric 2)),Compose $ Identity $ Attr "at1" (LeftTB1 $ Just (ArrayTB1 [TB1 $ SNumeric 1]))]
t1pk =  TB1 (SNumeric 2)
p1,p2,p3 :: PathT String
p1 = PIndex kvempty (Set.singleton ("id",t1pk)) $ Just $ PKey True (Set.fromList [Inline "at1"]) $ (POpt Nothing)
p2 = PIndex kvempty (Set.singleton ("id",t1pk)) $ Just $ PKey True (Set.fromList [Inline "at1"]) $ (POpt (Just (PIdx 0 (Just $ PAtom $ SNumeric 4))))
p3 = PIndex kvempty (Set.singleton ("id",t1pk)) $ Just $PKey True (Set.fromList [Inline "at1"]) $ (POpt (Just (PIdx 1 (Just $ PAtom $ SNumeric 5))))
p4 = PIndex kvempty (Set.singleton ("id",t1pk)) $ Just $PKey True (Set.fromList [Inline "at1"]) $ (POpt (Just (PIdx 1 Nothing )))
-}

data PathFTB   a
  = POpt (Maybe (PathFTB a))
  | PDelayed (Maybe (PathFTB a))
  | PSerial (Maybe (PathFTB a))
  | PIdx Int (Maybe (PathFTB a))
  | PInter Bool (PathFTB a)
  | PatchSet [PathFTB a]
  | PAtom a
  deriving(Show,Eq,Ord,Functor,Generic)

type family Index k
type instance Index Showable = Showable
type instance Index (TBData k a ) =  TBIdx k a

type PatchConstr k a = (a ~ Index a, Ord a , Show a,Show k , Ord k)

type TBIdx  k a = (KVMetadata k, Set (k ,FTB a ),[PathAttr k a])

data PathAttr k a
  = PAttr k (PathFTB a)
  | PInline k (PathFTB  (TBIdx k a ))
  deriving(Show,Eq,Ord,Generic)

instance (Binary k ) => Binary (PathFTB k )
instance (Binary k ,Binary a) => Binary (PathAttr k a)

data PathTID
  = PIdIdx Int
  | PIdOpt
  | PIdSerial
  | PIdDelayed
  | PIdInter Bool
  | PIdAtom
  deriving (Eq,Ord,Show)


firstPatch :: (Ord a ,Ord k , Ord j ) => (k -> j ) -> TBIdx k a -> TBIdx j a
firstPatch f (i,j,k) = (mapKVMeta f i , Set.map (first f) j ,fmap (firstPatchAttr f) k)

firstPatchAttr :: (Ord k , Ord j ,Ord a ) => (k -> j ) -> PathAttr k a -> PathAttr j a
firstPatchAttr f (PAttr k a) = PAttr (f k) a
firstPatchAttr f (PInline k a) = PInline (f k) (fmap (firstPatch f) a)


compactionLaw t l = diffTB1 t (foldl applyTB1 t l ) == compactPatches l

compactTB1 :: (Ord a , Show a, Ord b ,Show b) => [TBIdx a b] -> [TBIdx a b ]
compactTB1 i = fmap (\((i,j),p)-> (i,j,concat p)) $  groupSplit2 (\(i,j,_) -> (i,j))  (\(_,_,p) -> p) i

compactAttr :: (Ord a , Show a, Ord b ,Show b) => [PathAttr a b ] -> [PathAttr a b ]
compactAttr  i =  fmap recover .  groupSplit2 projectors pathProj $ i
  where
    pathProj (PAttr i j)  = Right j
    pathProj (PInline i j)  = Left j
    projectors (PAttr i j ) =  i
    projectors (PInline i j) = i
    recover (i,j) = PAttr i (last $ rights j)
    recover (i,j) = PInline i (last  $lefts j)



compactPatches :: (Ord a ,Show a)=> [PathFTB  a] -> Maybe (PathFTB  a)
compactPathces [] = Nothing
compactPatches i = patchSet . fmap recover .  groupSplit2 projectors pathProj . concat . fmap expandPSet $ i
  where
    pathProj (PIdx _ i) = i
    pathProj (POpt  i) = i
    pathProj (PSerial i) = i
    pathProj (PDelayed i) = i
    pathProj (PInter _ i) = Just i
    pathProj i@(PAtom _  ) = Just i
    pathProj i = errorWithStackTrace (show i)
    projectors (PIdx i _ ) = PIdIdx i
    projectors (POpt _  ) = PIdOpt
    projectors (PSerial _  ) = PIdSerial
    projectors (PDelayed _  ) = PIdDelayed
    projectors (PInter b _  ) = PIdInter b
    projectors (PAtom _  ) =  PIdAtom
    projectors i = errorWithStackTrace (show i)
    recover (PIdIdx i, j ) = PIdx i  (compact j)
    recover (PIdOpt , j ) = POpt  (compact j)
    recover (PIdSerial , j ) = PSerial (compact j)
    recover (PIdDelayed , j ) = PDelayed (compact j)
    recover (PIdInter i , j ) = PInter i (justError "no patch inter" $ compact j)
    recover (PIdAtom , j ) = justError "can't be empty " $ patchSet (catMaybes j)
    recover i = errorWithStackTrace (show i)
    compact j = join $ compactPatches <$> Just (catMaybes j)



expandPSet (PatchSet l ) =  l
expandPSet p = [p]

groupSplit2 :: Ord b => (a -> b) -> (a -> c ) -> [a] -> [(b ,[c])]
groupSplit2 f g = fmap (\i-> (f $ head i , g <$> i)) . groupWith f


applyTable
  ::  PatchConstr k a  => [FTB1 Identity k a ] -> PathFTB  (TBIdx k a )-> [FTB1 Identity k a ]
applyTable l pidx@(PAtom (m,i, p) ) =  case L.find (\tb -> getPK tb == i ) l  of
                  Just _ ->  catMaybes $ L.map (\tb@(TB1 (m, k)) -> if  getPK tb ==  i  then (case p of
                                                [] ->  Nothing
                                                ps -> Just $ TB1 $ applyRecord (m,k) (m,i,p)
                                              ) else  (Just tb )) l
                  Nothing -> (createFTB createTB1  pidx) : l
applyTable l i = errorWithStackTrace (show (l,i))


getPK (TB1 i) = getPKM i
getPKM (m, k) = Set.fromList (concat (fmap aattr $ F.toList $ (Map.filterWithKey (\k v -> Set.isSubsetOf  (Set.map _relOrigin k)(_kvpk m)) (  _kvvalues (runIdentity $ getCompose k)))))

getPKAttr (m, k) = traComp (concat . F.toList . (Map.filterWithKey (\k v -> Set.isSubsetOf  (Set.map _relOrigin k)(_kvpk m))   )) k

travPath f p (PatchSet i) = foldl f p i
travPath f p i = f p i

diffTable l l2 =   catMaybes $ F.toList $ Map.intersectionWith (\i j -> diffTB1 i j) (mkMap l) (mkMap l2)
  where mkMap = Map.fromList . fmap (\i -> (getPK i,i))


applyTB1
  :: (Index a~ a ,Show a , Ord a ,Show k , Ord k) =>
       FTB1 Identity k a -> PathFTB   (TBIdx k a ) -> FTB1 Identity k a
applyTB1 = applyFTB createTB1 applyRecord

createTB1
  :: (Index a~ a ,Show a , Ord a ,Show d, Ord d ) =>
     (Index (TBData d a )) ->
     (KVMetadata d , Compose Identity  (KV (Compose Identity  (TB Identity))) d a)
createTB1 (m ,s ,k)  = (m , _tb .KV . mapFromTBList . fmap (_tb . createAttr) $  k)
createTB1  i = errorWithStackTrace (show i)



applyRecord
  :: (Index a~ a ,Show a , Ord a ,Show d, Ord d  ) =>
    TBData d a
     -> TBIdx d a
     -> TBData d a
applyRecord t@((m, v)) (_ ,_  , k)  = (m ,mapComp (KV . Map.mapWithKey (\key vi -> foldl  (edit key) vi k  ) . _kvvalues ) v)
  where edit  key v k@(PAttr  s _)  = if (_relOrigin $ head $ F.toList $ key) == s then  mapComp (flip applyAttr k ) v else v
        edit  key v k@(PInline s _ ) = if (_relOrigin $ head $ F.toList $ key) == s then  mapComp (flip applyAttr k ) v else v

patchTB1 :: (Show a , Ord a ,a ~ Index a ,Show k,Ord k) => TBData k  a -> Index (TBData k  a)
patchTB1 (m, k)  = (m  ,(getPKM (m,k)) ,  F.toList $ patchAttr  . unTB <$> (unKV k))

difftable
  ::  (a ~ Index a, Ord a , Show a,Show k , Ord k) => TBData k a -> TBData k a
     -> Maybe (Index (TBData k a ))
difftable (m, v) (n, o) = if L.null attrs then Nothing else Just  (m, (getPKM (m,v)), attrs)
    where attrs = catMaybes $ F.toList  $ Map.intersectionWith (\i j -> diffAttr (unTB i) (unTB j)) (unKV v) (unKV o)

diffTB1 :: (a ~ Index a ,Ord a, Show a, Ord k ,Show k) =>  TB2 k a -> TB2  k  a -> Maybe (PathFTB   (Index (TBData k a )) )
diffTB1 = diffFTB patchTB1  difftable


patchSet i
  | L.length i == 0 = Nothing
  | L.length i == 1 = Just$ head i
  | otherwise = Just $ PatchSet (concat $ normalize <$> i)
      where normalize (PatchSet i) = concat $ fmap normalize i
            normalize i = [i]



applyAttr :: PatchConstr k a  => TB Identity k a -> PathAttr k a -> TB Identity k a
applyAttr (Attr k i) (PAttr _ p)  = Attr k (applyShowable i p)
applyAttr (IT k i) (PInline _   p)  = IT k (applyTB1 i p)
--applyAttr (FKT  k rel i) (PKey _ s (p@(PIndex m ix _)))  = FKT k rel  (applyTB1 i p)
-- applyAttr (FKT  k rel i) (PKey b s (p))  = FKT (mapComp (\i -> if Set.fromList (keyattri i)  == s  then applyAttr i (PKey b s (p )) else i ) <$>  k) rel  (applyTB1 i p)
applyAttr i j = errorWithStackTrace (show (i,j))



diffAttr :: PatchConstr k a  => TB Identity k a -> TB Identity k a -> Maybe (PathAttr k  a )
diffAttr (Attr k i) (Attr l m ) = fmap (PAttr k) (diffShowable i m)
diffAttr (IT k i) (IT _ l) = fmap (PInline (_relOrigin $ head $ keyattr k ) ) (diffTB1 i l)
-- diffAttr (FKT  k _ i) (FKT m _ l) = patchSet $ catMaybes $ zipWith (\i j -> diffAttr (unTB i) (unTB j)) k m  <> [diffTB1 i l]

patchAttr :: PatchConstr k a  => TB Identity k a -> PathAttr k (Index a)
patchAttr a@(Attr k v) = PAttr k  (patchFTB id v)
patchAttr a@(IT k v) = PInline (_relOrigin $ head $ (keyattr k)) (patchFTB patchTB1 v)
--patchAttr a@(FKT k rel v) = PKey False (Set.fromList (keyattri  a)) ( patchFTB patchTB1 v)

-- createAttr (PatchSet l) = concat $ fmap createAttr l
createAttr :: PatchConstr k a  => PathAttr k a -> TB Identity k a
createAttr (PAttr  k s  ) = Attr k  (createShowable s)
createAttr (PInline k s ) = IT (_tb $ Attr k (TB1 ())) (createFTB createTB1 s)

createAttr i = errorWithStackTrace (show i)



diffShowable ::  (Show a,Ord a ,a ~ Index a) => FTB a -> FTB a -> Maybe (PathFTB (Index a))
diffShowable = diffFTB id diffPrim

applyShowable ::  (Show a,Ord a ,a ~ Index a) => FTB a ->  PathFTB   (Index a)  -> FTB a
applyShowable = applyFTB id (flip const )

createShowable = createFTB id

diffPrim :: (Eq a ,a ~ Index a) => a -> a -> Maybe (Index a)
diffPrim i j
  | i == j = Nothing
  | otherwise = Just  j


-- FTB

patchFTB :: (a -> Index a) -> FTB a -> PathFTB   (Index a)
patchFTB p (LeftTB1 j )  = POpt (patchFTB p <$> j)
patchFTB p (ArrayTB1 j )  = justError "can't be empty" $  patchSet   $ zipWith (\i m ->  PIdx i  (Just m) ) [0..]  (F.toList $ patchFTB p <$> j)
patchFTB p (DelayedTB1 j ) = PDelayed (patchFTB p <$> j)
patchFTB p (SerialTB1 j ) = PSerial (patchFTB p <$> j)
patchFTB p (TB1 j) = PAtom $ p j
-- patchFTB p i = errorWithStackTrace (show i)

diffOpt :: (Ord a,Show a) => (a -> Index a ) -> (a -> a -> Maybe (Index a)) ->  Maybe (FTB a) -> Maybe (FTB a) -> Maybe (Maybe (PathFTB    (Index a)))
diffOpt p d i j
    | isJust i && isJust j = sequenceA $ liftA2 (diffFTB  p d ) i j
    | isJust i && isNothing j = Just $ Nothing
    | isNothing i && isJust j = Just $ (patchFTB p <$> j)
    | i /= j = ( liftA2 (diffFTB p d ) i j )
    | otherwise = Nothing

diffFTB :: (Ord a,Show a) => (a -> Index a) -> (a -> a -> Maybe (Index a) ) ->  FTB a -> FTB a -> Maybe (PathFTB   (Index a))
diffFTB p d (LeftTB1 i) (LeftTB1 j) = POpt <$> diffOpt p d i j
diffFTB p d (ArrayTB1 i) (ArrayTB1 j) =
    patchSet $  catMaybes $ zipWith (\i -> fmap (PIdx  i)  ) ( [0..]) (F.toList $ (zipWith (\i j ->fmap Just $ diffFTB p d i j ) i j)  <> (const (Just  Nothing) <$> drop (length j  ) i ) <> (Just . Just . patchFTB p <$> drop (length i  ) j ))
diffFTB p d (SerialTB1 i) (SerialTB1 j) = fmap PSerial $ diffOpt p d i j
diffFTB p d (DelayedTB1 i) (DelayedTB1 j) = fmap PDelayed $ diffOpt p d i j
diffFTB p d (IntervalTB1 i) (IntervalTB1 j)
  | i == j = Nothing
  | otherwise =  patchSet $  catMaybes   [fmap (PInter False) (diffFTB p d (unFinite $ Interval.lowerBound i) (unFinite $ Interval.lowerBound j) ),fmap (PInter True) (  diffFTB p d (unFinite $ Interval.upperBound i) (unFinite $ Interval.upperBound j) )]

diffFTB p d (TB1 i) (TB1  j) = fmap PAtom $ d i j
diffFTB p d  i j = errorWithStackTrace (show (i,j))

unFinite (Interval.Finite i ) =  i

instance Applicative Interval.Extended where
  pure i = Interval.Finite i
  (Interval.Finite i) <*> (Interval.Finite j) =  Interval.Finite $ i j

applyOpt  pr a i  o = case i of
                      Nothing -> case o of
                            Nothing -> Nothing
                            Just j -> createFTB pr <$> o
                      Just _ -> applyFTB pr a <$> i <*> o
applyFTB pr a (LeftTB1 i ) op@(POpt o) = LeftTB1 $ applyOpt pr a i o
applyFTB pr a (ArrayTB1 i ) (PIdx ix o) = case o of
                      Nothing -> ArrayTB1 $ take ix   i
                      Just p -> if ix <=  length i - 1
                                then ArrayTB1 $ imap (\i v -> if i == ix then applyFTB pr a v p else v )  i
                                else if ix == length i
                                      then ArrayTB1 $ i <> [createFTB pr p]
                                      else errorWithStackTrace $ "ix bigger than next elem" <> show (ix, length i)
applyFTB pr a (SerialTB1 i ) (PSerial o) = SerialTB1 $  applyOpt pr a i o
applyFTB pr a (DelayedTB1 i ) (PDelayed o) = DelayedTB1 $  applyOpt pr a i o
applyFTB pr a (IntervalTB1 i) (PInter b p)
    = IntervalTB1 $ if b
        then fmap (flip (applyFTB pr a) p) (lowerBound i)  Interval.<..<  upperBound i
        else lowerBound i Interval.<..<  fmap (flip (applyFTB pr a) p ) (upperBound i)
applyFTB pr a (TB1 i) (PAtom p)  =  TB1 $ a i p
applyFTB pr a  b (PatchSet l ) = foldl (applyFTB pr a ) b l

-- createFTB :: (Index a  ->  a) -> PathFTB (Index a) -> a
createFTB p (POpt i ) = LeftTB1 (createFTB p <$> i)
createFTB p (PSerial i ) = SerialTB1 (createFTB p <$> i)
createFTB p (PDelayed i ) = DelayedTB1 (createFTB p <$> i)
createFTB p (PIdx ix o ) = ArrayTB1 (fromJust  $  pure . createFTB p <$> o)
createFTB p (PInter b o ) = errorWithStackTrace "interval"
createFTB p (PAtom i )  = TB1 $ p i
createFTB p (PatchSet l) = foldl1 mappend (createFTB p <$> traceShow "createFTB PatchSet" l)


instance Monoid (FTB a) where
 mappend (LeftTB1 i) (LeftTB1 j) = LeftTB1 (i <> j)
 mappend (ArrayTB1 i) (ArrayTB1 j) = ArrayTB1 (i <> j)
 -- mappend (PatchSet i) (PatchSet j) = PatchSet (i <> j)

imap f = map (uncurry f) . zip [0..]

