{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor #-}
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
import Control.Lens.TH
import Data.Functor.Apply
import Data.Bifunctor
import Data.Maybe
import GHC.Generics
import Data.Text.Binary
import Data.Binary (Binary)
import Data.Vector.Binary
import qualified Data.Binary as B
import Data.Functor.Identity
import Data.Ord
import Utils
import Data.Typeable
import Data.Traversable(traverse,sequenceA)
import Data.Vector(Vector)
import qualified Data.Vector as Vector
import Data.Functor.Classes
import Data.Foldable (Foldable)
import qualified Data.Foldable as F
import qualified Data.Interval as Interval
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



t1 =  [tblistPK (Set.singleton "id")  [Compose $ Identity $ Attr "id" (TB1 (SNumeric 2)),Compose $ Identity $ Attr "at1" (LeftTB1 $ Just (ArrayTB1 [TB1 $ SNumeric 1]))]]
t1pk =  TB1 (SNumeric 2)
p1,p2,p3 :: PathT String
p1 = PIndex (Set.singleton t1pk) $ Just $ PKey (Set.fromList [Inline "at1"]) $ Just  (POpt Nothing)
p2 = PIndex (Set.singleton t1pk) $ Just $ PKey (Set.fromList [Inline "at1"]) $ Just (POpt (Just (PIdx 0 (Just $ PAtom $ SNumeric 4))))
p3 = PIndex (Set.singleton t1pk) $ Just $PKey (Set.fromList [Inline "at1"]) $ Just (POpt (Just (PIdx 1 (Just $ PAtom $ SNumeric 5))))


compactionLaw t l = diffTable t (foldl applyTable t l ) == Just (compactPatches l)


compactPatches :: Ord k => [PathT k] -> PathT k
compactPatches  = justError "cant be empty" . patchSet . fmap recover .  groupSplit2 projectors pathProj
  where
    pathProj (PIndex _ i) = i
    pathProj (PIdx _ i) = i
    pathProj (POpt  i) = i
    pathProj (PKey _ i  ) = i
    pathProj i@(PAtom _  ) = Just i
    projectors :: Ord k => PathT k -> PathTID k
    projectors (PKey i _ ) = PIdPK i
    projectors (PIndex i _ ) = PIdIndex i
    projectors (PIdx i _ ) = PIdIdx i
    projectors (POpt _  ) = PIdOpt
    projectors (PAtom _  ) =  PIdAtom
    recover (PIdPK i, j ) = PKey i  (compact j)
    recover (PIdIndex i, j ) = PIndex i  (compact j)
    recover (PIdIdx i, j ) = PIdx i  (compact j)
    recover (PIdOpt , j ) = POpt  (compact j)
    recover (PIdAtom , j ) = justError "can't be empty " $ patchSet (catMaybes j)
    compact j = compactPatches <$> Just (catMaybes j)

data PathTID k
  = PIdPK (Set (Rel k))
  | PIdIndex (Set (FTB Showable))
  | PIdIdx Int
  | PIdOpt
  | PIdAtom
  deriving (Eq,Ord)

groupSplit2 :: Ord b => (a -> b) -> (a -> c ) -> [a] -> [(b ,[c])]
groupSplit2 f g = fmap (\i-> (f $ head i , g <$> i)) . groupWith f


applyTable
  ::  (Ord k ,Show k) => [FTB1 Identity k Showable] -> PathT k -> [FTB1 Identity k Showable]
applyTable l (PIndex i  p) =  catMaybes $ L.map (\tb@(TB1 (m, k)) -> if  getPK tb ==  i  then (case p of
                                                Just ps -> Just $ travPath applyTB1  (TB1 (m, k)) ps
                                                Nothing ->  Nothing
                                              ) else  (Just tb )) l

getPK (TB1 (m, k)) = Set.fromList (concat (fmap (fmap snd . aattr)  $ F.toList $ (Map.filterWithKey (\k v -> Set.isSubsetOf (_kvpk m) (Set.map _relOrigin k)) (  _kvvalues (runIdentity $ getCompose k)))))

diffTable l l2 =  patchSet $ fmap (\(k,v) -> PIndex k  (Just v)) $  mapMaybe (\(k,v) -> (k,) <$> v ) $ Map.toList $ Map.intersectionWith (\i j -> diffTB1 i j) (mkMap l) (mkMap l2)
  where mkMap = Map.fromList . fmap (\i -> (getPK i,i))

travPath f p (PatchSet i) = foldl f p i
travPath f p i = f p i

applyTB1
  :: (Show k , Ord k) =>
       FTB1 Identity k Showable -> PathT k -> FTB1 Identity k Showable
applyTB1 t@(TB1 (m, v)) (PKey s (Just k)) = TB1 (m ,mapComp (KV . Map.mapWithKey (\key v -> if key == s then  mapComp (flip applyAttr (PKey s (Just k)) ) v else v ) . _kvvalues ) v)


patchSet i
  | L.length i == 0 = Nothing
  | L.length i == 1 = Just$ head i
  | otherwise = Just $ PatchSet (concat $ normalize <$> i)
      where normalize (PatchSet i) = concat $ fmap normalize i
            normalize i = [i]

unKV = _kvvalues . unTB

applyAttr (Attr k i) (PKey s (Just p))  = Attr k (applyShowable i p)
applyAttr (IT k i) (PKey s (Just p))  = IT k (applyTB1 i p)
applyAttr (FKT  k rel i) (PKey s (Just p@(PIndex ix _)))  = FKT k rel  (applyTB1 i p)
applyAttr (FKT  k rel i) (PKey s (Just p))  = FKT (mapComp (\i -> if Set.fromList (keyattri i)  == s  then applyAttr i (PKey s (Just p )) else i ) <$>  k) rel  (applyTB1 i p)


diffPrimitive :: (Show k , Ord k) => FTB Showable -> FTB Showable -> Maybe (PathT k)
diffPrimitive = diffFTB patchPrim diffPrim

diffAttr :: (Show k ,Ord k) => TB Identity k Showable -> TB Identity k Showable -> Maybe (PathT k )
diffAttr (Attr k i) (Attr l m ) = fmap (PKey (Set.singleton $ Inline k) . Just ) (diffPrimitive i m)
diffAttr (IT k i) (IT _ l) = fmap (PKey (Set.fromList $ keyattr k ) . Just ) (diffTB1 i l)
diffAttr (FKT  k _ i) (FKT m _ l) = patchSet $ catMaybes $ zipWith (\i j -> diffAttr (unTB i) (unTB j)) k m  <> [diffTB1 i l]


createAttr (PKey s (Just k) ) = Attr (_relOrigin $ head $ Set.toList s) (createShowable k)

applyShowable (LeftTB1 i ) op@(POpt o) = case i of
                      Nothing -> case o of
                            Nothing -> LeftTB1 Nothing
                            Just j -> createShowable op
                      Just _ -> LeftTB1 (applyShowable  <$> i <*> o )
applyShowable (ArrayTB1 i ) (PIdx ix o) = case o of
                      Nothing -> ArrayTB1 $ take (ix +1)  i
                      Just p -> if ix <=  length i - 1
                                then ArrayTB1 $ imap (\i v -> if i == ix then applyShowable v p else v )  i
                                else if ix == length i
                                      then ArrayTB1 $ i <> [createShowable p]
                                      else errorWithStackTrace $ "ix bigger than next elem" <> show (ix, length i)
applyShowable i p = errorWithStackTrace (show (i,p))

createShowable (PAtom i ) = TB1 i
createShowable (POpt i ) = LeftTB1 (createShowable <$> i)
createShowable (PIdx ix o ) = ArrayTB1 (fromJust  $  pure . createShowable <$> o)

patchPrim j = PAtom j

patchAttr a@(Attr k v) = PKey (Set.fromList (keyattri a)) (Just $ patchFTB patchPrim v)
patchAttr a@(IT k v) = patchFTB patchTB1 v
patchAttr a@(FKT k rel v) = patchFTB patchTB1 v


patchTB1 (m, k)  = justError "can't be empty"$ patchSet $  F.toList $ patchAttr  . unTB <$> (unKV k)

difftable
  ::  (Show k , Ord k) => (t,
      Compose
        Identity (KV (Compose Identity (TB Identity))) k Showable)
     -> (t1,
         Compose
           Identity (KV (Compose Identity (TB Identity))) k Showable)
     -> Maybe (PathT k )
difftable (m, v) (n, o) = patchSet $ catMaybes $ F.toList  $ Map.intersectionWith (\i j -> diffAttr (unTB i) (unTB j)) (unKV v) (unKV o)

diffTB1 :: (Ord k ,Show k) =>  TB2 k Showable -> TB2  k  Showable -> Maybe (PathT k )
diffTB1 = diffFTB patchTB1  difftable

patchFTB :: (a -> PathT k) -> FTB a -> PathT k
patchFTB p (LeftTB1 j )  = POpt  (patchFTB p <$> j)
patchFTB p (ArrayTB1 j )  = justError "can't be empty" $  patchSet   $ zipWith (\i m ->  PIdx i  (Just m) ) [0..]  (F.toList $ patchFTB p <$> j)
patchFTB p (TB1 j) = p j

diffFTB :: (Ord a,Show a,Show k) => (a -> PathT k ) -> (a -> a -> Maybe (PathT k)) ->  FTB a -> FTB a -> Maybe (PathT k)
diffFTB p d  (LeftTB1 i) (LeftTB1 j)
    | isJust i && isJust j = fmap POpt (sequenceA $ liftA2 (diffFTB  p d ) i j)
    | isJust i && isNothing j = Just $ POpt Nothing
    | isNothing i && isJust j = Just $ POpt (patchFTB p <$> j)
    | i /= j = fmap POpt ( liftA2 (diffFTB p d ) i j )
    | otherwise = Nothing -- POpt Nothing
diffFTB p d (ArrayTB1 i) (ArrayTB1 j) =
    patchSet $  catMaybes $ zipWith (\i -> fmap (PIdx  i . Just) ) ( [0..]) (F.toList $ (zipWith (diffFTB p d ) i j)  <> (Just . patchFTB p <$> drop (length j) i ) <> (Just . patchFTB p <$> drop (length i ) j ))
diffFTB p d (SerialTB1 i) (SerialTB1 j) = diffFTB p d (LeftTB1 i) (LeftTB1 j)
diffFTB p d (DelayedTB1 i) (DelayedTB1 j) = diffFTB p d (LeftTB1 i) (LeftTB1 j)
-- diffFTB (IntervalTB1 i) (IntervalTB1 j) = diffFTB i j
diffFTB p d (TB1 i) (TB1  j) = d i j
diffFTB p d  i j = errorWithStackTrace (show (i,j))


diffPrim i j
  | i == j = Nothing
  | otherwise = Just $ PAtom j

data PathT k
  = PKey (Set ( Rel k )) (Maybe (PathT k))
  | PIndex (Set (FTB Showable)) (Maybe (PathT k))
  | PatchSet [PathT k]
  | POpt (Maybe (PathT k))
  | PIdx Int (Maybe (PathT k))
  | PAtom Showable
  deriving (Eq,Ord,Show)

imap f = map (uncurry f) . zip [0..]

