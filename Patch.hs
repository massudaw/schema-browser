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



t1 =  [tblistPK (Set.singleton "id")  [Compose $ Identity $ Attr "id" (TB1 (SNumeric 2)),Compose $ Identity $ Attr "at1" (LeftTB1 $ Just (ArrayTB1 [TB1 $ SNumeric 1]))]]
t1pk =  TB1 (SNumeric 2)
p1,p2,p3 :: PathT String
p1 = PIndex kvempty (Set.singleton t1pk) $ Just $ PKey (Set.fromList [Inline "at1"]) $ (POpt Nothing)
p2 = PIndex kvempty (Set.singleton t1pk) $ Just $ PKey (Set.fromList [Inline "at1"]) $ (POpt (Just (PIdx 0 (Just $ PAtom $ SNumeric 4))))
p3 = PIndex kvempty (Set.singleton t1pk) $ Just $PKey (Set.fromList [Inline "at1"]) $ (POpt (Just (PIdx 1 (Just $ PAtom $ SNumeric 5))))

data PathT k
  = PKey (Set ( Rel k )) (PathT k)
  | PIndex (KVMetadata k) (Set (FTB Showable)) (Maybe (PathT k))
  | PatchSet [PathT k]
  | POpt (Maybe (PathT k))
  | PSerial (Maybe (PathT k))
  | PDelayed (Maybe (PathT k))
  | PInter  Bool (PathT k)
  | PIdx Int (Maybe (PathT k))
  | PAtom Showable
  deriving (Eq,Ord,Show)

data PathTID k
  = PIdPK (Set (Rel k))
  | PIdIndex (KVMetadata k) (Set (FTB Showable))
  | PIdIdx Int
  | PIdOpt
  | PIdSerial
  | PIdDelayed
  | PIdInter Bool
  | PIdAtom
  deriving (Eq,Ord,Show)



compactionLaw t l = diffTable t (foldl applyTable t l ) == compactPatches l


compactPatches :: (Show k ,Ord k )=> [PathT k] -> Maybe (PathT k)
compactPathces [] = Nothing
compactPatches i = patchSet . fmap recover .  groupSplit2 projectors pathProj . concat . fmap expandPSet $ i
  where
    pathProj (PIndex _ _ i) = i
    pathProj (PIdx _ i) = i
    pathProj (POpt  i) = i
    pathProj (PSerial i) = i
    pathProj (PDelayed i) = i
    pathProj (PInter _ i) = Just i
    pathProj (PKey _ i  ) = Just i
    pathProj i@(PAtom _  ) = Just i
    pathProj i = errorWithStackTrace (show i)
    projectors (PKey i _ ) = PIdPK i
    projectors (PIndex j i _ ) = PIdIndex j i
    projectors (PIdx i _ ) = PIdIdx i
    projectors (POpt _  ) = PIdOpt
    projectors (PSerial _  ) = PIdSerial
    projectors (PDelayed _  ) = PIdDelayed
    projectors (PInter b _  ) = PIdInter b
    projectors (PAtom _  ) =  PIdAtom
    projectors i = errorWithStackTrace (show i)
    recover (PIdPK i, j ) = PKey i  (justError "no patch key" $ compact j)
    recover (PIdIndex l i, j ) = PIndex l i  (compact j)
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
  ::  (Ord k ,Show k) => [FTB1 Identity k Showable] -> PathT k -> [FTB1 Identity k Showable]
applyTable l pidx@(PIndex m i  p) =  case L.find (\tb -> getPK tb == i ) l  of
                  Just _ ->  catMaybes $ L.map (\tb@(TB1 (m, k)) -> if  getPK tb ==  i  then (case p of
                                                Just ps -> Just $ travPath applyTB1  (TB1 (m, k)) ps
                                                Nothing ->  Nothing
                                              ) else  (Just tb )) l
                  Nothing -> (createFTB createTB1  pidx) : l

getPK (TB1 (m, k)) = Set.fromList (concat (fmap (fmap snd . aattr)  $ F.toList $ (Map.filterWithKey (\k v -> Set.isSubsetOf (_kvpk m) (Set.map _relOrigin k)) (  _kvvalues (runIdentity $ getCompose k)))))

diffTable l l2 =  patchSet $ fmap (\(k,v) -> PIndex undefined  k  (Just v)) $  mapMaybe (\(k,v) -> (k,) <$> v ) $ Map.toList $ Map.intersectionWith (\i j -> diffTB1 i j) (mkMap l) (mkMap l2)
  where mkMap = Map.fromList . fmap (\i -> (getPK i,i))

travPath f p (PatchSet i) = foldl f p i
travPath f p i = f p i

applyTB1
  :: (Show k , Ord k) =>
       FTB1 Identity k Showable -> PathT k -> FTB1 Identity k Showable
applyTB1 = applyFTB createTB1 applyRecord

createTB1
  :: (Show d, Ord d ) =>
     PathT d ->
     (KVMetadata d , Compose Identity  (KV (Compose Identity  (TB Identity))) d Showable)
createTB1 (PIndex m s (Just k)) = (m , _tb .KV . mapFromTBList . fmap _tb . createAttr $  k)



applyRecord
  :: (Show d, Ord d,  Functor t) =>
     (KVMetadata d , Compose t (KV (Compose t (TB Identity))) d Showable)
     -> PathT d
     -> (KVMetadata d , Compose t (KV (Compose t (TB Identity))) d Showable)
applyRecord t@((m, v)) (PKey s k) = (m ,mapComp (KV . Map.mapWithKey (\key v -> if key == s then  mapComp (flip applyAttr (PKey s k) ) v else v ) . _kvvalues ) v)

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


patchSet i
  | L.length i == 0 = Nothing
  | L.length i == 1 = Just$ head i
  | otherwise = Just $ PatchSet (concat $ normalize <$> i)
      where normalize (PatchSet i) = concat $ fmap normalize i
            normalize i = [i]


applyAttr (Attr k i) (PKey s (p))  = Attr k (applyShowable i p)
applyAttr (IT k i) (PKey s (p))  = IT k (applyTB1 i p)
applyAttr (FKT  k rel i) (PKey s (p@(PIndex m ix _)))  = FKT k rel  (applyTB1 i p)
applyAttr (FKT  k rel i) (PKey s (p))  = FKT (mapComp (\i -> if Set.fromList (keyattri i)  == s  then applyAttr i (PKey s (p )) else i ) <$>  k) rel  (applyTB1 i p)



diffAttr :: (Show k ,Ord k) => TB Identity k Showable -> TB Identity k Showable -> Maybe (PathT k )
diffAttr (Attr k i) (Attr l m ) = fmap (PKey (Set.singleton $ Inline k) ) (diffPrimitive i m)
diffAttr (IT k i) (IT _ l) = fmap (PKey (Set.fromList $ keyattr k ) ) (diffTB1 i l)
diffAttr (FKT  k _ i) (FKT m _ l) = patchSet $ catMaybes $ zipWith (\i j -> diffAttr (unTB i) (unTB j)) k m  <> [diffTB1 i l]

patchAttr a@(Attr k v) = PKey (Set.fromList (keyattri a)) (patchFTB patchPrim v)
patchAttr a@(IT k v) = patchFTB patchTB1 v
patchAttr a@(FKT k rel v) = patchFTB patchTB1 v

createAttr (PatchSet l) = concat $ fmap createAttr l
createAttr (PKey s (k) ) = [Attr (_relOrigin $ head $ Set.toList s) (createShowable k)]

applyPrim _ (PAtom i) = i

createPrim (PAtom i) = i

diffPrimitive :: (Show k , Ord k) => FTB Showable -> FTB Showable -> Maybe (PathT k)
diffPrimitive = diffFTB patchPrim diffPrim

applyShowable = applyFTB createPrim applyPrim

createShowable = createFTB createPrim

patchPrim j = PAtom j

diffPrim i j
  | traceShow (i,j) False = errorWithStackTrace "22"
  | i == j = Nothing
  | otherwise = Just $ PAtom j


data IntervalDiff  a
  = IntervalScale Bool a
  | IntervalMove a
  | IntervalCreate a



-- FTB

patchFTB :: (a -> PathT k) -> FTB a -> PathT k
patchFTB p (LeftTB1 j )  = POpt (patchFTB p <$> j)
patchFTB p (ArrayTB1 j )  = justError "can't be empty" $  patchSet   $ zipWith (\i m ->  PIdx i  (Just m) ) [0..]  (F.toList $ patchFTB p <$> j)
patchFTB p (DelayedTB1 j ) = PDelayed (patchFTB p <$> j)
patchFTB p (SerialTB1 j ) = PSerial (patchFTB p <$> j)
patchFTB p (TB1 j) = p j
-- patchFTB p i = errorWithStackTrace (show i)

diffOpt p d i j
    | isJust i && isJust j = (sequenceA $ liftA2 (diffFTB  p d ) i j)
    | isJust i && isNothing j = Just $ Nothing
    | isNothing i && isJust j = Just $ (patchFTB p <$> j)
    | i /= j = ( liftA2 (diffFTB p d ) i j )
    | otherwise = Nothing

diffFTB :: (Ord a,Show a,Ord k ,Show k) => (a -> PathT k ) -> (a -> a -> Maybe (PathT k)) ->  FTB a -> FTB a -> Maybe (PathT k)
diffFTB p d  (LeftTB1 i) (LeftTB1 j)
    | isJust i && isJust j = fmap POpt (sequenceA $ liftA2 (diffFTB  p d ) i j)
    | isJust i && isNothing j = Just $ POpt Nothing
    | isNothing i && isJust j = Just $ POpt (patchFTB p <$> j)
    | i /= j = fmap POpt ( liftA2 (diffFTB p d ) i j )
    | otherwise = Nothing -- POpt Nothing
diffFTB p d (ArrayTB1 i) (ArrayTB1 j) =
    patchSet $  catMaybes $ zipWith (\i -> fmap (PIdx  i . Just) ) ( [0..]) (F.toList $ (zipWith (diffFTB p d ) i j)  <> (Just . patchFTB p <$> drop (length j) i ) <> (Just . patchFTB p <$> drop (length i ) j ))
diffFTB p d (SerialTB1 i) (SerialTB1 j) = fmap PSerial $ diffOpt p d i j
diffFTB p d (DelayedTB1 i) (DelayedTB1 j) = fmap PDelayed $ diffOpt p d i j
diffFTB p d (IntervalTB1 i) (IntervalTB1 j)
  | i == j = Nothing
  | otherwise =  patchSet $  catMaybes   [fmap (PInter False) (diffFTB p d (unFinite $ Interval.lowerBound i) (unFinite $ Interval.lowerBound j) ),fmap (PInter True) (  diffFTB p d (unFinite $ Interval.upperBound i) (unFinite $ Interval.upperBound j) )]

diffFTB p d (TB1 i) (TB1  j) = d i j
diffFTB p d  i j = errorWithStackTrace (show (i,j))

unFinite (Interval.Finite i ) =  i

instance Applicative Interval.Extended where
  pure i = Interval.Finite i
  (Interval.Finite i) <*> (Interval.Finite j) =  Interval.Finite $ i j

applyOpt  pr a i  o = case i of
                      Nothing -> case o of
                            Nothing -> Nothing
                            Just j -> createFTB pr <$> o
                      Just _ -> (applyFTB pr a <$> i <*> o )
applyFTB pr a (LeftTB1 i ) op@(POpt o) = LeftTB1 $ applyOpt pr a i o
applyFTB pr a (ArrayTB1 i ) (PIdx ix o) = case o of
                      Nothing -> ArrayTB1 $ take (ix +1)  i
                      Just p -> if ix <=  length i - 1
                                then ArrayTB1 $ imap (\i v -> if i == ix then applyFTB pr a v p else v )  i
                                else if ix == length i
                                      then ArrayTB1 $ i <> [createFTB pr p]
                                      else errorWithStackTrace $ "ix bigger than next elem" <> show (ix, length i)
applyFTB pr a (SerialTB1 i ) (PSerial o) = SerialTB1 $  applyOpt pr a i o
applyFTB pr a (DelayedTB1 i ) (PDelayed o) = DelayedTB1 $  applyOpt pr a i o
applyFTB pr a (IntervalTB1 i) (PInter b p)
    = IntervalTB1 $ if b
        then fmap (flip (applyFTB pr a) p ) (lowerBound i)  Interval.<..<  upperBound i
        else lowerBound i Interval.<..<  fmap (flip (applyFTB pr a) p ) (upperBound i)

applyFTB pr a (TB1 i) p  =  TB1 $ a i p

createFTB p (POpt i ) = LeftTB1 (createFTB p <$> i)
createFTB p (PSerial i ) = SerialTB1 (createFTB p <$> i)
createFTB p (PDelayed i ) = DelayedTB1 (createFTB p <$> i)
createFTB p (PIdx ix o ) = ArrayTB1 (fromJust  $  pure . createFTB p <$> o)
createFTB p i  = TB1 $ p i


imap f = map (uncurry f) . zip [0..]

