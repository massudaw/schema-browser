{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}

module Patchs where

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
import Data.Traversable(traverse)
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

mergeWith f c d  a b = (zipWith f  a b ) <> fmap c (L.drop (length a) b) <> fmap d ((L.drop (length b) a ))

-- diffWith eqs k e = mergeWith (\i j -> if i `eqs` j then k i j else e i j )

-- diffWithMods  a i = zip [0..] $  diffWith (==) AKeep AEditPrim ACreate ADelete a i


t1 =  [tblistPK (Set.singleton "id")  [Compose $ Identity $ Attr "id" (SNumeric 2),Compose $ Identity $ Attr "at1" (SOptional $ Just (SComposite $ Vector.fromList [SNumeric 1]))]]
t1pk = SNumeric 2
p1,p2,p3 :: PathT String
p1 = PIndex (Set.singleton t1pk) $ Just $ PKey (Set.fromList [Inline "at1"]) $ Just  (POpt Nothing)
p2 = PIndex (Set.singleton t1pk) $ Just $ PKey (Set.fromList [Inline "at1"]) $ Just (POpt (Just (PIdx 0 (Just $ PAtom $ SNumeric 4))))
p3 = PIndex (Set.singleton t1pk) $ Just $PKey (Set.fromList [Inline "at1"]) $ Just (POpt (Just (PIdx 1 (Just $ PAtom $ SNumeric 4))))

p4 = diffTable t1 (applyTable t1  p1 )

compactPatches :: Ord k => [PathT k] -> [PathT k]
compactPatches  = fmap recover .  groupSplit2 projectors pathProj
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
    recover (PIdAtom , j ) = PatchSet (catMaybes j)
    compact j = PatchSet . compactPatches <$> Just (catMaybes j)

data PathTID k
  = PIdPK (Set (Rel k))
  | PIdIndex (Set Showable)
  | PIdIdx Int
  | PIdOpt
  | PIdAtom
  deriving (Eq,Ord)

groupSplit2 :: Ord b => (a -> b) -> (a -> c ) -> [a] -> [(b ,[c])]
groupSplit2 f g = fmap (\i-> (f $ head i , g <$> i)) . groupWith f

-- diffTB1 (TB1 k s)  (TB1 k s) =

applyTable
  ::  (Ord k ,Show k) => [FTB1 Identity k Showable] -> PathT k -> [FTB1 Identity k Showable]
applyTable l (PIndex i  p) =  catMaybes $ L.map (\tb@(TB1 m k) -> if  getPK tb ==  i  then (case p of
                                                Just ps -> Just $ travPath applyTB1  (TB1 m k) ps
                                                Nothing ->  Nothing
                                              ) else  (Just tb )) l
getPK (TB1 m k) = Set.fromList (concat (fmap (fmap snd . aattr)  $ F.toList $ (Map.filterWithKey (\k v -> Set.isSubsetOf (_kvpk m) (Set.map _relOrigin k)) (  _kvvalues (runIdentity $ getCompose k)))))

diffTable l l2 =  patchSet $ fmap (\(k,v) -> PIndex k  (Just v)) $  Map.toList $ Map.intersectionWith (\i j -> diffTB1 i j) (mkMap l) (mkMap l2)
  where mkMap = Map.fromList . fmap (\i -> (getPK i,i))

travPath f p (PatchSet i) = foldl f p i
travPath f p i = f p i

applyTB1
  :: (Show k , Ord k) =>
       FTB1 Identity k Showable -> PathT k -> FTB1 Identity k Showable
applyTB1 t@(TB1 m v) (PKey s (Just k)) = TB1 m (mapComp (KV . Map.mapWithKey (\key v -> if key == s then  mapComp (flip applyAttr k ) v else v ) . _kvvalues ) v)

diffTB1 (TB1 m v) (TB1 n o ) = patchSet $ catMaybes $ F.toList  $ Map.intersectionWith (\i j -> diffAttr (unTB i) (unTB j))   (unKV v) (unKV o)

patchSet i
  | L.length i == 1 = head i
  -- | L.length i == 0 = Nothing
  | otherwise = PatchSet i

unKV = _kvvalues . unTB
unTB = runIdentity . getCompose

applyAttr (Attr k i) p  = Attr k (applyShowable i p)

diffAttr (Attr k i) (Attr l m ) = fmap (PKey (Set.singleton $ Inline k) . Just ) (diffShowable i m)

createAttr (PKey s (Just k) ) = Attr (_relOrigin $ head $ Set.toList s) (createShowable k)

applyShowable (SOptional i ) (POpt o) = case i of
                      Nothing -> case o of
                            Nothing -> SOptional Nothing
                            Just j -> createShowable j
                      Just _ -> SOptional (applyShowable  <$> i <*> o )
applyShowable (SComposite i ) (PIdx ix o) = case o of
                      Nothing -> SComposite $ Vector.take (ix +1)  i
                      Just p -> if ix <=  Vector.length i - 1
                                then SComposite $ Vector.imap (\i v -> if i == ix then applyShowable v p else v )  i
                                else if ix == Vector.length i
                                      then SComposite $ i <> Vector.singleton (createShowable p)
                                      else errorWithStackTrace $ "ix bigger than next elem" <> show (ix, Vector.length i)
createShowable (PAtom i ) = i
createShowable (POpt i ) = SOptional (createShowable <$> i)
createShowable (PIdx ix o ) = SComposite (fromJust  $  Vector.singleton . createShowable <$> o)

patchShowable :: Showable -> PathT k
patchShowable (SOptional j )  = POpt  (patchShowable <$> j)
patchShowable (SComposite j )  = patchSet   $ zipWith (\i m ->  PIdx i  (Just m) ) [0..]  (F.toList $ patchShowable <$> j)
patchShowable j = PAtom j

diffShowable :: Showable -> Showable -> Maybe (PathT k)
diffShowable (SOptional i ) (SOptional j )
    -- | traceShow (i,j) False = error ""
    | isJust i && isJust j = fmap POpt (liftA2 diffShowable  i j)
    | isJust i && isNothing j = Just $ POpt Nothing
    | isNothing i && isJust j = Just $ POpt (patchShowable <$> j)
    | i /= j = fmap POpt ( liftA2 diffShowable i j )
    | otherwise = Nothing -- POpt Nothing
diffShowable (SComposite i) (SComposite j) =
    Just $ patchSet $  catMaybes $ zipWith (\i -> fmap (PIdx  i . Just) ) ( [0..]) (F.toList $ liftA2 diffShowable i j  <> (Just . patchShowable <$> Vector.drop (Vector.length j) i ) <> (Just . patchShowable <$> Vector.drop (Vector.length i ) j ))
diffShowable i j
  | i == j = Nothing
  | otherwise = Just $ PAtom j


data PathT k
  = PKey (Set ( Rel k )) (Maybe (PathT k))
  | PIndex (Set Showable) (Maybe (PathT k))
  | PatchSet [PathT k]
  | POpt (Maybe (PathT k))
  | PIdx Int (Maybe (PathT k))
  | PAtom Showable
  deriving (Eq,Ord,Show)


