{-# LANGUAGE OverloadedStrings,FlexibleContexts,NoMonomorphismRestriction #-}
module Step.Host (module Step.Common,attrT,findFK,findAttr,findFKAttr,isNested,findProd,replace,uNest,hasProd,indexField,indexFieldRec,indexer,genPredicate,joinFTB) where

import Types
import Control.Applicative.Lift
import Debug.Trace
import Data.Monoid
import Data.Functor.Identity
import qualified Data.Foldable  as F
import Control.Monad.Reader
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Maybe
import Data.Foldable (toList)
import Control.Applicative
import Data.Text (Text,splitOn)
import qualified Data.List as L


import Step.Common
import qualified Data.Interval as I
import GHC.Stack
import Control.Category (Category(..),id)
import Prelude hiding((.),id,head)
import Utils

import qualified Data.Traversable as T
import Data.Traversable (traverse)






unF i = L.head (F.toList (getCompose i))

findFK :: (Foldable f ,Show a) => [Key] -> (TB3Data f Key a) -> Maybe (Compose f (TB f ) Key a)
findFK  l v =  M.lookup (S.fromList l) $M.mapKeys (S.map ( _relOrigin)) $ _kvvalues $ unF (snd v)

findAttr :: (Foldable f ,Show a) => [Key] -> (TB3Data f Key a) -> Maybe (Compose f (TB f ) Key a)
findAttr l v =  M.lookup (S.fromList $ Inline <$> l) $ M.mapKeys (S.map mapFunctions ) $  _kvvalues $ unF (snd v)
  where mapFunctions (RelFun i _ ) = Inline i
        mapFunctions j = j

findFKAttr :: (Foldable f ,Show a) => [Key] -> (TB3Data f Key a) -> Maybe (Compose f (TB f ) Key a)
findFKAttr l v =   case fmap  (fmap unF )$ L.find (\(k,v) -> not $ L.null $ L.intersect l (S.toList k) ) $ M.toList $ M.mapKeys (S.map ( _relOrigin)) $ _kvvalues $ unF (snd v) of
      Just (k,(FKT a _ _ )) ->   L.find (\i -> not $ L.null $ L.intersect l $ fmap (_relOrigin) $ keyattr $ i ) (F.toList $ _kvvalues $a)
      Just (k ,i) -> errorWithStackTrace (show l)
      Nothing -> Nothing


replace ix i (Nested k nt) = Nested k (replace ix i nt)
replace ix i (Many nt) = Many (fmap (replace ix i) nt )
replace ix i (Point p)
  | ix == p = Rec ix i
  | otherwise = (Point p)
replace ix i v = v

indexField :: Access Key -> TBData Key Showable -> Maybe (Column Key Showable)
indexField p@(IProd b l) v = case unTB <$> findAttr  l  v of
                               Nothing -> case unTB <$>  findFK l (v) of
                                  Just (FKT ref _ _) ->  unTB <$> ((\l ->  L.find ((==[l]). fmap ( _relOrigin). keyattr ) $ unkvlist ref ) $head l)
                                  Nothing -> unTB <$> findFKAttr l v

                               i -> i

indexField n@(Nested ix@(IProd b l) nt ) v = unTB <$> findFK l v
indexField i _= errorWithStackTrace (show i)

joinFTB (LeftTB1 i) =  LeftTB1 $ fmap joinFTB i
joinFTB (ArrayTB1 i) =  ArrayTB1 $ fmap joinFTB i
joinFTB (TB1 i) =  i

indexFieldRec :: Access Key-> TBData Key Showable -> Maybe (FTB Showable)
indexFieldRec p@(Many [l]) v = indexFieldRec l v
indexFieldRec p@(IProd b l) v = _tbattr . unTB <$> findAttr  l  v
indexFieldRec n@(Nested ix@(IProd b l) (Many[nt]) ) v = join $ fmap joinFTB . traverse (indexFieldRec nt)  . _fkttable.  unTB <$> findFK l v
indexFieldRec n@(Nested ix@(IProd b l) nt) v = join $ fmap joinFTB . traverse (indexFieldRec nt)  . _fkttable.  unTB <$> findFK l v
indexFieldRec n v = errorWithStackTrace (show (n,v))

genPredicate i (Many l) = AndColl <$> (nonEmpty $ catMaybes $ genPredicate i <$> l)
genPredicate i (ISum l) = OrColl <$> (nonEmpty $ catMaybes $ genPredicate i <$> l)
genPredicate i (IProd b l) =  (\l -> if b then Just $ PrimColl (IProd b l,Right (if i then Not IsNull else IsNull) ) else Nothing ) $ l
genPredicate i n@(Nested (IProd b p ) l ) = fmap AndColl $ nonEmpty $ catMaybes $ (\a -> if i then genPredicate i (IProd b [a]) else  Nothing ) <$> p
genPredicate _ i = errorWithStackTrace (show i)

genNestedPredicate n i v = fmap (\(a,b) -> (Nested n a , b )) <$> genPredicate i v

hasProd :: (Access Key -> Bool) -> Access Key ->  Bool
hasProd p (Many i) = any p i
hasProd p i = False

findProd :: (Access Key -> Bool) -> Access Key -> Maybe (Access Key)
findProd p (Many i) = L.find p i
findProd p i = Nothing

isNested :: Access Key -> Access Key -> Bool
isNested (IProd _ p) (Nested (IProd b l ) i) =  L.sort p == L.sort l
isNested p i =  False

uNest :: Access Key -> Access Key
uNest (Nested pn i) = i


indexer field = foldr (\i j -> Nested  (IProd True i) (Many [j]) ) (IProd True (last vec)) (init vec )
  where vec = splitOn "," <$> splitOn ":" field

