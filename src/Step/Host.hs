{-# LANGUAGE OverloadedStrings,FlexibleContexts,NoMonomorphismRestriction #-}
module Step.Host (module Step.Common,attrT,findPK,findFK,findAttr,findFKAttr,isNested,findProd,replace,uNest,checkTable,hasProd,checkTable',indexField,indexFieldRec,indexer,genPredicate) where

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
findAttr l v =  M.lookup (S.fromList $ fmap Inline l) $  _kvvalues $ unF (snd v)

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
indexFieldRec p@(IProd b l) v = _tbattr . unTB <$> findAttr  l  v
indexFieldRec n@(Nested ix@(IProd b l) (Many[nt]) ) v = join $ fmap joinFTB . traverse (indexFieldRec nt)  . _fkttable.  unTB <$> findFK l v

genPredicate i (Many l) = AndColl <$> (nonEmpty $ catMaybes $ genPredicate i <$> l)
genPredicate i (ISum l) = OrColl <$> (nonEmpty $ catMaybes $ genPredicate i <$> l)
genPredicate i (IProd b l) =  (\l -> if b then Just $ PrimColl (IProd b l,if i then "is not null" else "is null" ,LeftTB1 Nothing) else Nothing ) $ l
genPredicate i n@(Nested p l ) = genPredicate i p -- AndColl <$> liftA2 (\i  j -> [i,j]) (genPredicate i p)  ( genNestedPredicate p i l)
genPredicate _ i = errorWithStackTrace (show i)

genNestedPredicate n i v = fmap (\(a,b,c) -> (Nested n a , b ,c)) <$> genPredicate i v


checkField :: Access Key -> Column Key Showable -> Errors [Access Key] (Column Key Showable)
checkField p@(Point ix) _ = failure [p]
checkField n@(Nested ix@(IProd b l) nt ) t
  = case t of
         IT l i -> IT l  <$> checkFTB  nt i
         FKT a  c d -> FKT a  c <$> (if not b then maybe (failure [n]) (checkFTB nt) $ unRSOptional' d else checkFTB nt d  )
         Attr k v -> failure [n]
checkField  p@(IProd b l) i
  = case i  of
      Attr k v -> maybe (failure [p]) (pure) $ fmap (Attr k ) . (\i -> if b then  unRSOptional' i else Just i ) $ v
      FKT a c d -> (\i -> FKT i c d) <$> (traverseKV (traComp (checkField p) )  a )
      i -> errorWithStackTrace ( show (b,l,i))
checkField i j = errorWithStackTrace (show (i,j))


checkFTB l (ArrayTB1 i )
  | otherwise =   ArrayTB1 <$> traverse (checkFTB  l) i

checkFTB l (LeftTB1 j) = LeftTB1 <$> traverse (checkFTB  l) j
checkFTB  l (DelayedTB1 j) = DelayedTB1 <$> traverse (checkFTB l) j
checkFTB  (Rec ix i) t = checkFTB  (replace ix i i ) t
checkFTB  (Many [m@(Many l)]) t = checkFTB  m t
checkFTB  (Many [m@(Rec _ _ )]) t = checkFTB  m t

checkFTB f (TB1 k) = TB1 <$> checkTable' f k

checkTable' :: Access Key -> TBData Key Showable -> Errors [Access Key] (TBData Key Showable)
checkTable' (ISum []) v
  = failure [ISum []]
checkTable'  f@(ISum ls) (m,v)
  = fmap (tblist . pure . _tb) $ maybe (failure [f]) id  $ listToMaybe . catMaybes $  fmap (\(Many [l]) ->  fmap (checkField l) . join . fmap ( traFAttr  unRSOptional') $ indexField l $ (m,v)) ls
checkTable' (Many l) (m,v) =
  ( (m,) . _tb . KV . mapFromTBList ) <$> T.traverse (\k -> maybe (failure [k]) (fmap _tb. checkField k ). indexField  k $ (m,v)) l


checkTable l b = eitherToMaybe $ runErrors (checkTable' l b)




hasProd :: (Access Key -> Bool) -> Access Key ->  Bool
hasProd p (Many i) = any p i
hasProd p i = False

findProd :: (Access Key -> Bool) -> Access Key -> Maybe (Access Key)
findProd p (Many i) = L.find p i
findProd p i = Nothing

isNested :: Access Key -> Access Key -> Bool
isNested p (Nested pn i) =  p == pn
isNested p i =  False

uNest :: Access Key -> Access Key
uNest (Nested pn i) = i

findPK = concat . fmap keyattr  .toList . _kvvalues  . unTB . tbPK

indexer field = foldr (\i j -> Nested  (IProd True i) (Many [j]) ) (IProd True (last vec)) (init vec )
  where vec = splitOn "," <$> splitOn ":" field

