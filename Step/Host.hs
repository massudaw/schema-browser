{-# LANGUAGE OverloadedStrings,FlexibleContexts,NoMonomorphismRestriction #-}
module Step.Host (module Step.Common,attrT,findPK,isNested,findProd,replace,uNest,checkTable,hasProd,checkTable',indexFieldRec,indexer,indexPred) where

import Types
import Control.Applicative.Lift
import Data.Monoid
import qualified Data.Foldable  as F
import Control.Monad.Reader
import Query
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










findFK  l v =  M.lookup (S.fromList l) $ M.mapKeys (S.map (keyString. _relOrigin)) $ _kvvalues $ unTB v
findAttr l v =  M.lookup (S.fromList $ fmap Inline l) $ M.mapKeys (S.map (fmap keyString)) $ _kvvalues $ unTB v

replace ix i (Nested k nt) = Nested k (replace ix i nt)
replace ix i (Many nt) = Many (fmap (replace ix i) nt )
replace ix i (Point p)
  | ix == p = Rec ix i
  | otherwise = (Point p)
replace ix i v = v
-- replace ix i v= errorWithStackTrace (show (ix,i,v))

indexPred (Many i ,eq,v) r = all (\i -> indexPred (i,eq,v) r) i
indexPred (n@(Nested k nt ) ,eq,v) r
  = case  indexField n r of
    Nothing -> errorWithStackTrace ("cant find attr" <> show n)
    Just i ->  recPred $ indexPred (nt , eq ,v) <$> _fkttable  i
  where
    recPred (SerialTB1 i) = maybe False recPred i
    recPred (LeftTB1 i) = maybe False recPred i
    recPred (TB1 i ) = i
    recPred (ArrayTB1 i) = all recPred (F.toList i)
indexPred (a@(IProd _ _),eq,v) r =
  case indexField a r of
    Nothing ->  errorWithStackTrace ("cant find attr" <> show a)
    Just (Attr _ rv) ->
      case eq of
        "=" -> rv == v
        "<@" -> case v of
                  IntervalTB1 l -> I.member  rv l
        i -> errorWithStackTrace ("Operator not implemented " <> i )

indexField :: Access Text -> TBData Key Showable -> Maybe (Column Key Showable)
indexField p@(IProd b l) v = unTB <$> findAttr  l  (snd v)
indexField n@(Nested ix@(IProd b l) nt ) v = unTB <$> findFK l (snd v)

indexFieldRec :: Access Text -> TBData Key Showable -> Maybe (Column Key Showable)
indexFieldRec p@(IProd b l) v = unTB <$> findAttr  l  (snd v)
indexFieldRec n@(Nested ix@(IProd b l) (Many[nt]) ) v = join $ join $ fmap (indexFieldRec nt) . listToMaybe . F.toList . _fkttable.  unTB <$> findFK l (snd v)


checkField :: Access Text -> Column Key Showable -> Errors [Access Text] (Column Key Showable)
checkField p@(Point ix) _ = failure [p]
checkField n@(Nested ix@(IProd b l) nt ) t
  = case t of
         IT l i -> IT l  <$> checkFTB  nt i
         FKT a  c d -> FKT a  c <$> (if not b then maybe (failure [n]) (checkFTB nt) $ unRSOptional' d else checkFTB nt d  )
         Attr k v -> failure [n]
checkField  p@(IProd b l) i
  = case i  of
      Attr k v -> maybe (failure [p]) (pure) $ fmap (Attr k ) . (\i -> if b then  unRSOptional' i else Just i ) $ v
      FKT a c d -> (\i -> FKT i c d) <$> (traverse (traComp (checkField p) )  a )
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

checkTable' :: Access Text -> TBData Key Showable -> Errors [Access Text] (TBData Key Showable)
checkTable' (ISum []) v
  = failure [ISum []]
checkTable'  f@(ISum ls) (m,v)
  = fmap (tblist . pure . _tb) $ maybe (failure [f]) id  $ listToMaybe . catMaybes $  fmap (\(Many [l]) ->  fmap (checkField l) . join . fmap ( traFAttr  unRSOptional') $ indexField l $ (m,v)) ls
checkTable' (Many l) (m,v) =
  ( (m,) . _tb . KV . mapFromTBList ) <$> T.traverse (\k -> maybe (failure [k]) (fmap _tb. checkField k ). indexField  k $ (m,v)) l


checkTable l b = eitherToMaybe $ runErrors (checkTable' l b)



hasProd :: (Access Text -> Bool) -> Access Text ->  Bool
hasProd p (Many i) = any p i
hasProd p i = False

findProd :: (Access Text -> Bool) -> Access Text -> Maybe (Access Text)
findProd p (Many i) = L.find p i
findProd p i = Nothing

isNested :: Access Text -> Access Text -> Bool
isNested p (Nested pn i) =  p == pn
isNested p i =  False

uNest :: Access Text -> Access Text
uNest (Nested pn i) = i

findPK = concat . fmap keyattr  .toList . _kvvalues  . unTB . tbPK

indexer field = foldr (\i j -> Nested  (IProd True i) (Many [j]) ) (IProd True (last vec)) (init vec )
  where vec = splitOn "," <$> splitOn ":" field

