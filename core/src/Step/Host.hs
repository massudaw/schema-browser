{-# LANGUAGE OverloadedStrings, FlexibleContexts,
  NoMonomorphismRestriction #-}

module Step.Host
  ( module Step.Common
  , attrT
  , findFK
  , findAttr
  , findFKAttr
  , isNested
  , findProd
  , replace
  , replaceU
  , uNest
  , hasProd
  , indexField
  , indexFieldRec
  , indexer
  , joinFTB
  ) where

import Control.Applicative
import Control.Category (Category(..))
import qualified NonEmpty as Non
import Control.Monad.Reader
import qualified Data.Foldable as F
import qualified Data.List as L
import qualified Data.Map as M
import Data.Maybe
import qualified Data.Set as S
import Data.Text (Text, splitOn)
import Data.Traversable (traverse)
import Prelude hiding ((.), head, id)
import Step.Common
import Types

findFK :: (Show k, Ord k, Show a) => [k] -> (TBData k a) -> Maybe (TB k a)
findFK l v =
  fmap snd $
  L.find (\(i, v) -> isFK v && S.map _relOrigin i == (S.fromList l)) $
  M.toList $ _kvvalues $ (v)
  where
    isRel (Rel _ _ _) = True
    isRel _ = False
    isFK i =
      case i of
        FKT _ _ _ -> True
        IT _ _ -> True
                   -- ARel _ _ -> True
                   -- ARef  _  -> True
        i -> False

-- findFK  l v =  fmap recoverAttr' $ L.find (\(i,v) -> isFK v && S.map _relOrigin i == (S.fromList l))  $ M.toList $ _kvvalues $ v
findAttr :: (Show k, Ord k, Show a) => k -> (TBData k a) -> Maybe (TB k a)
findAttr l v = kvLookup (S.singleton . Inline $ l) v <|> findFun l v

findFun :: (Show k, Ord k, Show a) => k -> (TBData k a) -> Maybe (TB k a)
findFun l v =
  fmap snd .
  L.find (((pure . Inline $ l) ==) . fmap mapFunctions . S.toList . fst) $
  M.toList $ _kvvalues $ (v)
  where
    mapFunctions (RelFun i _ _) = Inline i
    mapFunctions j = j

-- findFun l v = fmap recoverAttr' . L.find (((pure . Inline $ l) == ).fmap mapFunctions . S.toList .fst) $ M.toList $ _kvvalues $ v
findFKAttr :: (Show k, Ord k, Show a) => [k] -> (TBData k a) -> Maybe (TB k a)
findFKAttr l v =
  case L.find (\(k, v) -> not $ L.null $ L.intersect l (S.toList k)) $
       M.toList $ M.mapKeys (S.map (_relOrigin)) $ _kvvalues $ (v) of
    Just (k, FKT a _ _) ->
      L.find
        (\i -> not $ L.null $ L.intersect l $ fmap (_relOrigin) $ keyattr $ i)
        (F.toList $ _kvvalues $a)
   -- Just (k,ARel a _ ) ->   L.find (\i -> not $ L.null $ L.intersect l $ fmap (_relOrigin) $ keyattr $ i ) (unkvlist a)
    Just (k, i) -> error (show l)
    Nothing -> Nothing

replaceU ix i (Many nt) = Many $ (fmap (replace ix i) nt)

replace ix i (Nested k nt) = Nested k (replaceU ix i nt)
replace ix i (Point p)
  | ix == p = Rec ix i
  | otherwise = (Point p)
replace ix i v = v

indexField ::
     (Ord k, Show a, Show k) => Access k -> TBData k a -> Maybe (Column k a)
indexField p@(IProd b l) v =
  case findAttr l v of
    Nothing ->
      case findFK [l] (v) of
        Just (FKT ref _ _) ->
          ((\l -> L.find ((== [l]) . fmap _relOrigin . keyattr) $ unkvlist ref) $
           l)
        Nothing -> findFKAttr [l] v
    i -> i
indexField n@(Nested ix nt) v = findFK (F.toList ix) v
indexField i _ = error (show i)

joinFTB (LeftTB1 i) = LeftTB1 $ fmap joinFTB i
joinFTB (ArrayTB1 i) = ArrayTB1 $ fmap joinFTB i
joinFTB (TB1 i) = i

indexFieldRecU p@(ISum l) v =
  F.foldl' (<|>) Nothing (flip indexFieldRec v <$> l)
indexFieldRecU p@(Many [l]) v = indexFieldRec l v

indexFieldRec :: Access Key -> TBData Key Showable -> Maybe (FTB Showable)
indexFieldRec p@(IProd b l) v = _tbattr <$> findAttr l v
indexFieldRec n@(Nested l (Many [nt])) v =
  join $ fmap joinFTB . traverse (indexFieldRec nt) . _fkttable <$> findFK (F.toList l) v
indexFieldRec n@(Nested l nt) v =
  join $
    fmap joinFTB . traverse (indexFieldRecU nt) . _fkttable <$> findFK (F.toList l) v
indexFieldRec n v = error (show (n, v))

hasProd :: (Access Key -> Bool) -> Union (Access Key) -> Bool
hasProd p i = F.any p i

findProd :: (Access Key -> Bool) -> Union (Access Key) -> Maybe (Access Key)
findProd p i = F.find p i

isNested :: [Access Key] -> Access Key -> Bool
isNested p (Nested l i) = L.sort (iprodRef <$> p) == L.sort (F.toList l)
isNested p i = False

uNest :: Access Key -> Union (Access Key)
uNest (Nested pn i) = i

indexer :: Text -> [Access Text]
indexer field =
  foldr
    (\i j -> [Nested (Non.fromList i) (Many (j))])
    (IProd Nothing <$> last vec)
    (init vec)
  where
    vec = splitOn "," <$> splitOn ":" field
