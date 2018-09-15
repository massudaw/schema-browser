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
indexField n@(Nested ix nt) v = findFK (F.toList (_relOrigin <$> ix)) v
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
  join $ fmap joinFTB . traverse (indexFieldRec nt) . _fkttable <$> findFK (F.toList (_relOrigin <$>  l)) v
indexFieldRec n@(Nested l nt) v =
  join $
    fmap joinFTB . traverse (indexFieldRecU nt) . _fkttable <$> findFK (F.toList (_relOrigin <$> l)) v
indexFieldRec n v = error (show (n, v))

hasProd :: (Access Key -> Bool) -> Union (Access Key) -> Bool
hasProd p  = F.any p 

findProd :: (Access Key -> Bool) -> Union (Access Key) -> Maybe (Access Key)
findProd p  = F.find p 

isNested :: [Access Key] -> Access Key -> Bool
isNested p (Nested l i) = L.sort (iprodRef <$> p) == L.sort (F.toList (_relOrigin <$> l))
isNested p i = False

uNest :: Access Key -> Union (Access Key)
uNest (Nested pn i) = i

indexer :: Text -> [Access Text]
indexer field =
  foldr
    (\i j -> [Nested (Non.fromList (Inline <$> i)) (Many (j))])
    (IProd Nothing <$> last vec)
    (init vec)
  where
    vec = splitOn "," <$> splitOn ":" field
