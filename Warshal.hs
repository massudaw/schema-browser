{-# LANGUAGE ScopedTypeVariables,NoMonomorphismRestriction,DeriveFunctor,GeneralizedNewtypeDeriving,FlexibleContexts,DeriveFoldable ,TupleSections #-}
module Warshal where

import qualified Data.Foldable as F
import Data.Foldable (Foldable)
import Data.Char ( isAlpha )
import Data.Maybe
import Data.Monoid hiding(Product)
import Control.Monad
import GHC.Exts
import Data.Tuple
import Control.Applicative
import Data.List ( nubBy,nub, sort,intercalate,sortBy,isInfixOf )
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Map (Map)
import Data.Set (Set)
import Control.Monad.State
import Control.Monad.State.Class
import System.Environment ( getArgs )
import Text.Parsec hiding(State)
import Text.Parsec.String
import Text.Printf ( printf )
import Debug.Trace

data Vertex a  = Product  { unProduct :: [a]}
              deriving(Eq,Ord,Functor,Foldable)

instance (Show a ) => Show (Vertex a) where
  show (Product i) = intercalate ","  $ fmap show i

data Edge a b = Edge { hedge :: (Vertex a)
                     , tedge :: (Vertex a)
                     , tag ::  b}
              | ProductPath [Edge a b] [Edge a b]
            deriving(Eq,Ord,Functor,Foldable)

instance (Show a, Show b) => Show (Edge a b) where
    show (Edge x y o) = printf "%s-> %s| %s " (show x) (show y) (show o)
    show (ProductPath x y ) = printf "%s-> %s" (intercalate  "," $ fmap show x) (intercalate "," $ fmap show y)

data Graph a b = Graph { hvertices :: [Vertex a]
                     , tvertices :: [Vertex a]
                     , edges :: [Edge a b] }
                     deriving(Eq)

instance (Show a,Show b) => Show (Graph a b) where
    show g = printf "Inputs: %s\nOutputs: %s\nEdges:\n%s"
                    (unwords . map show $ hvertices g)
                    (unwords . map show $ tvertices g)
                    (unlines . map showEdge $ edges g)
        where
          showVertice (Product x ) = show x
          showEdge (Edge  x y p ) = printf "%s -> %s\n %s " (showVertice x) (showVertice y) (show p)


{-

mergeGraph :: Graph a b -> Graph a b -> Graph a b
mergeGraph i k = Graph { hvertices = nub $ sort $ hvertices i <>  hvertices k
                       , tvertices = nub $ sort $ tvertices i <> tvertices k
                       , edges = go hiedges (go tiedges (edges k) ) <> go tkedges (go hkedges (edges i))
                       }
    where
      linter = (S.fromList $ hvertices k) `S.intersection` (S.fromList $ tvertices i)
      rinter = (S.fromList $ tvertices k) `S.intersection` (S.fromList $ hvertices i)
      redges = snd
      tiedges =  filter ((`S.member` linter) . tedge . redges) (edges i)
      hiedges =  filter ((`S.member` linter) . hedge . redges)  (edges k)
      tkedges =  filter ((`S.member` linter) . tedge . redges)  (edges k)
      hkedges =  filter ((`S.member` linter) . hedge . redges)  (edges i)
      go []  es = es
      go nes es = go nees nonDup
         where
            nonDup = sortNub $ nees <> es
            nees =  traceShowId  $  sortNub
                [(ProductPath (fmap fst items) [p3] ,Edge (Product (head $ fmap (edgeT . snd ) items) ) (Product d) (Raw "" "")) |
                (p3,Edge  (Product p) (Product d) o) <- nes ,
                items <-  replicateM (length p) es ,
                (sort . concat $ fmap (edgeH . snd) items)  ==  p ,
                allTheSame (==)  (fmap(edgeT . snd) items) ,
                all (not . (==d)) (fmap(edgeT . snd) items) ]
                <> [(ProductPath [p3] (fmap fst items) ,Edge (Product p) (Product (head $ fmap (edgeH . snd ) items) ) (Raw "" "" ) ) |
                (p3,Edge  (Product p) (Product d) o) <- nes ,
                items <-  replicateM (length d) es ,
                (sort . concat $ fmap (edgeT . snd) items)  ==  d ,
                allTheSame (==)  (fmap(edgeH . snd) items) ,
                all (not . (==p)) (fmap(edgeH . snd) items) ]
            edgeH (Edge _ (Product k) _ ) = k
            edgeT (Edge (Product i) _ _ ) = i
-}
nubEdges = nubBy (\(Edge x y _)(Edge i j _)-> y == j)
sortEdges = sortBy (\(Edge x y _)(Edge i j _)-> compare y j)
sortNub = nubEdges . sortEdges


addEdge ::  (Ord a,Monoid b) => Edge a b -> Graph a b -> Graph a b
addEdge e@(Edge  pp pd o) g = Graph { edges = sortNub $ go intersects  $ go [e]  (e:edges g)
                   , hvertices = pp : hvertices g
                   , tvertices = pd : tvertices g }
    where
      intersects = filter (\((Edge (Product h) (Product t)  _ ))-> intersectsOne h (unProduct pd) ||  intersectsOne t (unProduct pp) ) (edges g)
      intersectsOne :: Eq a => [a] -> [a] -> Bool
      intersectsOne u p = or (fmap (\x -> elem x p) u)
      go :: (Ord a,Monoid b)=> [Edge a b] ->  [Edge a b] -> [Edge a b]
      go []  es = es
      go nes es = go nees nonDup
         where
            nonDup = sortNub $ nees <> es
            nees =   sortNub
                [Edge (Product (head $ fmap (edgeT ) items) ) (Product d) (foldr1  (<>) ((fmap tag items) <> [p3])) |
                (Edge  (Product p) (Product d) p3) <- nes ,
                items <-  replicateM (length p) es ,
                (sort . concat $ fmap (edgeH ) items)  ==  p ,
                allTheSame (==)  (fmap(edgeT ) items) ,
                all (not . (==d)) (fmap(edgeT ) items) ]
                <> [Edge (Product p) (Product (head $ fmap (edgeH) items) ) (foldr1 (<>) ((fmap tag items) <> [p3]))  |
                (Edge  (Product p) (Product d) p3) <- nes ,
                items <-  replicateM (length d) es ,
                (sort . concat $ fmap (edgeT ) items)  ==  d ,
                allTheSame (==)  (fmap(edgeH ) items) ,
                all (not . (==p)) (fmap(edgeH ) items) ]
            edgeH (Edge _ (Product k) _ ) = k
            edgeT (Edge (Product i) _ _ ) = i

warshall ::  (Ord a,Ord b, Monoid b) => Graph a b-> Graph a b
warshall g = Graph { edges = sort $ go (nub $ sort $ hvertices g<> tvertices g) (edges g)
                   , hvertices = sort $ nub $ hvertices g
                   , tvertices = sort $ nub $ tvertices g }
    where
      go [] es     = es
      go (v:vs) es = go vs (nub (es
         <> [ Edge (Product (head $ fmap edgeT items) ) (Product d) (foldr1 (<>) ((fmap tag items)<> [p3])) |
                Edge  (Product p) (Product d) p3 <- es ,
                items <-  replicateM (length p) es ,
                (sort . concat $ fmap (edgeH ) items)  ==  p ,
                allTheSame (==)  (fmap(edgeT ) items) ,
                all (not . (==d)) (fmap(edgeT) items) ]
         ))
         where
            edgeH (Edge _ (Product k) _ ) = k
            edgeT (Edge (Product i) _ _ ) = i

allTheSame ::  (a -> a -> Bool) ->  [a] -> Bool
allTheSame  f xs = and $ map (f ( head xs)) (tail xs)


nested ::  Edge a (Edge a b) -> [(a, [(a, [Edge a b])])]
nested (Edge (Product x) (Product y)  p ) = fmap (,fmap (,[p]) y) x


hashGraph  :: Ord a => Graph a (Edge a b)-> Map a (Map a [(Edge a b )])
hashGraph = M.map (M.fromListWith (++)) .  M.fromListWith (++)  . concat . fmap nested . edges

find norm end m = case M.lookup norm m of
                    Just i -> M.lookup end i
                    Nothing -> Nothing

queryHash :: Ord a => [a] -> Map a (Map a b) -> a  -> [Maybe b]
queryHash filters schema  base =  map (\f-> find base f schema)  filters




type HashSchema  a b = Map a (Map a [Edge a b ])

