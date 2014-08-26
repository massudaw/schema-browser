{-# LANGUAGE ScopedTypeVariables,BangPatterns,NoMonomorphismRestriction,DeriveFunctor,GeneralizedNewtypeDeriving,FlexibleContexts,DeriveFoldable ,TupleSections #-}
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
import Data.List ( nubBy,nub, sort,intercalate,sortBy,isInfixOf ,transpose)
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


type HashSchema  a b = Map (Set a) (Map a (Path a b ))

instance (Show a, Show b) => Show (Path a b) where
    show (Path x o y) = printf "%s-> %s| %s " (showVertex x) (showVertex y) (show o)
    show (ComposePath x (px,i,py) y ) = printf "Compose %s-> %s-> %s\n  Path: %s| %s"
        (showVertex x) (showVertex i) (showVertex y) (showVertex px) (showVertex py)
    show (PathOption x ps y)
      | otherwise = printf "Options: %s-> %s \n %s"
        (showVertex x) (showVertex y) (intercalate "\n " $ fmap (\(l,v) ->  show l <> "." <> show v) $ zip [0..1]  (S.toList ps))

showVertex = intercalate  "," . fmap show . S.toList

data Graph a b = Graph { hvertices :: [Set a]
                     , tvertices :: [Set a]
                     , edges :: Map (Set a,Set a) (Path a b) }
                     deriving(Eq)

instance (Show a,Show b) => Show (Graph a b) where
    show g = printf "Inputs: %s\nOutputs: %s\nEdges:\n%s"
                    (unwords . map show $ hvertices g)
                    (unwords . map show $ tvertices g)
                    (unlines . map show $ fmap snd $ M.toList $ edges g)

{-
mergeGraph :: Graph a b -> Graph a b -> Graph a b
mergeGraph i k = Graph { hvertices = nub $ sort $ hvertices i <>  hvertices k
                       , tvertices = nub $ sort $ tvertices i <> tvertices k
                       , edges = go hiedges (go tiedges (edges k) ) <> go tkedges (go hkedges (edges i))
                       }
    where
      kinter = ih `S.intersection` kt
      iknter = it `S.intersection` kh
      (kh,kt) = pbounds k
      (ih,it) = pbounds i
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

data Path a b
  -- Trivial Path
  = Path  (Set a)  b  (Set a)
  -- Path Composition And Product
  | ComposePath (Set a) (Set (Path a b),Set a,Set (Path a b)) (Set a)
  -- Path Options
  | PathOption (Set a) (Set (Path a b)) (Set a)
  deriving(Eq,Ord)

pbound (Path h1 _ t1) = (h1,t1)
pbound (ComposePath h1 _ t1) =  (h1,t1)
pbound (PathOption h1 _ t1) =  (h1,t1)
{-# INLINE pbound #-}

psame i j = pbound i == pbound j

punion i = psimplify . puniond i
  where
    puniond (PathOption h1 l1 t1) (PathOption h2 l2 t2) =  PathOption h1 (S.union l1 l2) t1
    puniond (PathOption h1 l1 t1) l2 = PathOption h1 (S.insert l2 l1 ) t1
    puniond l2 (PathOption h1 l1 t1) = PathOption h1 (S.insert l2 l1 ) t1
    puniond i j = PathOption h (S.fromList [i,j]) t
        where (h,t) = pbound i
    psimplify p@(PathOption h1 l1 t1)
      | S.size l1 == 1 = head (S.toList l1)
      | otherwise =  p
    psimplify p = p
{-# INLINE punion #-}

pathMap = M.fromList . edgesKeys

mergeGraph g1 g2 = Graph { hvertices = hvertices g1 <> hvertices g2
                         , tvertices = tvertices g1 <> tvertices g2
                         , edges = M.unionWith punion (edges g1 ) (edges g2)
                         }


connected :: Ord a => Graph a b -> Graph a b -> (Set a,Set a)
connected  i k = (S.unions [ m `S.intersection`  n |  m <- hi, n <-tk],S.unions [ m `S.intersection`  n |  m <- ti, n <-hk])
    where hi = hvertices i
          ti = tvertices i
          hk = hvertices k
          tk = tvertices k

--filterConnected :: => Graph a b -> Graph a b -> ([Path a b],[Path a b])
filterConnected i k = (filterEdges k ik i,filterEdges i ki k)
  where (ik,ki) = connected i k
        filterEdges k ik i = (M.filter (S.null . (`S.intersection` ik) . snd . pbound ) (edges k) ,M.filter (S.null . (`S.intersection` ik) . fst . pbound) (edges i) )

addEdge :: (Ord b,Ord a) => Path a b -> Graph a b -> Graph a b
addEdge e g = Graph { edges = go intersects  $ go (M.singleton (pbound e) e) (M.insert (pbound e) e $ edges g)
                   , hvertices = pp : hvertices g
                   , tvertices = pd : tvertices g }
    where
      (pp,pd) = pbound e
      intersects = pathMap $ filter ((\(h,t) -> S.null( S.intersection h pd) ||  S.null (S.intersection t pp) ).pbound) (fmap snd $ M.toList $ edges g)
      --go :: (Ord a, Ord b)=> [(Path a b)] ->  [(Path a b)] -> [(Path a b)]
      go nesM esM
        | M.null nesM = esM
        | otherwise =  go nees nonDup
         where
            nonDup = M.unionWith punion nees esM
            nees =  M.unionsWith punion $
                 fmap pathMap [[(ComposePath d (S.singleton p3,i,S.fromList items) h )  |
                    p3 <- nes ,
                    let bnd = pbound p3
                        d = fst bnd
                        p = snd bnd,
                    items <-  replicateM (S.size p) es ,
                    let
                        h = S.unions $ fmap edgeT items
                        i = S.unions $ fmap edgeH items,
                    i == p ,
                    S.size h == 1 ,
                    d /=  h ]
                    , [(ComposePath h (S.fromList items,i,S.singleton p3) d )  |
                    p3 <- nes ,
                    let bnd = pbound p3
                        p = fst bnd
                        d = snd bnd,
                    items <-  replicateM (S.size p) es ,
                    let
                        h = S.unions $ fmap edgeH items
                        i = S.unions $ fmap edgeT items,
                    i == p ,
                    S.size h == 1 ,
                    d /=  h ]]

             where
                es = fmap snd $ M.toList esM
                nes = fmap snd $ M.toList nesM
                edgeH = fst . pbound
                edgeT = snd . pbound


edgesKeys = fmap (\i-> (pbound i ,i))

nonOverlap items = filter (\i-> all (not . S.isProperSubsetOf  (snd $pbound $ i))  spi ) items
  where spi = fmap (snd.pbound) items
{-# INLINE nonOverlap #-}


warshall :: (Ord a,Ord b) => Graph a b -> Graph a b
warshall g = Graph { edges = go (hvertices g <> tvertices g) (edges g)
                   , hvertices = hvertices g
                   , tvertices = tvertices g }
    where
      go [] es     = es
      go (v:vs) esM =  go vs (M.unionWith punion esM
         ( M.fromList $ edgesKeys [(ComposePath h (S.fromList nonOverlapped,i,S.singleton p3) d )  |
                p3 <- es ,
                let bnd = pbound p3
                    p = fst bnd
                    d = snd bnd,
                items <- fmap nonOverlap $ concat $  fmap (flip replicateM $ es) [1..S.size p] ,
                let
                    nonOverlapped = nonOverlap items
                    h = S.unions $ fmap edgeH nonOverlapped
                    i = S.unions $ fmap edgeT nonOverlapped,
                i == p, h /= d , i /= h,
                all (==h) (fmap edgeH nonOverlapped)
                ]
         ))
         where
            es = fmap snd . M.toList $ esM
            edgeH = fst . pbound
            edgeT = snd . pbound

nestedInv ::  Path a b -> (Set a, [(a, Path a b )])
nestedInv p  = (x,fmap (,p) (S.toList y))
  where (y,x) = pbound p

nested ::  Path a b -> (Set a, [(a, Path a b )])
nested p  = (x,fmap (,p) (S.toList y))
  where (x,y) = pbound p


hashGraph  :: (Ord b,Ord a) => Graph a b -> HashSchema a b
hashGraph = M.map (M.fromListWith (punion)) .  M.fromListWith (++)  .   fmap nested . fmap snd . M.toList .  edges

hashGraphInv  :: (Ord b,Ord a) => Graph a b -> HashSchema a b
hashGraphInv = M.map (M.fromListWith (punion)) .  M.fromListWith (++)  .   fmap nestedInv . fmap snd . M.toList .  edges

find norm end m = case M.lookup norm m of
                    Just i -> M.lookup end i
                    Nothing -> Nothing

queryHash :: Ord a => [a] -> Map (Set a) (Map a b) -> (Set a)  -> [Maybe b]
queryHash filters schema  base =  map (\f-> find base f schema)  filters





