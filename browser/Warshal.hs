{-# LANGUAGE ScopedTypeVariables, NoMonomorphismRestriction,
  FlexibleContexts, TupleSections #-}module Warshal where

import Data.Maybe
import Data.Monoid hiding(Product)
import Control.Applicative
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Map (Map)
import Data.Set (Set)
import Text.Printf ( printf )
import Types

type HashSchema  a b = Map a (Map a [Path a b])


showVertex = show

data Graph a b = Graph { hvertices :: [a]
                     , tvertices :: [a]
                     , edges :: Map (a,a) [Path a b] }
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

{-
data Cardinality a
  = One a
  | Many a
  deriving(Eq,Ord,Show)
-}

instance Functor (Path a) where
  fmap f (Path i t j ) =  Path i (f t ) j

pbound (Path h1 _ t1) = (h1,t1)
pbound (ComposePath h1 _ t1) =  (h1,t1)
{-# INLINE pbound #-}

psame i j = pbound i == pbound j

pathMap = M.fromList . edgesKeys

{-
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

-}
edgesKeys = fmap (\i-> (pbound i ,i))



warshall2 :: (Ord a,Ord b) => Graph a b -> Graph a b
warshall2 g = Graph { edges = go (hvertices g <> tvertices g) (pmapnew (M.toList initE)) initE
                   , hvertices = hvertices g
                   , tvertices = tvertices g }
    where
      initE = Left Control.Applicative.<$> edges g
      pmapnew nedges = M.fromListWith mappend $ fmap (fmap S.singleton) nedges
      generateTrails es m = filter ((/=[]).snd) $ fmap (\e -> (e,go  e)) es
        where
          -- go :: (Set a ,Set a)-> [Path a b]
          go e@(h,t) =  concat $ maybeToList $ do
            i <- M.lookup e m
            return $ concat $ (\ii-> case ii of
                 Right p -> [ComposePath h  (S.singleton ho, p,S.singleton to) t | ho <- go (h,p) , to <- go (p,t)]
                 Left j -> j ) <$> i
      allWays :: Eq a => [a] -> [a] -> [(a,a)]
      allWays e t = [(i,j) | i <- e , j <- t , i /= j]
      go [] pmap _  = M.fromList $ generateTrails (allWays (hvertices g ) (tvertices g)) (fmap S.toList  pmap)
      go (v:vs) pmap esM =  go vs ( M.unionWith mappend pmap (pmapnew nedges)) ( M.union esM
          (M.fromList  nedges) )
         where
            nedges  =  [((h,d), Right i)    |
                items <- M.keys initE,
                p3 <- es,
                let bnd = p3
                    p = fst bnd
                    d = snd bnd,
                let
                    h = fst items
                    i = snd items,
                i == p, h /= d , i /= h
                ]
            es = M.keys esM

renderInv  = putStrLn . unlines . fmap (\(i,j) ->  show i <> "\n" <> unlines (fmap (\(k,v) -> "\t" <> show k  <> " -- " <> show (length v)<> "\n" <> unlines (fmap (("\t\t" <> ) .show)  v) )  (M.toList j )) )  . M.toList
{-
warshall :: (Ord a,Show a,Show b ,Ord b) => Graph a b -> Graph a b
warshall g = Graph { edges = go (hvertices g <> tvertices g) (edges g)
                   , hvertices = hvertices g
                   , tvertices = tvertices g }
    where
      go [] es     = es
      go (v:vs) esM =  go vs ( M.unionWith punion esM
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
-}
nestedInv' ::  (a , a) -> [Path a b] -> (a, [(a, Path a b )])
nestedInv' (y,x) p  = (x,fmap (y,) p)


nested :: (a , a) -> [Path a b] -> (a, [(a, Path a b )])
nested (x,y) p  = (x,fmap (y,) p  )


hashGraph  :: (Ord b,Ord a) => Graph a b -> HashSchema a b
hashGraph = M.map (M.fromListWith (++) .  fmap (fmap pure )) . M.fromListWith (++)  .   fmap (uncurry nested) . M.toList .  edges


hashGraphInv'  :: (Ord b,Ord a) => Graph a b -> Map a (Map a [Path a b])
hashGraphInv' = M.map (M.fromListWith (++) . fmap (fmap pure) ) .  M.fromListWith (++)  .   fmap (uncurry nestedInv') . M.toList .  edges

find norm end m = case M.lookup norm m of
                    Just i -> M.lookup end i
                    Nothing -> Nothing

queryHash :: Ord a => [a] -> HashSchema a b -> a  -> [Maybe [Path a b]]
queryHash filters schema  base =  map (\f-> find base f schema)  filters


