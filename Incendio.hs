{-# LANGUAGE TupleSections,RankNTypes ,OverloadedStrings #-}
module Incendio (readLinks) where

import Diagram
import Element
import Sprinkler
import Grid
import Test
import Debug.Trace

import Control.Applicative
import qualified Data.Traversable as Tra
import Data.Traversable (Traversable)
import Data.Functor.Identity

import qualified Data.Map as M
import Data.Map (Map)
import qualified Data.Foldable as F
import qualified Data.Set as S
import qualified Data.List as L

import qualified Data.Text.Lazy as TL
import Data.Unique

import Data.Maybe
import Schema
import Postgresql
import Query
import Diagrams.Prelude
import Diagrams.Backend.SVG.CmdLine
import Diagrams.Backend.SVG
import Text.Blaze.Svg.Renderer.Utf8

import Numeric.AD
import Numeric.AD.Mode

import qualified Data.Vector as V
import Database.PostgreSQL.Simple

makeFilter :: PK (Key,Showable) -> Map Key [Filter]
makeFilter i = M.fromListWith mappend ((\(fkv,kv)-> (fkv,[Category (S.fromList kv)])) <$> arg)
      where arg :: [(Key, [PK Showable])]
            arg =  fmap (\i -> [PK [i] []]) <$> F.toList (pkKey i )

projectKey
  :: Connection
     -> InformationSchema ->
     (forall t . Traversable t => QueryT Identity (t KAttribute)
         -> S.Set Key -> IO [t (Key,Showable)])
projectKey conn inf q  = (\(j,(h,i)) -> fmap (fmap (zipWithTF (,) (fmap (\(Metric i)-> i) j))) . queryWith_ (fromShowableList j) conn .  buildQuery $ i ) . projectAllKeys (pkMap inf ) (hashedGraph inf) q

insertNode conn inf proj l =
  insert conn (fmap (\(l,v)->(lookKey inf "node" l,v))  $ zip ["project","id","linklist"]  (SNumeric proj :makeNode l) ) (lookTable inf "node")

insertLink conn inf proj l =
  insert conn (fmap (\(l,v)->(lookKey inf "link" l,v))  $ zip ["project","id","headnode","tailnode","diameterhead","var","tag"]  (SNumeric proj :makeLink l) ) (lookTable inf "link")

makeNode (id,(s,(_,n))) = [SNumeric id,SComposite (SNumeric <$> fun n)]
  where fun (Tee (TeeConfig t _ _ _ _)) = V.fromList t
        fun n = V.fromList (S.toList s)

makeLink (id,h,t,i) = [SNumeric id,SNumeric h,SNumeric t,SDouble (head $ catMaybes $ diametroE <$>i) ,SComposite var,SComposite tag]
  where fun e = case e of
            (Tubo _ l _) -> ("L",l)
            (Joelho _ ("Conexao","Joelho","90") DLeft _) -> ("T",-90)
            (Joelho _ ("Conexao","Joelho","90") DRight _) -> ("T",90)
            (Joelho _ ("Conexao","Joelho","45") DLeft _) -> ("T",-45)
            (Joelho _ ("Conexao","Joelho","45") DRight _) -> ("T",45)
            (Bomba _ _ _ _)  -> ("L",0)
            i -> error $ show id <> " No element for " <> show i
        tag = V.fromList $fmap (SText .fst.fun) i
        var = V.fromList $fmap (SDouble .snd.fun) i

transformL [SNumeric id, SNumeric h,SNumeric t,SDouble dh, SComposite var,SComposite tag] = (id,h,t,fun <$> tgvr)
  where
          fun tu = case tu of
                   ("T",45) -> Joelho (Just dh) ("Conexao","Joelho","45") DRight 100
                   ("T",-45) -> Joelho (Just dh) ("Conexao","Joelho","45")  DLeft 100
                   ("T",-90) -> Joelho (Just dh) ("Conexao","Joelho","90")  DLeft 100
                   ("T",90)-> Joelho (Just dh) ("Conexao","Joelho","90")  DRight 100
                   ("L",l)-> Tubo (Just dh) l   100
                   i -> error $ show id <> " No element for turn " <> show i
          vr =  V.toList $ fmap (\(SDouble i)-> i) var
          tg =  V.toList $ fmap (\(SText i)-> i) tag
          tgvr = L.zip tg vr

transformL i = error $ show i

transformM [SNumeric id, SComposite h] =  (id,DesignRegion f)
  where f =  V.toList $ fmap (\(SNumeric i)-> i) h
transformM i = error $ show i

transformNH [SNumeric id, SComposite h,SDouble nh]
  | V.length h == 1 = (id,nh)

transformN [SNumeric id, SComposite h]
  | V.length h == 1 = (id,Open 0)
  | V.length h == 2 = (id,Sprinkler (Just (1,2) ) (Just 1) 1 1)
  | V.length h == 3 = (id,Tee (TeeConfig f 0.008 0.08  0.08 1000))
  where f =  V.toList $ fmap (\(SNumeric i)-> i) h
transformN i = error $ show i


readLinks conn inf input = do
  let projFilter = maybe M.empty (makeFilter . (\i -> PK [i][])) (L.find ((=="id_sprinkler").keyValue.fst) input)
  i <- projectKey conn inf (predicate (L.concat $ fmap (\(i,j)-> fmap (i,) j) $M.toList projFilter) >> projectAllRec' (tableMap inf )) (S.fromList $ lookKey inf "link" <$> [ "id", "project"])
  j <-projectKey conn inf (projectAllRec' (tableMap inf )) (S.fromList $ lookKey inf "node" <$> ["id","project"])
  jh <-projectKey conn inf (projectAllRec' (tableMap inf )) (S.fromList $ lookKey inf "nodehead" <$> ["id","project"])
  r <-projectKey conn inf (projectAllRec' (tableMap inf )) (S.fromList $ lookKey inf "design_region" <$> ["id","project"])
  let l =  transformL . fmap snd . fromJust . projeKeys ["id","headnode","tailnode","diameterhead","var","tag"] . F.toList <$> i
      n =  transformN . fmap snd . fromJust . projeKeys ["id","linklist"] . F.toList <$> j
      nh =  transformNH . fmap snd . fromJust . projeKeys ["id","linklist","pressure"] . F.toList <$> jh
      m =  transformM . fmap snd . fromJust . projeKeys ["id","bicos"] . traceShowId . F.toList <$> r
      grid = traceShowId $ Grid l nh n  []
      iter region =  solveIter (enableSprinklers region $ Iteration ((\(id,_,_,_) -> (id,4)) <$> l) ((\(i,_)->(i,200)) <$> n) (fmap realToFrac grid)) jacobianEqNodeHeadGrid
  return $ renderSvg $ renderDia SVG (SVGOptions (Width 500) Nothing) (L.foldr1 (|||) $fmap (assembleMap . drawGrid 212 31. iter. snd) m :: Diagram B R2)

projeKeys ks inp = allMaybes $ (\i -> L.find ((==i).keyValue.fst) inp ) <$> ks

testLinks = do
  m <-newUnique
  withConnInf "incendio" (\i j -> do
                         -- mapM (insertLink i j 64)  (links $ grid test3) )
                         --mapM (insertNode i j 64)  (nodesFlowSet $ grid test3) )
                         readLinks i j [(Key "id_sprinkler" (Just "id_sprinkler") Nothing  m (Primitive "bigint") ,SNumeric 64)])
