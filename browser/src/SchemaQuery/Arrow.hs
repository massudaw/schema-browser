{-# LANGUAGE Arrows, RankNTypes, TypeFamilies, FlexibleContexts,
  OverloadedStrings, TupleSections #-}

module SchemaQuery.Arrow
  (
   fromR
  , whereR
  , innerJoinR
  , leftJoinR
  , projectV
  ) where

import Control.Arrow
import qualified Control.Lens as Le
import qualified Data.List as L
import Data.Maybe
import qualified Data.Set as S
import qualified Data.Text as T
import Environment
import Query
import RuntimeTypes
import Step.Common
import Types
import qualified Types.Index as G
import Types.Patch
import Utils
import SchemaQuery.Read

fromR
  :: T.Text
  -> DatabaseM (View T.Text T.Text)  [(Rel T.Text , AccessOp Showable)]   (G.GiST (TBIndex Showable) (TBData Key Showable))
fromR m  = P (FromV m ) (Kleisli (\f-> fmap (\(_,_,i) -> i) $ fromTable m f))

whereR
  :: DatabaseM (View T.Text T.Text)  [(Rel T.Text , AccessOp Showable)]  (G.GiST (TBIndex Showable) (TBData Key Showable))
  -> [(Rel T.Text , AccessOp Showable)]
  -> DatabaseM (View T.Text T.Text)  [(Rel T.Text , AccessOp Showable)] (G.GiST (TBIndex Showable) (TBData Key Showable))
whereR (P i k) m  = P (WhereV i m) (proc i -> k -< (i ++ m))


sourceTable inf (JoinV t  j jty _ l ) = alterTable nt
  where path =  FKInlineTable k $ inlineName  ty
        fty = case jty of
                InnerJoin -> []
                LeftJoin -> [KOptional]
        ty = (Primitive fty (RecordPrim (_rawSchemaL tj ,_rawNameL tj)))
        tj = sourceTable inf j
        nt = sourceTable inf t
        k = newKey nt  l ty
        alterTable (Project r i) = r
                    Le.& rawAttrsR Le.%~ (k:)
                    Le.& _inlineFKS Le.%~ (path:)
        alterTable r  = r
                    Le.& rawAttrsR Le.%~ (k:)
                    Le.& _inlineFKS Le.%~ (path:)

sourceTable inf (FromV i) = lookTable inf i
sourceTable inf (WhereV i j) = sourceTable inf i


innerJoinR
  :: DatabaseM (View T.Text T.Text) a (G.GiST (TBIndex Showable) (TBData Key Showable))
  -> DatabaseM (View T.Text T.Text) a (G.GiST (TBIndex Showable) (TBData Key Showable))
  -> [Rel T.Text]
  -> T.Text
  -> DatabaseM (View T.Text T.Text) a (G.GiST (TBIndex Showable) (TBData Key Showable))
innerJoinR (P j k) (P l n) srel alias
  = P (JoinV j l InnerJoin srel alias)
    (proc i -> do
      kv <- k -< i
      nv <- n -< i
      Kleisli (\(emap,amap) -> do
        inf <- askInf
        let origin = sourceTable inf (JoinV j l InnerJoin srel alias)
            target = sourceTable inf l
        let
          rel = (\(Rel i o j) -> Rel (lkKey origin <$> i) o (lkKey target <$> j)) <$>  srel
          aliask = lkKey origin alias
          tar = S.fromList $ _relOrigin <$> rel
          joinFK :: TBData Key Showable ->  Maybe (Column Key Showable)
          joinFK m  = IT aliask <$> (joinRel2 (tableMeta target) (fmap replaceRel $ taratt ) amap)
            where
              replaceRel (Attr k v) = (justError "no rel" $ L.find ((==k) ._relOrigin) rel,v)
              taratt = getAtt tar (tableNonRef m)
          joined i = flip addAttr i <$> joinFK i
        return (G.fromList' $ catMaybes $ (\(i,j,k) -> (,j,k) <$> joined i)<$> G.getEntries emap)) -< (kv,nv))

leftJoinR
  :: DatabaseM (View T.Text T.Text)  a (G.GiST (TBIndex Showable) (TBData Key Showable))
  -> DatabaseM (View T.Text T.Text)  a (G.GiST (TBIndex Showable) (TBData Key Showable))
  -> [Rel T.Text]
  -> T.Text
  -> DatabaseM (View T.Text T.Text)  a (G.GiST (TBIndex Showable) (TBData Key Showable))
leftJoinR (P j k) (P l n) srel alias
  = P (JoinV j l LeftJoin srel alias)
    (proc p -> do
      kv <- k -< p
      nv <- n -< p
      Kleisli (\(emap,amap) -> do
        inf <- askInf
        let
          origin = sourceTable inf (JoinV j l LeftJoin srel alias)
          target = sourceTable inf l
          rel = (\(Rel i o j ) -> Rel (lkKey origin <$> i ) o (lkKey target <$> j) )<$>  srel
          aliask = lkKey origin alias
          tar = S.fromList $ _relOrigin <$> rel
          joinFK :: TBData Key Showable ->  Column Key Showable
          joinFK m  = IT aliask (LeftTB1 $ joinRel2 (tableMeta target ) (fmap replaceRel $ taratt ) amap)
            where
              replaceRel (Attr k v) = (justError "no rel" $ L.find ((==k) ._relOrigin) rel,v)
              taratt = getAtt tar (tableNonRef m)
          joined i = addAttr (joinFK i) i
        return $  joined  <$> emap)-< (kv,nv))

projectV
  :: (Show k , Traversable t2) =>
    DatabaseM  (View i k) [(Rel T.Text , AccessOp Showable)] (t2 (KV Key c))
     -> PluginM (Union (G.AttributePath k MutationTy))  (Atom ((TBData T.Text c)))  TransactionM () b
     -> DatabaseM (View i k) () (t2 b)
projectV  (P i (Kleisli j))  p@(P (k,_) _ ) = P (ProjectV i (foldl mult one k)) (Kleisli $  \_ -> (j [])  >>=  (\a -> traverse (evalEnv p . (,[]) . Atom .  mapKey' keyValue) a))


