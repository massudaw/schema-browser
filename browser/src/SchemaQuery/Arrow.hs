{-# LANGUAGE RecursiveDo,Arrows, RankNTypes, TypeFamilies, FlexibleContexts,
  OverloadedStrings, TupleSections #-}

module SchemaQuery.Arrow
  (
   fromR
  , whereR
  , innerJoinR
  , leftJoinR
  , fixLeftJoinR
  , projectV
  ) where

import Control.Arrow
import Control.Monad.State
import Control.Monad.IO.Class
import qualified Control.Lens as Le
import qualified Data.HashMap.Strict as HM
import qualified Data.List as L
import Debug.Trace
import qualified NonEmpty as Non
import Control.Monad
import Control.Applicative
import qualified Data.Sequence.NonEmpty as NonS
import Data.Functor.Identity
import qualified Data.Foldable as F
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
  -> DatabaseM (View T.Text T.Text)  (WherePredicateK T.Text)   (G.GiST (TBIndex Showable) (TBData Key Showable))
fromR m  = P (FromV m ) (Kleisli (\f-> fmap (\(_,_,i) -> i) $ fromTable m f))

whereR
  :: DatabaseM (View T.Text T.Text)  (WherePredicateK T.Text)  (G.GiST (TBIndex Showable) (TBData Key Showable))
  -> [(Rel T.Text , AccessOp Showable)]
  -> DatabaseM (View T.Text T.Text)  (WherePredicateK T.Text)  (G.GiST (TBIndex Showable) (TBData Key Showable))
whereR (P i@(FromV t) k) m  = P (WhereV i m) (proc i -> k -< tablePredicate' m <> i)


sourceTable inf table = evalState (sourceTableM table) inf

updateTable inf table = runState (sourceTableM table) inf

sourceTableM (JoinV t  j jty _ l ) = do
  inf <- get 
  tj <- sourceTableM j
  nt <- sourceTableM t
  let path =  FKInlineTable k $ inlineName  ty
      fty = case jty of
              InnerJoin -> []
              LeftJoin -> [KOptional]
      ty = (Primitive fty (RecordPrim (_rawSchemaL tj ,_rawNameL tj)))
      k = newKey nt  l ty
      alterTable (Project r i) = r
                  Le.& rawAttrsR Le.%~ (k:)
                  Le.& _inlineFKS Le.%~ (path:)
      alterTable r  = r
                  Le.& rawAttrsR Le.%~ (k:)
                  Le.& _inlineFKS Le.%~ (path:)
  modify (
    (keyMapL  Le.%~ HM.insert (tableName nt, l ) k ) .
      (tableMapL . Le.ix (tableName nt)   Le.%~  alterTable ))

  return $ alterTable nt

sourceTableM (FromV i) = do
  inf <- get
  return $ lookTable inf i
sourceTableM (WhereV i j) = sourceTableM i
  

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
  :: DatabaseM (View T.Text T.Text)  (WherePredicateK T.Text) (G.GiST (TBIndex Showable) (TBData Key Showable))
  -> DatabaseM (View T.Text T.Text)  (WherePredicateK T.Text) (G.GiST (TBIndex Showable) (TBData Key Showable))
  -> [Rel T.Text]
  -> T.Text
  -> DatabaseM (View T.Text T.Text)  (WherePredicateK T.Text) (G.GiST (TBIndex Showable) (TBData Key Showable))
leftJoinR (P j k) (P l n) srel alias
  = P (JoinV j l LeftJoin srel alias)
    (proc p -> do
      kv <- k -< p
      nv <- n -< maybe p (<> p) $ fkPredicate srel (mapKey' keyValue <$> G.toList kv )
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
        return $ joined <$> emap) -< (kv,nv))

fixLeftJoinR 
  :: DatabaseM (View T.Text T.Text) (WherePredicateK T.Text) (G.GiST (TBIndex Showable) (TBData Key Showable))
  -> DatabaseM (View T.Text T.Text) (WherePredicateK T.Text) (G.GiST (TBIndex Showable) (TBData Key Showable))
  -> [Rel T.Text]
  -> Maybe (Rel T.Text)
  -> T.Text
  -> DatabaseM (View T.Text T.Text) (WherePredicateK  T.Text)(G.GiST (TBIndex Showable) (TBData Key Showable))
fixLeftJoinR (P j k) (P l n) srel index alias 
  = P (JoinV j l LeftJoin srel alias)
    (proc p -> do
      kv <- k -< p
      Kleisli (go (relComp srel)  (0 ::Int)) -< kv)
    where 
      go _  ix _ | ix > 5 = error "max recursion"
      go cindex ix  kv = do

          let predM = fkPredicateIx mergedRel (mapKey' keyValue <$> G.toList kv )
              mergedRel = cindex 
          liftIO $ print ("fixLeftPred",ix,cindex,predM)
          case predM of 
            Nothing -> return kv 
            Just pred -> do  
              out <- (runKleisli n) pred 
              joined <- joinRelation cindex out
              go (relAppend (maybe (Inline alias) (relAppend (Inline alias)) index ) cindex ) (ix+1) (joined <$> kv) 
      joinRelation indext amap =  do
          preinf <- askInf
          let
            (origin ,inf) = updateTable preinf (JoinV j l LeftJoin srel alias)
            target = sourceTable preinf l
            targetPK = keyValue <$> rawPK target
            index = indext --liftRel inf (tableName target) indext
            aliask = alias
            joinFK :: TBData Key Showable ->  PathAttr Key Showable
            joinFK m  = traceShowId $ liftPatchAttr inf (tableName origin) $ justError ("cant index: "  ++ show  (srel , m) ) (indexRelation  indexTarget index (mapKey' keyValue m))
              where
                replaceRel (Attr k v) = (justError "no rel" $ L.find ((==k) ._relOrigin) srel,v)
                findRef i v = maybe (traceShow (i,v) Nothing) Just $ patch . mapKey' keyValue <$> G.lookup ( traceShowId $ G.getUnique targetRel (kvlist v)) amap
                  where targetRel = (_relOrigin <$> L.sortOn (\ i -> L.elemIndex (_relOrigin $ _relTarget i) targetPK )  i )

                indexTarget rel' v = Just . PInline aliask . POpt $  indexContainer (findRef rel ) (checkLength v rel <$> liftOrigin rel (unkvlist (tableNonRef v)))
                  where rel = relUnComp  rel' 
                        checkLength tb rel v 
                          | L.length rel == L.length v = v
                          | otherwise = error $ "missing parameters : " ++ show  (rel,v,indext,tb)
            joined i = apply  i [joinFK i]
          return joined 


indexContainer
  :: Show t => (t -> Maybe a) -> FTB t -> Maybe (PathFTB a)
indexContainer f i = recFTB  i
  where 
    -- recFTB :: FTB a -> Maybe (PathFTB a)
    recFTB (TB1 i ) = PAtom <$> f i
    recFTB (LeftTB1 i) = fmap POpt $  traverse recFTB i
    recFTB (ArrayTB1 i) = patchSet $  catMaybes $ F.toList $ NonS.imap (\ix i -> fmap (PIdx ix . Just) $ recFTB i ) i
    recFTB i = error (show ("IndexPredIx",i))

indexRelation 
  :: (Show k ,Show a,Ord k) 
  => (Rel k -> TBData k a -> Maybe (PathAttr k v)) 
  -> Rel k 
  -> TBData k a 
  -> Maybe (PathAttr k v) 
-- indexrelation i j k | traceShow j False = undefined
indexRelation f (RelAccess (Inline key ) nt) r
 = do 
   i <- refLookup (Inline key) r
   PInline key . fmap pure <$> indexContainer (indexRelation f nt) i
indexRelation f n@(RelAccess nk nt )  r
 = do
    i <- relLookup nk r 
    PFK (relUnComp nk) [] . fmap pure <$> indexContainer allRefs i
  where
    allRefs (TBRef (i,v))=  indexRelation f nt v
indexRelation f a  r
  =  f a r



projectV
  :: (Show k , Traversable t2) =>
    DatabaseM  (View i k) (WherePredicateK T.Text ) (t2 (KV Key c))
     -> PluginM (Union (G.AttributePath k MutationTy))  (Atom ((TBData T.Text c)))  TransactionM () b
     -> DatabaseM (View i k) () (t2 b)
projectV  (P i (Kleisli j))  p@(P (k,_) _ ) = P (ProjectV i (foldl mult one k)) (Kleisli $  \_ -> (j mempty)  >>=  (\a -> traverse (evalEnv p . (,mempty) . Atom .  mapKey' keyValue) a))


