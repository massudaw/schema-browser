{-# LANGUAGE RecursiveDo,Arrows, RankNTypes, TypeFamilies, FlexibleContexts,
  FlexibleInstances,TypeSynonymInstances,OverloadedStrings, TupleSections #-}

module SchemaQuery.Arrow
  (
    fromR
  , fromS
  , whereR
  , whereS
  , innerJoinR
  , innerJoinS
  , leftJoinR
  , fixLeftJoinR
  , fixLeftJoinS
  , projectV
  , projectS
  , runMetaArrow
  ) where

import Control.Arrow
import Control.Monad.State
import Data.Either
import Reactive.Threepenny hiding (apply)
import Control.Monad.RWS
import Reactive.Threepenny.PStream
import Control.Monad.IO.Class
import qualified Control.Lens as Le
import qualified Data.HashMap.Strict as HM
import Text
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
import SchemaQuery.Store

fromR
  :: T.Text
  -> DatabaseM (View T.Text T.Text)  (WherePredicateK T.Text) (G.GiST (TBIndex Showable) (TBData Key Showable))
fromR m  = P (FromV m ) (Kleisli (\e -> currentValue  =<< (fmap primary . psvalue . fst) <$>  fromTable m e))

fromS
  :: T.Text
  -> DatabaseM (View T.Text T.Text)  (PStream (WherePredicateK T.Text)) (PStream (TableRep  Key Showable))
fromS m  = P (FromV m ) (Kleisli (fmap fst <$> fromTableS m ))

whereS
  :: DatabaseM (View T.Text T.Text)  (PStream (WherePredicateK T.Text))  (PStream (TableRep  Key Showable))
  -> [(Rel T.Text , AccessOp Showable)]
  -> DatabaseM (View T.Text T.Text)  (PStream (WherePredicateK T.Text)) (PStream (TableRep  Key Showable)) 
whereS (P i@(FromV t) k) m  = P (WhereV i m) (proc i -> k -< constV (tablePredicate' m ) i)

constV v (PStream b e) = PStream ((v <>) <$> b) e



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
  
instance Patch (WherePredicateK v) where
  type Index (WherePredicateK v) = WherePredicateK v
  applyUndo (WherePredicate (AndColl i)) (WherePredicate (AndColl j)) = Right $ (WherePredicate (AndColl (i <> j)),WherePredicate (AndColl i))
  applyUndo (WherePredicate (OrColl i)) (WherePredicate (OrColl j)) = Right $ (WherePredicate (OrColl (i <> j)), WherePredicate (OrColl (i )))
    
pmap f fp (PStream b e ) = PStream (f <$> b) (fp <$> e)

pconst  b  = PStream (pure b) never 


pmerge :: (Patch c, Patch a , Patch b) => (a -> b -> TransactionM c ) -> (a -> Index b -> Index c) ->  (b -> Index a -> Index c) -> (PStream a , PStream b) -> TransactionM (PStream c)
pmerge fun fr fl (PStream br er, PStream bl el) = do
  let ev = unionWith const (fr <$> br <@> el ) (fl <$> bl <@> er )
  bri <- currentValue  br
  bli <- currentValue  bl
  ini <- fun bri bli 
  lift $ accumS ini  ev

  
innerJoinS
  :: DatabaseM (View T.Text T.Text) (PStream (WherePredicateK T.Text)) (PStream  (TableRep Key Showable))
  -> DatabaseM (View T.Text T.Text) (PStream (WherePredicateK T.Text)) (PStream  (TableRep Key Showable))
  -> [Rel T.Text]
  -> T.Text
  -> DatabaseM (View T.Text T.Text)  (PStream (WherePredicateK T.Text))  (PStream  (TableRep Key Showable)) 
innerJoinS (P j k) (P l n) srel alias =
  P (JoinV j l InnerJoin srel alias)
    (proc i -> do
      kv <- k -< i
      nv <- n -< pmap (\v ->  fromMaybe mempty $ fkPredicate srel (mapKey' keyValue <$> G.toList (primary v) )) (\v ->  fromMaybe mempty $ fkPredicate srel [ ((\(RowPatch (_,CreateRow i) ) -> mapKey' keyValue  i ) $ (v :: RowPatch Key Showable) )] ) kv 
      Kleisli (pmerge (\i k -> innerJoin j l srel alias (primary i, primary k)) (\_ i -> i) (\_ i -> i) ) -< (kv ,nv))

primaryRep (TableRep (m,s,p)) = PrimaryRep (m,p)

innerJoinR
  :: DatabaseM (View T.Text T.Text) (WherePredicateK T.Text) (G.GiST (TBIndex Showable) (TBData Key Showable))
  -> DatabaseM (View T.Text T.Text) (WherePredicateK T.Text) (G.GiST (TBIndex Showable) (TBData Key Showable))
  -> [Rel T.Text]
  -> T.Text
  -> DatabaseM (View T.Text T.Text)  (WherePredicateK T.Text)  (G.GiST (TBIndex Showable) (TBData Key Showable))
innerJoinR (P j k) (P l n) srel alias
  = P (JoinV j l InnerJoin srel alias)
    (proc i -> do
      kv <- k -< i
      nv <- n -< maybe i (<> i) $ fkPredicate srel (mapKey' keyValue <$> G.toList kv ) 
      Kleisli (fmap primary <$> innerJoin j l srel alias)-< (kv,nv))

innerJoin j l srel alias = (\(emap,amap) -> do
        inf <- askInf
        let origin = sourceTable inf (JoinV j l InnerJoin srel alias)
            target = sourceTable inf l
        let
          rel = (\(Rel i o j) -> Rel (lkKey origin <$> i) o (lkKey target <$> j)) <$>  srel
          aliask = lkKey origin alias
          tar = S.fromList $ _relOrigin <$> rel
          joinFK :: TBData Key Showable ->  Either String (Column Key Showable)
          joinFK m  = maybe (Left ("Missing reference: " ++ show taratt)) Right $ IT aliask <$> joinRel2 (tableMeta target) (fmap replaceRel $ taratt ) amap
            where
              replaceRel (Attr k v) = (justError "no rel" $ L.find ((==k) ._relOrigin) rel,v)
              taratt = getAtt tar (tableNonRef m)
          joined i = flip addAttr i <$> joinFK i
          result = (\(i,j,k) -> joined i)<$> G.getEntries emap
        when (L.any isLeft result) . liftIO $do
           putStrLn  $"Missing references: " ++  (L.intercalate "," $ renderRel <$> srel) ++ " - "++ T.unpack alias
           print (L.length $ rights result)
           print (G.keys amap)
           print (lefts result)
        return (F.foldl' apply (TableRep (tableMeta origin, mempty ,mempty)) (createRow' (tableMeta origin)<$> rights result ) ))

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

joinP t = do
  (e,h) <- newEvent
  init <- currentValue (facts t)
  el <- currentValue (psvalue init)
  mapTidingsDyn (flip onEventDyn (liftIO. h) .psevent ) t
  accumS el e

  

fixLeftJoinS
  :: DatabaseM (View T.Text T.Text) (PStream (WherePredicateK T.Text)) (PStream (TableRep Key Showable))
  -> DatabaseM (View T.Text T.Text) (PStream (WherePredicateK T.Text)) (PStream (TableRep Key Showable))
  -> [Rel T.Text]
  -> Maybe (Rel T.Text)
  -> T.Text
  -> DatabaseM (View T.Text T.Text) (PStream (WherePredicateK  T.Text)) (PStream (TableRep Key Showable))
fixLeftJoinS (P j k) (P l n) srel index alias 
  = P  join 
    (proc p -> do
      kv <- k -< p
      Kleisli (go (relComp srel)  (0 ::Int)) -< kv)
    where 
      join = JoinV j l LeftJoin srel alias
      go _  ix _ | ix > 5 = error "max recursion"
      go cindex ix  kv = do
        preinf <- askInf
        let 
          predS :: PStream (WherePredicateK T.Text)
          predS = pmap 
                  (\v ->  fromMaybe mempty $ fkPredicateIx cindex (mapKey' keyValue <$> G.toList (primary v))) 
                  (\(RowPatch (_,CreateRow i) ) ->  fromMaybe mempty $ fkPredicateIx cindex [ mapKey' keyValue  i ]) kv 
        lift $  joinP =<<  mapTidingsDyn (\predM -> if predM == mempty
            then return kv 
            else transaction preinf $ do  
              out <- (runKleisli n) (pconst predM)
              result <- pmerge (\i j ->  do
                let joined = joinRelation preinf join cindex (primary i )
                    (origin ,inf) = updateTable preinf  join 
                return $ F.foldl' apply (TableRep (tableMeta origin, mempty ,mempty)) $ 
                    (\ jix ->  createRow' (tableMeta origin) $ apply jix (joined jix )  ) <$> (G.toList (primary j ))) (\ _ i -> i ) (\ _ i -> i )  (out, kv)
              go (relAppend (maybe (Inline alias) (relAppend (Inline alias)) index ) cindex ) (ix+1)  result 
                                         ) (toTidings predS)


fixLeftJoinR 
  :: DatabaseM (View T.Text T.Text) (WherePredicateK T.Text) (G.GiST (TBIndex Showable) (TBData Key Showable))
  -> DatabaseM (View T.Text T.Text) (WherePredicateK T.Text) (G.GiST (TBIndex Showable) (TBData Key Showable))
  -> [Rel T.Text]
  -> Maybe (Rel T.Text)
  -> T.Text
  -> DatabaseM (View T.Text T.Text) (WherePredicateK  T.Text)(G.GiST (TBIndex Showable) (TBData Key Showable))
fixLeftJoinR (P j k) (P l n) srel index alias 
  = P  join 
    (proc p -> do
      kv <- k -< p
      Kleisli (go (relComp srel)  (0 ::Int)) -< kv)
    where 
      join = JoinV j l LeftJoin srel alias
      go _  ix _ | ix > 5 = error "max recursion"
      go cindex ix  kv = do
          let predM = fkPredicateIx mergedRel (mapKey' keyValue <$> G.toList kv )
              mergedRel = cindex 
          case predM of 
            Nothing -> do
              liftIO $ 
                putStrLn $  "## Fix " <> show l <> renderRel cindex <> show ix <> " " <> show (G.keys kv) 
              return kv 
            Just pred -> do  
              inf <- askInf 
              liftIO $ putStrLn $  "## Fix " <> show l <> renderPredicateWhere pred
              out <- (runKleisli n) pred 
              liftIO $ 
                putStrLn $  "## Fix " <> show l <> renderRel cindex <> show ix <> " " <> show (G.keys out) 
              let joined = joinRelation inf join cindex out
              go (relAppend (maybe (Inline alias) (relAppend (Inline alias)) index ) cindex ) (ix+1) ((\i -> apply i (joined i)) <$> kv) 

joinRelation preinf join@(JoinV j l LeftJoin srel alias) index amap =  do
    let
      (origin ,inf) = updateTable preinf  join 
      target = sourceTable preinf l
      targetPK = fmap keyValue <$> rawPK target
      joinFK :: TBData Key Showable ->  PathAttr Key Showable
      joinFK m  = liftPatchAttr inf (tableName origin) $ justError ("cant index: "  ++ show  (srel , m) ) (indexRelation  indexTarget index (mapKey' keyValue m))
        where
          replaceRel (Attr k v) = (justError "no rel" $ L.find ((==k) ._relOrigin) srel,v)
          findRef i v = maybe (traceShow (pk ,rawPK target , G.keys amap) Nothing) Just $ patch . mapKey' keyValue <$> G.lookup pk  amap

            where targetRel = (L.sortOn (\ i -> L.elemIndex (_relTarget i) targetPK )  i )
                  pk = (G.getUnique targetRel (kvlist v))

          indexTarget rel' v = Just . PInline alias . POpt $  indexContainer (findRef rel ) (checkLength v rel <$> liftOrigin rel (unkvlist (tableNonRef v)))
            where rel = relUnComp  rel' 
                  checkLength tb rel v 
                    | L.length rel == L.length v = v
                    | otherwise = error $ "missing parameters : " ++ show  (rel,v,index,tb)
      joined i = [joinFK i]
     in joined 


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
-- indexRelation i j k | traceShow ("indexRelation",j) False = undefined
indexRelation f (RelAccess (Inline key ) nt) r
 = do 
   let i = justError ("ref error" <> show key ) $ refLookup (Inline key) r
   PInline key . fmap pure <$> indexContainer (indexRelation f nt) i
indexRelation f n@(RelAccess nk nt )  r
 = do
   let i = justError ("rel error" <> show nk) $ relLookup nk r 
   PFK (relUnComp nk) [] . fmap pure <$> indexContainer allRefs i
  where
    allRefs (TBRef (i,v))=  indexRelation f nt v
-- indexRelation f n@(RelComposite l) = filter (S.null . relOutputSet )
indexRelation f a  r
  =  f a r

projectS
  :: Show k =>
    DatabaseM  (View i k) (PStream (WherePredicateK T.Text) ) (PStream (TableRep  Key Showable))
     -> PluginM (Union (G.AttributePath k MutationTy))  (Atom (TBData T.Text Showable))  TransactionM () b
     -> DatabaseM (View i k) () (Tidings (G.GiST (TBIndex Showable) b))
projectS  (P i (Kleisli j))  p@(P (k,_) _ ) = P (ProjectV i (foldl mult one k)) (Kleisli $  \_ -> (j empty )  >>= mapArrow . fmap primary . toTidings  )
        where empty = PStream (pure mempty) never
              mapArrow a = do
                  inf <- ask 
                  lift $ mapTidingsDyn (\a -> transaction (fst inf) $ traverse (evalEnv p . (,mempty) . Atom . mapKey' keyValue) a) a 



projectV
  :: (Show k , Traversable t2) =>
    DatabaseM  (View i k) (WherePredicateK T.Text ) (t2 (KV Key c))
     -> PluginM (Union (G.AttributePath k MutationTy))  (Atom ((TBData T.Text c)))  TransactionM () b
     -> DatabaseM (View i k) () (t2 b)
projectV  (P i (Kleisli j))  p@(P (k,_) _ ) = P (ProjectV i (foldl mult one k)) (Kleisli $  \_ -> (j mempty)  >>=  
      (\a -> traverse (evalEnv p . (,mempty) . Atom .  mapKey' keyValue) a))

runMetaArrow inf fun = transactionNoLog (meta inf) $ dynPK (fun inf) ()

runMetaArrowS inf fun = transactionNoLog (meta inf) $ dynPK (fun inf) ()

