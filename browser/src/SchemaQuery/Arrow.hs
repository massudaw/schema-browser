{-# LANGUAGE RecursiveDo,Arrows, RankNTypes, TypeFamilies, FlexibleContexts,
  FlexibleInstances,TypeSynonymInstances,OverloadedStrings, TupleSections #-}

module SchemaQuery.Arrow
  (
    fromS
  , whereS
  , innerJoinS
  , leftJoinS
  , fixLeftJoinS
  , projectS
  , runMetaArrow
  ) where

import Control.Arrow
import Control.Monad.State
import TP.Widgets (joinP,calmT)
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

type InputType = (WherePredicateK T.Text , KVMeta Key )


fromS
  :: T.Text
  -> DatabaseM (View T.Text T.Text)  (PStream InputType) (PStream (TableRep  Key Showable))
fromS m  = P (FromV m ) (Kleisli (trace "fromtable" . fmap fst <$> fromTableS m ))

whereS
  :: DatabaseM (View T.Text T.Text)  (PStream InputType)  (PStream (TableRep  Key Showable))
  -> [(Rel T.Text , AccessOp Showable)]
  -> DatabaseM (View T.Text T.Text)  (PStream InputType) (PStream (TableRep  Key Showable)) 
whereS (P i k) m  = P (WhereV i m) (proc i -> k -< constV (first (tablePredicate' m <>) ) i)

constV f (PStream b e) = PStream ( f  <$> b) e

emptyP inp = PStream (pure inp) never



sourceTable inf table = evalState (sourceTableM table) inf

updateTable inf table = runState (sourceTableM table) inf

predicateTree :: Ord t => View t t -> WherePredicateK t
predicateTree (FromV _  ) = mempty
predicateTree (WhereV m i  ) =  tablePredicate' i  <> predicateTree m 
predicateTree (JoinV t j jty rel) = predicateTree t <> mapPredicate (first (RelAccess (relComp rel))) (predicateTree j)
  where mapPredicate f (WherePredicate i ) = WherePredicate $ fmap f i 

sourceTableM (JoinV t  j jty rel) = do
  inf <- get 
  tj <- sourceTableM j
  nt <- sourceTableM t
  let path =  FKJoinTable (lkRel <$> rel)  (rawSchema tj ,rawName tj)
      lkRel (Rel i op j ) = Rel (lkKey nt <$> i) op (lkKey tj <$> j )
      fty = case jty of
              InnerJoin -> []
              LeftJoin -> [KOptional]
      ty = (Primitive fty (RecordPrim (rawSchema tj ,rawName tj)))
      alterTable (Project r i) = r
                  Le.& rawFKSL Le.%~ (path:)
      alterTable r  = r
                  Le.& rawFKSL Le.%~ (path:)
  modify (
        (tableMapL . Le.ix (tableName nt)   Le.%~  alterTable ))

  return $ alterTable nt

sourceTableM (FromV i) = do
  inf <- get
  return $ lookTable inf i
sourceTableM (WhereV i j) = sourceTableM i
  
instance Show v => Patch (WherePredicateK v) where
  type Index (WherePredicateK v) = WherePredicateK v
  applyUndo (WherePredicate (AndColl i)) (WherePredicate (AndColl j)) = Right $ (WherePredicate (AndColl (i <> j)),WherePredicate (AndColl i))
  applyUndo (WherePredicate (OrColl i)) (WherePredicate (OrColl j)) = Right $ (WherePredicate (OrColl (i <> j)), WherePredicate (OrColl (i )))
  applyUndo i j = Right ( i <> j  , i )
  applyUndo i j = error (show (i,j))
  diff i j = Nothing
  patch i = i 
  

pmap' f fp  (PStream b e ) = PStream (f <$> b) (fp <$> e)

   
pmap f fp  = Kleisli (\(PStream b e )->  lift $ do
  ini <- currentValue b
  accumS (f ini) (filterJust $  fp <$> e))

pmapA :: (KV Key Showable -> TransactionM b) 
      -> PStream (PrimaryRep  Key Showable) 
      -> TransactionM  (Tidings (G.GiST (TBIndex Showable ) b))
pmapA f (PStream b e ) =  mdo
  inf <- askInf
  let fp (PrimaryRep (m ,g)) (RowPatch (k,d)) = 
                (k,) <$> case d of 
                  CreateRow d -> Diff . fromMaybe <$> f d
                  PatchRow p -> (maybe Keep (\i -> Diff $ maybe i (const i) )<$> traverse f  (flip applyIfChange p =<< G.lookup k g))
                  DropRow -> return Delete 
  fre <- lift $ mapEventDyn (transactionNoLog inf) (fp <$> b <@> e )
  PrimaryRep (_,ini) <- currentValue b
  fini <- traverse f  ini
  o <- lift $ accumT fini ((\(k,i) j -> case i of 
                                          Keep -> j 
                                          Diff f -> G.alterWith f  k  j 
                                          Delete -> traceStack ("deleting: " ++ show k ++ show (G.keys j )) $ G.delete  k (8,8) j) <$> fre)
  return o 


pconst  b  = PStream (pure b) never 


pmerge :: (Patch c, Patch a , Patch b) => (a -> b -> TransactionM c ) -> (a -> c -> Index b -> TransactionM (Maybe (Index c))) ->  (b -> c -> Index a -> TransactionM (Maybe (Index c))) -> (PStream a , PStream b) -> TransactionM (PStream c)
pmerge fun fr fl (PStream br er, PStream bl el) = mdo
  inf <- askInf
  fre <- lift $ mapEventDyn (transactionNoLog inf) (fr <$> br <*> psvalue res <@> el )
  fle <- lift $ mapEventDyn (transactionNoLog inf) ( fl <$> bl <*> psvalue res<@> er )
  let ev = filterJust $ unionWith const  fre fle
  bri <- currentValue  br
  bli <- currentValue  bl
  ini <- fun  bri bli 
  res <-  lift $ accumS ini  ev
  return res

instance Patch CorePrim where

instance Compact () where
  compact _  = [()] 

pmapPredicateK ::  Rel Key -> Kleisli TransactionM (PStream InputType , PStream (TableRep Key Showable))   (PStream InputType)
pmapPredicateK cindex 
  = Kleisli (pmerge tconvert  predicate projection  )
  where 
    tconvert (p,i) v = do
      return $ (maybe mempty (mapPredicate (fmap keyValue)) $ fkPredicateIx cindex (G.toList (primary v)) 
                      , kvLookupMeta  cindex i :: KVMeta Key )
    predicate _ _ (RowPatch (i,CreateRow j ))  = do
      return $ (,[] :: [Index (KVMeta Key)] ) . pure . mapPredicate (fmap keyValue)<$> fkPredicateIx (cindex) [j]
    predicate _ _ (RowPatch (i,PatchRow  j ))  = return $ Nothing 
    predicate _ _ (RowPatch (i,DropRow ))  = return Nothing 
    projection _ _ i  = return Nothing -- Just (mempty,i)
 
pmapPredicate :: (View T.Text T.Text) -> Rel T.Text -> Kleisli TransactionM (PStream InputType , PStream (TableRep Key Showable))   (PStream InputType)
pmapPredicate inner cindex 
  = Kleisli (pmerge tconvert  predicate projection  )
  where 
    tconvert (p,i) v = do
      preinf <- askInf 
      let (origin ,inf) = updateTable preinf  inner  
      return $ (fromMaybe p $ fkPredicateIx cindex (mapKey' keyValue <$> G.toList (primary v)) 
                      , kvLookupMeta  (liftRel inf (tableName origin) cindex) i :: KVMeta Key )
    predicate _ _ (RowPatch (i,CreateRow j ))  = do
      inf <- askInf
      return $ (,[] :: [Index (KVMeta Key )]) . pure <$> fkPredicateIx cindex [mapKey' keyValue j]
    predicate _ _ (RowPatch (i,PatchRow  j ))  = return $ Nothing 
    predicate _ _ (RowPatch (i,DropRow ))  = return Nothing 
    projection _ _ i  = return Nothing -- Just (mempty,i)
 
kvLookupMeta i = head . F.toList . join . fmap _fkttable . (justError $ "cannot lookupMeta: " ++ (renderRel i) ) . recLookupKV i
  
innerJoinS
  :: DatabaseM (View T.Text T.Text) (PStream InputType) (PStream  (TableRep Key Showable))
  -> DatabaseM (View T.Text T.Text) (PStream InputType) (PStream  (TableRep Key Showable))
  -> [Rel T.Text]
  -> DatabaseM (View T.Text T.Text)  (PStream InputType)  (PStream  (TableRep Key Showable)) 
innerJoinS (P j k) (P l n) srel =
  P  joinS
    (proc i -> do
      kv <- k -< i
      pred <- pmapPredicate joinS (relComp srel ) -< (i,kv )
      nv <- n -<  pred
      Kleisli (pmerge (\i k -> innerJoin j l srel (primary i, primary k))  (\left last i -> do 
            inf <- askInf 
            let origin = sourceTable inf (JoinV j l InnerJoin srel )
                target = sourceTable inf l
                rel = (\(Rel i o j) -> Rel (lkKey origin <$> i) o (lkKey target <$> j)) <$>  srel
            return $  safeHead   $ joinPatch False rel target id [i] last ) (\_ _ i -> return (Just i)) ) -< (kv ,nv))
    where  
      joinS = JoinV j l InnerJoin srel

mapPatch f (RowPatch (ix,PatchRow i) ) = RowPatch (ix, PatchRow $ f i )

primaryRep (TableRep (m,s,p)) = PrimaryRep (m,p)

innerJoin j l srel (emap,amap) = do
        preinf <- askInf
        let 
          target = sourceTable preinf l
          (origin ,inf) = updateTable preinf j  
        let
          rel = (\(Rel i o j) -> Rel (lkKey origin <$> i) o (lkKey target <$> j)) <$>  srel
          tar = S.fromList $ _relOrigin <$> rel
          joinFK :: TBData Key Showable ->  Either String (Column Key Showable)
          joinFK m  = maybe (Left ("Missing reference: " ++ show taratt)) Right $ FKT mempty rel <$> joinRel2 (tableMeta target) (fmap replaceRel $ taratt ) amap
            where
              replaceRel (Attr k v) = (justError "no rel" $ L.find ((==k) ._relOrigin) rel,v)
              taratt = getAtt tar (tableNonRef m)
          joined i = flip addAttr i <$> joinFK i
          result = (\(i,j,k) -> joined i)<$> G.getEntries emap
        -- when (L.any isLeft result) . liftIO $do
           --putStrLn  $"Missing references: " ++  (L.intercalate "," $ renderRel <$> srel)
           -- print (L.length $ rights result)
           --print ("Target Relation" , G.toList amap)
           --print ("Target Relation" , (rawPK target) , G.getIndex (tableMeta target) <$>G.toList amap)
           -- print (lefts result)
        let idx = (F.foldl' apply (TableRep (tableMeta origin, mempty ,mempty)) (createRow' (tableMeta origin)<$> rights (F.toList result) ) )
        return  idx 

leftJoinS
  :: DatabaseM (View T.Text T.Text) (PStream (InputType)) (PStream  (TableRep Key Showable))
  -> DatabaseM (View T.Text T.Text) (PStream (InputType)) (PStream  (TableRep Key Showable))
  -> [Rel T.Text]
  -> DatabaseM (View T.Text T.Text)  (PStream (InputType))  (PStream  (TableRep Key Showable)) 
leftJoinS (P j k) (P l n) srel 
  = P joinS
    (proc p -> do
      kv <- k -< p
      pred <-  pmapPredicate joinS (relComp srel) -< (p,kv )
      nv <- n -< pred
      Kleisli (pmerge (\i k -> leftJoin joinS (primary i, primary k))  (\left last i -> do 
            inf <- askInf 
            let origin = sourceTable inf joinS 
                target = sourceTable inf l
                rel = (\(Rel i o j) -> Rel (lkKey origin <$> i) o (lkKey target <$> j)) <$>  srel
            return $ safeHead $ joinPatch True rel target id [i] last ) (\_ _ i -> return (Just i)) ) -< (kv ,nv))
  where 
    joinS = JoinV j l LeftJoin srel

leftJoin joinPred@(JoinV j l LeftJoin srel) (emap,amap)= do
        preinf <- askInf
        let
          (origin ,inf) = updateTable preinf  joinPred 
          target = sourceTable preinf l
          rel = (\(Rel i o j ) -> Rel (lkKey origin <$> i ) o (lkKey target <$> j) )<$>  srel
          tar = S.fromList $ _relOrigin <$> rel
          joinFK :: TBData Key Showable ->  Column Key Showable
          joinFK m  = FKT mempty rel (LeftTB1 $ joinRel2 (tableMeta target ) (fmap replaceRel $ taratt ) amap)
            where
              replaceRel (Attr k v) = (justError "no rel" $ L.find ((==k) ._relOrigin) rel,v)
              taratt = getAtt tar (tableNonRef m)
          joined i = addAttr (joinFK i) i
        let result = joined <$> F.toList emap
        let idx = (F.foldl' apply (TableRep (tableMeta origin, mempty ,mempty)) (createRow' (tableMeta origin)<$> result ) )
        return idx


fixLeftJoinS
  :: DatabaseM (View T.Text T.Text) (PStream (InputType)) (PStream (TableRep Key Showable))
  -> DatabaseM (View T.Text T.Text) (PStream (InputType)) (PStream (TableRep Key Showable))
  -> [Rel T.Text]
  -> Rel Key
  -> DatabaseM (View T.Text T.Text) (PStream (InputType)) (PStream (TableRep Key Showable))
fixLeftJoinS (P j k) (P l n) srel index 
  = P  joinS
    (proc p -> do
      preinf <- Kleisli (const askInf ) -< ()
      let (origin ,inf) = updateTable preinf  joinS
          target = sourceTable inf l
          srelc = relComp $ (\(Rel i o j) -> Rel (lkKey origin <$> i) o (lkKey target <$> j)) <$>  srel
      kv <- k -< p
      Kleisli (\(srelc ,p, kv ) -> go (0 ::Int) srelc p kv) -< (srelc , pmap' (\i -> (mempty, snd i)) id p , kv))
    where 
      joinS = JoinV j l LeftJoin srel 
      go ix _ _ _ | ix > 5 = error "max recursion"
      go ix cindex  p kv = do
        preinf <- askInf
        let 
          srelc = relComp $ (\(Rel i o j) -> Rel (lkKey origin <$> i) o (lkKey target <$> j)) <$>  srel
          (origin, inf) = updateTable preinf  joinS
          target = sourceTable inf l
          sindex = fmap keyValue cindex
          consIndex = relAppend index srelc
          unConsIndex (RelAccess i j )= j 
          unConsIndex i = i 
        predS <- runKleisli (pmapPredicateK cindex) (p,kv)
        isEmpty <- lift $ calmT ( fmap ((== mempty).fst) (toTidings predS))

        lift $  joinP =<<  mapTidingsDyn (\empty-> if empty
            then return kv 
            else transactionNoLog preinf $ do  
              liftIO $ print  ("Loading go " ++ show ix)
              out <- (runKleisli n) predS 
              result <- pmerge 
                (\j i ->  do
                  let joined = joinRelation inf joinS cindex (primary i )
                      result = (\ jix ->  createRow' (tableMeta origin) $ apply jix (joined jix )  ) <$> (G.toList (primary j ))
                  --liftIO $ when (tableName  target == "table_description") $ 
                  --  void $ do 
                  --    putStrLn (renderRel cindex)
                  --    mapM (\i -> do
                  --      putStrLn "@@@@================@@@"
                  --      putStrLn . ident . render $ i ) result

                  return $ F.foldl' apply (TableRep (tableMeta origin, mempty ,mempty)) $  result) 
                (\_ last i -> do 
                  return $ safeHead  $ joinPatch True (relUnComp cindex) target id [i] last )
                (\ _ _ i -> return (Just i))  
                (kv ,out)
              go (ix+1) (relAppend cindex consIndex)  p result 
                                         ) isEmpty 

traceShowIdPrefix p f i = trace (p ++ "-" ++ f i) i 

joinRelation
  :: InformationSchema
     -> View T.Text T.Text
     -> Rel Key 
     -> G.GiST (TBIndex Showable) (KV Key Showable)
     -> TBData Key Showable
     -> TBIdx Key  Showable
joinRelation preinf join@(JoinV j l LeftJoin _ ) index amap =  do
    let
      origin = sourceTable preinf join 
      target = sourceTable preinf l
      targetPK = rawPK target
      joinFK :: TBData Key Showable ->  PathAttr Key Showable
      joinFK m  = result
        where
          result = justError ("cant index: "  ++ renderRel index ++  "\n" ++ (ident $ render m) ) (indexRelation  indexTarget index m)
          findRef i v = maybe  Nothing Just $ patch  <$> G.lookup pk  amap
            where targetRel = (L.sortOn (\ i -> L.elemIndex (simplifyRel $ _relTarget i) (fmap simplifyRel targetPK ))  i )
                  pk = G.getUnique targetRel (kvlist v)

          indexTarget rel' v = Just . PFK  rel mempty . POpt $  indexContainer (findRef rel ) (checkLength v rel <$> liftOrigin rel (unkvlist (tableNonRef v)))
            where rel = relUnComp  rel' 
                  checkLength tb rel v 
                    | L.length rel == L.length v = v
                    | otherwise = error $ "missing parameters : " ++ show  (rel,v,index,tb)
      joined i = kvsingleton ( joinFK i)
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
  :: (Text.PrettyRender a,Show k ,Show a,Ord k) 
  => (Rel k -> TBData k a -> Maybe (PathAttr k v)) 
  -> Rel k 
  -> TBData k a 
  -> Maybe (PathAttr k v) 
-- indexRelation i j k | traceShow ("indexRelation",j) False = undefined
indexRelation f (RelAccess (Inline key ) nt) r
 = do 
   let i = justError ("ref error: " <> show key <>  (ident . render $ r)) $ refLookup (Inline key) r
   PInline key . fmap kvsingleton <$> indexContainer (indexRelation f nt) i
indexRelation f n@(RelAccess nk nt )  r
 = do
   let i = justError ("rel error" <> show nk) $ relLookup nk r 
   PFK (relUnComp nk) mempty . fmap kvsingleton <$> indexContainer allRefs i
  where
    allRefs (TBRef (i,v))=  indexRelation f nt v
indexRelation f a  r
  =  f a r

projectS
  :: 
    DatabaseM  (View T.Text T.Text ) (PStream (InputType) ) (PStream (TableRep  Key Showable))
     -> PluginM (Union (G.AttributePath T.Text MutationTy))  (Atom (TBData T.Text Showable))  TransactionM () b
     -> DatabaseM (View T.Text T.Text) () (Tidings (G.GiST (TBIndex Showable) b))
projectS  (P i (Kleisli j))  p@(P (k,_) _ ) = P  projection 
    (proc i -> do 
      set <- (Kleisli $  \_ -> do 
           inp <- projectMeta i k projection
           j (emptyP inp ) ) -< ()
      let setp = pmap' primaryRep id set
      Kleisli (pmapA convertState ) -< setp)
        where
          convertState = evalEnv p . (,mempty). Atom . mapKey' keyValue
          projection = ProjectV i (foldl mult one k)

projectMeta i k  projection  = do
    preinf <- askInf
    let 
        (table,inf) = updateTable preinf i
        fields = projectFields inf table k  predicate $ allFields inf table
        predicate = liftPredicateF lookupKeyName inf  (tableName table) $ predicateTree i 
    return (mempty,fields)


runMetaArrow inf fun = transactionNoLog (meta inf) $ dynPK (fun inf) ()
