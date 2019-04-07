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
import TP.Widgets (calmT)
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
fromS m  = P (FromV m ) (Kleisli (trace "fromtable" . fmap fst <$> fromTableS m ))

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

sourceTableM (JoinV t  j jty rel) = do
  inf <- get 
  tj <- sourceTableM j
  nt <- sourceTableM t
  let path =  FKJoinTable (lkRel <$> rel)  (_rawSchemaL tj ,_rawNameL tj)
      lkRel (Rel i op j ) = Rel (lkKey nt <$> i) op (lkKey tj <$> j )
      fty = case jty of
              InnerJoin -> []
              LeftJoin -> [KOptional]
      ty = (Primitive fty (RecordPrim (_rawSchemaL tj ,_rawNameL tj)))
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
  
instance Patch (WherePredicateK v) where
  type Index (WherePredicateK v) = WherePredicateK v
  applyUndo (WherePredicate (AndColl i)) (WherePredicate (AndColl j)) = Right $ (WherePredicate (AndColl (i <> j)),WherePredicate (AndColl i))
  applyUndo (WherePredicate (OrColl i)) (WherePredicate (OrColl j)) = Right $ (WherePredicate (OrColl (i <> j)), WherePredicate (OrColl (i )))

pmap' f fp  (PStream b e ) = PStream (f <$> b) (fp <$> e)

   
pmap f fp  = Kleisli (\(PStream b e )->  lift $ do
  ini <- currentValue b
  accumS (f ini) (filterJust $ trace "partial pmap".  fp <$> e))

pconst  b  = PStream (pure b) never 


pmerge :: (Patch c, Patch a , Patch b) => (a -> b -> TransactionM c ) -> (a -> c -> Index b -> TransactionM (Maybe (Index c))) ->  (b -> c -> Index a -> TransactionM (Maybe (Index c))) -> (PStream a , PStream b) -> TransactionM (PStream c)
pmerge fun fr fl (PStream br er, PStream bl el) = mdo
  inf <- askInf
  fre <- lift $ mapEventDyn (transactionNoLog inf. trace "pmerge right" ) (fr <$> br <*> psvalue res <@> el )
  fle <- lift $ mapEventDyn (transactionNoLog inf. trace "pmerge left" ) ( fl <$> bl <*> psvalue res<@> er )
  let ev = filterJust $ unionWith const  fre fle
  bri <- currentValue  br
  bli <- currentValue  bl
  ini <- (fun . trace "pmerge total" ) bri bli 
  res <-  lift $ accumS ini  (fmap (trace "PMerge#----------------------------" ) ev)
  return res

  
innerJoinS
  :: DatabaseM (View T.Text T.Text) (PStream (WherePredicateK T.Text)) (PStream  (TableRep Key Showable))
  -> DatabaseM (View T.Text T.Text) (PStream (WherePredicateK T.Text)) (PStream  (TableRep Key Showable))
  -> [Rel T.Text]
  -> DatabaseM (View T.Text T.Text)  (PStream (WherePredicateK T.Text))  (PStream  (TableRep Key Showable)) 
innerJoinS (P j k) (P l n) srel =
  P (JoinV j l InnerJoin srel )
    (proc i -> do
      kv <- k -< i
      pred <- pmapPredicate (relComp srel ) -< kv 
      nv <- n -<  pred
      Kleisli (pmerge (\i k -> innerJoin j l srel (primary i, primary k))  (\left last i -> do 
            inf <- askInf 
            let origin = sourceTable inf (JoinV j l InnerJoin srel )
                target = sourceTable inf l
                rel = (\(Rel i o j) -> Rel (lkKey origin <$> i) o (lkKey target <$> j)) <$>  srel
            return $  safeHead   $ joinPatch False rel target id [i] last ) (\_ _ i -> return (Just i)) ) -< (kv ,nv))

mapPatch f (RowPatch (ix,PatchRow i) ) = RowPatch (ix, PatchRow $ f i )

primaryRep (TableRep (m,s,p)) = PrimaryRep (m,p)

innerJoinR
  :: DatabaseM (View T.Text T.Text) (WherePredicateK T.Text) (G.GiST (TBIndex Showable) (TBData Key Showable))
  -> DatabaseM (View T.Text T.Text) (WherePredicateK T.Text) (G.GiST (TBIndex Showable) (TBData Key Showable))
  -> [Rel T.Text]
  -> DatabaseM (View T.Text T.Text)  (WherePredicateK T.Text)  (G.GiST (TBIndex Showable) (TBData Key Showable))
innerJoinR (P j k) (P l n) srel 
  = P (JoinV j l InnerJoin srel)
    (proc i -> do
      kv <- k -< i
      nv <- n -< maybe i (<> i) $ fkPredicate srel (mapKey' keyValue <$> G.toList kv ) 
      Kleisli (fmap primary <$> innerJoin j l srel )-< (kv,nv))

innerJoin j l srel (emap,amap) = do
        preinf <- askInf
        let 
          (origin ,inf) = updateTable preinf j  
          target = sourceTable preinf l
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
           -- putStrLn  $"Missing references: " ++  (L.intercalate "," $ renderRel <$> srel)
           -- print (L.length $ rights result)
           -- print (G.keys amap)
           -- print (lefts result)
        let idx = (F.foldl' apply (TableRep (tableMeta origin, mempty ,mempty)) (createRow' (tableMeta origin)<$> rights (F.toList result) ) )
        return  idx 

leftJoinS
  :: DatabaseM (View T.Text T.Text) (PStream (WherePredicateK T.Text)) (PStream  (TableRep Key Showable))
  -> DatabaseM (View T.Text T.Text) (PStream (WherePredicateK T.Text)) (PStream  (TableRep Key Showable))
  -> [Rel T.Text]
  -> DatabaseM (View T.Text T.Text)  (PStream (WherePredicateK T.Text))  (PStream  (TableRep Key Showable)) 
leftJoinS (P j k) (P l n) srel 
  = P joinS
    (proc p -> do
      kv <- k -< p
      pred <-  pmapPredicate (relComp srel) -< kv 
      nv <- n -< pred
      Kleisli (pmerge (\i k -> leftJoin joinS (primary i, primary k))  (\left last i -> do 
            inf <- askInf 
            let origin = sourceTable inf joinS 
                target = sourceTable inf l
                rel = (\(Rel i o j) -> Rel (lkKey origin <$> i) o (lkKey target <$> j)) <$>  srel
            return $ safeHead $ joinPatch True rel target id [i] last ) (\_ _ i -> return (Just i)) ) -< (kv ,nv))
    where joinS = JoinV j l LeftJoin srel


leftJoinR
  :: DatabaseM (View T.Text T.Text)  (WherePredicateK T.Text) (G.GiST (TBIndex Showable) (TBData Key Showable))
  -> DatabaseM (View T.Text T.Text)  (WherePredicateK T.Text) (G.GiST (TBIndex Showable) (TBData Key Showable))
  -> [Rel T.Text]
  -> DatabaseM (View T.Text T.Text)  (WherePredicateK T.Text) (G.GiST (TBIndex Showable) (TBData Key Showable))
leftJoinR (P j k) (P l n) srel 
  = P  joinS
    (proc p -> do
      kv <- k -< p
      nv <- n -< maybe p (<> p) $ fkPredicate srel (mapKey' keyValue <$> G.toList kv )
      Kleisli (fmap primary . leftJoin joinS ) -< (kv,nv))
    where joinS = JoinV j l LeftJoin srel

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

joinP t = do
  (e,h) <- newEvent
  init <- currentValue (facts t)
  el <- currentValue (psvalue init)
  (_,ini) <- liftIO $runDynamic $ do 
    onEventDyn  (psevent init) (liftIO. h)

  onChangeDynIni ini (facts t) (\i -> do
    onEventDyn  (psevent i) (liftIO. h)
    ) 
  accumS el e

pmapPredicate cindex 
  = pmap  
    tconvert
    pconvert
  where 
    tconvert v =  fromMaybe mempty $ fkPredicateIx cindex (mapKey' keyValue <$> G.toList (primary v))
    pconvert (RowPatch (i,CreateRow j )) = fkPredicateIx cindex [mapKey' keyValue j]
    pconvert (RowPatch (i,PatchRow  j )) = Nothing 
    pconvert (RowPatch (i,DropRow )) = Nothing 
  

fixLeftJoinS
  :: DatabaseM (View T.Text T.Text) (PStream (WherePredicateK T.Text)) (PStream (TableRep Key Showable))
  -> DatabaseM (View T.Text T.Text) (PStream (WherePredicateK T.Text)) (PStream (TableRep Key Showable))
  -> [Rel T.Text]
  -> Rel Key
  -> DatabaseM (View T.Text T.Text) (PStream (WherePredicateK  T.Text)) (PStream (TableRep Key Showable))
fixLeftJoinS (P j k) (P l n) srel index 
  = P  joinS
    (proc p -> do
      preinf <- Kleisli (const askInf ) -< ()
      let (origin ,inf) = updateTable preinf  joinS
          target = sourceTable inf l
          srelc = relComp $ (\(Rel i o j) -> Rel (lkKey origin <$> i) o (lkKey target <$> j)) <$>  srel
      kv <- k -< p
      Kleisli (\(srelc ,kv ) -> go (0 ::Int) srelc kv) -< (srelc , kv))
    where 
      joinS = JoinV j l LeftJoin srel 
      go ix _ _ | ix > 5 = error "max recursion"
      go ix cindex  kv = do
        preinf <- askInf
        let 
          srelc = relComp $ (\(Rel i o j) -> Rel (lkKey origin <$> i) o (lkKey target <$> j)) <$>  srel
          (origin, inf) = updateTable preinf  joinS
          target = sourceTable inf l
          sindex = fmap keyValue cindex
          consIndex = relAppend index srelc
          -- predS :: PStream (WherePredicateK T.Text)
        predS <- runKleisli (pmapPredicate sindex) kv
        isEmpty <- lift $ calmT ( fmap (== mempty) (toTidings predS))

        lift $  joinP =<<  mapTidingsDyn (\empty-> if empty
            then return kv 
            else transactionNoLog preinf $ do  
              liftIO $ print  ("Loading go " ++ show ix)
              out <- (runKleisli n) predS 
              result <- pmerge 
                (\j i ->  do
                  let joined = joinRelation inf joinS sindex (primary i )
                  return $ F.foldl' apply (TableRep (tableMeta origin, mempty ,mempty)) $ 
                      (\ jix ->  createRow' (tableMeta origin) $ apply jix (joined jix )  ) <$> (G.toList (primary j ))) 
                (\_ last i -> do 
                  inf <- askInf 
                  let origin = sourceTable inf joinS 
                      target = sourceTable inf l
                  return $ safeHead . traceShowIdPrefix ("right fix: " ++ renderRel cindex ) (L.intercalate "\n\n" . fmap (ident . render . snd . unRowPatch ) ) $ joinPatch True (relUnComp cindex) target id [i] last )
                (\ _ _ i -> return (Just i))  
                (kv ,out)
              go (ix+1) (relAppend cindex consIndex)   result 
                                         ) isEmpty 

traceShowIdPrefix p f i = trace (p ++ "-" ++ f i) i 

fixLeftJoinR 
  :: DatabaseM (View T.Text T.Text) (WherePredicateK T.Text) (G.GiST (TBIndex Showable) (TBData Key Showable))
  -> DatabaseM (View T.Text T.Text) (WherePredicateK T.Text) (G.GiST (TBIndex Showable) (TBData Key Showable))
  -> [Rel T.Text]
  -> Maybe (Rel T.Text)
  -> DatabaseM (View T.Text T.Text) (WherePredicateK  T.Text)(G.GiST (TBIndex Showable) (TBData Key Showable))
fixLeftJoinR (P j k) (P l n) srel index 
  = P  join 
    (proc p -> do
      kv <- k -< p
      Kleisli (go srelc  (0 ::Int)) -< kv)
    where 
      srelc = relComp srel
      join = JoinV j l LeftJoin srel 
      go _  ix _ | ix > 5 = error "max recursion"
      go cindex ix  kv = do
          -- liftIO $ print ("Fix Left Index",ix,cindex)
          let predM = fkPredicateIx cindex (mapKey' keyValue <$> G.toList kv )
          case predM of 
            Nothing -> do
              -- liftIO $ do
                -- putStrLn $  "## Fix Last " <> show l <> renderRel cindex <> show ix <> " " <> show (G.keys kv)  
                -- mapM (putStrLn. ident .renderTable) (mapKey' keyValue <$> G.toList kv )
              return kv 
            Just pred -> do  
              preinf <- askInf 
              let (origin ,inf) = updateTable preinf  join 
              -- liftIO $ putStrLn $  "## Fix Start " <> show ix <> " " <> show l <> renderPredicateWhere pred
              out <- (runKleisli n) pred 
              -- liftIO $  putStrLn $  "## Fix End " <> show ix <> " " <> show l <> renderRel cindex <> " " <> show (G.keys out) 
              let joined = joinRelation inf join cindex out
                  consIndex = maybe srelc (flip relAppend srelc) index
              go (relAppend cindex  consIndex) (ix+1) ((\i -> apply i (joined i)) <$> kv) 

joinRelation preinf join@(JoinV j l LeftJoin srel ) index amap =  do
    let
      origin = sourceTable preinf join 
      target = sourceTable preinf l
      targetPK = fmap keyValue <$> rawPK target
      joinFK :: TBData Key Showable ->  PathAttr T.Text Showable
      joinFK m  = result
        where
          result = justError ("cant index: "  ++ show  (srel , m) ) (indexRelation  indexTarget index (mapKey' keyValue m))
          findRef i v = maybe  Nothing Just $ patch . mapKey' keyValue <$> G.lookup pk  amap
            where targetRel = (L.sortOn (\ i -> L.elemIndex (simplifyRel $ _relTarget i) (fmap simplifyRel targetPK ))  i )
                  pk = G.getUnique targetRel (kvlist v)

          indexTarget rel' v = Just . PFK  rel []. POpt $  indexContainer (findRef rel ) (checkLength v rel <$> liftOrigin rel (unkvlist (tableNonRef v)))
            where rel = relUnComp  rel' 
                  checkLength tb rel v 
                    | L.length rel == L.length v = v
                    | otherwise = error $ "missing parameters : " ++ show  (rel,v,index,tb)
      joined i = [liftPatchAttr preinf (tableName origin) $ joinFK i]
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
projectS  (P i (Kleisli j))  p@(P (k,_) _ ) = P (ProjectV i (foldl mult one k)) (Kleisli $  \_ -> (j empty )  >>= mapArrow . fmap primary . toTidings  . pmap' id ( traceShowIdPrefix "project : "(ident . render)) )
        where empty = PStream (pure mempty) never
              execute a = traverse (evalEnv p . (,mempty) . Atom .
                {- traceShowIdPrefix "project : "(ident . renderTable) . -}  mapKey' keyValue) a
              mapArrow a = do
                  inf <- ask 
                  lift $ mapTidingsDyn  (transactionNoLog (fst inf) . execute) a 



projectV
  :: (Show k , Traversable t2) =>
    DatabaseM  (View i k) (WherePredicateK T.Text ) (t2 (KV Key c))
     -> PluginM (Union (G.AttributePath k MutationTy))  (Atom ((TBData T.Text c)))  TransactionM () b
     -> DatabaseM (View i k) () (t2 b)
projectV  (P i (Kleisli j))  p@(P (k,_) _ ) = P (ProjectV i (foldl mult one k)) (Kleisli $  \_ -> (j mempty)  >>=  
      (\a -> traverse (evalEnv p . (,mempty) . Atom .  mapKey' keyValue) a))

runMetaArrow inf fun = transactionNoLog (meta inf) $ dynPK (fun inf) ()

runMetaArrowS inf fun = transactionNoLog (meta inf) $ dynPK (fun inf) ()

