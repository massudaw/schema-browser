{-# LANGUAGE RecordWildCards, Arrows, RankNTypes, RecursiveDo,
  TypeFamilies, FlexibleContexts, OverloadedStrings, TupleSections
  #-}
module SchemaQuery.Store
  (
  -- Clear in memory cache
    resetCache
  -- Read current state
  , dynFork
  , readIndex
  , readState
  , joinPatch
  , cloneDBVar
  -- Get table pointer 
  , prerefTable
  , lookDBVar
  -- Transaction Operations
  , transactionNoLog
  , transaction
  -- Create table
  , createTable
  , logTable
  -- Log changes to current monad
  , fetchPatches 
  , tellPatches
  , asyncPatches 
  , newDBRef
  ) where

import Control.Concurrent
import Debug.Trace
import Control.Concurrent.STM
import Control.DeepSeq
import Data.Time
import Control.Monad.Catch
import Control.Monad.RWS
import qualified Data.Foldable as F
import qualified Data.HashMap.Strict as HM
import qualified Data.Interval as Interval
import qualified Data.List as L
import qualified Data.Map as M
import Data.Maybe
import Text
import qualified Data.Text as T
import Reactive.Threepenny hiding (apply)
import RuntimeTypes
import Safe
import Step.Common
import Types
import qualified Types.Index as G
import Types.Patch
import Utils

lookDBVar :: InformationSchema -> M.Map (KVMetadata Key) (DBRef Key Showable) -> KVMetadata Key -> IO (DBRef Key Showable)
lookDBVar inf mmap table =
    case M.lookup table mmap of
      Nothing ->  fmap fst $ runDynamic $  do
        snd <$> createTableRefs inf (lookTable inf (_kvname table))
      Just i-> return i

resetCache :: InformationSchema -> IO ()
resetCache inf = atomically $ modifyTVar (mvarMap inf) (const M.empty)

readIndex
  :: (Show k,Ord k,Show v)
  => DBRef k v
  -> STM
  (IndexMetadata  k v ,
     TChan (IndexMetadataPatch k v ))
readIndex dbvar = do
  ini <- readTVar (idxVar dbvar)
  nchan <- cloneTChan (idxChan dbvar)
  patches <- tryTakeMany nchan
  return (justError "no apply readIndex" $ applyIfChange ini patches,nchan)

readState
  :: (Show k ,Ord k ,NFData k)
      => (TBPredicate k Showable, [Rel k])
      -> DBRef k Showable
      -> STM (TableRep k Showable , TChan [TableModificationU k Showable])
readState fixed dbvar = do
  rep <-readTVar (collectionState dbvar)
  chan <- cloneTChan (patchVar dbvar)
  patches <- tryTakeMany chan
  let
    TableRep (m,s,v) = either (error "no apply readState") fst $ foldUndo rep filterPred
    filterPred = {-filter (checkPatch  fixed) -} (fmap tableDiff $ concat patches)
    fv =  filterfixedS (dbRefTable dbvar) (fst fixed) (s,v)
  return (TableRep (m,s,fv),chan)

cloneDBVar
  :: (NFData k ,Show k,Ord k)
  => (WherePredicateK k,[Rel k])
  -> DBRef k Showable
  -> STM ((IndexMetadata k Showable, TableRep k Showable), DBRef k Showable)
cloneDBVar pred dbvar@DBRef{..} = do
  ix <- readTVar refSize
  (i,idxchan) <- readIndex dbvar
  (s,statechan) <- readState pred dbvar
  let clonedVar = DBRef dbRefTable  (ix+1) refSize statechan idxVar idxchan collectionState [] dblogger
  return $ ((i,s),clonedVar)


transactionNoLog :: InformationSchema -> TransactionM a -> Dynamic a
transactionNoLog inf log = do
  (md,s,_)  <- runRWST log (inf ,[]) M.empty
  let aggr = s
  liftIO $ atomically $ traverse (\(k,(ref,v,ix)) -> do
    when (not $ L.null ix) . void $
      mapM (putIdxSTM (idxChan ref)) ix
    when (not $ L.null v) . void $
      putPatchSTM (patchVar ref) v
    ) (M.toList aggr)
  return md

withDynamic :: (forall b . IO b -> IO b) -> Dynamic a -> Dynamic a
withDynamic  f i =  do
  (v,e) <- liftIO . f $ (runDynamic i) `catch` (\e -> putStrLn ("Transaction Exception: "  ++ show (e  :: SomeException)) >> throwM e )
  mapM registerDynamic e
  return v

transaction :: InformationSchema -> TransactionM a -> Dynamic a
transaction inf log = withDynamic ((transactionEd $ schemaOps inf) inf ) $ transactionNoLog inf log


prerefTable :: InformationSchema -> Table -> IO (DBRef Key Showable)
prerefTable  inf table  = liftIO $ do
  mmap <- readTVarIO (mvarMap inf)
  lookDBVar inf mmap (tableMeta table)


mergeDBRef  (IndexMetadata j,i) (IndexMetadata m,l) = (IndexMetadata $ M.unionWith (\(a,b) (c,d) -> (a+c,M.unionWith mergeToken b d))  j  m , i <>  l )

mergeToken (pi,TableRef i)  (pj,TableRef j) = (pi <> pj,TableRef $ Interval.hull i  j)

type TableChannels k v =  (TChan (IndexMetadataPatch k v), TChan [TableModificationU k v])


-- TODO : Remove recjoin hack and add state to ignore recursive inline tables without foreign keys
--  What should be the behaviour for recursive inline tables with foreign keys? .
--  Maybe this should be solved by the where predicate with some CTE like query, that returns recursive traces

childrenRefsUnique
  :: Table
  -> InformationSchema
  -> (Rel Key -> Rel Key)
  -> SqlOperation
  -> [((InformationSchema,Table),[RowPatch Key Showable] -> TableRep  Key Showable  -> [RowPatch Key Showable])]
childrenRefsUnique  source inf pre (RecJoin i j@(FKJoinTable _ _) ) = childrenRefsUnique source inf pre j
childrenRefsUnique  source _  _    (RecJoin _ _ ) = []
childrenRefsUnique  source _  _    (FunctionField _ _ _ ) = []
childrenRefsUnique  source inf pre (FKInlineTable rel target) = concat $ childrenRefsUnique targetTable inf (pre .RelAccess (Inline rel) ) <$> fks
  where
    fks = rawFKS targetTable
    rinf = maybe inf id $ HM.lookup (fst target)  (depschema inf)
    targetTable = lookTable rinf $ snd target
childrenRefsUnique  source inf pre (FKJoinTable rel target)  =  [((rinf,targetTable),joinPatch False rel targetTable pre )]
  where
    rinf = maybe inf id $ HM.lookup (fst target)  (depschema inf)
    targetTable = lookTable rinf $ snd target

joinPatch
  :: (Functor t, Foldable t) =>
     Bool 
     -> [Rel Key]
     -> TableK Key
     -> (Rel Key -> Rel Key)
     -> t (RowPatch Key Showable)
     -> TableRep Key Showable
     -> [RowPatch Key Showable]
joinPatch isLeft rel targetTable prefix evs (TableRep (m,sidxs,base)) =
   let
    sidx = M.lookup rel sidxs
    pkTable = rawPK targetTable
    search idxM (BatchPatch ls op) = concat $ (\i -> search idxM (RowPatch (i ,op)) ) <$> ls
    search idxM (RowPatch p@(Idex v,PatchRow pattr))
      = case idxM of
          Just idx -> concat $ convertPatch <$> resIndex idx
          Nothing -> concat $ convertPatch <$> resScan base
      where
        pkIndex t = justError "no ref" $ do
            idx <- simplifyRel t `L.elemIndex` (simplifyRel <$> pkTable)
            field <- atMay v idx
            unSOptional (create <$> field)
        outputs = rel -- filter (isJust . _relOutputs ) rel
        predIndex = -- (\i -> traceShow (tableName source ,"index",isJust idxM,rel ,i)i ) $
          WherePredicate . AndColl $ ((\(Rel o op t) -> PrimColl (prefix o, [(o,Left (pkIndex t ,Flip op))])) <$> outputs)
        predScanOut = -- (\i -> traceShow (tableName source ,"scan",isJust idxM,rel ,i)i ) $
          WherePredicate  (go prefix (relComp outputs )) -- AndColl $ ((\(Rel o op t) -> PrimColl (prefix (RelAccess (relComp rel) o) ,  [(o,Left (pkIndex t ,Flip op))] )) <$> outputs)
        -- TODO: Is the logic for inputs only necessary  for functions?
        -- inputsOnly = filter (\i -> isJust (_relInputs i) && isNothing (_relOutputs i)) rel
        -- predScanIn = -- (\i -> traceShow (tableName source ,"scan",isJust idxM,rel ,i)i ) $
          -- WherePredicate . AndColl $ ((\(Rel o op t) -> PrimColl (prefix o ,  [(o,Left (pkIndex t ,Flip op))])) <$> inputsOnly )
            where go p (RelComposite output ) = AndColl (go p <$> output)
                  go p (Rel o op t) = PrimColl (p  o ,  [(o,Left (pkIndex t ,Flip op))] )
                  go p a@(RelAccess i j ) = go (\v -> p (RelAccess i v ) ) j 


        resIndex idx = -- traceShow ("resIndex",predIndex ) $
          concat . fmap (\(p,_,i) -> M.toList p) $ G.projectIndex rel predIndex idx
        resScan idx =  -- traceShow ("resScan", predScanOut) $ 
          catMaybes $  (\i->  traceShow ( renderPredicateWhere predScanOut )  $ (G.getIndex m i,) <$>     G.checkPredId i predScanOut)  <$> {-G.filterRows predScanIn -}(G.toList idx)
        convertPatch (pk,ts) = (\t -> RowPatch (pk ,PatchRow  [joinPathRelation isLeft rel t pattr]) ). traceShowId <$> ts
    search idxM (RowPatch (Idex v, CreateRow _ )) = [] 
    search idxM (RowPatch (Idex v, DropRow )) = [] 
        
    result = search sidx <$>  evs
   in  concat result

relLast (RelAccess _ i  ) = relLast i 
relLast i = i

joinPathFTB :: G.PathIndex PathTID a -> (a -> b) -> PathFTB b
joinPathFTB i p =  go i
  where
    go (G.ManyPath j) = justError "empty" .  patchSet .F.toList $ go <$> j
    go (G.NestedPath i j) = matcher i (go j)
      where
        matcher (PIdIdx ix )  = PIdx ix . Just
        matcher PIdOpt   = POpt . Just
    go (G.TipPath j) = PAtom (p j)

joinPathRelation :: Show a => Bool -> [Rel Key] -> G.AttributePath Key () -> TBIdx Key a -> PathAttr Key a
joinPathRelation isLeft prel (G.PathForeign rel i) p 
  | prel == rel =
      PFK prel [] (joinPathFTB i (const p)) 
  | otherwise   = 
      PFK rel  [] (joinPathFTB i nested)
  where
    nested  (Many i) =  flip (joinPathRelation isLeft prel) p <$> i
joinPathRelation isLeft rel (G.PathInline r i) p = PInline r (joinPathFTB i  nested)
  where
    nested  (Many i) =  flip (joinPathRelation isLeft rel) p <$> i
joinPathRelation isLeft rel (G.PathAttr i v) p   = PFK (relUnComp $ relLast (relComp rel)) [] ((if isLeft && not (isLeftTB1 v) then (POpt . Just) else id) $ joinPathFTB v (const p))
  where isLeftTB1 (G.NestedPath PIdOpt _ ) = True
        isLeftTB1 _ = False


dynFork a = do
  i <- liftIO $  forkIO a
  registerDynamic  ( killThread i )
  return i 


tryTakeMany :: TChan a -> STM [a]
tryTakeMany mvar = maybe (return[]) (go . (:[])) =<< tryReadTChan mvar
  where
    go v = do
      i <- tryReadTChan mvar
      maybe (return (reverse v )) (go . (:v)) i

takeMany :: TChan a -> STM [a]
takeMany mvar = go . (:[]) =<< readTChan mvar
  where
    go v = do
      i <- tryReadTChan mvar
      maybe (return (reverse v )) (go . (:v)) i


readCollectionSTM ref = do
   idx <- readTVar (idxVar ref )
   TableRep (_,_,st) <- readTVar (collectionState ref)
   return (( idx,  st) ,ref)

eventChan ini = do
  v <- newTVar  ini
  c <- newBroadcastTChan 
  nc <- dupTChan c
  return (v,nc)

newDBRef inf table (iv,v)= do
    let
      sidx :: M.Map [Rel Key] (SecondaryIndex Key Showable)
      sidx = M.fromList $ fmap (\un-> (un ,G.fromList' ( fmap (\(i,n,j) -> (uncurry M.singleton (G.getUnique un i,[]),n,j)) $ G.getEntries v))) (L.delete (rawPK table) $ _kvuniques (tableMeta table ))
    mdiff <-  liftIO$ atomically $ newBroadcastTChan
    chanidx <-  liftIO$ atomically $ newBroadcastTChan
    nchanidx <- liftIO$ atomically $ dupTChan chanidx
    nmdiff <- liftIO$ atomically $ dupTChan mdiff
    midx <-  liftIO$ atomically$ newTVar iv
    dblogger <-  liftIO$ atomically$ eventChan []
    refSize <- liftIO $ atomically $  newTVar 1
    collectionState <-  liftIO$ atomically $ newTVar  (TableRep (tableMeta table,sidx,v))
    let dbref = DBRef table 0 refSize nmdiff midx nchanidx collectionState [] dblogger
    liftIO$ atomically $ modifyTVar (mvarMap inf) (M.insert (tableMeta table ) dbref)
    return dbref

logTable :: InformationSchema -> KVMetadata Key -> String -> IO ()
logTable inf t s = do 
  mmap <- readTVarIO (mvarMap inf)
  ref <- lookDBVar inf mmap t 
  t <- getCurrentTime 
  atomically $ writeTChan (snd (dblogger ref)) (show t <> " : " <> s )

createTableRefs :: InformationSchema -> Table -> Dynamic (Collection Key Showable,DBRef Key Showable)
createTableRefs inf (Project table (Union l)) = do
  map <- liftIO$ atomically $ readTVar (mvarMap inf)
  case  M.lookup (tableMeta table) map of
    Just ref  ->  do
      liftIO$ putStrLn $ "Loading Cached Union Table: " ++ T.unpack (rawName table)
      liftIO $ atomically $ readCollectionSTM ref
    Nothing -> do
      liftIO$ putStrLn $ "Loading New Union Table: " ++ T.unpack (rawName table)
      let keyRel t k = do
            let look i = HM.lookup (tableName i , keyValue k) (keyMap inf)
            new <- look table
            old <- look t
            return (old,new)
          tableRel t = M.fromList $ catMaybes $ keyRel t <$> rawAttrs t
      res <- mapM (\t -> do
        ((IndexMetadata idx,sdata),ref) <- createTableRefs inf t
        return ((IndexMetadata $ M.mapKeys (mapPredicate (fmap (\k -> fromMaybe k (M.lookup k (tableRel t))))) $ idx, mapKey' (\k -> fromMaybe k (M.lookup k (tableRel t))) <$> G.toList sdata),ref)) l
      let
        (uidx,udata) = foldr mergeDBRef (IndexMetadata M.empty,[]) (fst <$> res)
        udata2 = createUn (tableMeta table) (rawPK table) udata

      dbref <- newDBRef inf table (uidx,udata2)
      return ((uidx,udata2) ,dbref)
createTableRefs inf table = do
  map <- liftIO$ atomically $ readTVar (mvarMap inf)
  case  M.lookup (tableMeta table) map of
    Just ref -> do
      liftIO$ putStrLn $ "Loading Cached Table: " ++ T.unpack (rawName table)
      liftIO $ atomically $ readCollectionSTM ref
    Nothing -> do
      liftIO$ putStrLn $ "Loading New Table: " ++ T.unpack (rawName table)
      let (iv,v)  = (IndexMetadata M.empty,G.empty)
      map2 <- liftIO$ atomically $ readTVar (mvarMap inf)
      case M.lookup (tableMeta table) map2 of
        Just ref ->  do
          liftIO$ putStrLn $ "Skiping Reference Table: " ++ T.unpack (rawName table)
          liftIO $ atomically $ readCollectionSTM ref
        Nothing -> do
          dbref@(DBRef {..}) <- newDBRef inf table (iv,v)
          tilog <- dynFork $ forever $ logChanges dblogger 
          tidix <- dynFork $ forever $ updateIndex dbref
          tidst <- dynFork $ forever $ updateTable inf dbref
          let
            -- Collect all nested references and add one per relation avoided duplicated refs
            childrens = M.fromListWith mappend $ fmap (fmap (\i -> [i])) $  concat $ fmap (childrenRefsUnique table inf id  . unRecRel ) (rawFKS table)
          -- TODO : Add evaluator for functions What to do when one of the function deps change?
          nestedFKS <- mapM (\((rinf, t),l) -> do
            liftIO $ putStrLn $ "Load table reference: from " <> (T.unpack $ tableName table) <> " to "  <> (T.unpack $ tableName t)
            o <- liftIO $ prerefTable rinf t
            return (l,o)) (M.toList childrens)
          newNestedFKS <- liftIO . atomically$ traverse (traverse (\DBRef {..}-> cloneTChan  patchVar)) nestedFKS
          tidsrefs <- mapM (\(j,var)-> dynFork $ forever $ updateReference j var dbref) newNestedFKS
          return ((iv,v),dbref {threadIds = tilog:tidix:tidst:tidsrefs})

logChanges :: TEvent String ->  IO ()
logChanges  (e,c) = 
    atomically $ do
       m <- takeMany c
       i <- readTVar e 
       writeTVar e (m ++ i)


updateReference ::
     (v ~ Index v, PatchConstr k1 v, Foldable t, Functor t)
  => t ([RowPatch k1 v] -> TableRep k1 v -> [RowPatch k1 v])
  -> TChan [TableModificationK (TableK k1) (RowPatch k1 v)]
  -> DBRef k1 v
  -> IO ()
updateReference j var (DBRef {..}) = do
  let label = "Update Reference: " ++ T.unpack (tableName dbRefTable )
  putStrLn label
  catchJust
    notException
    (atomically
       (do let isPatch (RowPatch (_, PatchRow _)) = True
               isPatch (BatchPatch i (PatchRow _)) = True
               isPatch _ = False
           ls <- filter isPatch . concat . fmap tableDiffs . concat <$> takeMany var
           when (not $ L.null ls) $ do
             state <- readTVar collectionState
             let patches = compact . concat $ (\f -> f ls state) <$> j
             when (not $ L.null patches) $
               writeTChan patchVar (FetchData dbRefTable <$> patches)))
    (\e -> atomically (readTChan var) >>= printException e)

tableDiffs (BatchedAsyncTableModification _ i) = concat $ tableDiffs <$> i
tableDiffs i = [tableDiff i]

updateIndex :: (Ord k, Show k, Show v) => DBRef k v -> IO ()
updateIndex (DBRef {..}) = do
  putStrLn ("Update Index: " ++ T.unpack (tableName dbRefTable ) )
  catchJust
    notException
    (do atomically
          (do ls <- takeMany idxChan
              modifyTVar' idxVar (\s -> apply s ls)))
    (\e -> atomically (readTChan idxChan) >>= printException e)

printException :: Show a => SomeException -> a -> IO ()
printException e d = do
  putStrLn $ "Failed applying patch: " <> show d
  putStrLn   "================================="
  putStrLn $ show (e :: SomeException)

updateTable
  :: InformationSchema -> DBRef Key Showable -> IO ()
updateTable inf (DBRef {..})
  = do
  putStrLn ("Update Table : " ++ T.unpack (tableName dbRefTable ))
  catchJust notException (do
    upa <- atomically $ do
        patches <- fmap concat $ takeMany patchVar
        e <- readTVar collectionState
        let cpatches = compact patches
        let out = foldUndo e (concat $ tableDiffs <$> cpatches)
        traverse (\v -> writeTVar collectionState . fst$  v) out
        return  $ zip cpatches . snd <$> out
    either (putStrLn  .("### Error applying: " ++ ) . show ) (
      mapM_ (\(m,u) -> do
        mmod2 <- case m of
          BatchedAsyncTableModification t l -> do
            let m = tableMeta t
            closeDynamic . transactionNoLog inf $ do
              ed <- (batchedEd $ schemaOps inf) m (tableDiff <$> l )
              BatchedAsyncTableModification t <$> mapM (wrapModification m) ed
          AsyncTableModification  t (RowPatch (pk,PatchRow p))  ->  do
            let m = tableMeta t
            closeDynamic . transactionNoLog inf $ do
              l <- (patchEd $ schemaOps inf) m  [pk] p
              wrapModification m l

          AsyncTableModification  t (BatchPatch pk (PatchRow p))  ->  do
            let m = tableMeta t
            closeDynamic . transactionNoLog inf $ do
              l <- (patchEd $ schemaOps inf) m  pk p
              wrapModification m l
          i -> return i
        val <- logger (schemaOps inf) inf mmod2
        undo (schemaOps inf) inf (RevertModification val  u) )
      ) upa `catchAll` (\e -> putStrLn $ "Failed logging modification"  ++ show (e :: SomeException))
    return ())  (\e -> atomically ( readTChan patchVar ) >>= printException e )


createTable fixed m = do
  inf <- askInf
  let mvar = mvarMap inf
  mmap <- liftIO . atomically $ readTVar mvar
  map <-get
  predbvar <- liftIO (lookDBVar inf mmap m)
  ((fixedmap,table),dbvar)
      <- liftIO . atomically $
        cloneDBVar  (fixed ,_kvpk m) predbvar
  (log ,logix)<-case M.lookup m map of
    Just (_,i,l) -> return $ (concat $ tableDiffs <$> i,l)
    Nothing -> do
      modify (M.insert m (dbvar,[],[]))
      return ([],[])
  return ((either error fst $ applyUndo fixedmap logix,either error fst $ foldUndo table log ),dbvar)



modifyTable :: KVMetadata Key ->  [IndexMetadataPatch Key Showable] -> [TableModification (RowPatch Key Showable)] -> TransactionM ()
modifyTable t ix p = do
  inf <- askInf
  m <- get
  o <- case M.lookup t m of
    Just (ref,po,ixp) -> return $ M.insert t (ref,p ++ po,ix ++ ixp ) m
    Nothing -> do
      mmap <- liftIO$ atomically $ readTVar (mvarMap inf)
      ref <- liftIO $ lookDBVar inf mmap t
      return $ M.singleton t (ref,p,ix)
  put o


fetchModification m a = do
  inf <- askInf
  now <- liftIO getCurrentTime
  FetchData (lookTable inf (_kvname m) )<$>  return (force a)

wrapModification m a = do
  inf <- askInf
  now <- liftIO getCurrentTime
  TableModification Nothing now (username inf) (lookTable inf (_kvname m) )<$>  return (force a)

asyncModification m a = do
  inf <- askInf
  now <- liftIO getCurrentTime
  AsyncTableModification  (lookTable inf (_kvname m) )<$>  return a

fetchPatches ::  KVMetadata Key ->  [IndexMetadataPatch Key Showable] -> [RowPatch Key Showable] -> TransactionM ()
fetchPatches m ix i =
  modifyTable m ix =<< mapM (fetchModification m) i

asyncPatches :: KVMetadata Key ->  [RowPatch Key Showable] -> TransactionM ()
asyncPatches m i =
  modifyTable m [] =<< mapM (asyncModification m) i

tellPatches :: KVMetadata Key ->  [RowPatch Key Showable] -> TransactionM ()
tellPatches m i =
  modifyTable m [] =<< mapM (wrapModification m ) i


