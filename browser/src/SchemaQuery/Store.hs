{-# LANGUAGE RecordWildCards, Arrows, RankNTypes, RecursiveDo,
  TypeFamilies, FlexibleContexts, OverloadedStrings, TupleSections
  #-}
module SchemaQuery.Store
  (
  -- Clear in memory cache
    resetCache
  , cloneDBVar
  -- , readIndex
  -- , readState
  -- Flush to disk in memory DB
  -- Pointer Only
  , prerefTable
  , lookDBVar
  -- Transaction Operations
  , transactionNoLog
  ) where

import Control.Concurrent
import Control.Concurrent.STM
import Control.DeepSeq
import Control.Monad.Catch
import Control.Monad.RWS
import qualified Data.Foldable as F
import qualified Data.HashMap.Strict as HM
import qualified Data.Interval as Interval
import qualified Data.List as L
import qualified Data.Map as M
import Data.Maybe
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
      Nothing ->  do
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
      => (TBPredicate k Showable, [k])
      -> DBRef k Showable
      -> STM (TableRep k Showable , TChan [TableModificationU k Showable])
readState fixed dbvar = do
  TableRep (m,s,v) <-readTVar (collectionState dbvar)
  chan <- cloneTChan (patchVar dbvar)
  patches <- tryTakeMany chan
  let
    filterPred = filter (checkPatch  fixed)
    fv = filterfixedS (dbRefTable dbvar) (fst fixed) (s,v)
    result=either (error "no apply readState") fst $ foldUndo (TableRep (m,s,fv)) (filterPred  $ fmap tableDiff $ concat patches)
  return (result,chan)

cloneDBVar
  :: (NFData k ,Show k,Ord k)
  => (WherePredicateK k,[k])
  -> DBRef k Showable
  -> STM ((IndexMetadata k Showable, TableRep k Showable), DBRef k Showable)
cloneDBVar pred dbvar@DBRef{..} = do
  ix <- readTVar refSize
  (i,idxchan) <- readIndex dbvar
  (s,statechan) <- readState pred dbvar
  let clonedVar = DBRef dbRefTable  (ix+1) refSize statechan idxVar idxchan collectionState []
  return $ ((i,s),clonedVar)


transactionNoLog :: InformationSchema -> TransactionM a -> Dynamic a
transactionNoLog inf log = do
  (md,s,_)  <- runRWST log (inf ,[]) M.empty
  let aggr = s
  liftIO $ atomically $ traverse (\(k,(ref,v,ix)) -> do
    mapM (putIdxSTM (idxChan ref)) ix
    putPatchSTM (patchVar ref) v
    ) (M.toList aggr)
  return md

prerefTable :: InformationSchema -> Table -> IO (DBRef Key Showable)
prerefTable  inf table  = do
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
childrenRefsUnique  source inf pre (FKInlineTable rel target) = concat $ childrenRefsUnique targetTable inf (pre .RelAccess [Inline rel] ) <$> fks
  where
    fks = rawFKS targetTable
    rinf = maybe inf id $ HM.lookup (fst target)  (depschema inf)
    targetTable = lookTable rinf $ snd target
childrenRefsUnique  source inf pre (FKJoinTable rel target)  =  [((rinf,targetTable),(\evs (TableRep (m,sidxs,base)) ->
   let
    sidx = M.lookup (_relOrigin <$> rel) sidxs
    search idxM (BatchPatch ls op) = concat $ (\i -> search idxM (RowPatch (i ,op)) ) <$> ls
    search idxM (RowPatch p@(G.Idex v,PatchRow pattr))
      = case idxM of
          Just idx -> concat $ convertPatch <$> resIndex idx
          Nothing -> concat $ convertPatch <$> resScan base
      where
        pkIndex t = justError "no ref" $ do
            idx <- t `L.elemIndex` pkTable
            field <- atMay v idx
            unSOptional (create <$> field)
        outputs = filter (isJust . _relOutputs ) rel
        inputsOnly = filter (\i -> isJust (_relInputs i) && isNothing (_relOutputs i)) rel
        predK = -- (\i -> traceShow (tableName source ,"index",isJust idxM,rel ,i)i ) $
          WherePredicate . AndColl $ ((\(Rel o op t) -> PrimColl (pre o, [(_relOrigin o,Left (pkIndex t ,Flip op))])) <$> outputs)
        predScanOut = -- (\i -> traceShow (tableName source ,"scan",isJust idxM,rel ,i)i ) $
          WherePredicate . AndColl $ ((\(Rel o op t) -> PrimColl (pre (RelAccess rel o) ,  [(_relOrigin o,Left (pkIndex t ,Flip op))] )) <$> outputs)
        predScanIn = -- (\i -> traceShow (tableName source ,"scan",isJust idxM,rel ,i)i ) $
          WherePredicate . AndColl $ ((\(Rel o op t) -> PrimColl (pre o ,  [(_relOrigin o,Left (pkIndex t ,Flip op))])) <$> inputsOnly )
        resIndex idx = -- traceShow ("resIndex",G.projectIndex (_relOrigin <$> rel) predKey idx ,predKey ,G.keys idx,G.toList idx) $
          concat . fmap (\(p,_,i) -> M.toList p) $ G.projectIndex (_relOrigin <$> rel) predK idx
        resScan idx = -- traceShow ("resScan", v,pkTable,(\i->  (i,) <$> G.checkPredId i predScan ) <$> G.toList idx,predScan,G.keys idx) $
          catMaybes $  (\i->  (G.getIndex m i,) <$> G.checkPredId i predScanOut)  <$> {-G.filterRows predScanIn -}(G.toList idx)
        convertPatch (pk,ts) = (\t -> RowPatch (pk ,PatchRow  [recurseAttr t pattr]) ) <$> ts
        taggedRef :: G.PathIndex PathTID a -> (a -> b) -> PathFTB b
        taggedRef i p =  go i
          where
            go (G.ManyPath j) = justError "empty" .  patchSet .F.toList $ go <$> j
            go (G.NestedPath i j) = matcher i (go j)
            go (G.TipPath j) = PAtom (p j)
            matcher (PIdIdx ix )  = PIdx ix . Just
            matcher PIdOpt   = POpt . Just
        recurseAttr (G.PathForeign _ i) p = PFK rel [] $ taggedRef i (const p)
        recurseAttr (G.PathInline r i) p = PInline r $ taggedRef i  nested
          where
            nested  (Many i) =  flip recurseAttr p <$> i
        recurseAttr (G.PathAttr _ i ) p = PFK rel [] $ taggedRef i (const p)
    result = search sidx <$>  evs
   in  concat $ result))]
  where
    rinf = maybe inf id $ HM.lookup (fst target)  (depschema inf)
    targetTable = lookTable rinf $ snd target
    pkTable = rawPK targetTable


dynFork a = do
  liftIO $  forkIO a

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

newDBRef inf table (iv,v)= do
    let
      sidx :: M.Map [Key] (SecondaryIndex Key Showable)
      sidx = M.fromList $ fmap (\un-> (un ,G.fromList' ( fmap (\(i,n,j) -> (uncurry M.singleton (G.getUnique un i,[]),n,j)) $ G.getEntries v))) (L.delete (rawPK table) $ _rawIndexes table )
    mdiff <-  liftIO$ atomically $ newBroadcastTChan
    chanidx <-  liftIO$ atomically $ newBroadcastTChan
    nchanidx <- liftIO$ atomically $ dupTChan chanidx
    nmdiff <- liftIO$ atomically $ dupTChan mdiff
    midx <-  liftIO$ atomically$ newTVar iv
    refSize <- liftIO $ atomically $  newTVar 1
    collectionState <-  liftIO$ atomically $ newTVar  (TableRep (tableMeta table,sidx,v))
    let dbref = DBRef table 0 refSize nmdiff midx nchanidx collectionState []
    liftIO$ atomically $ modifyTVar (mvarMap inf) (M.insert (tableMeta table ) dbref)
    return dbref


createTableRefs :: InformationSchema -> Table -> IO (Collection Key Showable,DBRef Key Showable)
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
          tableRel t = M.fromList $ catMaybes $ keyRel t<$> rawAttrs t
      res <- mapM (\t -> do
        ((IndexMetadata idx,sdata),ref) <- createTableRefs inf t
        return ((IndexMetadata $ M.mapKeys (mapPredicate (\k -> fromMaybe k (M.lookup k (tableRel t)))) $ idx, mapKey' (\k -> fromMaybe k (M.lookup k (tableRel t))) <$> G.toList sdata),ref)) l
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
          tidix <- dynFork $ forever $ updateIndex dbref
          tidst <- dynFork $ forever $ updateTable inf dbref
          let
            -- Collect all nested references and add one per relation avoided duplicated refs
            childrens = M.fromListWith mappend $ fmap (fmap (\i -> [i])) $  concat $ fmap (childrenRefsUnique table inf id  . unRecRel ) (rawFKS table)
          -- TODO : Add evaluator for functions What to do when one of the function deps change?
          nestedFKS <- mapM (\((rinf, t),l) -> do
            liftIO $ putStrLn $ "Load table reference: from " <> (T.unpack $ tableName table) <> " to "  <> (T.unpack $ tableName t)
            o <- prerefTable rinf t
            return (l,o)) (M.toList childrens)
          newNestedFKS <- liftIO . atomically$ traverse (traverse (\DBRef {..}-> cloneTChan  patchVar)) nestedFKS
          tidsrefs <- mapM (\(j,var)-> dynFork $ forever $ updateReference j var dbref) newNestedFKS
          return ((iv,v),dbref {threadIds = tidix:tidst:tidsrefs})

updateReference ::
     (v ~ Index v, PatchConstr k1 v, Foldable t, Functor t)
  => t ([RowPatch k1 v] -> TableRep k1 v -> [RowPatch k1 v])
  -> TChan [TableModificationK (TableK k1) (RowPatch k1 v)]
  -> DBRef k1 v
  -> IO ()
updateReference j var (DBRef {..}) = catchJust
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
updateIndex (DBRef {..}) =
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
  = catchJust notException (do
    upa <- atomically $ do
        patches <- fmap concat $ takeMany patchVar
        e <- readTVar collectionState
        let cpatches = compact patches
        let out = foldUndo e (concat $ tableDiffs <$> cpatches)
        traverse (\v -> writeTVar collectionState . fst$  v) out
        return  $ zip cpatches . snd <$> out
    either (putStrLn  .("### Error applying: " ++ ) . show ) (
      mapM_ (\(m,u) -> (do
        let mmod =   m
        mmod2 <- case mmod of
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
        case val of
          TableModification (Just v) i j k _ -> do
            undo (schemaOps inf) inf (RevertModification val ( u))
            return ()
          _ -> return () ))
      ) upa `catchAll` (\e -> putStrLn $ "Failed logging modification"  ++ show (e :: SomeException))
    return ())  (\e -> atomically ( readTChan patchVar ) >>= printException e )
