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
  , writeSchema
  , writeTable
  -- Pointer Only
  , prerefTable
  , lookDBVar
  , loadFKSDisk
  -- Transaction Operations
  , transactionNoLog
  ) where
import Control.Arrow
import Control.Concurrent
import Text
import Control.Concurrent.STM
import Control.DeepSeq
import Control.Exception (throw)
import qualified Control.Lens as Le
import Control.Monad.Catch
-- import Debug.Trace
import Control.Monad.RWS
import Control.Monad.Trans.Maybe
import qualified Data.Binary as B
import Data.Either
import qualified Data.Foldable as F
import qualified Data.HashMap.Strict as HM
import qualified Data.Interval as Interval
import qualified Data.List as L
import qualified Data.Map as M
import Data.Maybe
import qualified Data.Set as S
import Data.String (fromString)
import qualified Data.Text as T
import Data.Time
import qualified Data.Traversable as Tra
import Expression
import Query
import Reactive.Threepenny hiding (apply)
import RuntimeTypes
import Safe
import Step.Common
import System.Directory
import Types
import qualified Types.Index as G
import Types.Patch
import Utils

lookDBVar :: InformationSchema -> M.Map (KVMetadata Key) (DBRef Key Showable) -> (KVMetadata Key ) -> Dynamic (DBRef Key Showable)
lookDBVar inf mmap table =
    case M.lookup table mmap of
      Nothing ->  do
        (dyn ,fin) <- liftIO $ runDynamic $ snd <$> createTableRefs inf [] (lookTable inf (_kvname table))
        return dyn
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
  return (justError "no apply readIndex" $applyIfChange ini patches,nchan)

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
  let clonedVar = DBRef dbRefTable  (ix+1) refSize statechan idxVar idxchan collectionState
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

prerefTable :: InformationSchema -> Table -> Dynamic (DBRef Key Showable)
prerefTable  inf table  = do
  mmap <- liftIO $  readTVarIO (mvarMap inf)
  lookDBVar inf mmap (tableMeta table)


mergeDBRef  (IndexMetadata j,i) (IndexMetadata m,l) = (IndexMetadata $ M.unionWith (\(a,b) (c,d) -> (a+c,M.unionWith mergeToken b d))  j  m , i <>  l )

mergeToken (pi,TableRef i)  (pj,TableRef j) = (pi <> pj,TableRef $ Interval.hull i  j)

type TableChannels k v =  (TChan (IndexMetadataPatch k v), TChan [TableModificationU k v])


readTableFromFile
  :: InformationSchemaKV Key Showable
     -> T.Text
     -> TableK Key
     -> IO (Maybe
             (IndexMetadata Key Showable, [TBData Key Showable]))
readTableFromFile  inf r t = do
  let tname = fromString $ T.unpack $ r <> "/" <> s <> "/" <> tableName t
      s = schemaName inf
  liftIO $ putStrLn $ "Load from file:"  ++ tname
  has <- liftIO$ doesFileExist tname
  if has
    then do
      f <- (Right  <$> B.decodeFile tname ) `catch` (\e -> return $ Left ("error decoding" <> tname  <> show  (e :: SomeException )))
      either (\i -> do
        putStrLn ("Failed Loading Dump: " ++ show t ++ " - "  ++ show i )
        return Nothing)
             (\(m,g) ->
               return $ (Just (IndexMetadata $ M.fromList  m   ,  g) :: Maybe ( IndexMetadata Key Showable ,[TBData Key Showable])))  f
      else return Nothing



-- TODO : Remove recjoin hack and add state to ignore recursive inline tables without foreign keys
--  What should be the behaviour for recursive inline tables with foreign keys? .
--  Maybe this should be solved by the where predicate with some CTE like query, that returns recursive traces

childrenRefsUnique
  :: InformationSchema
  -> (Rel Key -> Rel Key)
  -> S.Set Key
  -> SqlOperation
  -> [((InformationSchema,Table),[RowPatch Key Showable] -> TableRep  Key Showable  -> [RowPatch Key Showable])]
childrenRefsUnique  inf pre set (RecJoin i j@(FKJoinTable _ _) ) = childrenRefsUnique inf pre set j
childrenRefsUnique  _  _  _ (RecJoin _ _ ) = []
childrenRefsUnique  _  _  _ (FunctionField _ _ _ ) = []
childrenRefsUnique  inf pre set (FKInlineTable rel target) = concat $ childrenRefsUnique inf (pre .RelAccess [Inline rel] ) set <$> fks
  where
    fks = rawFKS targetTable
    rinf = maybe inf id $ HM.lookup (fst target)  (depschema inf)
    targetTable = lookTable rinf $ snd target
childrenRefsUnique  inf pre set (FKJoinTable rel target)  =  [((rinf,targetTable),(\evs (TableRep (m,sidxs,base)) ->
   let
    sidx = M.lookup (_relOrigin <$> rel) sidxs
    search (BatchPatch ls op ) idxM = concat $ (\i -> search (RowPatch (i ,op)) idxM) <$> ls
    search (RowPatch p@(G.Idex v,PatchRow pattr)) idxM
      = case idxM of
        Just idx -> concat $ concat .fmap convertPatch  <$> resIndex idx
        Nothing -> concat $ convertPatch <$> resScan base
      where
        pkIndex t = justError "no key" $  t `L.elemIndex` pkTable
        predK = WherePredicate $ AndColl $ ((\(Rel o op t) -> PrimColl (pre o ,  [(_relOrigin o,Left (justError "no ref" $ unSOptional $ fmap create $ justError "no value" $ atMay v (pkIndex t) ,Flip op))] )) <$> filter (not . flip S.member set . _relOrigin )rel  )
        resIndex idx = -- traceShow ("resIndex",G.projectIndex (_relOrigin <$> rel) predKey idx ,predKey ,G.keys idx,G.toList idx) $
           fmap (\(p,_,i) -> M.toList p) $ G.projectIndex (_relOrigin <$> rel) predK idx
        resScan idx =  -- traceShow ("resScan", v,pkTable,(\i->  (i,) <$> G.checkPredId i predKey) <$> G.toList idx,predKey ,G.keys idx) $
          catMaybes $  (\i->  (G.getIndex m i,) <$> G.checkPredId i predK) <$> G.toList idx
        convertPatch (pk,ts) = (\t -> RowPatch (pk ,PatchRow  [recurseAttr t pattr]) ) <$> ts
        taggedRef :: G.PathIndex PathTID a -> (a -> b) -> PathFTB b
        taggedRef i p =  go i
          where
            go (G.ManyPath j ) = justError "empty" .  patchSet .F.toList $ go <$> j
            go (G.NestedPath i j ) = matcher i (go j)
            go (G.TipPath j ) = PAtom (p j)
            matcher (PIdIdx ix )  = PIdx ix . Just
            matcher PIdOpt   = POpt . Just
        recurseAttr (G.PathForeign  _ i ) p = PFK rel [] $ taggedRef i (const p)
        recurseAttr (G.PathInline r i ) p = PInline r $ taggedRef i  nested
          where
            nested  (Many i) =  flip recurseAttr p <$> i
        recurseAttr (G.PathAttr _ i ) p = PFK rel [] $ taggedRef i (const p)
    result = (\i -> search  i  sidx) <$>  evs
   in  concat $ result))]
  where
    rinf = maybe inf id $ HM.lookup (fst target)  (depschema inf)
    targetTable = lookTable rinf $ snd target
    pkTable = rawPK targetTable

createTable fixed m = do
  inf <- askInf
  let mvar = mvarMap inf
  mmap <- liftIO . atomically $ readTVar mvar
  map <-get
  predbvar <- lift (lookDBVar inf mmap m)
  ((fixedmap,table),dbvar)
      <- liftIO . atomically $
        cloneDBVar  (fixed ,_kvpk m) predbvar
  (log ,logix)<-case M.lookup m map of
    Just (_,i,l) -> return $ (concat $ tableDiffs <$> i,l)
    Nothing -> do
      modify (M.insert m (dbvar,[],[]))
      return ([],[])
  return ((either error fst $ applyUndo fixedmap logix,either error fst $ foldUndo table log ),dbvar)


dynFork a = do
  t <- liftIO $  forkIO a
  registerDynamic (killThread t)

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
    let dbref = DBRef table 0 refSize nmdiff midx nchanidx collectionState
    liftIO$ atomically $ modifyTVar (mvarMap inf) (M.insert (tableMeta table ) dbref)
    return dbref


createTableRefs :: InformationSchema -> [MutRec [[Rel Key]]] -> Table ->   Dynamic (Collection Key Showable,DBRef Key Showable)
createTableRefs inf re (Project table (Union l)) = do
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
        ((IndexMetadata idx,sdata),ref) <- createTableRefs inf re t
        return ((IndexMetadata $ M.mapKeys ( mapPredicate (\k -> fromMaybe k (M.lookup k (tableRel t)))) $ idx, (mapKey' (\k -> fromMaybe k (M.lookup k (tableRel t))) <$> G.toList sdata)),ref)) l
      let
        (uidx,udata) = foldr mergeDBRef (IndexMetadata M.empty,[]) (fst <$> res)
        udata2 = createUn (tableMeta table) (rawPK table) udata

      dbref <- newDBRef inf table (uidx,udata2)
      return ((uidx,udata2) ,dbref)
createTableRefs inf re table = do
  map <- liftIO$ atomically $ readTVar (mvarMap inf)
  case  M.lookup (tableMeta table) map of
    Just ref -> do
      liftIO$ putStrLn $ "Loading Cached Table: " ++ T.unpack (rawName table)
      liftIO $ atomically $ readCollectionSTM ref
    Nothing -> do
      liftIO$ putStrLn $ "Loading New Table: " ++ T.unpack (rawName table)
      (iv,v) <- readTable inf "dump" table re
      map2 <- liftIO$ atomically $ readTVar (mvarMap inf)
      case M.lookup (tableMeta table) map2 of
        Just ref ->  do
          liftIO$ putStrLn $ "Skiping Reference Table: " ++ T.unpack (rawName table)
          liftIO $ atomically $ readCollectionSTM ref
        Nothing -> do
          dbref@(DBRef {..}) <- newDBRef inf table (iv,v)
          dynFork $ forever $ updateIndex dbref
          dynFork $ forever $ updateTable inf dbref
          let
            -- Collect all nested references and add one per relation avoided duplicated refs
            childrens = M.fromListWith mappend $ fmap (fmap (\i -> [i])) $  snd $ F.foldl' (\(s,l)  fk -> (s <> S.map _relOrigin (pathRelRel fk),l ++ childrenRefsUnique inf id  s (unRecRel fk ))) (S.empty,[])  (rawFKS table)
          -- TODO : Add evaluator for functions What to do when one of the function deps change?
          nestedFKS <- mapM (\((rinf, t),l) -> do
            liftIO $ putStrLn $ "Load table reference: from " <> (T.unpack $ tableName table) <> " to "  <> (T.unpack $ tableName t)
            o <- prerefTable rinf t
            return (l,o)) (M.toList childrens)
          newNestedFKS <- liftIO . atomically$ traverse (traverse (\DBRef {..}-> cloneTChan  patchVar)) nestedFKS
          mapM_ (\(j,var)-> dynFork $ forever $ updateReference j var dbref) newNestedFKS
          return ((iv,v),dbref)

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

loadFKSDisk inf targetTable re = do
  let
    psort = rawFKS targetTable
    (fkSet2,pre) = F.foldl' (\(s,l) i -> ( (pathRelOri i)<> s  ,liftA2 (\j i -> j ++ [i]) l ( loadFKDisk inf s re i )))  (S.empty , return []) psort
  prefks <- pre
  return (\table ->
    let
      items = unKV $ table
      fks = catMaybes $  ($ table) <$>  prefks
      fkSet:: S.Set Key
      fkSet =    S.unions . fmap (S.fromList . fmap _relOrigin . (\i -> if all isInlineRel i then i else filterReflexive i ) . S.toList . pathRelRel ) $ filter isReflexive  psort
      nonFKAttrs :: [(S.Set (Rel Key) ,Column Key Showable)]
      nonFKAttrs =  M.toList $  M.filterWithKey (\i a -> not $ S.isSubsetOf (S.map _relOrigin i) (S.intersection fkSet fkSet2)) items
   in kvlist  (fmap snd nonFKAttrs <> fks ))

loadFKDisk :: InformationSchema ->  S.Set Key -> [MutRec [[Rel Key]]] ->  SqlOperation -> Dynamic (TBData Key Showable -> Maybe (Column Key Showable))
loadFKDisk inf old re (FKJoinTable rel (st,tt) ) = do
  let
    targetSchema = if schemaName inf == st then   inf else justError "no schema" $ HM.lookup st (depschema inf)
    targetTable = lookTable targetSchema tt
  ((_,mtable ),_) <- createTableRefs targetSchema re targetTable
  return (\table ->  do
    let
      relSet = S.fromList $ _relOrigin <$> relU
      refl = S.fromList $ _relOrigin <$> filterReflexive rel
      relU = rel
      tb  = F.toList (M.filterWithKey (\k l -> not . S.null $ S.map _relOrigin  k `S.intersection` relSet)  (unKV . tableNonRef $ table))
      fkref = joinRel2 (tableMeta targetTable) (replaceRel relU <$> tb) mtable
    case fkref of
      Nothing ->
        if F.any (isKOptional.keyType . _relOrigin) rel
          then Just $ FKT (kvlist $ filter ((\i -> not (S.member i old) &&  S.member i refl ) . _tbattrkey ) tb) relU (LeftTB1 Nothing)
          else Nothing
      i -> FKT (kvlist $ filter ((\i -> not (S.member i old) &&  S.member i refl ) . _tbattrkey ) tb) relU <$> i )
loadFKDisk inf old re (FKInlineTable ori (st,tt)) = do
  let targetTable = lookTable targetSchema tt
      targetSchema = if schemaName inf == st then   inf else justError "no schema" $ HM.lookup st (depschema inf)
  loadVtPre <- loadFKSDisk inf  targetTable re
  return (\table ->
    let v = do
          IT rel vt  <- M.lookup ( (S.singleton. Inline )   ori) (unKV $ table)
          let loadVt = loadVtPre  <$> vt
          return $ IT rel loadVt
    in case v of
        Nothing ->  if  (isKOptional .keyType) ori
                      then  Just (IT (ori ) (LeftTB1 Nothing))
                      else  Nothing
        v -> v)

loadFKDisk  inf old  re (RecJoin i l)
  | L.elem i re = do
    return  (const Nothing)
  | otherwise = do
    loadFKDisk inf old (i:re) l
loadFKDisk  _ _ _ _  = return (const Nothing)


writeSchema (schema,schemaVar) = do
  varmap <- atomically $ M.toList <$>  readTVar (mvarMap schemaVar)
  putStrLn $ "Dumping Schema: " ++ T.unpack schema
  let sdir = "dump/"<> (fromString $ T.unpack schema)
  hasDir <- doesDirectoryExist sdir
  when (not hasDir ) $  do
    putStrLn $ "Create directory : " <> sdir
    createDirectory sdir
  mapM_ (uncurry (writeTable schemaVar sdir)) varmap



writeTable :: InformationSchema -> String -> KVMetadata Key -> DBRef Key Showable -> IO ()
writeTable inf s t v = do
  let tname = s <> "/" <> (fromString $ T.unpack (_kvname t))
  putStrLn("Dumping Table: " <> tname)
  (TableRep (_,_,iv),_) <- atomically $ readState mempty  v
  (IndexMetadata iidx ,_)<- atomically $ readIndex v
  let
    sidx = first (mapPredicate keyFastUnique)  <$> M.toList iidx
    sdata = traverse (\i ->  fmap (mapKey' keyFastUnique) .  typecheck (typeCheckTable (_kvschema t,_kvname t)) .tableNonRef $ i) $  iv
  either (putStrLn .unlines ) (\sdata ->  do
    when (not (L.null sdata) )$
      B.encodeFile  tname (sidx, G.toList sdata)) sdata
  return ()


readTable :: InformationSchema -> T.Text -> Table -> [MutRec [[Rel Key]]] -> Dynamic (Collection Key Showable)
readTable inf r  t  re = do
  let
      s = schemaName inf
  o <- liftIO $ readTableFromFile inf r t
  let (m,prev) = fromMaybe (IndexMetadata M.empty ,[]) o
  disk <- loadFKSDisk inf t re
  let v = createUn (tableMeta t) (rawPK t) $ (\f -> disk  f) <$> prev
  return (m,v)


