{-# LANGUAGE RecordWildCards, Arrows, RankNTypes, RecursiveDo,
  TypeFamilies, FlexibleContexts, OverloadedStrings, TupleSections
  #-}
module SchemaQuery
  (
  -- Clear in memory cache
   resetCache
  -- Flush to disk in memory DB
  , writeSchema
  -- Create fresh variables
  , createFresh
  -- Database Mutable Operations
  , fullInsert
  , fullEdit
  , patchFrom
  , deleteFrom
  -- Database Read Only Operations
  , selectFrom
  , getFrom
  , refTable
  , refTables
  , refTablesPorj
  , tableLoaderAll
  , selectFromTable
  , refTables'
  -- Pointer Only
  , revertModification
  , prerefTable
  -- Cache Only Operations
  , loadFKS
  -- Transaction Operations
  , transaction
  , transactionNoLog
  -- Constraint Checking
  , tableCheck
  -- SQL Arrow API
  , fromR
  , innerJoinR
  , leftJoinR
  , projectV
  ) where
import Control.Arrow (first)
import Control.Arrow
import Control.Concurrent
import Serializer
import Control.Concurrent.STM
import Control.DeepSeq
import Control.Exception (throw)
import qualified Control.Lens as Le
import Control.Monad.Catch
import Debug.Trace
import Control.Monad.RWS
import Control.Monad.Trans.Maybe
import qualified Data.Binary as B
import Data.Either
import qualified Data.Foldable as F
import qualified Data.GiST.BTree as G
import qualified Data.HashMap.Strict as HM
import qualified Data.Interval as Interval
import qualified Data.List as L
import qualified Data.Map as M
import Data.Maybe
import qualified Data.Poset as P
import qualified Data.Set as S
import Data.String (fromString)
import qualified Data.Text as T
import Data.Time
import qualified Data.Traversable as Tra
import Environment
import Expression
import qualified NonEmpty as Non
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

lookDBVar inf mmap table =
    case M.lookup table mmap of
      Nothing ->  do
        (dyn ,fin) <- liftIO $ runDynamic $ snd <$> createTableRefs inf [] table
        return dyn
      Just i-> return i

estLength page size est = fromMaybe 0 page * size  +  est

resetCache :: InformationSchema -> IO ()
resetCache inf = atomically $ modifyTVar (mvarMap inf) (const M.empty)


prerefTable :: InformationSchema -> Table -> Dynamic (DBRef Key Showable)
prerefTable  inf table  = do
  mmap <- liftIO $  readTVarIO (mvarMap inf)
  lookDBVar inf mmap table

projunion :: Show a=>InformationSchema -> Table -> TBData Key a -> TBData Key a
projunion inf table = res
  where
    res =  liftTable' inf (tableName table) . mapKey' keyValue. transformTable
    transformTable (KV v) =  KV (transformAttr <$> M.filterWithKey (\k _ -> S.isSubsetOf (S.map (keyValue._relOrigin) k) attrs) v)
      where
        attrs = S.fromList $ keyValue <$> tableAttrs table
        transformAttr (Fun k l i) = Fun  k l (transformKey (keyType k) (keyType nk) i)
          where nk = lkKey table (keyValue k)
        transformAttr (Attr k i ) = Attr k (transformKey (keyType k) (keyType nk) i)
          where nk = lkKey table (keyValue k)
        transformAttr (IT k i ) = IT k (transformKey (keyType k) (keyType nk) i)
          where nk = lkKey table (keyValue k)
        transformAttr (FKT r rel v)  = FKT (transformTable r ) rel (transformKeyList ok nk  v)
          where ok = mergeFKRef ( keyType. _relOrigin <$> rel)
                nk = mergeFKRef ( keyType. lkKey table . keyValue . _relOrigin <$> rel)

mapIndex :: InformationSchema  -> Table -> IndexMetadata Key Showable -> IndexMetadata Key Showable
mapIndex inf table (IndexMetadata i)  = IndexMetadata $ M.mapKeys (liftPredicateF lookupKeyName inf (tableName table) . mapPredicate keyValue) . filterPredicate $ i
  where
    filterPredicate  = M.filterWithKey (\k _ -> isJust $ traPredicate  check  $ k)
    check i = if S.member (keyValue i) attrs  then Just i else Nothing
    attrs = S.fromList $ keyValue <$> tableAttrs table

lookIndexMetadata pred (IndexMetadata i ) = M.lookup pred i
mapIndexMetadata f (IndexMetadata v ) = IndexMetadata $ M.mapKeys (mapPredicate f )  v
mapIndexMetadataPatch f (i,j,k,l) = (mapPredicate f i,j,k,l)

mapDBVar inf table (DBVar2 e i j l  )
  = ([e], mapIndex inf table <$> i, createUn (tableMeta table)  (rawPK table) . fmap (projunion inf table) . G.toList <$> j, l)

mergeDBRef  (IndexMetadata j,i) (IndexMetadata m,l) = (IndexMetadata $ M.unionWith (\(a,b) (c,d) -> (a+c,M.unionWith mergeToken b d))  j  m , i <>  l )

mergeDBRefT  (ref1,j ,i,o) (ref2,m ,l,p) = (ref1 <> ref2 ,liftA2 (\(IndexMetadata a) (IndexMetadata b) -> IndexMetadata $ M.unionWith (\(a,b) (c,d) -> (a+c,M.unionWith mergeToken  b d)) a b)  j  m , liftA2 (<>) i l , liftA2 (M.intersectionWith (<>)) o p )

refTable :: InformationSchema -> Table -> Dynamic DBVar
refTable  inf table  = do
  mmap <- liftIO$ atomically $ readTVar (mvarMap inf)
  ref <-lookDBVar inf mmap table
  (idxTds,dbTds ) <- convertChan inf table mempty ref
  return (DBVar2 ref idxTds  (primary <$> dbTds) (secondary <$>dbTds) )


secondary (TableRep (m,s,g)) = s
primary (TableRep (m,s,g)) = g


selectFrom t a b c d = do
  inf <- askInf
  let tb = lookTable inf t
  tableLoader  tb a b c d (allRec' (tableMap inf) tb)

updateFrom  m a  pk b = do
  inf <- askInf
  let
    kv = apply a b
    overloaded  = M.lookup (_kvschema m ,_kvname m) overloadedRules
    overloadedRules = (rules $ schemaOps inf)
    isUpdate (i,UpdateRule _ ) =  i (mapKey' keyValue a)
    isUpdate _ = False
  v <- case L.find isUpdate =<< overloaded of
    Just (_,UpdateRule i) -> i a b
    Nothing -> (editEd $ schemaOps inf) m a pk b
  tellPatches m (pure v)
  return v

patchFrom m  r   = do
  let l = RowPatch r
  asyncPatches m (pure l)
  return l


fullInsert :: KVMetadata Key ->TBData Key Showable -> TransactionM  (RowPatch Key Showable)
fullInsert k1 v1 = createRow' k1 <$> recInsert k1 v1

fullEdit ::  KVMetadata Key -> TBData Key Showable -> TBData Key Showable -> TransactionM (RowPatch Key Showable)
fullEdit k1 old v2 = do
  i <- fullDiffEdit k1 old v2
  return $ patchRow' k1 old i

insertFrom  m a   = do
  inf <- askInf
  let overloaded  = M.lookup (_kvschema m ,_kvname m) overloadedRules
      overloadedRules = (rules $ schemaOps inf)
      isCreate (i,CreateRule _ ) = i (mapKey' keyValue a)
      isCreate _ = False
  v <- case L.find isCreate  =<< overloaded of
    Just (_,CreateRule l) -> l a
    Nothing -> (insertEd $ schemaOps inf)  m a
  tellPatches m (pure v)
  return  v


getFrom m b = do
  inf <- askInf
  v <- (getEd $ schemaOps inf)  m b
  let toPatch :: TBData Key Showable -> RowPatch Key  Showable -> TBData Key Showable
      toPatch b = (\(PatchRow i ) -> justError "no apply getFrom" $ applyIfChange b i).snd .unRowPatch
      newRow = toPatch b <$> v
      allFields = allRec' (tableMap inf) m
      comp = recComplement inf (tableMeta m) b allFields
  case newRow of
    Just i -> do
      resFKS  <- traverse (getFKS inf mempty m (maybeToList newRow)) comp
      let
        result :: Maybe (TBIdx Key Showable)
        result = do
          r <- newRow
          res <- resFKS
          res <- either (const Nothing) Just (res r) :: Maybe (TBData Key Showable)
          return $ patch res
      traverse (tell . pure . ((mempty,). FetchData m .RowPatch. (G.getIndex (tableMeta m) b,).PatchRow )) result
      return result
    Nothing ->  return Nothing

deleteFrom  m a   = do
  inf <- askInf
  let overloaded  = M.lookup (_kvschema m,_kvname m) overloadedRules
      overloadedRules = (rules $ schemaOps inf)
      isRule (i,DropRule _ ) = i (mapKey' keyValue a)
      isRule _ = False
      idx = G.getIndex m a
  log <- case L.find isRule =<< overloaded of
    Nothing -> (deleteEd $ schemaOps inf) m a
    Just (_,DropRule i) -> i a
  tellPatches m (pure log)
  return log


paginateTable table pred tbf = do
  (ref,(nidx,TableRep (_,_,ndata))) <-  tableLoaderAll  table  (Just 0) Nothing [] pred (Just tbf)
  let
    check ix (i,tb2) = do
        let
          iempty = (IndexMetadata M.empty,G.empty)
          next = ix +1
          -- Check if estimated size exist and if is bigger then the next page size (next * pagesize)
          -- or the current is already bigger or euqals the estimated
          cond = maybe False (\i -> fst i >= G.size tb2 && fst i >= next * 400 )  (lookIndexMetadata pred i)
        output <- if cond
            then  do
              (_,(nidx,TableRep(_,_,ndata))) <- tableLoaderAll  table  (Just next  ) Nothing []  pred (Just tbf)
              -- Check if nothing has changed  or no more data to load
              if G.size ndata == G.size tb2
                 then return iempty
                 else check next (nidx,ndata)
            else return iempty
        return $ mergeDBRef (i,tb2) output
  snd <$> check 0 (nidx,ndata)

predicate
  :: [Rel (FKey (KType a1))]
     -> TBPredicate (FKey (KType a1)) a
     -> Maybe (TBPredicate (FKey (KType a1)) a)
predicate i (WherePredicate l ) =
   fmap WherePredicate (go (test i) l)
  where
    go pred (AndColl l) = AndColl <$> nonEmpty (catMaybes $ go pred <$> l)
    go pred (OrColl l) = OrColl <$> nonEmpty (catMaybes $ go pred <$> l)
    go pred (PrimColl l) = PrimColl <$> pred l
    test f (RelAccess p i ,j)  = if p == f then Just ( i ,fmap (mapLeft (fmap (removeArray (_keyFunc $ mergeFKRef $ fmap (keyType . _relOrigin) $ p)))) <$> j) else Nothing
    test v f = Nothing
    removeArray (KOptional :i)  o = removeArray i o
    removeArray (KArray : i)  (AnyOp o) = o
    removeArray i  o = o

-- getFKRef _  _   _  old i j |  traceShow (i,old)  False = undefined
getFKRef inf predtop (me,old) set (FKInlineTable  r j ) tbf =  do
    let
      rinf = maybe inf id $ HM.lookup (fst j) (depschema inf)
      table = lookTable rinf $ snd j
      editAttr fun (KV i) = fmap KV (flip Le.at (traverse ((Le.traverseOf ifkttable (traverse fun)))) (S.singleton $ Inline r)  i )
      nextRef :: [FTB (TBData Key Showable)]
      nextRef = fmap (\i -> _fkttable $ justError "no it" $ M.lookup (S.singleton $ Inline r) (_kvvalues  i) ) set

    case nonEmpty (concat $ fmap F.toList nextRef) of
      Just refs -> do
        joinFK <- getFKS rinf predtop table  refs tbf
        let joined = editAttr joinFK
        return (me >=> joined,old <> S.singleton r)
      Nothing ->
        return (me ,old <> S.singleton r)

getFKRef inf predtop (me,old) v (FunctionField a b c) tbf = do
  let
    addAttr :: TBData Key Showable -> Either ([TB Key Showable],[Rel Key]) (TBData Key Showable)
    addAttr i = Right $ maybe i (\r -> (\(KV i) -> KV (M.insert (keyattrs r) r i) ) i) (evaluate  a b funmap c i)
  return (me >=> addAttr ,old <> S.singleton a )

getFKRef inf predtop (me,old) set (RecJoin i j) tbf = getFKRef inf predtop (me,old) set j tbf

getFKRef inf predtop (me,old) set (FKJoinTable i j) tbf =  do
    let
        rinf = maybe inf id $ HM.lookup (fst j)  (depschema inf)
        table = lookTable rinf $ snd j
        genpredicate (KV o) = fmap AndColl . allMaybes . fmap (primPredicate o)  $ i
        primPredicate o k  = do
          i <- unSOptional (_tbattr (lkAttr k o))
          return $ PrimColl (Inline (_relTarget k) ,[(_relTarget k,Left (i,Flip $ _relOperator k))])
        lkAttr k v = justError ("no attr " <> show k) $ M.lookup (S.singleton (Inline (_relOrigin k))) (_kvvalues $ tableNonRef (KV v))
        refs = fmap (WherePredicate .OrColl. L.nub) $ nonEmpty $ catMaybes $  genpredicate <$> set
        predm = refs <> predicate i predtop
    tb2 <-  case predm of
      Just pred -> do
        localInf (const rinf) $ paginateTable table pred tbf
      Nothing -> return (G.empty)
    let
        tar = S.fromList $ fmap _relOrigin i
        refl = S.fromList $ fmap _relOrigin $ filterReflexive i
        inj = S.difference refl old
        joinFK :: TBData Key Showable -> Either ([TB Key Showable],[Rel Key]) (Column Key Showable)
        joinFK m  = maybe (Left (taratt,i)) Right $ FKT (kvlist tarinj ) i <$> joinRel2 (tableMeta table ) (fmap (replaceRel i )$ taratt ) tb2
          where
            replaceRel rel (Attr k v) = (justError "no rel" $ L.find ((==k) ._relOrigin) rel,v)
            taratt = getAtt tar (tableNonRef m)
            tarinj = getAtt inj (tableNonRef m)
        addAttr :: Column Key Showable -> TBData Key Showable -> TBData Key Showable
        addAttr r = (\(KV i) -> KV (M.insert (keyattrs r) r  $ M.filterWithKey (\k _ -> not $ S.map _relOrigin k `S.isSubsetOf` refl && F.all isInlineRel k) i ))
        joined i = do
           fk <- joinFK i
           return $ addAttr  fk i
    return (me >=> joined,old <> refl)

mapLeft f (Left i ) = Left (f i)
mapLeft f (Right i ) = (Right i)

getAtt i k  = filter ((`S.isSubsetOf` i) . S.fromList . fmap _relOrigin. keyattr ) . F.toList . _kvvalues  $ k


getFKS
  :: InformationSchemaKV Key Showable
     -> TBPredicate Key Showable
     -> TableK Key
     -> [TBData Key Showable]
     -> KV Key ()
     -> TransactionM
        (TBData Key Showable -> Either
              ([TB Key Showable],[Rel Key])
              (TBData Key Showable))
getFKS inf predtop table v tbf = fmap fst $ F.foldl' (\m f  -> m >>= (\i -> maybe (return i) (getFKRef inf predtop i v f  . head . F.toList )  (refLookup (pathRelRel f) tbf) )) (return (return ,S.empty )) sorted
  where
    sorted = P.sortBy (P.comparing (RelSort . F.toList .  pathRelRel))  (rawFKS table)

rebaseKey inf t  (WherePredicate fixed ) = WherePredicate $ lookAccess inf (tableName t) . (Le.over Le._1 (fmap  keyValue) ) . fmap (fmap (first (keyValue)))  <$> fixed

mergeToken (TableRef i)  (TableRef j) = TableRef (Interval.hull i  j)

type TableChannels k v =  (TChan (IndexMetadataPatch k v), TChan [TableModificationU k v])

tableLoader :: Table -> Maybe Int -> Maybe Int -> [(Key,Order)] -> WherePredicate -> TBData Key ()
    -> TransactionM DBVar
tableLoader (Project table  (Union l)) page size presort fixed  tbf = do
    liftIO$ putStrLn $ "start loadTable " <> show (tableName table)
    inf <- askInf
    let
      dbvarMerge i = foldr mergeDBRefT  ([],pure (IndexMetadata M.empty)  ,pure G.empty, pure (M.fromList $ (,G.empty)<$> _rawIndexes table) ) (mapDBVar inf table <$>i )
      dbvar (l,i,j,p) = DBVar2 (justError "head5" $ safeHead l) i j p
    i <- mapM (\t -> tableLoader t page size presort (rebaseKey inf t  fixed) (projunion inf t tbf)) l
    return $ dbvar (dbvarMerge i)
tableLoader  table page size presort fixed tbf = do
  liftIO$ putStrLn $ "start loadTable " <> show (tableName table)
  ((fixedChan,nchan),(nidx,rep)) <- tableLoader'  table page size presort fixed tbf
  let
    tableU = table
    fixedU = fixed

  inf <- askInf
  vpt <- lift $ convertChanTidings0 inf table (fixed ,rawPK table) rep  nchan
  idxTds <- lift $ convertChanStepper0 inf table nidx fixedChan
  dbvar <- lift $ prerefTable inf table
  return (DBVar2 dbvar idxTds (fmap primary vpt) (fmap secondary vpt))

tableLoader'
  :: Table
   -> Maybe Int
   -> Maybe Int
   -> [(Key,Order)]
   -> WherePredicate
   -> TBData Key ()
   -> TransactionM (TableChannels Key Showable,(IndexMetadata Key Showable,TableRep Key Showable ))
tableLoader' table  page size presort fixed tbf = do
  pageTable (\table page token size presort predicate -> do
    inf <- askInf
    let
      unestPred (WherePredicate l) = WherePredicate $ go predicate l
        where
          go pred (AndColl l) = AndColl (go pred <$> l)
          go pred (OrColl l) = OrColl (go pred <$> l)
          go pred (PrimColl l) = AndColl $ PrimColl <$> pred l
          predicate (RelAccess i j ,_ ) = (\a -> (a, [(_relOrigin a,Right (Not IsNull))])) <$> i
          predicate i  = [i]
    (res ,x ,o) <- (listEd $ schemaOps inf) (tableMeta table) (tableNonRef tbf) page token size presort (unestPred predicate)
    resFKS  <- getFKS inf predicate table res tbf
    let result = fmap resFKS   res
    liftIO $ when (not $ null (lefts result)) $ do
      print ("lefts",tableName table ,lefts result)
    return (rights  result,x,o )) table page size presort fixed


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


predNull (WherePredicate i) = L.null i

filterfixedS table fixed (s,v)
  = if predNull fixed
       then v
       else queryCheckSecond (fixed ,rawPK table) (TableRep (tableMeta table,s,v))


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
childrenRefsUnique  inf pre set (FKInlineTable rel target)  =    concat $ childrenRefsUnique inf (pre .RelAccess [Inline rel] ) set <$> fks
  where
    fks = rawFKS targetTable
    rinf = maybe inf id $ HM.lookup (fst target)  (depschema inf)
    targetTable = lookTable rinf $ snd target
childrenRefsUnique  inf pre set (FKJoinTable rel target)  =  [((rinf,targetTable),(\evs (TableRep (m,sidxs,base)) ->
   let
    sidx = M.lookup (_relOrigin  <$> rel) sidxs
    search (BatchPatch ls op ) idxM = concat $ (\i -> search (RowPatch (i ,op)) idxM)  <$> ls
    search (RowPatch p@(G.Idex v,PatchRow pattr)) idxM
      = case idxM of
        Just idx -> concat $ concat .fmap convertPatch  <$> resIndex idx
        Nothing -> concat $ convertPatch <$> resScan base
      where
        pkIndex t = justError "no key" $  t`L.elemIndex` pkTable
        predK = WherePredicate $ AndColl $ ((\(Rel o op t) -> PrimColl (pre (Inline o) ,  [(o,Left (justError "no ref" $ unSOptional $ fmap create $ justError "no value" $ atMay v (pkIndex t) ,Flip op))] )) <$> filter (not . flip S.member set . _relOrigin )rel  )
        predKey =  predK
        resIndex idx =  -- traceShow ("resIndex",G.projectIndex (_relOrigin <$> rel) predKey idx ,predKey ,G.keys idx,G.toList idx) $
           fmap (\(p,_,i) -> M.toList p) $ G.projectIndex (_relOrigin <$> rel) predKey idx
        resScan idx =  -- traceShow ("resScan", v,pkTable,(\i->  (i,) <$> G.checkPredId i predKey) <$> G.toList idx,predKey ,G.keys idx) $
           catMaybes $ fmap (\(i,t) -> (G.getIndex m i,t)) . (\i->  (i,) <$> G.checkPredId i predKey) <$> G.toList idx
        convertPatch (pk,ts) = (\t -> RowPatch (pk ,PatchRow  [ recurseAttr t pattr]) ) <$> ts
        taggedRef :: G.PathIndex PathTID a -> (a -> b) -> PathFTB b
        taggedRef i p =  go i
          where
            go (G.ManyPath j ) = PatchSet $ go <$> j
            go (G.NestedPath i j ) = matcher i (go j)
            go (G.TipPath j ) = PAtom (p j)
            matcher (PIdIdx ix )  = PIdx ix . Just
            matcher PIdOpt   = POpt . Just
        recurseAttr (G.PathForeign  _ i ) p = PFK relf [] $ taggedRef i (const p)
        recurseAttr (G.PathInline r i ) p = PInline r $ taggedRef i   nested
          where
            nested  (Many i) =  flip recurseAttr p <$> i
        recurseAttr (G.PathAttr _ i ) p = PFK relf [] $ taggedRef i (const p)
     in traceShow (target,rel) $ concat $ (\i -> search  i  sidx) <$>  evs))]
  where
    rinf = maybe inf id $ HM.lookup (fst target)  (depschema inf)
    relf = filterReflexive rel
    targetTable = lookTable rinf $ snd target
    pkTable = rawPK targetTable


pageTable method table page size presort fixed = do
    inf <- askInf
    let mvar = mvarMap inf
        tableU = table
        fixedU = fixed
        defSort = fmap (,Desc) $  rawPK table
        sortList  = if L.null presort then defSort else  presort
        pagesize = maybe (opsPageSize $ schemaOps inf) id size
    mmap <- liftIO . atomically $ readTVar mvar
    predbvar <- lift $ lookDBVar inf mmap table
    ((IndexMetadata fixedmap,TableRep (_,sidx,reso)),dbvar)
      <- liftIO . atomically $
        cloneDBVar  (fixedU ,rawPK tableU) predbvar
    modify (M.insert (table,fixed) dbvar)
    let
      nchan = patchVar dbvar
      fixedChan = idxChan dbvar
      pageidx =  (fromMaybe 0 page +1) * pagesize
      hasIndex = M.lookup fixedU fixedmap
      readNew sq = do
         let
           predreq = (fixedU,G.Contains (pageidx - pagesize,pageidx))
         (nidx,ndata) <-  if
              ((isNothing hasIndex|| (sq > G.size reso)) -- Tabela é maior que a tabela carregada
              && pageidx  > G.size reso) -- O carregado é menor que a página
           then do
             let pagetoken = join $ flip M.lookupLE  mp . (*pagesize) <$> page
                 (_,mp) = fromMaybe (0,M.empty ) hasIndex
             (resOut,token ,s ) <- method table (liftA2 (-) (fmap (*pagesize) page) (fst <$> pagetoken)) (fmap snd pagetoken) size sortList fixed
             let res =  resK
                 -- # postFilter fetched results
                 resK = if predNull fixed then resOut else G.filterRows fixed resOut
                 -- # removeAlready fetched results
                 diffNew i = case G.lookup (G.getIndex (tableMeta table) i) reso of
                               Just v -> patchRowM' (tableMeta table) v i
                               Nothing -> Just $ createRow' (tableMeta table) i

                 newRes = catMaybes  $ fmap diffNew resK
             -- Add entry for this query
             putIdx (idxChan dbvar) (fixedU, estLength page pagesize s, pageidx, token)
             -- Only trigger the channel with new entries
             -- TODO: Evaluate if is better to roll the deltas inside the monad instead of applying directly
             traverse (\i ->  putPatch (patchVar dbvar) (FetchData table  <$> i)) $ nonEmpty newRes
             return $ if L.null newRes then
                (maybe (estLength page pagesize s,M.singleton pageidx token ) (\(s0,v) -> (estLength page pagesize  s, M.insert pageidx token v)) hasIndex,reso)
                    else
                (maybe (estLength page pagesize s,M.singleton pageidx token ) (\(s0,v) -> (estLength page pagesize  s, M.insert pageidx token v)) hasIndex,createUn (tableMeta tableU) (rawPK tableU) res <> reso)
           else do
             return (fromMaybe (0,M.empty) hasIndex, reso)
         return $ (M.insert fixedU nidx fixedmap, sidx,ndata )
    (nidx2,sidx2,ndata2) <-  case hasIndex of
          Just (sq,idx) -> case  M.lookup pageidx idx of
             Just v -> return (fixedmap , sidx,reso)
             Nothing -> readNew sq
          Nothing -> readNew maxBound
    return ((fixedChan,nchan) ,(IndexMetadata nidx2 ,TableRep(tableMeta table,sidx2, ndata2)))

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


readIndex
  :: (Show k,Ord k,Show v)
  => DBRef k v
  -> STM
  (IndexMetadata  k v ,
     TChan (WherePredicateK k, Int, Int, PageTokenF v))
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
    result=justError "no apply readState" $ applyIfChange (TableRep (m,s,fv)) (filterPred  $ fmap tableDiff $ concat patches)
  return (result,chan)


tableCheck
  :: (Show t, Show a) =>
     KVMetadata (FKey (KType t))
     -> KV (FKey (KType t)) a -> Either [Char] (KV (FKey (KType t)) a)
tableCheck m t = if checkAllFilled then Right t else Left ("tableCheck: non nullable rows not filled " ++ show ( need `S.difference` available ,m,t))
  where
      checkAllFilled =  need `S.isSubsetOf`  available
      available = S.fromList $ concat $ fmap _relOrigin . keyattr <$> unKV  t
      need = S.fromList $ L.filter (\i -> not (isKOptional (keyType i) || isSerial (keyType i) || isJust (keyStatic i )) )  (kvAttrs m)

dynFork a = do
  t <- liftIO $  forkIO a
  registerDynamic (killThread t)

convertChanEventIndex inf table nchan = do
    (e,h) <- newEvent
    dynFork $ forever $ catchJust notException ( do
      a <- atomically $ takeMany nchan
      h ( a )) (\e -> atomically (takeMany nchan) >>= (\d ->  putStrLn $ show ("error convertChanStep"  ,e :: SomeException,d)<>"\n"))
    return e

convertChanStepper0
  :: Show v =>
    InformationSchema
    -> TableK Key
    -> IndexMetadata Key v
    -> TChan (WherePredicateK Key,Int,Int,PageTokenF v)
    -> Dynamic
        (Tidings (IndexMetadata Key v ))
convertChanStepper0  inf table ini nchan = do
    e <- convertChanEventIndex inf table nchan
    accumT  ini (flip apply <$> e)

convertChan
  :: InformationSchema
  -> TableK Key
     -> (TBPredicate Key Showable, [Key])
     -> DBRef Key Showable
     -> Dynamic
      (Tidings (IndexMetadata Key Showable ),Tidings (TableRep Key Showable))
convertChan inf table fixed dbvar = do
  ((ini,result),cloneddbvar) <- liftIO $ atomically $
    cloneDBVar ( fixed) dbvar
  (,) <$> convertChanStepper0 inf table ( ini) (idxChan cloneddbvar)
      <*> convertChanTidings0 inf table fixed ( result ) (patchVar cloneddbvar)

convertChanEvent
  ::
    InformationSchema -> TableK Key
     -> (TBPredicate Key Showable, [Key])
     -> Behavior (TableRep Key Showable)
     -> TChan [TableModificationU Key Showable]
     -> Dynamic
          (Event [RowPatch Key Showable])
convertChanEvent inf table fixed bres chan = do
  (e,h) <- newEvent
  dynFork $ forever $ catchJust notException (do
    ml <- atomically $ takeMany chan
    TableRep (_,_,v) <- currentValue bres
    let
      meta = tableMeta table
      m =  tableDiff <$> concat  ml
      newRows =  filter (\d -> checkPatch fixed d && L.any (\i -> isNothing  (G.lookup i  v)) (index d) ) m
      filterPred = nonEmpty . filter (checkPatch fixed)
      filterPredNot j = nonEmpty . catMaybes . map (\d -> if L.any (\i -> isJust (G.lookup i  j) ) (index d) && not (checkPatch fixed d) then Just (rebuild (index d) DropRow )  else Nothing )
      oldRows = filterPredNot v m
      patches = oldRows <> filterPred m
    traverse  h patches
    return ()) (\e -> atomically (takeMany chan) >>= (\d -> putStrLn $  show ("error convertChanEvent"  ,e :: SomeException,d)<>"\n"))
  return e


mapTableRep f (TableRep (m,i,j))= TableRep (f <$> m, mapSecondary f i, mapPrimary f j)
mapSecondary f = M.mapKeys (fmap f) . fmap (fmap (fmap (fmap (G.mapAttributePath f))))
mapPrimary  f = fmap (mapKey' f)


convertChanTidings0
  :: InformationSchema
  -> TableK Key
  -> (TBPredicate Key Showable, [Key])
  -> TableRep Key Showable
  -> TChan [TableModificationU Key Showable]
  -> Dynamic (Tidings (TableRep Key Showable))
convertChanTidings0 inf table fixed ini nchan = mdo
    evdiff <-  convertChanEvent inf table  fixed (facts t) nchan
    t <- accumT ini (flip apply <$> evdiff)
    return  t

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

createRow (RowPatch (_,CreateRow i)) = i
createRow (RowPatch (_,PatchRow i)) = create i



tableLoaderAll table  page size presort fixed tbf = do
  inf <- askInf
  tableLoader'  table page size presort fixed (fromMaybe (allRec' (tableMap inf) table ) tbf)

recInsert :: KVMetadata Key -> TBData Key Showable -> TransactionM  (TBData Key Showable)
recInsert k1  v1 = do
   inf <- askInf
   ret <- KV <$>  Tra.traverse (tbInsertEdit k1 )  (unKV v1)
   let tb  = lookTable inf (_kvname k1)
   (_,(_,TableRep(_,_,l))) <- tableLoaderAll  tb Nothing Nothing [] mempty Nothing
   if  (isNothing $ join $ fmap (flip G.lookup l) $ G.tbpredM k1  ret ) && rawTableType tb == ReadWrite
      then catchAll (do
        tb  <- insertFrom k1 ret
        return $ createRow tb) (\e -> liftIO $ do
          throw e
          putStrLn $ "Failed insertion: "  ++ (show (e :: SomeException))
          return ret)
      else do
        return ret


itRefFun :: RelOperations (KV Key Showable)
itRefFun = (id,id,noEdit,noInsert)
  where
    noInsert k1 v1   = do
      KV <$>  Tra.traverse (tbInsertEdit k1)  (unKV v1)
    noEdit k1 v1 v2  = do
      KV <$>  Tra.sequence ( M.intersectionWith (tbDiffEditInsert k1) (unKV v1) (unKV v2))

asyncPatches :: KVMetadata Key ->  [RowPatch Key Showable] -> TransactionM ()
asyncPatches m i =
  tell =<< mapM (fmap (mempty,) . asyncModification m) i

tellPatches :: KVMetadata Key ->  [RowPatch Key Showable] -> TransactionM ()
tellPatches m i =
  tell =<< mapM (fmap (mempty,) . wrapModification m) i

transactionNoLog :: InformationSchema -> TransactionM a -> Dynamic a
transactionNoLog inf log = do
  (md,s,mods)  <- runRWST log (inf ,[]) M.empty
  let aggr = foldr (\(l,t) m -> M.insertWith mappend (tableObj t,l) [t] m) M.empty mods
  liftIO $ atomically $ traverse (\(k,v) -> do
    ref <- case M.lookup k s of
      Nothing -> do
        let rinf = fromMaybe inf $ HM.lookup (rawSchema (fst k)) $  depschema inf
        mmap <- readTVar (mvarMap rinf)
        return $ justError ("No table found" ++ show k) $ M.lookup (fst k) mmap
      Just i -> return i
    putPatchSTM (patchVar ref) v
    ) (M.toList aggr)
  return md


withDynamic :: (forall b . IO b -> IO b) -> Dynamic a -> Dynamic a
withDynamic  f i =  do
  (v,e) <- liftIO . f $ (runDynamic i) `catch` (\e -> putStrLn ("Transaction Exception: "  ++ show (e  :: SomeException)) >> throw e )
  mapM registerDynamic e
  return v

transaction :: Show a=>InformationSchema -> TransactionM a -> Dynamic a
transaction inf log = withDynamic ((transactionEd $ schemaOps inf) inf ) $ transactionNoLog inf log


fullDiffEdit :: KVMetadata Key -> TBData Key Showable -> TBData Key Showable -> TransactionM (TBData Key Showable)
fullDiffEdit k1 old v2 = do
   edn <-  KV <$>  Tra.sequence (M.intersectionWith (tbDiffEditInsert k1)  (unKV old) (unKV v2))
   when (isJust $ diff (tableNonRef old) (tableNonRef edn)) . void $do
     traverse (patchFrom k1 . (G.getIndex k1 edn,) . PatchRow)  (diff old edn)
   return edn

tbDiffEditInsert :: KVMetadata Key ->  Column Key Showable -> Column Key Showable -> TransactionM (Column Key  Showable)
tbDiffEditInsert k1 i j
  | isJust (diff i  j) = tbEdit k1 i j
  | otherwise =  return j


tbEdit :: KVMetadata Key -> Column Key Showable -> Column Key Showable -> TransactionM (Column Key Showable)
tbEdit m (Fun _ _ _ ) (Fun k1 rel k2)= return $ (Fun k1 rel k2)
tbEdit m (Attr _ _ ) (Attr k1 k2)= return $ (Attr k1 k2)
tbEdit m (IT a1 a2) (IT k2 t2) = do
  inf <- askInf
  let r = _keyAtom $ keyType k2
      m2 = lookSMeta inf r
  IT k2 <$> tbEditRef itRefFun m2 [Inline k2] a2 t2
tbEdit m g@(FKT apk arel2  a2) f@(FKT pk rel2  t2) = do
  inf <- askInf
  let
    ptable = lookTable inf $ _kvname m
    m2 = lookSMeta inf  $ RecordPrim $ findRefTableKey ptable rel2
    pkrel = fmap (_relOrigin. head. F.toList) .M.keys  $ _kvvalues pk
  recoverFK pkrel rel2 <$> (tbEditRef (tbRefFun rel2) m2 rel2 (liftFK g) (liftFK f))

type RelOperations b
  = (b -> TBData Key Showable
    , TBData Key Showable -> b
    , KVMetadata Key -> KV Key Showable -> KV Key Showable -> TransactionM (KV Key Showable)
    , KVMetadata Key -> KV Key Showable -> TransactionM (KV Key Showable) )

tbEditRef :: Show b => RelOperations b -> KVMetadata Key -> [Rel Key] -> FTB b -> FTB b -> TransactionM (FTB b)
tbEditRef fun@(funi,funo,edit,insert) m2 rel v1 v2 = mapInf (go rel v1 v2)
  where
    mapInf = localInf (\inf -> fromMaybe inf (HM.lookup (_kvschema m2) (depschema inf)))
    go rel2 a2 t2 = case (a2,t2) of
      (TB1 ol,TB1 l) -> do
        if G.getIndex m2 (funi ol) == G.getIndex m2 (funi l)
          then (TB1 . funo  <$> edit m2 (funi ol) (funi l))
          else (TB1 . funo <$> insert m2 (funi l))
      (LeftTB1  i ,LeftTB1 j) -> do
        LeftTB1 <$> if isNothing i
          then traverse (tbInsertRef fun m2 rel2) j
          else Tra.sequence $ liftA2 (go (Le.over relOri unKOptional <$> rel2)) i j
      (ArrayTB1 o,ArrayTB1 l) -> do
        v <- Tra.sequence (Non.zipWith (go (Le.over relOri unKArray <$> rel2)) o l)
        a <- Tra.traverse (tbInsertRef fun m2 rel2) (Non.drop (Non.length o) l)
        return $ ArrayTB1 $ Non.fromList $ F.toList v ++ a
      i -> error (show i)

tbInsertEdit :: KVMetadata Key -> Column Key Showable -> TransactionM (Column Key Showable)
tbInsertEdit m (Attr k1 k2) = return $ (Attr k1 k2)
tbInsertEdit m (Fun k1 rel k2) = return $ (Fun k1 rel k2)
tbInsertEdit m (IT k2 t2) = do
  inf <- askInf
  let RecordPrim r = _keyAtom $ keyType k2
  IT k2 <$> tbInsertRef itRefFun (tableMeta $ lookSTable inf r) [Inline k2]  t2
tbInsertEdit m f@(FKT pk rel2 t2) = do
  inf <- askInf
  let
    ptable = lookTable inf $ _kvname m
    m2 = lookSMeta inf  $ RecordPrim $ findRefTableKey ptable rel2
    pkrel = fmap (_relOrigin. head. F.toList) .M.keys  $ _kvvalues pk
  recoverFK  pkrel rel2 <$> tbInsertRef (tbRefFun rel2) m2 rel2 (liftFK f)

tbRefFun :: [Rel Key ] -> RelOperations (TBRef Key Showable)
tbRefFun rel2 = (snd.unTBRef,(\tb -> TBRef (fromMaybe (kvlist []) $ reflectFK rel2 tb,tb)),fullDiffEdit,recInsert)

tbInsertRef ::Show b => RelOperations b -> KVMetadata Key -> [Rel Key] -> FTB b -> TransactionM (FTB b)
tbInsertRef (funi,funo,_,insert) m2 rel = mapInf . go rel
  where
    mapInf = localInf (\inf -> fromMaybe inf (HM.lookup (_kvschema m2) (depschema inf)))
    go rel t2  = case t2 of
      TB1 l -> do
        TB1. funo  <$> insert m2 (funi l)
      LeftTB1 i ->
        LeftTB1 <$> traverse (go (Le.over relOri unKOptional <$> rel))  i
      ArrayTB1 l -> do
        ArrayTB1 <$>  Tra.traverse (go (Le.over relOri unKArray <$> rel) ) l

loadFKS targetTable table = do
  inf <- askInf
  let
    fkSet:: S.Set Key
    fkSet =   S.unions . fmap (S.fromList . fmap _relOrigin . (\i -> if all isInlineRel i then i else filterReflexive i ) . S.toList . pathRelRel ) $ filter isReflexive  $  (rawFKS targetTable)
    items = unKV $ table
  fks <- catMaybes <$> mapM (loadFK ( table )) (F.toList $ rawFKS targetTable)
  let
    nonFKAttrs :: [(S.Set (Rel Key) ,Column Key Showable)]
    nonFKAttrs =  M.toList $  M.filterWithKey (\i a -> not $ S.isSubsetOf (S.map _relOrigin i) fkSet) items
  return  $ kvlist (fmap snd nonFKAttrs <> fks )

loadFK :: TBData Key Showable -> SqlOperation -> TransactionM (Maybe (Column Key Showable))
loadFK table (FKJoinTable rel (st,tt) )  = do
  inf <- askInf
  let targetTable = lookTable inf tt
  (i,(_,TableRep (_,_,mtable ))) <- tableLoaderAll targetTable Nothing Nothing [] mempty Nothing
  let
    relSet = S.fromList $ _relOrigin <$> rel
    tb  = F.toList (M.filterWithKey (\k l ->  not . S.null $ S.map _relOrigin  k `S.intersection` relSet)  (unKV . tableNonRef $ table))
    fkref = joinRel2  (tableMeta targetTable) (fmap (replaceRel rel) tb ) mtable
  return $ FKT (kvlist  tb) rel   <$> fkref
loadFK table (FKInlineTable ori to )   = do
  inf <- askInf
  runMaybeT $ do
    let targetTable = lookSTable inf to
    IT rel vt  <- MaybeT . return $ M.lookup (S.singleton $ Inline   ori) (unKV $ table)
    loadVt <- lift $ Tra.traverse (loadFKS targetTable) vt
    return $ IT rel loadVt

loadFK  _ _ = return Nothing

refTablesPorj inf table page pred proj = do
  ref  <-  transactionNoLog inf $ tableLoader  table page Nothing [] pred proj
  return (idxTid ref,collectionTid ref,collectionSecondaryTid ref ,patchVar $ iniRef ref)

refTables' inf table page pred = do
  ref  <-  transactionNoLog inf $ selectFrom (tableName table ) page Nothing  [] pred
  return (idxTid ref,collectionTid ref,collectionSecondaryTid ref ,patchVar $ iniRef ref)

refTables inf table = refTables' inf table Nothing mempty

projectRec :: T.Text
 -> Maybe Int
 -> Maybe Int
 -> [(Key, Order)]
 -> [(Rel T.Text , AccessOp Showable )]
 -> TransactionM
      DBVar
projectRec t a b c p = do
  inf  <- askInf
  selectFrom  t a b c (tablePredicate inf t p)


selectFromTable :: T.Text
 -> Maybe Int
 -> Maybe Int
 -> [(Key, Order)]
 -> [(Rel T.Text , AccessOp Showable )]
 -> TransactionM
      DBVar
selectFromTable t a b c p = do
  inf  <- askInf
  selectFrom  t a b c (tablePredicate inf t p)
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
    liftIO$ atomically $ modifyTVar (mvarMap inf) (M.insert table  dbref)
    return dbref


createTableRefs :: InformationSchema -> [MutRec [[Rel Key]]] -> Table ->   Dynamic (Collection Key Showable,DBRef Key Showable)
createTableRefs inf re (Project table (Union l)) = do
  map <- liftIO$ atomically $ readTVar (mvarMap inf)
  case  M.lookup table  map of
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
          tableRel t = M.fromList $ catMaybes $ keyRel t<$> tableAttrs t
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
  case  M.lookup table map of
    Just ref -> do
      liftIO$ putStrLn $ "Loading Cached Table: " ++ T.unpack (rawName table)
      liftIO $ atomically $ readCollectionSTM ref
    Nothing -> do
      liftIO$ putStrLn $ "Loading New Table: " ++ T.unpack (rawName table)
      (iv,v) <- readTable inf "dump" table re
      map2 <- liftIO$ atomically $ readTVar (mvarMap inf)
      case M.lookup table map2 of
        Just ref ->  do
          liftIO$ putStrLn $ "Skiping Reference Table: " ++ T.unpack (rawName table)
          liftIO $ atomically $ readCollectionSTM ref
        Nothing -> do
          dbref@(DBRef {..}) <- newDBRef inf table (iv,v)
          dynFork $ forever $ updateIndex dbref
          dynFork $ forever $ updateTable inf dbref
          let
            -- Collect all nested references and add one per relation avoided duplicated refs
            childrens = M.fromListWith mappend $ fmap (fmap (\i -> [i])) $  snd $ F.foldl' (\(s,l)  fk -> (s <> S.map _relOrigin (pathRelRel fk),l ++ childrenRefsUnique inf id  s (unRecRel fk ))) (S.empty,[]) $ P.sortBy (P.comparing (RelSort . F.toList . pathRelRel)) (rawFKS table)
          -- TODO : Add evaluator for functions What to do when one of the function deps change?
          nestedFKS <- mapM (\((rinf, t),l) -> do
            liftIO $ putStrLn $ "Load table reference: from " <> (T.unpack $ tableName table) <> " to "  <> (T.unpack $ tableName t)
            o <- prerefTable rinf t
            return (l,o)) (M.toList childrens)
          newNestedFKS <- liftIO . atomically$ traverse (traverse (\DBRef {..}-> cloneTChan  patchVar)) nestedFKS
          mapM_ (\(j,var)-> dynFork $ forever $ updateReference j var table dbref) newNestedFKS
          return ((iv,v),dbref)

updateReference ::
     (v ~ Index v, PatchConstr k1 v, Foldable t, Functor t)
  => t ([RowPatch k1 v] -> TableRep k1 v -> [RowPatch k1 v])
  -> TChan [TableModificationK (TableK k1) (RowPatch k1 v)]
  -> TableK k1
  -> DBRef k1 v
  -> IO ()
updateReference j var table (DBRef {..}) =
  catchJust
    notException
    (atomically
       (do let isPatch (RowPatch (_, PatchRow _)) = True
               isPatch (BatchPatch i (PatchRow _)) = True
               isPatch _ = False
           ls <- filter isPatch . fmap tableDiff . concat <$> takeMany var
           when (not $ L.null ls) $ do
             state <- readTVar collectionState
             let patches = compact . concat $ (\f -> f ls state) <$> j
             when (not $ L.null patches) $
               writeTChan patchVar (FetchData table <$> patches)))
    (\e -> atomically (readTChan var) >>= printException e)


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
  putStrLn $ "Failed applying patch:" <> show d
  putStrLn "========================="
  putStrLn $ show (e :: SomeException)

updateTable
  :: InformationSchema -> DBRef Key Showable -> IO ()
updateTable inf (DBRef {..})
  = catchJust notException (do
            upa <- atomically $ do
                patches <- fmap concat $ takeMany patchVar
                e <- readTVar collectionState
                let cpatches = compact patches
                let out = applyUndo e (tableDiff <$> cpatches)
                traverse (writeTVar collectionState . fst) out
                return  $ zip cpatches . snd <$> out
            either (putStrLn  .("### Error applying: " ++ ) . show ) (
              mapM_ (\(m,u) -> (do
                let mmod =   m
                mmod2 <- case mmod of
                  AsyncTableModification  t (RowPatch (pk,PatchRow p))  ->  do
                    let m = tableMeta t
                    closeDynamic $ transactionNoLog inf $ do
                      l <- (patchEd $ schemaOps inf) m  [pk] p
                      wrapModification m l

                  AsyncTableModification  t (BatchPatch pk (PatchRow p))  ->  do
                    let m = tableMeta t
                    closeDynamic $ transactionNoLog inf $ do
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
            return ())  (\e -> atomically ( takeMany patchVar ) >>= (\d ->  putStrLn $ "Failed applying patch:" <> show (e :: SomeException,d)<>"\n"))

loadFKSDisk inf targetTable re = do
  let
    psort = P.sortBy (P.comparing (RelSort . F.toList . pathRelRel)) $ F.toList (rawFKS targetTable)
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

addAttr :: Ord k => S.Set k -> TBData k Showable -> Column k Showable ->  TBData k Showable
addAttr refl  i r = (\(KV i) -> KV (M.insert (keyattrs r) (r)  $ M.filterWithKey (\k _ -> not $ S.map _relOrigin k `S.isSubsetOf` refl && F.all isInlineRel k   ) i )) i


writeSchema (schema,schemaVar) = do
  varmap <- atomically $ M.toList <$>  readTVar (mvarMap schemaVar)
  putStrLn $ "Dumping Schema: " ++ T.unpack schema
  let sdir = "dump/"<> (fromString $ T.unpack schema)
  hasDir <- doesDirectoryExist sdir
  when (not hasDir ) $  do
    putStrLn $ "Create directory : " <> sdir
    createDirectory sdir
  mapM_ (uncurry (writeTable schemaVar sdir ) ) varmap



writeTable :: InformationSchema -> String -> Table -> DBRef Key Showable -> IO ()
writeTable inf s (Project i (Union l)) v = return ()
writeTable inf s t v = do
  let tname = s <> "/" <> (fromString $ T.unpack (tableName t))
  putStrLn("Dumping Table: " <> tname)
  (TableRep (_,_,iv),_) <- atomically $ readState mempty  v
  (IndexMetadata iidx ,_)<- atomically $ readIndex v
  let
    sidx = first (mapPredicate keyFastUnique)  <$> M.toList iidx
    sdata = traverse (\i ->  fmap (mapKey' keyFastUnique) .  typecheck (typeCheckTable (tablePK t)) .tableNonRef $ i) $  iv
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


fromTable origin whr = do
  inf <- askInf
  (_,(n,rep )) <- tableLoaderAll (lookTable inf origin) Nothing Nothing [] (tablePredicate inf origin whr) Nothing
  return (origin,inf,primary rep)

innerJoin
  :: TransactionM  (T.Text,InformationSchema,G.GiST (TBIndex Showable) (TBData Key Showable))
   -> [Rel T.Text]
   -> T.Text
   -> (T.Text,InformationSchema,G.GiST (TBIndex Showable) (TBData Key Showable))
   -> TransactionM  (T.Text,InformationSchema,G.GiST (TBIndex Showable) (TBData Key Showable))
innerJoin targetM srel alias (origin,pinf,emap)= do
  (target,_,amap ) <- targetM
  inf <- liftIO $ createFresh origin pinf alias (Primitive [] (RecordPrim (schemaName pinf ,target)))
  let
    rel = (\(Rel i o j ) -> Rel (lookKey inf origin i) o (lookKey inf target j)) <$>  srel
    table = lookTable inf target
    aliask = lookKey inf origin alias
    tar = S.fromList $ _relOrigin <$> rel
    joinFK :: TBData Key Showable ->  Maybe (Column Key Showable)
    joinFK m  = IT aliask <$> (joinRel2 (tableMeta table ) (fmap replaceRel $ taratt ) amap)
        where
          replaceRel (Attr k v) = (justError "no rel" $ L.find ((==k) ._relOrigin) rel,v)
          taratt = getAtt tar (tableNonRef m)
    addAttr :: Maybe (Column Key Showable) -> TBData Key Showable -> Maybe (TBData Key Showable)
    addAttr r (KV i) = (\l -> KV (M.insert (S.singleton $ Inline aliask) l i)) <$> r
    joined i = addAttr (joinFK i) i
  return $ (origin,inf,G.fromList' $ catMaybes $ (\(i,j,k) -> (,j,k) <$> joined i)<$> G.getEntries emap)


leftJoin = joinTable

joinTable
  :: TransactionM  (T.Text,InformationSchema,G.GiST (TBIndex Showable) (TBData Key Showable))
     -> [Rel T.Text]
     -> T.Text
     -> (T.Text,InformationSchema,G.GiST (TBIndex Showable) (TBData Key Showable))
     -> TransactionM  (T.Text,InformationSchema,G.GiST (TBIndex Showable) (TBData Key Showable))
joinTable  targetM srel alias (origin,pinf,emap)= do
  (target,_,amap ) <- targetM
  inf <- liftIO $ createFresh origin pinf alias (Primitive [KOptional] (RecordPrim (schemaName pinf ,target)))
  let
    rel = (\(Rel i o j ) -> Rel (lookKey inf origin i ) o (lookKey inf target j) )<$>  srel
    table = lookTable inf target
    aliask = lookKey inf origin alias
    tar = S.fromList $ _relOrigin <$> rel
    joinFK :: TBData Key Showable ->  Column Key Showable
    joinFK m  = IT aliask (LeftTB1 $ joinRel2 (tableMeta table ) (fmap replaceRel $ taratt ) amap)
            where
              replaceRel (Attr k v) = (justError "no rel" $ L.find ((==k) ._relOrigin) rel,v)
              taratt = getAtt tar (tableNonRef m)
    addAttr :: Column Key Showable -> TBData Key Showable -> TBData Key Showable
    addAttr r = (\(KV i) -> KV (M.insert ( S.singleton $ Inline aliask ) r i ))
    joined i = addAttr (joinFK i) i
  return $ (origin,inf,joined <$> emap)


--- Plugins Interface Methods
createFresh :: T.Text -> InformationSchema -> T.Text -> KType CorePrim -> IO InformationSchema
createFresh  tname inf i ty@(Primitive l  atom)  =
  case atom of
    AtomicPrim _  -> do
      let k = newKey tableO i ty
      return $ inf
          Le.& keyMapL Le.%~ (HM.insert (tname,i) k )
    RecordPrim (s,t) -> do
      let k = newKey tableO i ty
          path =  FKInlineTable k $ inlineName ty
          alterTable (Project r i) = r
                    Le.& rawAttrsR Le.%~  (k:)
                    Le.& rawFKSL Le.%~  (path:)
          alterTable r  = r
                    Le.& rawAttrsR Le.%~  (k:)
                    Le.& rawFKSL Le.%~  (path:)
      let newinf =  inf
            Le.& tableMapL . Le.ix tname Le.%~ alterTable
            Le.& keyUnique Le.%~ M.insert (keyFastUnique k) k
            Le.& keyMapL Le.%~ HM.insert (tname,i) k
      return newinf
  where tableO = lookTable inf tname

getRow (G.Idex ix) table =  do
  inf <- askInf
  let pred = AndColl $ zipWith (\v i -> PrimColl (Inline i ,[(i,Left (v,Equals))])) ix (rawPK table)
  (ref,(nidx,rep)) <-  tableLoaderAll table  Nothing Nothing [] (WherePredicate pred) Nothing
  return $safeHead (G.toList $ primary rep)

revertModification :: Int ->  TransactionM ()
revertModification idx = do
  inf <- askInf
  let table = lookTable (meta inf) "undo_modification_table"
      pred = [(keyRef "modification_id",Left (int idx,Equals))]
  (ref,(nidx,TableRep (_,_,ndata))) <- localInf (const (meta inf)) $ tableLoaderAll table  (Just 0) Nothing [] (tablePredicate (meta inf) (tableName table) pred) Nothing
  let
    mod :: RevertModification (T.Text,T.Text) (RowPatch T.Text Showable)
    mod@(RevertModification source delta)  = decodeT (mapKey' keyValue $ justError "row not found" $ safeHead $ F.toList ndata)
    targetName = snd (tableObj source)
    targetTable = lookTable inf targetName

  let op = unRowPatch $ liftRowPatch inf targetName  delta
  r <- getRow (fst op) targetTable
  traverse (\r ->
    case  snd op of
      DropRow -> do
        deleteFrom (tableMeta targetTable) r
      PatchRow p -> do
        fullEdit (tableMeta targetTable) r (apply r p)
      CreateRow p -> do
        fullInsert (tableMeta targetTable) r
          ) r
  return ()

newKey table name ty =
  let un = maximum (keyPosition <$> tableAttrs table) + 1
  in  Key name Nothing [FRead,FWrite] un Nothing (tableUnique table) ty

asyncModification m a = do
  inf <- askInf
  now <- liftIO getCurrentTime
  AsyncTableModification  (lookTable inf (_kvname m) )<$>  return a


tableModification inf m a = do
  now <- getCurrentTime
  TableModification Nothing now (snd $username inf) m<$>  return a

wrapModification m a = do
  inf <- askInf
  now <- liftIO getCurrentTime
  TableModification Nothing now (snd $username inf) (lookTable inf (_kvname m) )<$>  return a

fromR
  :: T.Text
  -> [(Rel T.Text , AccessOp Showable)]
  -> DatabaseM (View T.Text T.Text)  a   (G.GiST (TBIndex Showable) (TBData Key Showable))
fromR m f = P (WhereV (FromV m) f ) (Kleisli (\_-> fmap (\(_,_,i) -> i) $ fromTable m f))

whereR
  :: [(Rel T.Text , AccessOp Showable)]
  -> DatabaseM (View T.Text T.Text)  [(Rel T.Text , AccessOp Showable)]  (G.GiST (TBIndex Showable) (TBData Key Showable))
  -> DatabaseM (View T.Text T.Text)  () (G.GiST (TBIndex Showable) (TBData Key Showable))
whereR m (P i k) = P (WhereV i m) (proc _ -> k -< m)

lkKey table key = justError "no key" $ L.find ((key==).keyValue) (tableAttrs table)

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
                    Le.& rawAttrsR Le.%~  (k:)
                    Le.& rawFKSL Le.%~  (path:)
        alterTable r  = r
                    Le.& rawAttrsR Le.%~  (k:)
                    Le.& rawFKSL Le.%~  (path:)

sourceTable inf (FromV i) = lookTable inf i
sourceTable inf (WhereV i j) = sourceTable inf i


innerJoinR
  :: DatabaseM (View T.Text T.Text)  () (G.GiST (TBIndex Showable) (TBData Key Showable))
  -> DatabaseM (View T.Text T.Text)  () (G.GiST (TBIndex Showable) (TBData Key Showable))
  -> [Rel T.Text]
  -> T.Text
  -> DatabaseM (View T.Text T.Text)  () (G.GiST (TBIndex Showable) (TBData Key Showable))
innerJoinR (P j k) (P l n) srel alias
  = P (JoinV j l InnerJoin srel alias)
    (proc _ -> do
      kv <- k -< ()
      nv <- n -< ()
      Kleisli (\(emap,amap) -> do
        inf <- askInf
        let origin = sourceTable inf (JoinV j l InnerJoin srel alias)
            target = sourceTable inf l
        let
          rel = (\(Rel i o j) -> Rel (lkKey origin i) o (lkKey target j)) <$>  srel
          aliask = lkKey origin alias
          tar = S.fromList $ _relOrigin <$> rel
          joinFK :: TBData Key Showable ->  Maybe (Column Key Showable)
          joinFK m  = IT aliask <$> (joinRel2 (tableMeta target) (fmap replaceRel $ taratt ) amap)
            where
              replaceRel (Attr k v) = (justError "no rel" $ L.find ((==k) ._relOrigin) rel,v)
              taratt = getAtt tar (tableNonRef m)
          addAttr :: Maybe (Column Key Showable) -> TBData Key Showable -> Maybe (TBData Key Showable)
          addAttr r (KV i) = (\l -> KV (M.insert (S.singleton $ Inline aliask) l i)) <$> r
          joined i = addAttr (joinFK i) i
        return (G.fromList' $ catMaybes $ (\(i,j,k) -> (,j,k) <$> joined i)<$> G.getEntries emap)) -< (kv,nv))

leftJoinR
  :: DatabaseM (View T.Text T.Text)  () (G.GiST (TBIndex Showable) (TBData Key Showable))
  -> DatabaseM (View T.Text T.Text)  () (G.GiST (TBIndex Showable) (TBData Key Showable))
  -> [Rel T.Text]
  -> T.Text
  -> DatabaseM (View T.Text T.Text)  () (G.GiST (TBIndex Showable) (TBData Key Showable))
leftJoinR (P j k) (P l n) srel alias
  = P (JoinV j l LeftJoin srel alias)
    (proc _ -> do
      kv <- k -< ()
      nv <- n -< ()
      Kleisli (\(emap,amap) -> do
        inf <- askInf
        let
          origin = sourceTable inf (JoinV j l LeftJoin srel alias)
          target = sourceTable inf l
          rel = (\(Rel i o j ) -> Rel (lkKey origin i ) o (lkKey target j) )<$>  srel
          aliask = lkKey origin alias
          tar = S.fromList $ _relOrigin <$> rel
          joinFK :: TBData Key Showable ->  Column Key Showable
          joinFK m  = IT aliask (LeftTB1 $ joinRel2 (tableMeta target ) (fmap replaceRel $ taratt ) amap)
            where
              replaceRel (Attr k v) = (justError "no rel" $ L.find ((==k) ._relOrigin) rel,v)
              taratt = getAtt tar (tableNonRef m)
          addAttr :: Column Key Showable -> TBData Key Showable -> TBData Key Showable
          addAttr r = (\(KV i) -> KV (M.insert ( S.singleton $ Inline aliask ) r i ))
          joined i = addAttr (joinFK i) i
        return $  joined  <$> emap)-< (kv,nv))



projectV
  :: (Show k ,Monad m, Traversable t2) =>
     Parser (Kleisli m) (View i k) a1 (t2 (KV (FKey a) c))
     -> Parser
          (Kleisli (RWST (Atom (KV T.Text c), [t]) t1 () m))
          ([Union (G.AttributePath k MutationTy)],[Union (G.AttributePath k MutationTy)])
          ()
          b
     -> Parser (Kleisli m) (View i k) a1 (t2 b)
projectV  (P i (Kleisli j) )  p@(P (k,_) _ ) = P (ProjectV i  (foldl mult one k)) (Kleisli $  j  >=> (\a -> traverse (evalEnv p . (,[]) . Atom .  mapKey' keyValue) a))


