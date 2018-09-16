{-# LANGUAGE RecordWildCards, Arrows, RankNTypes, RecursiveDo,
  TypeFamilies, FlexibleContexts, OverloadedStrings, TupleSections
  #-}
module SchemaQuery.Read
  (
  -- Create fresh variables
   createFresh
  -- Database Read Only Operations
  , select
  , selectFrom
  , selectFromProj
  , getFrom
  , refTable
  , refTables
  , refTablesDesc
  , refTablesProj
  , tableLoaderAll
  , selectFromTable
  , fromTable
  , refTables'
  -- Pointer Only
  , prerefTable
  -- Cache Only Operations
  , loadFKS
  -- Transaction Operations
  , transaction
  , transactionNoLog
  -- Core
  , modifyTable
  -- Constraint Checking
  , tableCheck
  -- SQL Arrow API
  ) where
import Control.Arrow
import Control.Concurrent
import SchemaQuery.Store
import Serializer
import Text
import Control.Concurrent.STM
import Control.Exception (throw)
import qualified Control.Lens as Le
import Control.Monad.Catch
import Debug.Trace
import Control.Monad.RWS
import Control.Monad.Trans.Maybe
import Data.Either
import qualified Data.Foldable as F
import qualified Data.HashMap.Strict as HM
import qualified Data.Interval as Interval
import qualified Data.List as L
import qualified Data.Map as M
import Data.Maybe
import qualified Data.Set as S
import qualified Data.Text as T
import Data.Time
import qualified Data.Traversable as Tra
import Expression
import Query
import Reactive.Threepenny hiding (apply)
import RuntimeTypes
import Safe
import Step.Common
import Types
import qualified Types.Index as G
import Types.Patch
import Utils


estLength page size est = fromMaybe 0 page * size  +  est

projunion :: Show a=>InformationSchema -> Table -> TBData Key a -> TBData Key a
projunion inf table = res
  where
    res =  liftTable' inf (tableName table) . mapKey' keyValue. transformTable
    transformTable = mapKV transformAttr . kvFilter (\k -> S.isSubsetOf (S.map keyString $ relOutputSet k) attrs)
      where
        attrs = S.fromList $ keyValue <$> rawAttrs table
        transformAttr (Fun k l i) = Fun k l (transformKey (keyType k) (keyType nk) i)
          where nk = lkKey table (keyValue k)
        transformAttr (Attr k i ) = Attr k (transformKey (keyType k) (keyType nk) i)
          where nk = lkKey table (keyValue k)
        transformAttr (IT k i ) = IT k (transformKey (keyType k) (keyType nk) i)
          where nk = lkKey table (keyValue k)
        transformAttr (FKT r rel v) = FKT (transformTable r ) rel (transformKeyList ok nk  v)
          where ok = mergeFKRef (keyType. _relOrigin <$> rel)
                nk = mergeFKRef (keyType. lkKey table . keyValue . _relOrigin <$> rel)

mapIndex :: InformationSchema  -> Table -> IndexMetadata Key Showable -> IndexMetadata Key Showable
mapIndex inf table (IndexMetadata i)  = IndexMetadata $ M.mapKeys (liftPredicateF lookupKeyName inf (tableName table) . mapPredicate keyValue) . filterPredicate $ i
  where
    filterPredicate  = M.filterWithKey (\k _ -> isJust $ traPredicate  check  $ k)
    check i = if S.member (keyValue i) attrs  then Just i else Nothing
    attrs = S.fromList $ keyValue <$> rawAttrs table

lookIndexMetadata pred (IndexMetadata i ) = M.lookup pred i

mapIndexMetadata f (IndexMetadata v ) = IndexMetadata $ M.mapKeys (mapPredicate f )  v
mapIndexMetadataPatch f (i,j,k,l) = (mapPredicate f i,j,k,l)

mapDBVar :: InformationSchema -> Table -> DBVar2 Showable -> ([DBRef Key Showable],Tidings (IndexMetadata Key Showable),Tidings (M.Map [Key] (SecondaryIndex Key Showable),TableIndex Key Showable ))
mapDBVar inf table (DBVar2 e i l  )
  = ([e], mapIndex inf table <$> i,  (\(TableRep (_,i,j)) -> (i,createUn (tableMeta table)  (rawPK table) . fmap (projunion inf table) . G.toList $ j)) <$> l)

mergeDBRef  (IndexMetadata j,i) (IndexMetadata m,l) = (IndexMetadata $ M.unionWith (\(a,b) (c,d) -> (a+c,M.unionWith mergeToken b d))  j  m , i <>  l )

mergeDBRefT  (ref1,j ,i) (ref2,m ,l) = (ref1 <> ref2 ,liftA2 (\(IndexMetadata a) (IndexMetadata b) -> IndexMetadata $ M.unionWith (\(a,b) (c,d) -> (a+c,M.unionWith mergeToken  b d)) a b)  j  m , liftA2 (\(i,j) (i2,j2)-> (M.intersectionWith (<>)i i2 ,  j <> j2))  i l   )

refTable :: InformationSchema -> Table -> Dynamic DBVar
refTable  inf table  = do
  mmap <- liftIO$ atomically $ readTVar (mvarMap inf)
  ref <- liftIO $ lookDBVar inf mmap (tableMeta table)
  (idxTds,dbTds ) <- convertChan inf table mempty ref
  return (DBVar2 ref idxTds  dbTds )


selectFromTable
 :: T.Text
 -> Maybe Int
 -> [(Rel T.Text , AccessOp Showable )]
 -> TransactionM DBVar
selectFromTable t a p = do
  inf  <- askInf
  selectFrom t a (tablePredicate inf t p)


selectFromProj t a d p = do
  inf <- askInf
  let tb = lookTable inf t
  tableLoader tb a d p


selectFrom t a d = do
  inf <- askInf
  let tb = lookTable inf t
  tableLoader tb a d (allFields inf tb)


getFrom table allFields b = do
  inf <- askInf
  let
    m = tableMeta table
    comp = recComplement inf m b allFields
  join <$> traverse (\comp -> debugTime ("getFrom: " <> show (tableName table)) $ do
    liftIO . putStrLn $ "Loading complement"  <> (ident . renderTable $ comp)

    ((IndexMetadata fixedmap,TableRep (_,sidx,reso)),dbvar)
      <- createTable mempty (tableMeta table)
    let n = (\c -> recComplement inf m c allFields) =<< new
        new = G.lookup (G.getIndex m b) reso
    (maybe (return $ diff b =<< new) (\comp -> do
      v <- (getEd $ schemaOps inf) table (restrictTable nonFK comp) (G.getIndex m b)
      let newRow = apply b v
      resFKS  <- getFKS inf mempty table  [newRow] comp
      let
        output = (resFKS newRow)
        result = either (const Nothing) (diff b)  output
      traverse (modifyTable m [] . pure . (FetchData table .RowPatch. (G.getIndex m b,).PatchRow)) result
      traverse (\i -> liftIO . putStrLn $ "Remaining complement"  <> (ident .renderTable $ i)) $ (\c -> recComplement inf m c allFields) =<<  (applyIfChange b =<< result )
      return result ) n)) comp


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



paginateTable table pred tbf = do
  inf <- askInf
  (ref,(nidx,TableRep (_,_,ndata))) <-  tableLoaderAll table (Just 0) pred (Just tbf)
  let
    check ix (i,tb2) = do
        let
          iempty = (IndexMetadata M.empty,G.empty)
          next = ix +1
          -- Check if estimated size exist and if is bigger then the next page size (next * pagesize)
          -- or the current is already bigger or euqals the estimated
          cond = maybe False (\i -> fst i >= G.size tb2 && fst i >= next * (opsPageSize $ schemaOps inf))  (lookIndexMetadata pred i)
        output <- if cond
            then  do
              (_,(nidx,TableRep(_,_,ndata))) <- tableLoaderAll table (Just next) pred (Just tbf)
              -- Check if nothing has changed  or no more data to load
              if G.size ndata == G.size tb2
                 then return iempty
                 else check next (nidx,ndata)
            else return iempty
        return $ mergeDBRef (i,tb2) output
  snd <$> check 0 (nidx,ndata)

predicate
  :: Show a1 => [Rel (FKey (KType a1))]
     -> TBPredicate (FKey (KType a1)) a
     -> Maybe (TBPredicate (FKey (KType a1)) a)
predicate i (WherePredicate l ) =
   fmap WherePredicate (go (test (relComp i)) l)
  where
    go pred (AndColl l) = AndColl <$> nonEmpty (catMaybes $ go pred <$> l)
    go pred (OrColl l) = OrColl <$> nonEmpty (catMaybes $ go pred <$> l)
    go pred (PrimColl l) = PrimColl <$> pred l
    test f (RelAccess p i ,j)  = if p == f then Just ( i ,fmap (mapLeft (fmap (removeArray (_keyFunc $ relType  p)))) <$> j) else Nothing
    test v f = Nothing
    removeArray (KOptional :i)  o = removeArray i o
    removeArray (KArray : i)  (AnyOp o) = o
    removeArray i  o = o

getFKRef inf predtop (me,old) set (FKInlineTable  r j ) tbf =  do
    let
      rinf = maybe inf id $ HM.lookup (fst j) (depschema inf)
      table = lookTable rinf $ snd j
      nextRef :: [FTB (TBData Key Showable)]
      nextRef = catMaybes $ fmap (\i -> _fkttable  <$> kvLookup (Inline r) i ) set
    case nonEmpty (concat $ fmap F.toList nextRef) of
      Just refs -> do
        joinFK <- getFKS rinf predtop table  refs tbf
        let joined = alterAtF (Inline r) (traverse joinFK)
        return (me >=> joined,old <> S.singleton r)
      Nothing ->
        return (me ,old <> S.singleton r)

getFKRef inf predtop (me,old) v f@(FunctionField a b c) tbf
  | L.any isRelAccess c = do
    let
      evalFun :: TBData Key Showable -> Either ([TB Key Showable],[Rel Key]) (TBData Key Showable)
      evalFun i = maybe (Left $( [],S.toList  $ pathRelRel f)  )  (Right . flip addAttr i) (evaluate  a b funmap c i)
    return (me >=> evalFun ,old <> S.singleton a )
  | otherwise = return (me,old)
getFKRef  inf predtop (me,old) v f@(PluginField (ix,FPlugins s t  c)) tbf =  do
  liftIO $ putStrLn $ show (s,t)
  let
    -- Only evaluate pure plugins
    evalPlugin (PurePlugin a) v = if isJust (checkPredFull inf t (fst $ staticP a) v) then Right (maybe v (apply v)  (diff v =<<  (liftTable' inf t <$> (dynPure a $ mapKey' keyValue v)))) else Right v
    evalPlugin (DiffPurePlugin a) v = if isJust (checkPredFull inf t (traceShowId $ fst $ staticP a) v) then Right (maybe v (apply v) (liftPatch inf t <$> (dynPure a $ mapKey' keyValue v))) else Right v
    evalPlugin (StatefullPlugin j) v = F.foldl' (\i j -> evalPlugin j =<< i) (Right v) (snd <$> j)
    evalPlugin i v = Right v
  return (me >=> evalPlugin c ,old)

getFKRef inf predtop (me,old) set (RecJoin i j) tbf = getFKRef inf predtop (me,old) set j tbf

getFKRef inf predtop (me,old) set (FKJoinTable i j) tbf =  do
    let
      tar = S.fromList $ fmap _relOrigin i
      refl = S.fromList $ fmap _relOrigin $ filterReflexive i
      rinf = maybe inf id $ HM.lookup (fst j)  (depschema inf)
      table = lookTable rinf $ snd j
      genpredicate o = fmap AndColl . allMaybes . fmap (primPredicate o)  $ i
      primPredicate o k  = do
        i <- unSOptional ._tbattr  =<< lkAttr k o
        return $ PrimColl (_relTarget k ,[(_relOrigin $ _relTarget k,Left (i,Flip $ _relOperator k))])
      lkAttr k v =  kvLookup ((Inline (_relOrigin k))) (tableNonRef v)
      refs = fmap (WherePredicate .OrColl. L.nub) $ nonEmpty $ catMaybes $  genpredicate <$> set
      predm = refs <> predicate i predtop
    tb2 <-  case predm of
      Just pred -> do
        localInf (const rinf) $ paginateTable table pred tbf
      Nothing -> return (G.empty)
    let
      inj = S.difference refl old
      joinFK :: TBData Key Showable -> Either ([TB Key Showable],[Rel Key]) (Column Key Showable)
      joinFK m  = maybe (Left (atttar,i)) Right $ FKT (kvlist attinj) i <$> joinRel2 (tableMeta table ) (fmap (replaceRel i )$ atttar ) tb2
        where
          replaceRel rel (Attr k v) = (justError "no rel" $ L.find ((==k) ._relOrigin) rel,v)
          nonRef = tableNonRef m
          atttar = getAtt tar nonRef
          attinj = getAtt inj nonRef
      add :: Column Key Showable -> TBData Key Showable -> TBData Key Showable
      add r = addAttr r  . kvFilter (\k -> not $ relOutputSet k `S.isSubsetOf` refl && isInlineRel k)
      joined i = do
         fk <- joinFK i
         return $ add fk i
    return (me >=> joined,old <> refl)

mapLeft f (Left i ) = Left (f i)
mapLeft f (Right i ) = (Right i)


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
getFKS inf predtop table v tbf = fmap fst $ F.foldl' (\m f  -> m >>= (\i -> maybe (return i) (getFKRef inf predtop i v f  . head . F.toList )  (pluginCheck  f tbf) )) (return (return ,S.empty )) sorted
  where
    pluginCheck i@(PluginField _) tbf = Just mempty
    pluginCheck i tbf  = refLookup (relComp $ pathRelRel i) tbf

    sorted =  sortValues (relComp . pathRelInputs inf (tableName table)) $ rawFKS table <> functionRefs table <> pluginFKS table

rebaseKey inf t  (WherePredicate fixed ) = WherePredicate $ lookAccess inf (tableName t) . (Le.over Le._1 (fmap  keyValue) ) . fmap (fmap (first (keyValue)))  <$> fixed

mergeToken (pi,TableRef i)  (pj,TableRef j) = (pi <> pj,TableRef $ Interval.hull i  j)

type TableChannels k v =  (TChan (IndexMetadataPatch k v), TChan [TableModificationU k v])

tableLoader
    :: Table
    -> Maybe Int
    -> WherePredicate
    -> TBData Key ()
    -> TransactionM DBVar
tableLoader (Project table  (Union l)) page fixed  tbf = do
    liftIO$ putStrLn $ "start loadTable " <> show (tableName table)
    inf <- askInf
    let
      dbvarMerge i = foldr mergeDBRefT  ([],pure (IndexMetadata M.empty)  ,pure ( M.fromList $ (,G.empty)<$> _rawIndexes table,G.empty )) (mapDBVar inf table <$>i )
      dbvar (l,i,j) = DBVar2 (justError "head5" $ safeHead l) i ((\(i,j) -> TableRep (tableMeta table , i,j) :: TableRep Key Showable) <$> j)
    i <- mapM (\t -> tableLoader t page (rebaseKey inf t  fixed) (projunion inf t tbf)) l
    return $ dbvar (dbvarMerge i)
tableLoader  table page fixed tbf = do
  liftIO$ putStrLn $ "start loadTable " <> show (tableName table)
  ((fixedChan,nchan),(nidx,rep)) <- tableLoader'  table page fixed tbf

  inf <- askInf
  vpt <- lift $ convertChanTidings0 inf table (fixed ,rawPK table) rep  nchan
  idxTds <- lift $ convertChanStepper0 inf table nidx fixedChan
  dbvar <- liftIO $ prerefTable inf table
  return (DBVar2 dbvar idxTds vpt)

tableLoader'
  :: Table
   -> Maybe Int
   -> WherePredicate
   -> TBData Key ()
   -> TransactionM (TableChannels Key Showable,(IndexMetadata Key Showable,TableRep Key Showable ))
tableLoader' table  page fixed tbf = do
  pageTable (\table page token size presort predicate tbf -> do
    inf <- askInf
    let
      unestPred (WherePredicate l) = WherePredicate $ go predicate l
        where
          go pred (AndColl l) = AndColl (go pred <$> l)
          go pred (OrColl l) = OrColl (go pred <$> l)
          go pred (PrimColl l) = PrimColl $ pred l
          predicate (RelAccess i j ,_ ) = (i, maybe [] ((\a -> (a,Right (Not IsNull)))<$>) $ _relInputs i)
          predicate i  = i
    (res ,x ,o) <- (listEd $ schemaOps inf) (tableMeta table) ( restrictTable nonFK  tbf) page token size presort (unestPred predicate)
    resFKS  <- getFKS inf predicate table res tbf
    let result = fmap resFKS   res
    liftIO $ when (not $ null (lefts result)) $ do
      print ("lefts",tableName table ,lefts result)
    return (rights  result,x,o )) table page fixed tbf



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

-- TODO: Could we derive completeness information from bounds
-- or have some negative information about explored empty bounds
pageTable method table page fixed tbf = debugTime ("pageTable: " <> T.unpack (tableName table)) $ do
    inf <- askInf
    let
      m = tableMeta table
      sortList = fmap (,Desc) $  rawPK table
      pagesize = (opsPageSize $ schemaOps inf)
    ((IndexMetadata fixedmap,TableRep (_,sidx,reso)),dbvar)
      <- createTable fixed (tableMeta table)
    let
      nchan = patchVar dbvar
      fixedChan = idxChan dbvar
      pageidx =  (fromMaybe 0 page +1) * pagesize
      hasIndex = M.lookup fixed fixedmap
      readNew sq l =  do
         let pagetoken = join $ flip M.lookupLE  mp . (*pagesize) <$> page
             (_,mp) = fromMaybe (maxBound,M.empty ) hasIndex
         (resOut,token ,s ) <- method table (liftA2 (-) (fmap (*pagesize) page) (fst <$> pagetoken)) (fmap (snd.snd) pagetoken) (Just pagesize) sortList fixed tbf
         let
             -- # postFilter fetched results
             resK = if predNull fixed then resOut else G.filterRows fixed resOut
             -- # removeAlready fetched results
             diffNew i
                = case G.lookup (G.getIndex (tableMeta table) i) reso of
                   Just v -> patchRowM' (tableMeta table) v i
                   Nothing -> Just $ createRow' (tableMeta table) i
             newRes = catMaybes  $ fmap diffNew resK
         -- Only trigger the channel with new entries
         modifyTable (tableMeta table) [(fixed, estLength page pagesize s, pageidx, tbf,token)] . fmap (FetchData table) $ newRes
         let nidx = maybe (estLength page pagesize s,M.singleton pageidx (tbf,token) ) (\(s0,v) -> (estLength page pagesize  s, M.insert pageidx (tbf,token) v)) hasIndex
         if L.null newRes
            then do
              liftIO $ putStrLn $ "No new fields";
              return (nidx,reso)
            else return (nidx,snd $ F.foldl' (\i j -> either error fst $ applyGiSTChange i j) (m,reso) newRes)
    (nidx,ndata) <- case hasIndex of
      Just (sq,idx) ->
        if (sq > G.size reso)
        then case  M.lookup pageidx idx of
          Just v -> case recComplement inf (tableMeta table) (fst v) tbf of
            Just i -> do
              liftIO $ putStrLn $ "Load complement: " <> (ident . renderTable $ i)
              readNew sq i
            Nothing -> do
              liftIO $ putStrLn $ "Empty complement: " <> show (fst v)
              return ((sq,idx), reso)
          Nothing -> do
            liftIO $ putStrLn $ "No page: " <> show (pageidx)
            readNew sq tbf
        else  do
          when (sq < G.size reso) $ do
            modifyTable (tableMeta table) [(fixed, G.size reso, pageidx, tbf,TableRef $ G.getBounds (tableMeta table) (G.toList reso))] []
            liftIO $print (tableName table,fixed,G.keys reso)
          liftIO . putStrLn $ "Current table is complete: " <> show (fixed,sq,G.size reso)
          return ((max (G.size reso) sq,idx), reso)
      Nothing -> do
        liftIO $ putStrLn $ "No index: " <> show (fixed)
        let m = rawPK table
            isComplete (WherePredicate i) = match i
              where
                match (AndColl l) = product $ match <$> l
                match (OrColl l) =  sum $ match <$> l
                match (PrimColl (i,_)) = if L.elem (_relOrigin i) m then 1 else 0
            complements = catMaybes $ (\i -> recComplement inf (tableMeta table) i tbf) <$> G.toList reso
            size = G.size reso
        if fixed /= mempty && isComplete fixed == size && size /= 0
           then
            case L.null complements of
              True -> do
                liftIO $ putStrLn $ "Reusing existing complete predicate : " <> show (G.size reso)
                return ((G.size reso ,M.empty), reso)
              False -> do
                if L.length  complements  == 1
                   then do
                     liftIO $ putStrLn $ "Loading complement : " <> show (G.size reso)
                     readNew maxBound (head complements)
                   -- TODO: Compute the max of complements for now just use all required
                   else do
                     liftIO $ putStrLn $ "Loading Not unique complement : " <> show (G.size reso)
                     readNew maxBound tbf
           else do
             liftIO $ putStrLn $ "Loading empty predicate" <> show (G.size reso)
             readNew maxBound tbf
    return ((fixedChan,nchan) ,(IndexMetadata (M.insert fixed nidx fixedmap),TableRep (tableMeta table,sidx, ndata)))



tableCheck
  :: (Show t, Show a) =>
     KVMetadata (FKey (KType t))
     -> KV (FKey (KType t)) a
     -> Either [Char] (KV (FKey (KType t)) a)
tableCheck m t = if checkAllFilled then Right t else Left ("tableCheck: non nullable rows not filled " ++ show ( need `S.difference` available ,_kvname m,t))
  where
    checkAllFilled =  need `S.isSubsetOf`  available
    available = S.unions $ relOutputSet . keyattr <$> unkvlist t
    need = S.fromList $ L.filter (\i -> not (isKOptional (keyType i) || isSerial (keyType i) || isJust (keyStatic i )) )  (_kvattrs m)

dynFork a = do
  t <- liftIO $  forkIO a
  registerDynamic (killThread t)

convertChanEventIndex inf table nchan = do
    (e,h) <- newEvent
    dynFork $ forever $ catchJust notException ( do
      h =<<  atomically (takeMany nchan)
      ) (\e -> atomically (takeMany nchan) >>= (\d ->  putStrLn $ show ("error convertChanStep"  ,e :: SomeException,d)<>"\n"))
    return e

convertChanStepper0
  :: Show v =>
    InformationSchema
    -> TableK Key
    -> IndexMetadata Key v
    -> TChan (IndexMetadataPatch Key v)
    -> Dynamic
        (Tidings (IndexMetadata Key v ))
convertChanStepper0  inf table ini nchan = do
    e <- convertChanEventIndex inf table nchan
    accumT ini (flip apply <$> e)

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
      newRows =  filter (\d -> checkPatch fixed d && L.any (\i -> isNothing  (G.lookup i v)) (index d) ) m
      filterPred = nonEmpty . filter (checkPatch fixed)
      filterPredNot j = nonEmpty . catMaybes . map (\d -> if L.any (\i -> isJust (G.lookup i j) ) (index d) && not (checkPatch fixed d) then Just (rebuild (index d) DropRow )  else Nothing )
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
    evdiff <-  convertChanEvent inf table  fixed (snd <$> facts t) nchan
    ti <- liftIO getCurrentTime
    t <- accumT (0,ini) ((\i (ix,j) -> (ix+1,either error fst $ foldUndo j i )) <$> evdiff)
    return  (snd <$> t)

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



tableLoaderAll table  page fixed tbf = do
  inf <- askInf
  tableLoader'  table page fixed (fromMaybe (allFields inf table ) tbf)

tellPatches :: KVMetadata Key ->  [RowPatch Key Showable] -> TransactionM ()
tellPatches m i =
  modifyTable m [] =<< mapM (wrapModification m ) i

withDynamic :: (forall b . IO b -> IO b) -> Dynamic a -> Dynamic a
withDynamic  f i =  do
  (v,e) <- liftIO . f $ (runDynamic i) `catch` (\e -> putStrLn ("Transaction Exception: "  ++ show (e  :: SomeException)) >> throw e )
  mapM registerDynamic e
  return v

transaction :: Show a=>InformationSchema -> TransactionM a -> Dynamic a
transaction inf log = withDynamic ((transactionEd $ schemaOps inf) inf ) $ transactionNoLog inf log

loadFKS targetTable table = do
  inf <- askInf
  let
    fkSet:: S.Set Key
    fkSet =   S.unions . fmap (S.fromList . fmap _relOrigin . (\i -> if all isInlineRel i then i else filterReflexive i ) . S.toList . pathRelRel ) $ filter isReflexive  $  (rawFKS targetTable)
    items = table
  fks <- catMaybes <$> mapM (loadFK ( table )) (rawFKS targetTable)
  let
    nonFKAttrs :: [Column Key Showable]
    nonFKAttrs = filter ((\ i -> not $ S.isSubsetOf (relOutputSet i) fkSet).keyattr) (unkvlist items)
  return  $ kvlist (nonFKAttrs <> fks )

loadFK :: TBData Key Showable -> SqlOperation -> TransactionM (Maybe (Column Key Showable))
loadFK table (FKJoinTable rel (st,tt) )  = do
  inf <- askInf
  let targetTable = lookTable inf tt
  (i,(_,TableRep (_,_,mtable ))) <- tableLoaderAll targetTable Nothing mempty Nothing
  let
    relSet = S.fromList $ _relOrigin <$> rel
    tb  = F.toList (M.filterWithKey (\k l ->  not . S.null $ relOutputSet k `S.intersection` relSet)  (unKV . tableNonRef $ table))
    fkref = joinRel2  (tableMeta targetTable) (fmap (replaceRel rel) tb ) mtable
  return $ FKT (kvlist  tb) rel   <$> fkref
loadFK table (FKInlineTable ori to )   = do
  inf <- askInf
  runMaybeT $ do
    let targetTable = lookSTable inf to
    IT rel vt  <- MaybeT . return $ M.lookup (Inline   ori) (unKV $ table)
    loadVt <- lift $ Tra.traverse (loadFKS targetTable) vt
    return $ IT rel loadVt

loadFK  _ _ = return Nothing

refTablesProj inf table page pred proj = do
  ref  <-  transactionNoLog inf $ tableLoader table page pred proj
  return (idxTid ref,collectionTid ref,patchVar $ iniRef ref)

refTablesDesc inf table page pred = do
  ref  <-  transactionNoLog inf $ tableLoader table page pred (recPKDesc inf (tableMeta table) $ allFields inf table)
  return (idxTid ref,collectionTid ref,patchVar $ iniRef ref)

refTables' inf table page pred = do
  ref  <-  transactionNoLog inf $ tableLoader table page pred (allFields inf  table)
  return (idxTid ref,collectionTid ref,patchVar $ iniRef ref)

refTables inf table = refTables' inf table Nothing mempty

projectRec :: T.Text
 -> Maybe Int
 -> [(Rel T.Text , AccessOp Showable )]
 -> TransactionM
      DBVar
projectRec t a p = do
  inf  <- askInf
  selectFrom t a (tablePredicate inf t p)


tableDiffs (BatchedAsyncTableModification _ i) = concat $ tableDiffs <$> i
tableDiffs i = [tableDiff i]

printException :: Show a => SomeException -> a -> IO ()
printException e d = do
  putStrLn $ "Failed applying patch: " <> show d
  putStrLn   "================================="
  putStrLn $ show (e :: SomeException)


fromTable origin whr = do
  inf <- askInf
  (_,(n,rep )) <- tableLoaderAll (lookTable inf origin) Nothing (tablePredicate inf origin whr) Nothing
  return (origin,inf,primary rep)

select table  = do
  inf <-askInf
  (_,(_,TableRep (_,_,evMap ))) <- tableLoaderAll (lookTable inf table) Nothing mempty Nothing
  return (decodeT . mapKey' keyValue <$> evMap)


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
                    Le.& _inlineFKS Le.%~  (path:)
          alterTable r  = r
                    Le.& rawAttrsR Le.%~  (k:)
                    Le.& _inlineFKS Le.%~  (path:)
      let newinf =  inf
            Le.& tableMapL . Le.ix tname Le.%~ alterTable
            Le.& keyMapL Le.%~ HM.insert (tname,i) k
      return newinf
  where tableO = lookTable inf tname
