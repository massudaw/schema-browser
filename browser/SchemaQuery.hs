{-# LANGUAGE RecordWildCards,Arrows, RankNTypes ,RecursiveDo,TypeFamilies,FlexibleContexts,OverloadedStrings,TupleSections #-}
module SchemaQuery
  (createUn
  ,takeMany
  ,tablePK
  ,resetCache
  ,writeSchema
  ,createFresh
  ,fixfilters
  ,fixrel
  ,childrenRefsUnique
  ,selectFromTable
  ,tablePredicate
  ,refTables'
  ,lookAttrM
  ,lookRef
  ,lookAttr'
  ,lookAttrs'
  ,refTables
  ,tellPatches
  ,selectFrom
  ,updateFrom
  ,patchFrom
  ,insertFrom
  ,getFrom
  ,deleteFrom
  ,prerefTable
  ,refTable
  ,loadFKS
  ,fullDiffInsert
  ,fullDiffEdit
  ,tableLoader'
  ,fullDiffEditInsert
  ,transaction
  ,transactionNoLog
  ,patchCheckInf
  ,patchCheck
  ,tableCheck
  ,fromR
  ,innerJoinR
  ,leftJoinR
  ,projectV
  )where
import Graphics.UI.Threepenny.Core (mapEventDyn)

import RuntimeTypes
import qualified Data.Interval as Interval
import Environment
import Control.Exception (throw)
import Data.Unique
import PStream
import Data.Semigroup(Semigroup)
import Control.Arrow (first)
import Control.DeepSeq
import Step.Host
import Expression
import System.Directory
import Data.String (fromString)
import qualified Data.Binary as B
import Types.Primitive
import Types.Index (checkPred)
import Control.Concurrent
import Control.Monad.Catch
import Control.Arrow
import Default

import qualified Data.GiST.BTree as G
import Control.Monad.RWS
import Step.Common

import Data.Time
import qualified Control.Lens as Le
import Database.PostgreSQL.Simple
import Data.Either
import Control.Concurrent.Async
import Control.Monad.Trans.Maybe
import qualified Data.Poset as P
import Debug.Trace
import Data.Ord
import GHC.Stack
import qualified NonEmpty as Non
import Safe
import Data.Functor.Identity
import Control.Concurrent.STM
import Reactive.Threepenny hiding (apply)
import Utils
import qualified Data.Map as M
import qualified Data.HashMap.Strict as HM
import qualified Data.Set as S
import qualified Data.Traversable as Tra
import qualified Data.List as L
import qualified Data.Foldable as F
import Types
import Types.Patch
import Query
import qualified Types.Index as G
import Data.Maybe
import qualified Data.Text as T

--
--  MultiTransaction Postgresql insertOperation
--


lookDBVar inf mmap table =
    case M.lookup table mmap of
      Nothing ->  do
        (dyn ,fin) <- liftIO $ runDynamic $ snd <$> createTableRefs inf [] table
        return dyn
      Just i-> return i

estLength page size est = fromMaybe 0 page * size  +  est

resetCache :: InformationSchema -> IO ()
resetCache inf = do
  atomically $ modifyTVar (mvarMap inf) (const M.empty)


prerefTable :: InformationSchema -> Table -> Dynamic (DBRef KeyUnique Showable)
prerefTable  inf table  = do
  mmap <- liftIO $ atomically $ readTVar (mvarMap inf)
  lookDBVar inf mmap table

projunion :: InformationSchema -> Table -> TBData Key Showable -> TBData Key Showable
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
  ref <- lookDBVar inf mmap table
  (idxTds,dbTds ) <- convertChan inf table mempty ref
  return (DBVar2 ref idxTds  (primary <$> dbTds) (secondary <$>dbTds) )


secondary (m,s,g) = s
primary (m,s,g) = g


createUn :: (Show k ,Ord k) => KVMetadata k -> [k] -> [TBData k Showable] -> G.GiST (G.TBIndex Showable) (TBData k Showable)
createUn m un   =  G.fromList  (justError ("empty"  ++ show un) .transPred) .  filter (isJust . transPred)
  where transPred =   G.notOptionalM . G.getUnique m un




selectFrom t a b c d = do
  inf <- askInf
  tableLoader (lookTable inf t) a b c d

updateFrom  m a  pk b = do
  inf <- askInf
  let
    kv = apply a b
    overloaded  = M.lookup (_kvschema m ,_kvname m) overloadedRules
    overloadedRules = (rules $ schemaOps inf)
    isUpdate (i,UpdateRule _ ) =  i (mapKey' keyValue a)
    isUpdate _ = False
  v <- case L.find isUpdate =<< overloaded of
    Just (_,UpdateRule i) ->  i a b
    Nothing -> (editEd $ schemaOps inf)m  a pk b
  tellPatches m (pure v)
  return v

patchFrom m  (pk,PatchRow a)   = do
  inf <- askInf
  l <- (patchEd $ schemaOps inf)  m pk a
  tellPatches m (pure l)
  return l

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


getFrom a b = do
  inf <- askInf
  (getEd $ schemaOps inf)  a b

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


paginateTable table pred = do
    (ref,(nidx,(_,_,ndata))) <-  tableLoader' table  (Just 0) Nothing [] pred
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
                (_,(nidx,(_,_,ndata))) <- tableLoader' table  (Just next  ) Nothing []  pred
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

getFKRef inf predtop rtable (me,old) set (FKInlineTable  r j ) =  do
    let
      rinf = maybe inf id $ HM.lookup (fst j) (depschema inf)
      table = lookTable rinf $ snd j
      editAttr fun (KV i) = fmap KV (flip Le.at (traverse ((Le.traverseOf ifkttable (traverse fun)))) (S.singleton $ Inline r)  i )
      nextRef :: [FTB (TBData Key Showable)]
      nextRef= fmap (\i -> _fkttable $ justError "no it" $ M.lookup (S.singleton $ Inline r) (_kvvalues  i) ) set

    case nonEmpty (concat $ fmap F.toList nextRef) of
      Just refs -> do
        joinFK <- getFKS rinf predtop table  refs
        let joined = editAttr joinFK
        return (me >=> joined,old <> S.singleton r)
      Nothing ->
        return (me ,old <> S.singleton r)

getFKRef inf predtop rtable (me,old) v (FunctionField a b c) = do
  let
    addAttr :: TBData Key Showable -> Either ([TB Key Showable],[Rel Key]) (TBData Key Showable)
    addAttr i = Right $ maybe i (\r -> (\(KV i) -> KV (M.insert (keyattrs r) r i) ) i) (evaluate  a b funmap c i)
  return (me >=> addAttr ,old <> S.singleton a )

getFKRef inf predtop rtable (me,old) set (RecJoin i j) = getFKRef inf predtop rtable (me,old) set j

getFKRef inf predtop rtable (me,old) set (FKJoinTable i j) =  do
    let
        rinf = maybe inf id $ HM.lookup (fst j)  (depschema inf)
        table = lookTable rinf $ snd j
        genpredicate (KV o) = fmap AndColl . allMaybes . fmap (primPredicate o)  $ i
        primPredicate o k  = do
          i <- unSOptional (_tbattr (lkAttr k o))
          return $ PrimColl (Inline (_relTarget k) ,[(_relTarget k,Left (i,Flip $ _relOperator k))])
        lkAttr k = justError "no attr" . M.lookup (S.singleton (Inline (_relOrigin k)))
        refs = fmap (WherePredicate .OrColl. L.nub) $ nonEmpty $ catMaybes $  genpredicate <$> set
        predm = refs <> predicate i predtop
    tb2 <-  case predm of
      Just pred -> do
        localInf (const rinf) $ paginateTable table pred
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
     -> TransactionM
        (TBData Key Showable -> Either
              ([TB Key Showable],[Rel Key])
              (TBData Key Showable))
getFKS inf predtop table v = fmap fst $ F.foldl' (\m f  -> m >>= (\i -> getFKRef inf predtop  table i v f)) (return (return ,S.empty )) sorted
  where
    sorted = P.sortBy (P.comparing (RelSort . F.toList .  pathRelRel))  (rawFKS table)

rebaseKey inf t  (WherePredicate fixed ) = WherePredicate $ lookAccess inf (tableName t) . (Le.over Le._1 (fmap  keyValue) ) . fmap (fmap (first (keyValue)))  <$> fixed

mergeToken (TableRef i)  (TableRef j) = TableRef (Interval.hull i  j)

type TableChannels k v =  (TChan (WherePredicateK k ,Int,Int,PageTokenF v),TChan [TableModificationU k v ])

tableLoader :: Table -> Maybe Int -> Maybe Int -> [(Key,Order)] -> WherePredicate
    -> TransactionM DBVar
tableLoader (Project table  (Union l)) page size presort fixed  = do
    liftIO$ putStrLn $ "start loadTable " <> show (tableName table)
    inf <- askInf
    let
      dbvarMerge i = foldr mergeDBRefT  ([],pure (IndexMetadata M.empty)  ,pure G.empty, pure (M.fromList $ (,G.empty)<$> _rawIndexes table) ) (mapDBVar inf table <$>i )
      dbvar (l,i,j,p) = DBVar2 (justError "head5" $ safeHead l) i j p
    i <- mapM (\t -> tableLoader t page size presort (rebaseKey inf t  fixed)) l
    return $ dbvar (dbvarMerge i)
tableLoader  table page size presort fixed = do
  ((fixedChan,nchan),(nidx,(_,sidx,ndata))) <- tableLoader'  table page size presort fixed
  let
    tableU = fmap keyFastUnique table
    fixedU = mapPredicate keyFastUnique fixed

  inf <- askInf
  vpt <- lift $ convertChanTidings0 inf table (fixed ,rawPK table) (tableMeta table,sidx ,ndata) nchan
  idxTds <- lift $ convertChanStepper0 inf table nidx fixedChan
  dbvar <- lift $ prerefTable inf table
  return (DBVar2 dbvar idxTds (fmap primary vpt) (fmap secondary vpt))

tableLoader' :: Table -> Maybe Int -> Maybe Int -> [(Key,Order)] -> WherePredicate
             -> TransactionM (TableChannels KeyUnique Showable,(IndexMetadata Key Showable,TableRep Key Showable ))
tableLoader' table  page size presort fixed = do
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
          tbf = allRec' (tableMap inf) table
        (res ,x ,o) <- (listEd $ schemaOps inf) (tableMeta table) (tableNonRef tbf) page token size presort (unestPred predicate)
        resFKS  <- getFKS inf predicate table res
        let result = fmap resFKS   res
        liftIO $ when (not $ null (lefts result)) $ do
          print ("lefts",tableName table ,lefts result)
        return (rights  result,x,o )) table page size presort fixed


readTableFromFile
  :: InformationSchemaKV Key Showable
     -> T.Text
     -> TableK Key
     -> IO (Maybe
             (IndexMetadata KeyUnique Showable, [TBData KeyUnique Showable]))
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
               return $ (Just (IndexMetadata $ M.fromList  m   ,  g) :: Maybe ( IndexMetadata KeyUnique Showable ,[TBData KeyUnique Showable])))  f
      else return Nothing


predNull (WherePredicate i) = L.null i

filterfixedS table fixed (s,v)
  = if predNull fixed
       then v
       else queryCheckSecond (fixed ,rawPK table) (tableMeta table,s,v)


childrenRefsUnique
  :: InformationSchema
  -> TableK KeyUnique
  -> TableRep  KeyUnique Showable
  -> (SqlOperation , [RowPatch KeyUnique Showable])
  -> [RowPatch KeyUnique Showable]
childrenRefsUnique  inf table (m,sidxs,base) (FKJoinTable rel j ,evs)  =  concat $ (\i -> search  i  sidx) <$>  evs
  where
    rinf = maybe inf id $ HM.lookup (fst j)  (depschema inf)
    relf = fmap keyFastUnique <$> filterReflexive rel
    jtable = lookTable rinf $ snd j
    sidx = M.lookup (keyFastUnique . _relOrigin  <$> rel) sidxs
    search (RowPatch p@(G.Idex v,PatchRow pattr)) idxM
      = case idxM of
        Just idx -> concat $ convertPatch  <$> resIndex idx
        Nothing -> concat $ convertPatch <$> resScan base
      where
        predK = WherePredicate $ AndColl $ ((\(Rel o op t) -> PrimColl (RelAccess rel (Inline t) ,  [(t,Left (justError "no ref" $ unSOptional $ fmap create $ justError "no value" $ atMay v (justError "no key" $  t`L.elemIndex` rawPK jtable),op))] )) <$> rel  )
        predKey =  mapPredicate keyFastUnique predK
        resIndex idx = fmap (\(p,_,i) -> (p,i)) $ G.projectIndex (keyFastUnique . _relOrigin <$> rel) predKey idx
        resScan idx = catMaybes $ fmap (\(i,t) -> ((G.getIndex m i,t), G.getUnique (tableMeta table) (fmap (keyFastUnique._relOrigin) rel) i)) . (\i->  (i,) <$> G.checkPredId i predKey) <$> G.toList idx
        convertPatch ((pk,ts),G.Idex fks) = (\t -> RowPatch (pk ,PatchRow  [PFK relf [] (recurseAttr t pattr)]) ) <$> ts
        taggedRef i p =  go i
          where
            go (G.ManyPath j ) = PatchSet $ go <$> j
            go (G.NestedPath i j ) = matcher i (go j)
            go (G.TipPath j ) = PAtom p
            matcher (PIdIdx ix )  = PIdx ix . Just
            matcher PIdOpt   = POpt . Just
        recurseAttr (G.PathForeign  _ i ) p = taggedRef i p
        recurseAttr (G.PathAttr _ i ) p = taggedRef i p
        recurseAttr i p = error (show i)


pageTable method table page size presort fixed = do
    inf <- askInf
    let mvar = mvarMap inf
        tableU = fmap keyFastUnique table
        fixedU = mapPredicate keyFastUnique fixed
        defSort = fmap (,Desc) $  rawPK table
        sortList  = if L.null presort then defSort else  presort
        pagesize = maybe (opsPageSize $ schemaOps inf) id size
    mmap <- liftIO . atomically $ readTVar mvar
    predbvar <- lift $ lookDBVar inf mmap table
    ((IndexMetadata fixedmap,(_,sidx,reso)),dbvar)
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
             let res =  mapKey' keyFastUnique <$> resK
                 -- # postFilter fetched results
                 resK = if predNull fixed then resOut else G.filterRows fixed resOut
                 -- # removeAlready fetched results
                 newRes = filter (\i -> isNothing $ G.lookup (G.getIndex (tableMeta table) i) reso) resK
             -- Add entry for this query
             putIdx (idxChan dbvar) (fixedU, estLength page pagesize s, pageidx, token)
             -- Only trigger the channel with new entries
             traverse (\i ->  putPatch (patchVar dbvar) (F.toList $ FetchData table . createRow' (tableMeta table)  <$>  i)) $ nonEmpty newRes
             return $ if L.null newRes then
                (maybe (estLength page pagesize s,M.singleton pageidx token ) (\(s0,v) -> (estLength page pagesize  s, M.insert pageidx token v)) hasIndex,reso)
                    else
                (maybe (estLength page pagesize s,M.singleton pageidx token ) (\(s0,v) -> (estLength page pagesize  s, M.insert pageidx token v)) hasIndex,createUn (tableMeta tableU) (rawPK tableU) res <> reso)
           else do
             return (fromMaybe (0,M.empty) hasIndex, reso)
         return $ (M.insert fixedU nidx fixedmap, sidx,ndata )
    (nidx,sidx,ndata) <-  case hasIndex of
          Just (sq,idx) -> case  M.lookup pageidx idx of
             Just v -> return (fixedmap , sidx,reso)
             Nothing -> readNew sq
          Nothing -> readNew maxBound
    return ((fixedChan,nchan) ,(mapIndexMetadata (recoverKey inf ) (IndexMetadata nidx) ,(tableMeta table,mapSecondary (recoverKey inf) sidx,fmap (mapKey' (recoverKey inf)) ndata)))

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
  return (apply ini patches,nchan)

readState
  :: (Show k ,Ord k ,NFData k)
      => (TBPredicate k Showable, [k])
      -> DBRef k Showable
      -> STM (TableRep k Showable , TChan [TableModificationU k Showable])
readState fixed dbvar = do
  (m,s,v) <-readTVar (collectionState dbvar)
  chan <- cloneTChan (patchVar dbvar)
  patches <- tryTakeMany chan
  let
    filterPred = filter (checkPatch  fixed)
    update l v = apply l v
    fv = filterfixedS (dbRefTable dbvar) (fst fixed) (s,v)
    result= update (m,s,fv) (filterPred  $ fmap tableDiff $ concat patches)
  return (result,chan)


-- Default Checks

patchCheckInf ::  InformationSchema -> KVMetadata Key -> TBIdx Key Showable ->  Either String (TBIdx Key Showable)
patchCheckInf inf m i = if isJust (createIfChange (defp  ++ i) :: Maybe (TBData Key Showable)) then Right i else Left ("patchCheck: non nullable rows not filled " ++ show ( need `S.difference` available ))
  where
    defp = maybe (deftable inf  (lookTable inf (_kvname m  ))) (defaultTable inf (lookTable inf (_kvname m  )))  (createIfChange i)
    available = S.unions $ S.map _relOrigin . index <$> i
    need = S.fromList $ L.filter (\i -> not (isKOptional (keyType i) || isSerial (keyType i) || isJust (keyStatic i )) )  (kvAttrs m)


patchCheck m (s,i) = if checkAllFilled then Right (s,i) else Left ("patchCheck: non nullable rows not filled " ++ show ( need `S.difference` available ))
  where
      checkAllFilled =  need `S.isSubsetOf`  available
      available = S.unions $ S.map _relOrigin . index <$> i
      need = S.fromList $ L.filter (\i -> not (isKOptional (keyType i) || isSerial (keyType i) || isJust (keyStatic i )) )  (kvAttrs m)

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
            h (mapIndexMetadataPatch (recoverKey inf) <$> a )) (\e -> atomically (takeMany nchan) >>= (\d ->  putStrLn $ show ("error convertChanStep"  ,e :: SomeException,d)<>"\n"))
    return e
convertChanStepper0
  :: Show v =>
    InformationSchema
    -> TableK Key
    -> IndexMetadata Key v
    -> TChan (WherePredicateK KeyUnique,Int,Int,PageTokenF v)
    -> Dynamic
        (Tidings (IndexMetadata Key v ))
convertChanStepper0  inf table ini nchan = do
    e <- convertChanEventIndex inf table nchan
    toTidings <$> accumS  ini e

convertChan
  :: InformationSchema
  -> TableK Key
     -> (TBPredicate Key Showable, [Key])
     -> DBRef KeyUnique Showable
     -> Dynamic
      (Tidings (IndexMetadata Key Showable ),Tidings (TableRep Key Showable))
convertChan inf table fixed dbvar = do
  ((ini,result),cloneddbvar) <- liftIO $ atomically $
    cloneDBVar (first (mapPredicate keyFastUnique ) $ fmap keyFastUnique <$> fixed) dbvar
  (,) <$> convertChanStepper0 inf table (mapIndexMetadata (recoverKey inf) ini) (idxChan cloneddbvar)
      <*> convertChanTidings0 inf table fixed (mapTableRep (recoverKey inf) result ) (patchVar cloneddbvar)

convertChanEvent
  ::
    InformationSchema -> TableK Key
     -> (TBPredicate Key Showable, [Key])
     -> Behavior (TableRep Key Showable)
     -> TChan [TableModificationU KeyUnique Showable]
     -> Dynamic
          (Event [RowPatch Key Showable])
convertChanEvent inf table fixed bres chan = do
  (e,h) <- newEvent
  dynFork $ forever $ catchJust notException (do
    ml <- atomically $ takeMany chan
    (_,_,v) <- currentValue bres
    let
      meta = tableMeta table
      m = firstPatchRow (recoverKey inf) . tableDiff <$> concat  ml
      newRows =  filter (\d -> checkPatch fixed d && isNothing (G.lookup (index d) v) ) m
      filterPred = nonEmpty . filter (checkPatch fixed)
      filterPredNot j = nonEmpty . catMaybes . map (\d -> if isJust (G.lookup (index d) j) && not (checkPatch fixed d) then Just (RowPatch (index d,DropRow ))  else Nothing )
      oldRows = filterPredNot v m
      patches = oldRows <> filterPred m
    traverse  h patches
    return ()) (\e -> atomically (takeMany chan) >>= (\d -> putStrLn $  show ("error convertChanEvent"  ,e :: SomeException,d)<>"\n"))
  return e


mapTableRep f (m,i,j)= (f <$> m, mapSecondary f i, mapPrimary f j)
mapSecondary f = M.mapKeys (fmap f) . fmap (fmap (fmap (fmap (G.mapAttributePath f))))
mapPrimary  f = fmap (mapKey' f)


convertChanTidings0
  :: InformationSchema
  -> TableK Key
  -> (TBPredicate Key Showable, [Key])
  -> TableRep Key Showable
  -> TChan [TableModificationU KeyUnique Showable]
  -> Dynamic (Tidings (TableRep Key Showable))
convertChanTidings0 inf table fixed ini nchan = mdo
    evdiff <-  convertChanEvent inf table  fixed (facts t) nchan
    s <- accumS ini evdiff
    let t = toTidings s
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


fullDiffInsert :: KVMetadata Key ->TBData Key Showable -> TransactionM  (RowPatch Key Showable)
fullDiffInsert k1 v1 = do
   inf <- askInf
   ret <- KV <$>  Tra.traverse (tbInsertEdit k1) (unKV v1)
   mod <- insertFrom k1 ret
   return mod


fullInsert :: KVMetadata Key -> TBData Key Showable -> TransactionM  (TBData Key Showable)
fullInsert k1  v1 = do
   inf <- askInf
   ret <- KV <$>  Tra.traverse (tbInsertEdit k1 )  (unKV v1)
   let tb  = lookTable inf (_kvname k1)
   (_,(_,(_,_,l))) <- tableLoader'  tb Nothing Nothing [] mempty
   if  (isNothing $ join $ fmap (flip G.lookup l) $ G.tbpredM k1  ret ) && rawTableType tb == ReadWrite
      then catchAll (do
        tb  <- insertFrom k1 ret
        return $ createRow tb) (\e -> liftIO $ do
          throw e
          putStrLn $ "failed insertion: "  ++ (show (e :: SomeException))
          return ret)
      else do
        return ret

noEdit :: KVMetadata Key -> TBData Key Showable -> TBData Key Showable -> TransactionM  (TBData Key Showable)
noEdit k1 v1 v2  = do
  KV <$>  Tra.sequence ( M.intersectionWith (tbDiffEditInsert k1) (unKV v1) (unKV v2))


noInsert :: KVMetadata Key -> TBData Key Showable -> TransactionM  (TBData Key Showable)
noInsert k1 v1   = do
  KV <$>  Tra.traverse (tbInsertEdit k1)  (unKV v1)


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
        mmap <- readTVar (mvarMap inf)
        return $ justError (show k) $ M.lookup (fst k) mmap
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

fullDiffEditInsert :: KVMetadata Key -> TBData Key Showable -> TBData Key Showable -> TransactionM (TBData Key Showable)
fullDiffEditInsert k1 old v2 = do
   inf <- askInf
   edn <-  KV <$>  Tra.sequence (M.intersectionWith (tbDiffEditInsert k1)  (unKV old) (unKV v2))
   when (isJust $ diff (tableNonRef old) (tableNonRef edn)) $ void $ do
      traverse (updateFrom  k1 old  (G.getIndex k1 edn)) (diff old edn)
   return edn

fullDiffEdit :: KVMetadata Key -> TBData Key Showable -> TBData Key Showable -> TransactionM (TBData Key Showable)
fullDiffEdit = fullDiffEditInsert


tbDiffEditInsert :: KVMetadata Key ->  Column Key Showable -> Column Key Showable -> TransactionM (Column Key  Showable)
tbDiffEditInsert k1 i j
  | i == j =  return j
  | isJust (diff i  j) = tbEdit k1 i j
  | otherwise = tbInsertEdit  k1 j


tbEdit :: KVMetadata Key -> Column Key Showable -> Column Key Showable -> TransactionM (Column Key Showable)
tbEdit m (Fun _ _ _ ) (Fun k1 rel k2)= return $ (Fun k1 rel k2)
tbEdit m (Attr _ _ ) (Attr k1 k2)= return $ (Attr k1 k2)
tbEdit m (IT a1 a2) (IT k2 t2) = do
  inf <- askInf
  let r = _keyAtom $ keyType k2
      m2 = lookSMeta inf r
      fun =(id,id,noEdit,noInsert)
  IT k2 <$> tbEditRef fun m2 [Inline k2] a2 t2
tbEdit m g@(FKT apk arel2  a2) f@(FKT pk rel2  t2) = do
  inf <- askInf
  let
    ptable = lookTable inf $ _kvname m
    m2 = lookSMeta inf  $ RecordPrim $ findRefTableKey ptable rel2
    pkrel = fmap (_relOrigin. head. F.toList) .M.keys  $ _kvvalues pk
    fun = (snd.unTBRef,(\tb -> TBRef (fromMaybe (kvlist []) $ reflectFK rel2 tb,tb)),fullDiffEdit,fullInsert)
  recoverFK pkrel rel2 <$> (tbEditRef fun m2 rel2 (liftFK g) (liftFK f))

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
      fun =(id,id,noEdit,noInsert)
  IT k2 <$> tbInsertRef fun  (tableMeta $ lookSTable inf r) [Inline k2]  t2
tbInsertEdit m f@(FKT pk rel2 t2) = do
  inf <- askInf
  let
    ptable = lookTable inf $ _kvname m
    m2 = lookSMeta inf  $ RecordPrim $ findRefTableKey ptable rel2
    pkrel = fmap (_relOrigin. head. F.toList) .M.keys  $ _kvvalues pk
    fun = (snd.unTBRef,(\tb -> TBRef (fromMaybe (kvlist []) $ reflectFK rel2 tb,tb)),fullDiffEdit,fullInsert)
  recoverFK  pkrel rel2 <$> tbInsertRef fun m2 rel2 (liftFK f)

tbInsertRef ::Show b => RelOperations b -> KVMetadata Key -> [Rel Key] -> FTB b -> TransactionM (FTB b)
tbInsertRef (funi,funo,_,insert) m2 rel = mapInf . go rel
  where
    mapInf = localInf (\inf -> fromMaybe inf (HM.lookup (_kvschema m2) (depschema inf)))
    go rel t2  = case t2 of
      TB1 l -> do
        (TB1. funo  <$> insert m2 (funi l))
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
  (i,(_,(_,_,mtable ))) <- tableLoader' targetTable Nothing Nothing [] mempty
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

refTables' inf table page pred = do
  (ref)  <-  transactionNoLog inf $ selectFrom (tableName table ) page Nothing  [] pred
  return (idxTid ref,collectionTid ref,collectionSecondaryTid ref ,patchVar $ iniRef ref)

refTables inf table = refTables' inf table Nothing mempty

lookRef k = _fkttable . lookAttrs' k

lookAttrs' k = err . lookAttrsM k
  where
      err= justError ("no attr " <> show k )

lookAttr' k = _tbattr . err . lookAttrM k
  where
      err= justError ("no attr " <> show k )

lookAttrsM k m = M.lookup (S.fromList k) ta
    where
      ta = M.mapKeys (S.map (keyValue._relOrigin)) (unKV m)

lookAttrM k =  lookAttrsM [k]

fixrel (Inline  i,op) = (Inline i,[(i,op)])
fixrel (RelAccess i j , op) = (RelAccess i (fst sub),snd sub)
  where sub = fixrel . (,op) $ j
fixrel (i,op) = (i,[])

fixfilters (IProd j i,op) = (IProd j i,[(i,op)])
fixfilters (Nested i j , op) = (Nested i (fmap fst sub),concat $  fmap snd sub)
  where sub = fixfilters . (,op) <$> j
fixfilters (i,op) = (i,[])

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

tablePredicate inf t p = (WherePredicate $ AndColl $ fmap (lookAccess inf t). PrimColl .fixrel <$> p)

createTableRefs :: InformationSchema -> [MutRec [[Rel Key]]] -> Table ->   Dynamic (Collection KeyUnique Showable,DBRef KeyUnique Showable)
createTableRefs inf re (Project i (Union l)) = do
  let table = fmap keyFastUnique i
  map <- liftIO$ atomically $ readTVar (mvarMap inf)
  case  M.lookup i map of
    Just ref  ->  do
      liftIO$ putStrLn $ "Loading Cached Table: " ++ T.unpack (rawName i)
      liftIO $ atomically $ do
        idx <- readTVar (idxVar ref )
        (_,_,st) <- readTVar (collectionState ref)
        return (( idx,  st) ,ref)
    Nothing -> do
      liftIO$ putStrLn $ "Loading Union Table: " ++ T.unpack (rawName i)
      let keyRel t k = do
              let look i = HM.lookup (tableName i , keyValue k) (keyMap inf)
              new <- look i
              old <- look t
              return (keyFastUnique old,keyFastUnique new)
          tableRel t = M.fromList $ catMaybes $ keyRel t<$> tableAttrs t
      res <- mapM (\t -> do
        ((IndexMetadata idx,sdata),ref) <- createTableRefs inf re t
        return ((IndexMetadata $ M.mapKeys ( mapPredicate (\k -> fromMaybe k (M.lookup k (tableRel t)))) $ idx, (mapKey' (\k -> fromMaybe k (M.lookup k (tableRel t))) <$> G.toList sdata)),ref)) l
      let
        (uidx,udata) = foldr mergeDBRef (IndexMetadata M.empty,[]) (fst <$> res)
        udata2 = createUn (tableMeta table) (rawPK table) udata
        sidx :: M.Map [KeyUnique] (SecondaryIndex KeyUnique Showable)
        sidx = M.fromList $ fmap (\un-> (un ,G.fromList' ( fmap (\(i,n,j) -> ((G.getUnique (tableMeta table)un  i,[]),n,j)) $ G.getEntries udata2))) (L.delete (rawPK table) $ _rawIndexes table )

      midx <-  liftIO$ atomically$ newTVar uidx
      collectionState <-  liftIO$ atomically $ newTVar  (tableMeta table,sidx, udata2)
      mdiff <-  liftIO$ atomically $ newBroadcastTChan
      nmdiff <- liftIO$ atomically $ dupTChan mdiff
      chanidx <-  liftIO$ atomically $ newBroadcastTChan
      nchanidx <- liftIO$ atomically $ dupTChan chanidx
      refSize <- liftIO $ atomically $  newTVar 1
      let dbref = DBRef table 0 refSize nmdiff midx nchanidx collectionState
      liftIO$ atomically $ modifyTVar (mvarMap inf) (M.insert i  dbref)
      return ((uidx,udata2) ,dbref)
createTableRefs inf re tableK = do
  let table = fmap keyFastUnique tableK
      i = tableK
  map <- liftIO$ atomically $ readTVar (mvarMap inf)
  case  M.lookup tableK map of
    Just ref -> do
      liftIO$ putStrLn $ "Loading Cached Table: " ++ T.unpack (rawName i)
      liftIO $ atomically $ do
        idx <- readTVar (idxVar ref )
        (_,_,st) <- readTVar (collectionState ref)
        return (( idx,  st) ,ref)
    Nothing -> do
      liftIO$ putStrLn $ "Loading New Table: " ++ T.unpack (rawName i)
      let
          diffIni :: [TBIdx KeyUnique Showable]
          diffIni = []
      mdiff <-  liftIO$ atomically $ newBroadcastTChan
      chanidx <-  liftIO$ atomically $ newBroadcastTChan
      nchanidx <- liftIO$ atomically $ dupTChan chanidx
      nmdiff <- liftIO$ atomically $ dupTChan mdiff
      (iv,v) <- readTable inf "dump" i re
      midx <-  liftIO$ atomically$ newTVar iv
      refSize <- liftIO $ atomically $  newTVar 1
      depmap <- liftIO $ atomically $ readTVar (mvarMap inf )
      let
        move (FKJoinTable i j)  =  do
              let rtable = M.lookup (lookSTable inf j) depmap
                  rinf = fromMaybe inf $ HM.lookup (fst j) (depschema inf)
              Just . (FKJoinTable i j,)<$> maybe (fmap snd $ createTableRefs rinf re (lookSTable inf j)) return rtable
        move (FKInlineTable _ _) = return Nothing
        move i = return Nothing
        sidx :: M.Map [KeyUnique] (SecondaryIndex KeyUnique Showable)
        sidx = M.fromList $ fmap (\un-> (un ,G.fromList' ( fmap (\(i,n,j) -> ((G.getUnique (tableMeta table)un i,[]),n,j)) $ G.getEntries v))) (L.delete (rawPK table) $ _rawIndexes table )

      nestedFKS <-   (fmap catMaybes $ traverse move $   F.toList (rawFKS i))
      newNestedFKS <- liftIO . atomically$ traverse (traverse (cloneTChan . patchVar)) nestedFKS
      collectionState <-  liftIO$ atomically $ newTVar  (tableMeta table,sidx,v)
      mapM_ (\(j,var)-> dynFork $ forever $ catchJust notException(do
          atomically (do
              let isPatch (RowPatch (_,PatchRow _ )) = True
                  isPatch _ = False
              ls <- filter isPatch . fmap tableDiff .  concat  <$> takeMany var
              when (not $ L.null $ ls ) $ do
                state <- readTVar collectionState
                let patches = childrenRefsUnique inf table state (j,ls)
                when (not $ L.null $ patches) $
                  writeTChan  nmdiff (FetchData table <$> patches)
              )
          )  (\e -> atomically (readTChan var) >>= (\d ->  putStrLn $ "Failed applying patch:" <>show (e :: SomeException,d)<>"\n"))
          ) newNestedFKS
      dynFork $ forever $ catchJust notException (do
          atomically (do
              ls <- takeMany nchanidx
              modifyTVar' midx (\s -> apply   s ls)
              )
          )  (\e -> atomically (readTChan nchanidx ) >>= (\d ->  putStrLn $ "Failed applying patch:" <>show (e :: SomeException,d)<>"\n"))
      dynFork $ forever $ catchJust notException (do
        pa <- atomically $ do
            patches <- fmap concat $ takeMany nmdiff
            e <- readTVar collectionState
            let out = applyUndo e (tableDiff <$> patches)
            traverse (writeTVar collectionState . fst) out
            return (patches,fmap snd out)
        either (putStrLn  .("### Error applying: " ++ ) . show ) (\li -> do
          mapM (\(m,u) -> (do
            val <- logger (schemaOps inf) inf. mapModification (recoverKey inf) $ m
            case val of
              TableModification (Just v) i j k _ -> do
                logger (schemaOps inf) inf (RevertModification v (firstPatchRow (recoverKey inf) u))
                return ()
              _ -> return () )`catchAll` (\e -> putStrLn $ "Failed logging modification"  ++ show (e :: SomeException)))  (zip (fst pa) (reverse li))
          return ()) (snd pa)
        return ()
            )  (\e -> atomically ( takeMany nmdiff ) >>= (\d ->  putStrLn $ "Failed applying patch:" <> show (e :: SomeException,d)<>"\n"))
      let dbref = DBRef table 0 refSize nmdiff midx nchanidx collectionState
      liftIO$ atomically $ modifyTVar (mvarMap inf) (M.insert i  dbref)
      return ((iv,v),dbref)

loadFKSDisk inf targetTable re = do
  let
    (fkSet2,pre) = F.foldl' (\(s,l) i   -> (S.map keyFastUnique (pathRelOri i)<> s  ,liftA2 (\j i -> j ++ [i]) l ( loadFKDisk inf s re i )) )  (S.empty , return []) (P.sortBy (P.comparing (RelSort . S.toList . pathRelRel)) $ F.toList (rawFKS targetTable))
  prefks <- pre
  return (\table ->
    let
      items = unKV $ table
      fks = catMaybes $  ($ table) <$>  prefks
      fkSet:: S.Set KeyUnique
      fkSet =   S.map keyFastUnique . S.unions . fmap (S.fromList . fmap _relOrigin . (\i -> if all isInlineRel i then i else filterReflexive i ) . S.toList . pathRelRel ) $ filter isReflexive  $ (P.sortBy (P.comparing (RelSort . F.toList . pathRelRel)) $ F.toList (rawFKS targetTable))
      nonFKAttrs :: [(S.Set (Rel KeyUnique) ,Column KeyUnique Showable)]
      nonFKAttrs =  M.toList $  M.filterWithKey (\i a -> not $ S.isSubsetOf (S.map _relOrigin i) (S.intersection fkSet fkSet2)) items
   in kvlist  (fmap snd nonFKAttrs <> fks ))

loadFKDisk :: InformationSchema ->  S.Set KeyUnique -> [MutRec [[Rel Key]]] ->  SqlOperation -> Dynamic (TBData KeyUnique Showable -> Maybe (Column KeyUnique Showable))
-- loadFKDisk _ old  _ m | traceShow (old,m) False = undefined
loadFKDisk inf old re (FKJoinTable rel (st,tt) ) = do
  let
    targetSchema = if schemaName inf == st then   inf else justError "no schema" $ HM.lookup st (depschema inf)
    targetTable = lookTable targetSchema tt
  ((_,mtable ),_) <- createTableRefs targetSchema re targetTable

  return (\table ->  do
    let
        relSet = S.fromList $ _relOrigin <$> relU
        refl = S.fromList $ keyFastUnique . _relOrigin <$> filterReflexive rel
        relU = (fmap keyFastUnique <$> rel)
        tb  = F.toList (M.filterWithKey (\k l ->  not . S.null $ S.map _relOrigin  k `S.intersection` relSet)  (unKV . tableNonRef $ table))
        fkref = joinRel2  (keyFastUnique <$> tableMeta targetTable) (replaceRel  relU <$> tb) mtable
    case  FKT (kvlist $ filter ((\i -> not (S.member i old) &&  S.member i refl ) . _tbattrkey ) tb) relU  <$>  fkref of
      Nothing ->  if F.any (isKOptional.keyType . _relOrigin) rel
                     then Just $ FKT (kvlist $ filter ((\i -> not (S.member i old) &&  S.member i refl ) . _tbattrkey ) tb) relU (LeftTB1 Nothing)
                     else Nothing
      i -> i)
loadFKDisk inf old re (FKInlineTable ori (st,tt) )  = do
  let targetTable = lookTable targetSchema tt
      targetSchema = if schemaName inf == st then   inf else justError "no schema" $ HM.lookup st (depschema inf)
  loadVtPre <- loadFKSDisk inf  targetTable re
  return (\table ->
    let v = do
          IT rel vt  <- M.lookup ( (S.singleton. Inline .keyFastUnique)   ori) (unKV $ table)
          let loadVt = loadVtPre  <$> vt
          return $ IT rel loadVt
    in case v of
        Nothing ->  if  (isKOptional .keyType) ori
                      then  Just (IT (keyFastUnique $ ori ) (LeftTB1 Nothing))
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

tablePK t = (_rawSchemaL t ,_rawNameL t)


writeTable :: InformationSchema -> String -> Table -> DBRef KeyUnique Showable -> IO ()
writeTable inf s (Project i (Union l)) v = return ()
writeTable inf s t v = do
  let tname = s <> "/" <> (fromString $ T.unpack (tableName t))
  putStrLn("Dumping Table: " <> tname)
  ((_,_,iv),_) <- atomically $ readState mempty  v
  (IndexMetadata iidx ,_)<- atomically $ readIndex v
  let
    sidx = first (mapPredicate (keyFastUnique.recoverKey inf))  <$> M.toList iidx
    sdata = traverse (\i ->   fmap (mapKey' keyFastUnique) . typecheck (typeCheckTable (tablePK t)) .mapKey' (recoverKey inf).tableNonRef $ i) $  iv
  either (putStrLn .unlines ) (\sdata ->  do
    when (not (L.null sdata) )$
      B.encodeFile  tname (sidx, G.toList sdata)) sdata
  return ()


readTable :: InformationSchema -> T.Text -> Table -> [MutRec [[Rel Key]]] -> Dynamic (Collection KeyUnique Showable)
readTable inf r  t  re = do
  let
      s = schemaName inf
  o <- liftIO $ readTableFromFile inf r t
  let (m,prev) = fromMaybe (IndexMetadata M.empty ,[]) o
  disk <- loadFKSDisk inf t re
  let v = createUn (tableMeta (fmap keyFastUnique t)) (keyFastUnique <$> rawPK t) $ (\f -> disk  f) <$> prev
  return (m,v)


fromTable origin whr = do
  inf <- askInf
  (_,(n,(_,_,amap) )) <- tableLoader' (lookTable inf origin) Nothing Nothing [] (tablePredicate inf origin whr)
  return (origin,inf,amap)

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


newKey table name ty =
  let un = maximum (keyPosition <$> tableAttrs table) + 1
  in  Key name Nothing [FRead,FWrite] un Nothing (tableUnique table) ty


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
        let origin = sourceTable inf (JoinV j l LeftJoin srel alias)
            target = sourceTable inf l
        let
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
  :: (Monad m, Traversable t2) =>
     Parser (Kleisli m) (View i k) a1 (t2 (KV (FKey a) c))
     -> Parser
          (Kleisli (RWST (Atom (KV T.Text c), [t]) t1 () m))
          (Union (G.AttributePath k MutationTy),Union (G.AttributePath k MutationTy))
          ()
          b
     -> Parser (Kleisli m) (View i k) a1 (t2 b)
projectV  (P i (Kleisli j) )  p@(P (k,_) _ ) = P (ProjectV i  k) (Kleisli $  j  >=> (\a -> traverse (evalEnv p . (,[]) . Atom .  mapKey' keyValue) a))


