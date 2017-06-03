{-# LANGUAGE RankNTypes ,RecursiveDo,TypeFamilies,FlexibleContexts,OverloadedStrings,TupleSections #-}
module SchemaQuery
  (
  createUn
  ,takeMany
  ,convertChanEvent
  ,childrenRefsUnique
  ,refTables'
  ,lookAttrM
  ,lookAttr'
  ,lookAttrs'
  ,refTables
  ,applyBackend
  ,tellPatches
  ,selectFromA
  ,selectFrom
  ,updateFrom
  ,patchFrom
  ,insertFrom
  -- ,syncFrom
  ,getFrom
  ,deleteFrom
  ,prerefTable
  ,refTable
  ,refTableSTM
  ,loadFKS
  ,fullDiffInsert
  ,fullDiffEdit
  ,fullDiffEditInsert
  ,transaction
  ,transactionLog
  ,transactionNoLog
  ,patchCheck
  ,tableCheck
  ,filterfixedS
  ,filterfixed
  ,readState
  ,readIndex
  )where
import Graphics.UI.Threepenny.Core (mapEventDyn)

import RuntimeTypes
import Control.Arrow (first)
import Control.DeepSeq
import Step.Host
import Expression
import Types.Primitive
import Types.Index (checkPred)
import Control.Concurrent
import Control.Monad.Catch

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

defsize = 200

lookDBVar mmap table = justError ("cant find mvar: " <> show table ++ show (tableName <$> M.keys mmap)) (M.lookup table mmap )

estLength page size est = fromMaybe 0 page * size  +  est

refTableSTM :: InformationSchema -> Table -> STM (DBRef KeyUnique Showable)
refTableSTM  inf table  = do
  mmap <- readTMVar (mvarMap inf)
  return $ lookDBVar mmap table


prerefTable :: MonadIO m => InformationSchema -> Table -> m (DBRef KeyUnique Showable)
prerefTable  inf table  = do
  mmap <- liftIO$ atomically $ readTMVar (mvarMap inf)
  return $ lookDBVar mmap table

projunion :: InformationSchema -> Table -> TBData Key Showable -> TBData Key Showable
projunion inf table = res
  where
    res = liftTable' inf (tableName table) . filterAttrs . mapKey' keyValue
    filterAttrs (m,v)=  (m, mapComp (\(KV v)-> KV $ M.filterWithKey (\k _ -> S.isSubsetOf (S.map _relOrigin k) attrs)  v ) v)
      where
        attrs = S.fromList $ keyValue <$> tableAttrs table

refTable :: InformationSchema -> Table -> Dynamic DBVar
refTable  inf (Project table (Union origin) )  = do
  refs <- mapM (refTable inf ) origin

  let mergeDBRefT  (ref1,j ,i,o,k) (ref2,m ,l,p,n) = (ref1 <> ref2 ,liftA2 (M.unionWith (\(a,b) (c,d) -> (a+c,b<>d)))  j  m , liftA2 (<>) i l , liftA2 (zipWith (\(i,j) (l,m) -> (i,j<>m))) o p ,unionWith mappend k n)
      dbvarMerge = foldr mergeDBRefT  ([],pure M.empty ,pure G.empty, pure ((,G.empty)<$> _rawIndexes table) ,never) (Le.over Le._3 (fmap (createUn (rawPK table).fmap (projunion inf table).G.toList)) .(\(DBVar2 e i j l k ) -> ([e],i,j,l,k)) <$>refs )
      dbvar (l,i,j,p,k) = DBVar2 (L.head l) i j p k

  return $ dbvar dbvarMerge
refTable  inf table  = do
  mmap <- liftIO$ atomically $ readTMVar (mvarMap inf)
  let ref = lookDBVar mmap table
  idxTds<- convertChanStepper  inf (mapTableK keyFastUnique table) ref
  (dbTds ,dbEvs)<- convertChanTidings inf (mapTableK keyFastUnique table) mempty  never ref
  return (DBVar2 ref idxTds  (fmap snd dbTds) (fmap fst dbTds ) dbEvs)

tbpredM un  = G.notOptional . G.getUnique un

createUn :: Ord k => [k] -> [TBData k Showable] -> G.GiST (G.TBIndex Showable) (TBData k Showable)
createUn un   =  G.fromList  transPred  .  filter (isJust . Tra.traverse (Tra.traverse unSOptional' ) . getUn (S.fromList un) . tableNonRef' )
  where transPred  =  G.notOptional . G.getUnique un . tableNonRef'


applyBackend (CreateRow t@(m,i)) =
   insertFrom   t
applyBackend (DropRow t) =
   deleteFrom   t
applyBackend (PatchRow p@(m,pk@(G.Idex pki),i)) = do
   inf <- ask
   let table = lookTable inf (_kvname m)
   ref <- prerefTable inf table
   (sidx,v,_,_) <- liftIO $ atomically $ readState inf (WherePredicate (AndColl []),keyFastUnique <$> _kvpk m) (mapTableK keyFastUnique table ) ref
   let oldm = mapKey' (recoverKey inf ) <$>  G.lookup pk v
   old <- maybe (do
     (_,(i,o)) <- selectFrom (_kvname m) Nothing Nothing [] (WherePredicate (AndColl ((\(k,o) -> PrimColl (keyRef k,Left (justError "no opt " $ unSOptional' o,Equals))) <$> zip (_kvpk m) pki)))
     return $ L.head $ G.toList o
        ) return oldm
   if isJust (diff old  (apply old p))
     then updateFrom   old   p
     else return Nothing

selectFromA t a b c d = do
  inf <- ask
  tableLoader (lookTable inf t) a b c d

selectFrom t a b c d = do
  inf <- ask
  tableLoader (lookTable inf t) a b c d
    {-
syncFrom t page size presort fixed = do
  let table = t
  inf <- ask
  let sref =  case filter (\(Path i _) -> S.isSubsetOf i (S.fromList $ _rawScope table)) (S.toList $ rawFKS table) of
            [sref] -> sref
            i ->  errorWithStackTrace ("no sref " <> show sref)
      Path kref (FKJoinTable rel stable ) =  sref
  let mvar = mvarMap inf
  mmap <- liftIO $ atomically $ readTMVar mvar
  let dbvar =  justError ("cant find mvar" <> show table  ) (M.lookup (table) mmap )
  let
      rinf = fromMaybe inf $ HM.lookup (fst stable) (depschema inf)
      fromtable = (lookTable rinf $ snd stable)
      defSort = fmap (,Desc) $  rawPK t
  (l,i) <- local (const rinf) $ tableLoader fromtable Nothing Nothing []  fixed
  let
  ix <- mapM (\i -> do
      let
       --   fil = WherePredicate $ AndColl [("=", FKT ( kvlist $ _tb <$> backPathRef sref i) rel (TB1 i) )]
      (_,t) <- selectFrom "history" Nothing Nothing defSort mempty -- (fil)
      let latest = fmap (("=",) . uncurry Attr). M.toList . getPKM   $ ( L.maximumBy (comparing getPKM) $ G.toList $ snd t)
      (joinSyncTable  [(fromtable ,i,sref)] table page size presort mempty . F.toList ) (latest)
      ) $ F.toList (snd i)

  return (dbvar ,(M.empty ,G.empty))--foldr mergeDBRef  (M.empty,G.empty) $ fmap snd $ ix )
-}

updateFrom  a  b = do
  inf <- ask
  (editEd $ schemaOps inf)  a b
patchFrom  a   = do
  inf <- ask
  (patchEd $ schemaOps inf)  a
insertFrom  a   = do
  inf <- ask
  (insertEd $ schemaOps inf)  a
getFrom  a   b = do
  inf <- ask
  (getEd $ schemaOps inf)  a b
deleteFrom  a   = do
  inf <- ask
  a <- (deleteEd $ schemaOps inf)  a
  tell (maybeToList a)
  return a


mergeDBRef  (j,i) (m,l) = (M.unionWith (\(a,b) (c,d) -> (a+c,b<>d))  j  m , i <>  l )

getFKRef inf predtop rtable (evs,me,old) v (Path r (FKInlineTable  j )) =  do
            let rinf = maybe inf id $ HM.lookup ((fst j))  (depschema inf)
                table = lookTable rinf $ snd j
                predicate predtop
                      = case predtop of
                            WherePredicate l ->
                              let
                                go pred (AndColl l) = AndColl <$> nonEmpty (catMaybes $ go pred <$> l)
                                go pred (OrColl l) = OrColl <$> nonEmpty (catMaybes $ go pred <$> l)
                                go pred (PrimColl l) = PrimColl <$> pred l
                                test f (Nested p (Many[i] ),j)  = if (iprodRef <$> p) == f then Just (i ,j) else Nothing
                                -- test f (Nested p i ,j)  = if (iprodRef <$> p) == f then Just (i ,j) else Nothing
                                test v f = Nothing
                             in  fmap WherePredicate (go (test (S.toList r)) l)

                -- editAttr :: (TBData Key Showable -> TBData Key Showable) -> TBData Key Showable -> TBData Key Showable
                editAttr fun  (m,i) = (m,mapComp (\(KV i) -> KV (M.alter  (fmap (mapComp (Le.over ifkttable (fmap (either (errorWithStackTrace . ("no inline table " ++) . show  ) id .fun))))) (S.map Inline r)  i )) i )
                nextRef :: [TBData Key Showable]
                nextRef= (concat $ catMaybes $ fmap (\i -> fmap (F.toList . _fkttable.unTB) $ M.lookup (S.map Inline r) (_kvvalues $ unTB $ snd  i) )v)

            (_,joinFK,_) <- getFKS rinf predtop table nextRef
            let
                joined i = do
                  return $ editAttr joinFK i

            return (evs,me >=> joined,old <> r)
    where
        getAtt i (m ,k ) = filter ((`S.isSubsetOf` i) . S.fromList . fmap _relOrigin. keyattr ) . F.toList . _kvvalues . unTB $ k

getFKRef inf predtop rtable (evs,me,old) v (Path ref (FunctionField a b c)) = do
  let
    addAttr :: TBData Key Showable -> Either ([Compose Identity (TB Identity)  Key Showable],[Rel Key]) (TBData Key Showable)
    addAttr (m,i) = maybe (Right (m,i)) (\r -> Right (m,mapComp (\(KV i) -> KV (M.insert (S.fromList $ keyattri r) (_tb r)   i) ) i)) r
      where
        r =  evaluate a b funmap c (m,i)
  return (evs,me >=> addAttr ,old <> ref )
getFKRef inf predtop rtable (evs,me,old) v (Path ref (RecJoin i j )) = do
  return (evs,me,old)



getFKRef inf predtop rtable (evs,me,old) v path@(Path _ (FKJoinTable i j ) ) =  do
                let rinf = maybe inf id $ HM.lookup ((fst j))  (depschema inf)
                    table = lookTable rinf $ snd j
                    predicate predtop = case predtop of
                                  WherePredicate l ->
                                    let
                                      go pred (AndColl l) = AndColl <$> nonEmpty (catMaybes $ go pred <$> l)
                                      go pred (OrColl l) = OrColl <$> nonEmpty (catMaybes $ go pred <$> l)
                                      go pred (PrimColl l) = PrimColl <$> pred l
                                      test f (Nested p (Many[i] ),j)  = if (iprodRef <$> p) == f then Just ( i ,left (fmap (removeArray (keyType $ iprodRef $ L.head p))) j) else Nothing
                                      -- test f (Nested p i ,j)  = if (iprodRef <$> p) == f then Just ( i ,left (fmap (removeArray (keyType $ iprodRef $ L.head p))) j) else Nothing
                                      test v f = Nothing
                                      removeArray (KOptional i)  o = removeArray i o
                                      removeArray (KArray i)  (AnyOp o) = o
                                      removeArray i  o = o
                                   in  fmap WherePredicate (go (test (_relOrigin <$> i)) l)
                let refs = fmap (WherePredicate .OrColl. L.nub) $ nonEmpty $ catMaybes $ (\o -> fmap AndColl . allMaybes . fmap (\k ->join . fmap (fmap ( (\i->PrimColl (keyRef(_relTarget $ k) ,Left (i,Flip $ _relOperator k)))) . unSOptional' . _tbattr.unTB) . M.lookup (S.singleton (Inline (_relOrigin k))) $ o) $ i ) . unKV .snd <$> v
                    predm =(refs <> predicate predtop)
                (ref,tb2) <- case refs of
                  Just refspred-> do
                    let pred = maybe refspred (refspred <> ) (predicate predtop)
                    (ref,out) <- local (const rinf) (tableLoader table  (Just 0) Nothing [] pred)
                    let check ix (i,tb2) = do
                          mergeDBRef (i,tb2) <$> if (isJust (M.lookup pred i)
                                                    && (fst $ justError "" $ M.lookup pred i) >= G.size tb2
                                                    && (fst $ justError "" $ M.lookup pred i) >= 200)
                            then  do
                              (_,out) <- local (const rinf) (tableLoader table  (Just (ix +1) ) Nothing []  pred)
                              if G.size (snd out) == G.size tb2
                                 then  do
                                   return (M.empty , G.empty)
                                 else  check (ix +1) out
                            else do
                              return (M.empty , G.empty)
                    (_,tb2) <- check 0 out
                    -- liftIO $print (tableName table,length v,G.size tb2)
                    return (collectionPatches ref,tb2)
                  Nothing -> return (never,G.empty)

                let
                    evt = (FKJoinTable i j ,  filter isPatch <$> ref)
                    isPatch (PatchRow _ ) = True
                    isPatch i = False
                    tar = S.fromList $ fmap _relOrigin i
                    refl = S.fromList $ fmap _relOrigin $ filterReflexive i
                    inj = S.difference refl old
                    joinFK :: TBData Key Showable -> Either ([Compose Identity (TB Identity)  Key Showable],[Rel Key]) (Column Key Showable)
                    joinFK m  = maybe (Left (taratt,i)) Right $ FKT (kvlist tarinj ) i <$> joinRel2 (tableMeta table ) (fmap (replaceRel i )$ fmap unTB $ taratt ) tb2
                      where
                        replaceRel rel (Attr k v) = (justError "no rel" $ L.find ((==k) ._relOrigin) rel,v)
                        taratt = getAtt tar (tableNonRef' m)
                        tarinj = getAtt inj (tableNonRef' m)
                    addAttr :: Column Key Showable -> TBData Key Showable -> TBData Key Showable
                    addAttr r (m,i) = (m,mapComp (\(KV i) -> KV (M.insert (S.fromList $ keyattri r) (_tb r)  $ M.filterWithKey (\k _ -> not $ S.map _relOrigin k `S.isSubsetOf` refl && F.all isInlineRel k   ) i )) i )
                    joined i = do
                       fk <- joinFK i
                       return $ addAttr  fk i
                return (evt :evs,me >=> joined,old <> refl)
    where
        getAtt i (m ,k ) = filter ((`S.isSubsetOf` i) . S.fromList . fmap _relOrigin. keyattr ) . F.toList . _kvvalues . unTB $ k
getFKRef inf predtop rtable (evs,me,old) v path = errorWithStackTrace (show path)

left f (Left i ) = Left (f i)
left f (Right i ) = (Right i)

getFKS
  :: InformationSchemaKV Key Showable
     -> TBPredicate Key Showable
     -> TableK Key
     -> [TBData Key Showable]
     -> TransactionM
          ([(SqlOperation,Event [RowPatch Key Showable])],TBData Key Showable -> Either
                ([Compose Identity (TB Identity) Key Showable],[Rel Key])
                (TBData Key Showable),
           S.Set Key)
getFKS inf predtop table v = F.foldl' (\m f  -> m >>= (\i -> getFKRef inf predtop  table i v f)) (return ([],return ,S.empty )) $ sorted -- first <> second
  where
    sorted = P.sortBy (P.comparing (RelSort . F.toList .  pathRelRel))  (S.toList (rawFKS table))

rebaseKey inf t  (WherePredicate fixed ) = WherePredicate $ ( lookAccess inf (tableName t) . (Le.over Le._1 (fmap  keyValue) )<$> fixed)

tableLoader :: Table -> Maybe Int -> Maybe Int -> [(Key,Order)] -> WherePredicate
    -> TransactionM (DBVar,Collection Key Showable)
tableLoader (Project table  (Union l)) page size presort fixed  = do
    liftIO$ putStrLn $ "start loadTable " <> show (tableName table)
    li <- liftIO getCurrentTime
    inf <- ask
    i <- mapM (\t -> do
      l <- tableLoader t page size presort (rebaseKey inf t  fixed)
      return l) l
    let mvar = mvarMap inf
    mmap <- liftIO $ atomically $ readTMVar mvar
    let mergeDBRefT  (ref1,j ,i,o,k) (ref2,m ,l,p,n) = (ref1 <> ref2 ,liftA2 (M.unionWith (\(a,b) (c,d) -> (a+c,b<>d)))  j  m , liftA2 (<>) i l , liftA2 (zipWith (\(i,j) (l,m) -> (i,j<>m))) o p ,unionWith mappend k n)
        dbvarMerge = foldr mergeDBRefT  ([],pure M.empty ,pure G.empty, pure ((,G.empty)<$> _rawIndexes table) ,never) (Le.over Le._3 (fmap (createUn (rawPK table).fmap (projunion inf table).G.toList)) .(\(DBVar2 e i j l k ) -> ([e],i,j,l,k)). fst <$>i )
        dbvar (l,i,j,p,k) = DBVar2 (L.head l) i j p k
        o = foldr mergeDBRef  (M.empty,G.empty) (fmap (createUn (rawPK table).fmap (projunion inf table).G.toList) . snd <$>i )

    lf <- liftIO getCurrentTime
    liftIO $ putStrLn $ "finish loadTable" <> show  (tableName table) <> " - " <> show (diffUTCTime lf  li)
    modify (M.insert (table,fixed) (dbvar dbvarMerge ,o) )
    return $ (dbvar dbvarMerge, o)
  -- (Scoped || Partitioned) Tables
    {-| not  (null $ _rawScope table ) && not (S.null (rawFKS table) )= do
      inf <- ask
      let sref =  case filter (\(Path i _) -> S.isSubsetOf i (S.fromList $ _rawScope table)) (S.toList $ rawFKS table) of
                [sref] -> sref
                i ->  errorWithStackTrace ("no sref " <> show sref)
          Path kref (FKJoinTable rel stable ) =  sref
      let mvar = mvarMap inf
      mmap <- liftIO $ atomically $ readTMVar mvar
      dbvar <- lift $ refTable   inf table
     --  let dbvar =  justError ("cant find mvar" <> show table  ) (M.lookup (tableMeta table) mmap )
      let
          rinf = fromMaybe inf $ HM.lookup (fst stable) (depschema inf)
          fromtable = (lookTable rinf $ snd stable)
          defSort = fmap (,Desc) $  rawPK fromtable
      (l,i) <- local (const rinf) $ tableLoader  fromtable page  size defSort mempty
      ix <- mapM (\i -> do
          (l,v) <- joinTable [(fromtable ,i,sref)] table page size presort fixed
          return v ) $ F.toList (snd i)
      return (dbvar ,foldr mergeDBRef  (M.empty,G.empty) ix )
-}
  -- Primitive Tables
tableLoader table  page size presort fixed = do
    inf <- ask
    liftIO$ putStrLn $ "start loadTable " <> show (tableName table)
    li <- liftIO getCurrentTime
    o <- pageTable False (\table page size presort fixed predtop  -> do
          let
            unestPred  (WherePredicate l ) = WherePredicate $ go predicate l
              where
                go pred (AndColl l) = AndColl (go pred <$> l)
                go pred (OrColl l) = OrColl (go pred <$> l)
                go pred (PrimColl l) = AndColl $ PrimColl <$> pred l
                predicate (Nested i j ,Left _ ) = (\a -> (a, Right (Not IsNull))) <$> i
                predicate i  = [i]
            tbf = tableView  (tableMap inf) table
          (res ,x ,o) <- (listEd $ schemaOps inf) (tableNonRef2 tbf) page size presort fixed (unestPred predtop)
          (evs,resFKS ,_)<- getFKS inf predtop table res
          let result = fmap resFKS   res
          liftIO $ when (not $ null (lefts result)) $ do
            print ("lefts",tableName table ,lefts result)
          return (rights  result,x,o ,evs)) table page size presort fixed
    lf <- liftIO getCurrentTime
    liftIO $ putStrLn $ "finish loadTable" <> show  (tableName table) <> " - " <> show (diffUTCTime lf  li)
    return o


{-
joinSyncTable reflist  a b c d f e =
    ask >>= (\inf -> pageTable True ((joinSyncEd $ schemaOps inf) reflist e ) a b c d f )



joinTable :: [(Table,TBData Key Showable,Path (S.Set Key ) SqlOperation )]-> Table -> Maybe Int -> Maybe Int -> [(Key,Order)] -> WherePredicate
    -> TransactionM (DBVar,Collection Key Showable)
joinTable reflist  a b c d e =
    ask >>= (\ inf -> pageTable False ((joinListEd $ schemaOps inf) reflist) a b c d e )

-}

predNull (WherePredicate i) = L.null i

filterfixed table fixed v
  = if predNull fixed
       then v
       else G.queryCheck (fixed ,rawPK table) v


filterfixedS table fixed v
  = if predNull fixed
       then snd v
       else queryCheckSecond (fixed ,rawPK table) v

childrenRefsUnique :: InformationSchema -> TableK KeyUnique -> ([SecondaryIndex KeyUnique Showable],TableIndex KeyUnique Showable) -> (SqlOperation , [RowPatch KeyUnique Showable]) -> [RowPatch KeyUnique Showable]
childrenRefsUnique  inf table (sidxs,base) (FKJoinTable rel j ,evs)  =  concat $ (\i -> search  i  sidx) <$>  evs
              where
                rinf = maybe inf id $ HM.lookup ((fst j))  (depschema inf)
                relf = fmap keyFastUnique <$> rel
                jtable = lookTable rinf $ snd j
                sidx = M.lookup (keyFastUnique . _relOrigin  <$> rel) (M.fromList sidxs)
                search (PatchRow p@(_,G.Idex v,_)) idxM = case idxM of
                  Just idx -> concat $ conv <$> resIndex idx
                  Nothing -> concat $ conv <$> resScan base
                  where
                    predK = WherePredicate $ AndColl ((\(Rel o op t) -> PrimColl (keyRef o  , Left (fromJust $ unSOptional' $fmap create $ v !! (justError "no key" $  t`L.elemIndex` rawPK jtable),op))) <$> rel )
                    predKey =  mapPredicate keyFastUnique predK
                    pred =  mapPredicate (\o -> justError "no pk" $ L.elemIndex o (fmap _relOrigin rel)) predK
                    resIndex idx = G.query pred idx
                    resScan idx = catMaybes $ fmap (\(i,t) -> ((G.getIndex i,t), G.getUnique (fmap (keyFastUnique._relOrigin) rel) i)) . (\i->  (i,) <$> G.checkPredId i predKey) <$> G.toList idx
                    conv ((pk,ts),G.Idex fks) = (\t -> PatchRow (kvempty,pk ,[PFK relf (zipWith (\i j -> PAttr (_relOrigin i) (patch j)) relf fks ) (recurse2 t p)]) ) <$> ts
                    unKOptional (KOptional i) = i
                    unKOptional i = i
                    recurse2 (G.PathAttr _ i ) p = go i
                      where
                        go (G.ManyPath (j Non.:| _) ) = go  j
                        go (G.NestedPath i j ) = matcher i (go j)
                        go (G.TipPath j ) = PAtom p
                        matcher (PIdIdx ix )  = PIdx ix . Just
                        matcher PIdOpt   = POpt . Just
                        -- matcher PIdAtom = PAtom
                    recurse2 i p = errorWithStackTrace (show i)




pageTable flag method table page size presort fixed = do
    inf <- ask
    let mvar = mvarMap inf
        tableU = mapTableK keyFastUnique table
        fixedU = mapPredicate keyFastUnique fixed
        defSort = fmap (,Desc) $  rawPK table
        sortList  = if L.null presort then defSort else  presort
        pagesize = maybe (opsPageSize $ schemaOps inf)id size
        ffixed = filterfixedS  tableU fixedU
    mmap <- liftIO $ atomically $ readTMVar mvar
    let
      dbvar :: DBRef KeyUnique Showable
      dbvar =  lookDBVar mmap table
    (fixedmap,fixedChan) <- liftIO $ atomically $readIndex dbvar
    let pageidx = (fromMaybe 0 page +1) * pagesize



    res <- do
       if isNothing (join $ fmap (M.lookup pageidx . snd) $ M.lookup fixedU fixedmap)  -- Ignora quando página já esta carregando
         then do
           (sidx,reso ,nchan,iniVar) <- liftIO $ atomically $
             readState inf (fixedU ,rawPK tableU) tableU dbvar
           let
                 freso =  ffixed (sidx,reso)
                 predreq = (fixedU,G.Contains (pageidx - pagesize,pageidx))
                 hasIndex = M.lookup fixedU fixedmap
                 (sq ,_)= justError "no index" hasIndex
           (nidx,ndata) <-  if
                    flag || ( (isNothing hasIndex|| (sq > G.size freso)) -- Tabela é maior que a tabela carregada
                    && pageidx  > G.size freso ) -- O carregado é menor que a página
                                                                                           -- && isJust diffpred

                 then do
                   let pagetoken =  (join $ flip M.lookupLE  mp . (*pagesize) <$> page)
                       (_,mp) = fromMaybe (0,M.empty ) hasIndex
                   liftIO$ putStrLn $ "new page " <> show (tableName table, pageidx, G.size freso,G.size reso,page, pagesize)
                   (resK,nextToken ,s ,evs) <- method table (liftA2 (-) (fmap (*pagesize) page) (fst <$> pagetoken)) (fmap snd pagetoken) size sortList fixed
                   let
                       res = fmap (mapKey' keyFastUnique ) resK
                       token =  nextToken
                       index = (estLength page pagesize (s + G.size freso) , maybe (M.insert pageidx HeadToken) (M.insert pageidx ) token $ mp)
                   liftIO$ do
                     putIdx (idxChan dbvar ) (fixedU ,estLength page pagesize s, pageidx ,fromMaybe HeadToken token)
                     putPatch (patchVar dbvar) (F.toList $ CreateRow <$> filter (\i -> isNothing $ G.lookup (G.getIndex i) reso  )   resK)
                   return (index,res <> G.toList freso)
                 else do
                   liftIO$ putStrLn $ "keep page " <> show (tableName table, pageidx, G.size freso,G.size reso,page, pagesize)
                   return (fromMaybe (0,M.empty) hasIndex ,[])
           return $Right(M.insert fixedU nidx fixedmap, sidx,iniVar,nchan,if L.length ndata > 0 then createUn (rawPK tableU)  ndata <> freso else  freso )
         else do
           loadmap <- get
           let preloaded = M.lookup (table ,fixed) loadmap
           case preloaded  of
             Just pre ->
                return $Left (fromJust $ preloaded)
             Nothing -> do
                (sidx,reso ,nchan,iniVar) <- liftIO $ atomically $
                  readState inf (fixedU ,rawPK tableU) tableU dbvar
                let
                   freso =  ffixed (sidx,reso)
                return $ Right(fixedmap , sidx,iniVar,nchan,freso)
    case res of
      Left i -> return i
      Right (nidx,sidx,iniVar,nchan,ndata) -> do
        let iniFil = (nidx,ndata)
        (vpt ,evpt)<- lift $ convertChanTidings0 inf tableU (fixedU ,rawPK tableU) never (sidx ,snd iniFil) iniVar nchan
        idxTds <- lift $ convertChanStepper0 inf (tableU) fixedmap fixedChan
        let result = (DBVar2 dbvar idxTds (fmap snd vpt) (fmap fst vpt) evpt ,first (M.mapKeys (mapPredicate (recoverKey inf))).fmap (fmap (mapKey' (recoverKey inf)) )$iniFil)
        modify (M.insert (table,fixed)  result)
        return result

readIndex
  :: (Ord k )
  => DBRef k v
  -> STM
     (M.Map (WherePredicateK k) (Int, M.Map Int (PageTokenF v)),
     TChan (WherePredicateK k, Int, Int, PageTokenF v))
readIndex dbvar = do
    (ini,nchan) <-
      (,) <$> readTVar (idxVar dbvar)<*> cloneTChan (idxChan dbvar)
    patches <- takeMany' nchan
    let conv (v,s,i,t) = (M.alter (\j -> fmap ((\(_,l) -> (s,M.insert i t l ))) j  <|> Just (s,M.singleton i t)) v)
    return (F.foldl' (flip conv) ini patches,nchan)

readState
  :: (Ord k ,NFData v,NFData k,Eq (Index v), Ord k, Ord v, Show k, Show v,
      G.Predicates (TBIndex v), Patch v, Index v ~ v) =>
        InformationSchema
        -> (TBPredicate k Showable, [k ])
      -> TableK k
     -> DBRef k v
     -> STM ([SecondaryIndex k v],TableIndex k v, TChan [RowPatch k v], TVar ([SecondaryIndex k v],TableIndex k v))
readState inf fixed table dbvar = do
  var <-readTVar (collectionState dbvar)
  chan <- cloneTChan (patchVar dbvar)
  patches <- takeMany' chan
  let
      filterPred = nonEmpty . filter (\d -> splitMatch fixed (indexPK d) && indexFilterR (fst fixed) d )
      update l v = F.foldl' (\i j-> fromMaybe i $  applyTableRep inf table i j)   l v
      (sidxs, pidx) = update var (concat patches)
  return (sidxs,pidx,chan,collectionState dbvar)

indexPK (DropRow i) = G.getIndex i
indexPK (CreateRow i) = G.getIndex i
indexPK (PatchRow (_,i,_) ) = i

indexFilterR j (CreateRow i) = checkPred i j
indexFilterR j (DropRow i) = checkPred i j
indexFilterR j (PatchRow i) = indexFilterP j i


-- Default Checks

patchCheck (m,s,i) = if checkAllFilled then Right (m,s,i) else Left ("patchCheck: non nullable rows not filled " ++ show ( need `S.difference` available ))
  where
      checkAllFilled =  need `S.isSubsetOf`  available
      available = S.unions $ S.map _relOrigin . pattrKey <$> i
      need = S.fromList $ L.filter (\i -> not (isKOptional (keyType i) || isSerial (keyType i) || isJust (keyStatic i )) )  (kvAttrs m)

tableCheck (m,t) = if checkAllFilled then Right (m,t) else Left ("tableCheck: non nullable rows not filled " ++ show ( need `S.difference` available ))
  where
      checkAllFilled =  need `S.isSubsetOf`  available
      available = S.fromList $ concat $ fmap _relOrigin . keyattr <$> unKV  t
      need = S.fromList $ L.filter (\i -> not (isKOptional (keyType i) || isSerial (keyType i) || isJust (keyStatic i )) )  (kvAttrs m)



convertChanStepper0
  :: (Show v) =>
    InformationSchema -> TableK KeyUnique
    -> (M.Map (WherePredicateK KeyUnique) (Int, M.Map Int (PageTokenF v)))
    -> TChan (WherePredicateK KeyUnique,Int,Int,PageTokenF v)
     -> Dynamic
          (Tidings (M.Map (WherePredicateK Key) (Int, M.Map Int (PageTokenF v))))
convertChanStepper0  inf table ini nchan = do
        (e,h) <- newEvent
        t <- liftIO $ forkIO  $ forever $catchJust notException ( do
            a <- atomically $ takeMany nchan
            h a ) (\e -> atomically ( takeMany nchan ) >>= (\d ->  putStrLn $ show (e :: SomeException,d)<>"\n"))
        let conv (v,s,i,t) = (M.alter (\j -> fmap ((\(_,l) -> (s,M.insert i t l ))) j  <|> Just (s,M.singleton i t)) (mapPredicate (recoverKey inf) v) )
            dup i =(i,i)
        registerDynamic (killThread t)
        accumT (M.mapKeys (mapPredicate (recoverKey inf))ini) ((\l i-> F.foldl' (flip conv) i l)<$> e)


convertChanStepper
  :: (Show v) =>
    InformationSchema -> TableK KeyUnique
     -> DBRef KeyUnique v
     -> Dynamic
          (Tidings (M.Map (WherePredicateK Key) (Int, M.Map Int (PageTokenF v))))
convertChanStepper inf table dbvar = do
        (ini,nchan) <- liftIO $atomically $
          readIndex dbvar
        convertChanStepper0 inf table ini nchan

convertChanEvent
  :: (Ord k, Show k) =>
     TableK k
     -> (TBPredicate k Showable, [k])
     -> Behavior ([SecondaryIndex k Showable],G.GiST (TBIndex Showable) (TBData k Showable))
     -> TVar ([SecondaryIndex k Showable],G.GiST (TBIndex Showable) (TBData k Showable))
     -> TChan [RowPatch k Showable ]
     -> Dynamic
          (Event [RowPatch k Showable])
convertChanEvent table fixed bres inivar chan = do
  (e,h) <- newEvent
  t <- liftIO $ forkIO $ forever $ catchJust notException (do
    (ml,(sidx,oldM)) <- atomically $ (,) <$> takeMany chan <*> readTVar inivar
    (_,v) <- currentValue bres
    let
        m = concat ml
        newRows =  filter (\d -> splitMatch fixed (indexPK d) && indexFilterR (fst fixed) d && isNothing (G.lookup (indexPK d) v) ) m
        filterPred = nonEmpty . filter (\d -> splitMatch fixed (indexPK d) && indexFilterR (fst fixed) d )
        lookNew  d = fmap CreateRow $ G.lookup (indexPK d) oldM
        filterPredNot j = nonEmpty . catMaybes . map (\d -> if isJust ( G.lookup (indexPK d) j) && not (splitMatch fixed (indexPK d) && indexFilterR (fst fixed) d ) then DropRow <$> G.lookup (indexPK d) j else Nothing )
        newpatches = lookNew <$> newRows
        oldRows =  filterPredNot v m
        patches =  nonEmpty ( catMaybes newpatches )<> oldRows <> filterPred m

    traverse  h patches
    return () )(\e -> atomically ( takeMany chan ) >>= (\d -> putStrLn $  show (e :: SomeException,d)<>"\n"))
  registerDynamic (killThread t)
  return e

convertChanTidings
 ::
  InformationSchema -> TableK KeyUnique
  -> (TBPredicate KeyUnique Showable, [KeyUnique ])
     -> Event [RowPatch Key Showable]
     -> DBRef KeyUnique Showable
     -> Dynamic
    (Tidings (TableRep Key Showable),Event [RowPatch Key Showable])
convertChanTidings inf table fixed evdep dbvar = do
      (sidx,ini,nchan,inivar) <- liftIO $atomically $
        readState inf fixed  table dbvar
      convertChanTidings0 inf table fixed evdep (sidx,ini) inivar nchan


splitMatch (WherePredicate b,o) p = maybe True (\i -> G.match (mapPredicate (justError "no index" . flip L.elemIndex o ) $ WherePredicate i ) (Right p)  ) (G.splitIndexPK b o)

convertChanTidings0
  ::
  InformationSchema -> TableK KeyUnique
     -> (TBPredicate KeyUnique Showable, [KeyUnique])
     -> Event [RowPatch Key Showable]
     ->([SecondaryIndex KeyUnique Showable],G.GiST (TBIndex Showable) (TBData KeyUnique Showable))
     -> TVar ([SecondaryIndex KeyUnique Showable],G.GiST (TBIndex Showable) (TBData KeyUnique Showable))
     -> TChan
          [RowPatch KeyUnique Showable ]
          -> Dynamic (Tidings (TableRep Key Showable),Event [RowPatch Key Showable])
convertChanTidings0 inf table fixed evdep ini iniVar nchan = mdo
    evdiffp <-  convertChanEvent table fixed (first (fmap (first (fmap keyFastUnique). fmap (fmap (fmap (fmap (G.mapAttributePath keyFastUnique)))))) . fmap (fmap (mapKey' keyFastUnique))<$> facts t) iniVar nchan
    ti <- liftIO$ getCurrentTime
    let
      evdiff = filterE (not.L.null) $ unionWith mappend evdep (fmap (firstPatchRow (recoverKey inf)) <$> evdiffp)
      update :: TableRep Key Showable -> [RowPatch Key Showable] -> TableRep Key Showable
      -- update l v | traceShow (ti,tableName table,v)  False = undefined
      update l v = F.foldl' (\i j-> fromMaybe i $  applyTableRep inf (mapTableK (recoverKey inf)table) i j)   l  v
      recoverIni :: TableRep KeyUnique Showable -> TableRep Key Showable
      recoverIni (i,j)= (first (fmap (recoverKey inf )) . fmap (fmap (fmap (fmap (G.mapAttributePath (recoverKey inf ))))) <$> i, recover j)
        where recover = fmap (mapKey' (recoverKey inf))

    t <- accumT (recoverIni ini) (flip update <$> evdiff)
    return (t ,evdiff)

takeMany' :: TChan a -> STM [a]
takeMany' mvar = maybe (return[]) (go . (:[])) =<< tryReadTChan mvar
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




createRow (CreateRow i) = i
createRow (PatchRow i) = create i


fullInsert = Tra.traverse fullInsert'

fullInsert' :: TBData Key Showable -> TransactionM  (TBData Key Showable)
-- fullInsert' v | traceShow ("fullInsert",v) False = undefined
fullInsert' (k1,v1) = do
   inf <- ask
   let proj = _kvvalues . unTB
       tb  = lookTable inf (_kvname k1)
   ret <-  (k1,) . _tb . KV <$>  Tra.traverse (\j -> _tb <$>  tbInsertEdit (unTB j) )  (proj v1)
   (_,(_,l)) <- tableLoader  tb Nothing Nothing [] mempty
   liftIO $ print ("fullInsert",tbpredM (_kvpk k1)  ret , G.lookup (tbpredM (_kvpk k1)  ret) l ,ret)
   if  (isNothing $ flip G.lookup l $ tbpredM (_kvpk k1)  ret ) && rawTableType tb == ReadWrite
      then catchAll (do
        i@(Just (TableModification _ _ tb))  <- insertFrom  ret
        tell (maybeToList i)
        return $ createRow tb) (\e -> do
          let pred = WherePredicate (AndColl ((\(k,o) -> PrimColl (keyRef k,Left (justError "no opt " $ unSOptional' o,Equals))) <$> zip (_kvpk k1) pki))
              G.Idex pki = G.getIndex ret
          (_,(_,l)) <- tableLoader  tb Nothing Nothing []  pred
          liftIO$ putStrLn $ "failed insertion: "  ++ (show e)
          return ret)
      else do
        return ret

tellPatches :: [TableModification (RowPatch Key Showable)] -> TransactionM ()
tellPatches = tell

noInsert = Tra.traverse noInsert'

noInsert' :: TBData Key Showable -> TransactionM  (TBData Key Showable)
noInsert' (k1,v1)   = do
   let proj = _kvvalues . unTB
   (k1,) . _tb . KV <$>  Tra.sequence (fmap (\j -> _tb <$>  tbInsertEdit (unTB j) )  (proj v1))

transactionLog :: InformationSchema -> TransactionM a -> Dynamic [TableModification (RowPatch Key Showable)]
transactionLog inf log = withDynamic ((transactionEd $ schemaOps inf) inf ) $ do
  (md,_,mods)  <- runRWST log inf M.empty
  let aggr = foldr (\(TableModification id t f) m -> M.insertWith mappend t [TableModification id t f] m) M.empty mods
  agg2 <- Tra.traverse (\(k,v) -> do
    ref <- prerefTable (if rawSchema k == schemaName inf then inf else justError "no schema" $ HM.lookup ((rawSchema k ))  (depschema inf) ) k
    nm <- mapM (logger (schemaOps inf) inf) v
    putPatch (patchVar ref ) $ (\(TableModification _ _ p) -> p) <$> nm
    return nm
    ) (M.toList aggr)
  return $ concat $ agg2



transactionNoLog :: InformationSchema -> TransactionM a -> Dynamic a
transactionNoLog inf log = do -- withTransaction (conn inf) $ do
  (md,_,mods)  <- runRWST log inf M.empty
  let aggr = foldr (\tm@(TableModification id t f) m -> M.insertWith mappend t [tm] m) M.empty mods
  Tra.traverse (\(k,v) -> do
    ref <- prerefTable (if rawSchema k == schemaName inf then inf else justError "no schema" $ HM.lookup ((rawSchema k ))  (depschema inf) ) k
    putPatch (patchVar ref ) $ (\(TableModification id t f)-> f) <$>v
    ) (M.toList aggr)
  return md


withDynamic :: (forall b . IO b -> IO b) -> Dynamic a -> Dynamic a
withDynamic  f i =  do
  (v,e) <- liftIO $ f (runDynamic i)
  mapM registerDynamic e
  return v


transaction :: InformationSchema -> TransactionM a -> Dynamic a
transaction inf log = withDynamic ((transactionEd $ schemaOps inf) inf ) $ do
  (md,_,mods)  <- runRWST log inf M.empty
  let aggr = foldr (\tm@(TableModification id t f) m -> M.insertWith mappend t [tm] m) M.empty mods
  Tra.traverse (\(k,v) -> do
    ref <- prerefTable (if rawSchema k == schemaName inf then inf else justError "no schema" $ HM.lookup ((rawSchema k ))  (depschema inf) ) k
    nm <- mapM (logger (schemaOps inf) inf) v
    putPatch (patchVar ref ) $ (\(TableModification id t f)-> f) <$> nm
    ) (M.toList aggr)
  return md

fullDiffEditInsert :: TBData Key Showable -> TBData Key Showable -> TransactionM  (TBData Key Showable)
-- fullDiffEditInsert old@((k1,v1) ) (k2,v2)  | traceShow ("fullDiffEditInsert",v1,v2) False = undefined
fullDiffEditInsert old@((k1,v1) ) (k2,v2) = do
   inf <- ask
   let proj = _kvvalues . unTB
   edn <- (k2,) . _tb . KV <$>  Tra.sequence (M.intersectionWith (\i j -> _tb <$>  tbDiffEditInsert (unTB i) (unTB j) ) (proj v1 ) (proj v2))
   when (isJust $ diff (tableNonRef' old) (tableNonRef' edn) ) $ do
      mod <- traverse (updateFrom   old ) (diff old edn)
      tell (maybeToList $ join  mod)
   return edn


fullDiffEdit :: TBData Key Showable -> TBData Key Showable -> TransactionM  (TBData Key Showable)
-- fullDiffEdit old@((k1,v1) ) (k2,v2)  | traceShow ("fullDiffEditInsert",v1,v2) False = undefined
fullDiffEdit old@((k1,v1) ) (k2,v2) = do
   inf <- ask
   let proj = _kvvalues . unTB
   edn <- (k2,) . _tb . KV <$>  Tra.sequence (M.intersectionWith (\i j -> _tb <$>  tbDiffEdit (unTB i) (unTB j) ) (proj v1 ) (proj v2))
   when (isJust $ diff (tableNonRef' old) (tableNonRef' edn) ) $ do
      mod <- traverse (updateFrom   old ) (diff old edn)
      tell (maybeToList $ join mod)
   return edn

fullDiffInsert :: TBData Key Showable -> TransactionM  (Maybe (TableModification (RowPatch Key Showable)))
fullDiffInsert (k2,v2) = do
   inf <- ask
   let proj = _kvvalues . unTB
   edn <- (k2,) . _tb . KV <$>  Tra.sequence ((\ j -> _tb <$>  tbInsertEdit ( unTB j) ) <$>  (proj v2))
   mod <- insertFrom  (edn)
   tell (maybeToList $mod)
   return mod


tbDiffEditInsert :: Column Key Showable -> Column Key Showable -> TransactionM (Column Key  Showable)
tbDiffEditInsert i j
  | i == j =  return j
  | otherwise = tbInsertEdit  j

tbDiffEdit :: Column Key Showable -> Column Key Showable -> TransactionM (Column Key  Showable)
tbDiffEdit i j
  | i == j =  return j
  | otherwise = tbEdit i j

tbEdit :: Column Key Showable -> Column Key Showable -> TransactionM (Column Key Showable)
tbEdit (Fun a1 _ a2) (Fun k1 rel k2)= return $ (Fun k1 rel k2)
tbEdit (Attr a1 a2) (Attr k1 k2)= return $ (Attr k1 k2)
tbEdit (IT a1 a2) (IT k2 t2) = IT k2 <$> noInsert t2
tbEdit g@(FKT apk arel2  a2) f@(FKT pk rel2  t2) =
   case (a2,t2) of
        (TB1 o@(om,ol),TB1 t@(m,l)) -> do
           let relTable = M.fromList $ fmap (\(Rel i _ j ) -> (j,i)) rel2
           local (\inf -> fromMaybe inf (HM.lookup (_kvschema m) (depschema inf))) ((\tb -> FKT ((maybe (kvlist []) ( kvlist . fmap _tb ) $ backFKRef relTable  (keyAttr .unTB <$> unkvlist pk) (unTB1 tb))) rel2 tb ) . TB1  <$> fullDiffEdit o t)
        (LeftTB1  _ ,LeftTB1 _) ->
           maybe (return f ) (fmap attrOptional) $ liftA2 tbEdit (unLeftItens g) (unLeftItens f)
        (ArrayTB1 o,ArrayTB1 l) ->
           (fmap (attrArray f .Non.fromList)) $  Tra.traverse (\ix ->   tbEdit ( justError ("cant find " <> show (ix,f)) $ unIndex ix g )( justError ("cant find " <> show (ix,f)) $ unIndex ix f ) )  [0.. Non.length l - 1 ]
        i -> errorWithStackTrace (show i)


tbInsertEdit :: Column Key Showable -> TransactionM (Column Key Showable)
tbInsertEdit j@(Attr k1 k2) = return $ (Attr k1 k2)
tbInsertEdit j@(Fun k1 rel k2) = return $ (Fun k1 rel k2)
tbInsertEdit (IT k2 t2) = IT k2 <$> noInsert t2
tbInsertEdit f@(FKT pk rel2  t2) =
   case t2 of
        t@(TB1 (m,l)) -> do
           let relTable = M.fromList $ fmap (\(Rel i _ j ) -> (j,i)) rel2
           local (\inf -> fromMaybe inf (HM.lookup (_kvschema m) (depschema inf))) ((\tb -> FKT ((maybe (kvlist []) ( kvlist . fmap _tb ) $ backFKRef relTable  (keyAttr .unTB <$> unkvlist pk) (unTB1 tb))) rel2 tb ) <$> fullInsert  t)
        LeftTB1 i ->
           maybe (return f ) ((fmap attrOptional) . tbInsertEdit ) (unLeftItens f)
        ArrayTB1 l -> do
          (fmap (attrArray f .Non.fromList)) $  Tra.traverse (\ix ->   tbInsertEdit $ justError ("cant find " <> show (ix,f)) $ unIndex ix f  )  [0.. Non.length l - 1 ]


loadFKS table = do
  inf <- ask
  let
    targetTable = lookTable inf (_kvname (fst table))
    fkSet:: S.Set Key
    fkSet =   S.unions . fmap (S.fromList . fmap _relOrigin . (\i -> if all isInlineRel i then i else filterReflexive i ) . S.toList . pathRelRel ) $ filter isReflexive  $ S.toList  (rawFKS targetTable)
    items = unKV . snd  $ table
  fks <- catMaybes <$> mapM (loadFK ( table )) (F.toList $ rawFKS targetTable)
  let
    nonFKAttrs :: [(S.Set (Rel Key) ,Column Key Showable)]
    nonFKAttrs =  fmap (fmap unTB) $M.toList $  M.filterWithKey (\i a -> not $ S.isSubsetOf (S.map _relOrigin i) fkSet) items
  return  $ tblist' targetTable (fmap _tb $fmap snd nonFKAttrs <> fks )

loadFK :: TBData Key Showable -> Path (S.Set Key ) SqlOperation -> TransactionM (Maybe (Column Key Showable))
loadFK table (Path ori (FKJoinTable rel (st,tt) ) ) = do
  inf <- ask
  let targetTable = lookTable inf tt
  (i,(_,mtable )) <- tableLoader targetTable Nothing Nothing [] mempty
  let
      relSet = S.fromList $ _relOrigin <$> rel
      tb  = unTB <$> F.toList (M.filterWithKey (\k l ->  not . S.null $ S.map _relOrigin  k `S.intersection` relSet)  (unKV . snd . tableNonRef' $ table))
      fkref = joinRel  (tableMeta targetTable) (fmap (replaceRel rel) tb ) mtable
  return $ Just $ FKT (kvlist $ _tb <$> tb) rel   fkref
loadFK table (Path ori (FKInlineTable to ) )   = do
  runMaybeT $ do
    IT rel vt  <- MaybeT . return $ unTB <$> M.lookup (S.map Inline   ori) (unKV .snd $ table)
    loadVt <- lift $ Tra.traverse loadFKS vt
    return $ IT rel loadVt

loadFK  _ _ = return Nothing

refTables' inf table page pred = do
    (ref,res)  <-  transactionNoLog inf $ selectFrom (tableName table ) page Nothing  [] pred
    return (idxTid ref,res,collectionTid ref,collectionSecondaryTid ref ,patchVar $ iniRef ref)


refTables inf table = refTables' inf table Nothing mempty


lookAttrM  inf k (i,m) = unTB <$> M.lookup (S.singleton (Inline (lookKey inf (_kvname i) k))) (unKV m)

lookAttrs' inf k (i,m) = unTB $ err $  M.lookup (S.fromList (lookKey inf (_kvname i) <$> k)) ta
    where
      ta = M.mapKeys (S.map _relOrigin) (unKV m)
      err= justError ("no attr " <> show k <> " for table " <> show (_kvname i,M.keys ta ))

lookAttr' inf k (i,m) = unTB $ err $  M.lookup (S.singleton ((lookKey inf (_kvname i) k))) ta
    where
      ta = M.mapKeys (S.map _relOrigin) (unKV m)
      err= justError ("no attr " <> show k <> " for table " <> show (_kvname i,M.keys ta))


