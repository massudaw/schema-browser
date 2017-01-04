{-# LANGUAGE RecursiveDo,TypeFamilies,FlexibleContexts,OverloadedStrings,TupleSections #-}
module SchemaQuery
  (
  createUn
  ,takeMany
  ,convertChanEvent
  ,applyBackend
  ,tellPatches
  ,selectFromA
  ,selectFrom
  ,updateFrom
  ,patchFrom
  ,insertFrom
  ,syncFrom
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
import Types.Index (checkPred)
import Control.Concurrent
import Control.Monad.Catch

import qualified Data.GiST.BTree as G
import Control.Monad.RWS
import Step.Common

import Data.Time
import qualified Control.Lens as Le
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

estLength page size est = fromMaybe 0 page * size  +  est

refTableSTM :: InformationSchema -> Table -> STM (DBRef KeyUnique Showable)
refTableSTM  inf table  = do
  mmap <- readTMVar (mvarMap inf)
  return $ justError ("cant find mvar" <> show table) (M.lookup (table) mmap )


prerefTable :: MonadIO m => InformationSchema -> Table -> m (DBRef KeyUnique Showable)
prerefTable  inf table  = do
  mmap <- liftIO$ atomically $ readTMVar (mvarMap inf)
  return $ justError ("cant find mvar" <> show table) (M.lookup (table) mmap )




refTable :: InformationSchema -> Table -> Dynamic DBVar
  {-refTable  inf (Union table origin )  = do
  refs <- mapM (refTable inf ) origin
  let mergeDBRefT  (ref1,j ,i) (ref2,m ,l) = (ref1 <> ref2 ,liftA2 (M.unionWith (\(a,b) (c,d) -> (a+c,b<>d)))  j  m , liftA2 (<>) i l )
      dbvarMerge = foldr mergeDBRefT  ([],pure M.empty ,pure G.empty) (Le.over Le._3 (fmap (createUn (rawPK table).fmap projunion.G.toList)) .(\(DBVar2 e i j) -> ([e],i,j)) <$>refs )
      dbvar (l,i,j) = DBVar2 (L.head l) i j
      projunion :: TBData Key Showable -> TBData Key Showable
      projunion  i = res
            where
              res = liftTable' inf (tableName table ) .mapKey' keyValue $i

  return $ dbvar dbvarMerge-}
refTable  inf table  = do
  mmap <- liftIO$ atomically $ readTMVar (mvarMap inf)
  let ref = justError ("cant find mvar" <> show table) (M.lookup (table) mmap )
  idxTds<- convertChanStepper  inf (mapTableK keyFastUnique table) ref
  (dbTds ,dbEvs)<- convertChanTidings inf (mapTableK keyFastUnique table) mempty  ref
  return (DBVar2 ref idxTds  dbTds dbEvs)

tbpredM un  = G.notOptional . G.getUnique un

createUn :: Ord k => [k] -> [TBData k Showable] -> G.GiST (G.TBIndex Showable) (TBData k Showable)
createUn un   =  G.fromList  transPred  .  filter (\i-> isJust $ Tra.traverse (Tra.traverse unSOptional' ) $ getUn (S.fromList un) (tableNonRef' i) )
  where transPred  =  G.notOptional . G.getUnique un . tableNonRef'


applyBackend (CreateRow t@(m,i)) = do
   insertFrom   t
applyBackend (PatchRow t@(m,i,[])) = do
   deleteFrom   t
applyBackend (PatchRow p@(m,pk@(G.Idex pki),i)) = do
   inf <- ask
   ref <- prerefTable inf  (lookTable inf (_kvname m))
   (v,_,_) <- liftIO$ atomically $ readState (WherePredicate (AndColl []),fmap keyFastUnique $ _kvpk m) ref
   let oldm = mapKey' (recoverKey inf ) <$>  G.lookup pk v

   old <- maybe (do
     (_,(i,o)) <- selectFrom (_kvname m) Nothing Nothing [] (WherePredicate (AndColl ((\(k,o) -> PrimColl (IProd Nothing [k],Left (justError "no opt " $ unSOptional' o,Equals))) <$> zip (_kvpk m) pki)))
     return $ L.head $ G.toList o
        ) return oldm
   if isJust (diff old  (apply old p))
     then updateFrom   old   (apply  old p)
     else return Nothing

selectFromA t a b c d = do
  inf <- ask
  tableLoader (lookTable inf t) a b c d

selectFrom t a b c d = do
  inf <- ask
  tableLoader (lookTable inf t) a b c d

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
  (deleteEd $ schemaOps inf)  a


mergeDBRef  = (\(j,i) (m,l) -> ((M.unionWith (\(a,b) (c,d) -> (a+c,b<>d))  j  m , i <>  l )))

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
                                test f (Nested (IProd _ p) (Many[i] ),j)  = if p == f then Just (i ,j) else Nothing
                                test f (Nested (IProd _ p) i ,j)  = if p == f then Just (i ,j) else Nothing
                                test v f = Nothing
                             in  fmap WherePredicate (go (test (S.toList r)) l)

                -- editAttr :: (TBData Key Showable -> TBData Key Showable) -> TBData Key Showable -> TBData Key Showable
                editAttr fun  (m,i) = (m,mapComp (\(KV i) -> KV (M.alter  (fmap (mapComp (Le.over fkttable (fmap (either undefined  id .fun))))) (S.map Inline r)  i )) i )
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
    addAttr :: TBData Key Showable -> Either [Compose Identity (TB Identity)  Key Showable] (TBData Key Showable)
    addAttr (m,i) = maybe (Left []) (\r -> Right (m,mapComp (\(KV i) -> KV (M.insert (S.fromList $ keyattri r) (_tb r)   i) ) i)) r
      where
        r =  evaluate a b funmap c (m,i)
  return (evs,me >=> addAttr ,old <> ref )


getFKRef inf predtop rtable (evs,me,old) v path@(Path _ (FKJoinTable i j ) ) =  do
                let rinf = maybe inf id $ HM.lookup ((fst j))  (depschema inf)
                    table = lookTable rinf $ snd j
                    predicate predtop = case predtop of
                                  WherePredicate l ->
                                    let
                                      go pred (AndColl l) = AndColl <$> nonEmpty (catMaybes $ go pred <$> l)
                                      go pred (OrColl l) = OrColl <$> nonEmpty (catMaybes $ go pred <$> l)
                                      go pred (PrimColl l) = PrimColl <$> pred l
                                      test f (Nested (IProd _ p) (Many[i] ),j)  = if p == f then Just ( i ,left (fmap (removeArray (keyType $ L.head p))) j) else Nothing
                                      test f (Nested (IProd _ p) i ,j)  = if p == f then Just ( i ,left (fmap (removeArray (keyType $L.head p))) j) else Nothing
                                      test v f = Nothing
                                      removeArray (KOptional i)  o = removeArray i o
                                      removeArray (KArray i)  (AnyOp o) = o
                                      removeArray i  o = o
                                   in  fmap WherePredicate (go (test (_relOrigin <$> i)) l)
                let refs = (   fmap (WherePredicate .OrColl. L.nub) $ nonEmpty $ catMaybes $ (\o -> fmap AndColl . allMaybes . fmap (\k ->join . fmap (fmap (OrColl. fmap (\i->PrimColl (IProd notNull [_relTarget $ k] ,Left (i,Flip $ _relOperator k))).F.toList .unArray') . unSOptional' . _tbattr.unTB) . M.lookup (S.singleton (Inline (_relOrigin k))) $ o) $ i ) . unKV .snd <$> v )
                    predm = (refs<> predicate predtop)
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
                    evt = filterJust $ nonEmpty  . fmap (\(PatchRow p@(_,G.Idex v,_)) ->  (WherePredicate $ AndColl ((\(Rel o op t) -> PrimColl (IProd Nothing [o] , Left (v !! (justError "no key" $  t`L.elemIndex` rawPK table),op))) <$> i ), (kvempty,G.Idex [] ,[PFK i [] (PAtom p)]))) . filter isPatch <$> ref
                    isPatch (PatchRow _ ) = True
                    isPatch i = False
                    tar = S.fromList $ fmap _relOrigin i
                    refl = S.fromList $ fmap _relOrigin $ filterReflexive i
                    inj = S.difference refl old
                    joinFK :: TBData Key Showable -> Either [Compose Identity (TB Identity)  Key Showable] (Column Key Showable)
                    joinFK m  = maybe (Left taratt) Right $ FKT (kvlist tarinj ) i <$> joinRel2 (tableMeta table ) (fmap (replaceRel i )$ fmap unTB $ taratt ) tb2
                      where
                        replaceRel rel (Attr k v) = (justError "no rel" $ L.find ((==k) ._relOrigin) rel,v)
                        taratt = getAtt tar (tableNonRef' m)
                        tarinj = getAtt inj (tableNonRef' m)
                    addAttr :: Column Key Showable -> TBData Key Showable -> TBData Key Showable
                    addAttr r (m,i) = (m,mapComp (\(KV i) -> KV (M.insert (S.fromList $ keyattri r) (_tb r)  $ M.filterWithKey (\k _ -> not $ S.map _relOrigin k `S.isSubsetOf` refl && F.all isInlineRel k   ) i )) i )
                    joined i = do
                       fk <- joinFK i
                       return $ addAttr  fk i
                return (unionWith mappend evt evs,me >=> joined,old <> refl)
    where
        getAtt i (m ,k ) = filter ((`S.isSubsetOf` i) . S.fromList . fmap _relOrigin. keyattr ) . F.toList . _kvvalues . unTB $ k

left f (Left i ) = Left (f i)
left f (Right i ) = (Right i)

getFKS
  :: InformationSchemaKV Key Showable
     -> TBPredicate Key Showable
     -> TableK Key
     -> [TBData Key Showable]
     -> TransactionM
          (Event [(WherePredicate,TBIdx Key Showable)],TBData Key Showable -> Either
                [Compose Identity (TB Identity) Key Showable]
                (TBData Key Showable),
           S.Set Key)
getFKS inf predtop table v = F.foldl' (\m f  -> m >>= (\i -> getFKRef inf predtop  table i v f)) (return (never,return ,S.empty )) $ sorted -- first <> second
  where first =  filter (not .isFunction . pathRel )$ sorted
        second = filter (isFunction . pathRel )$ sorted
        sorted = P.sortBy (P.comparing pathRelRel)  (S.toList (rawFKS table))

rebaseKey inf t  (WherePredicate fixed ) = WherePredicate $ ( lookAccess inf (tableName t) . (Le.over Le._1 (fmap  keyValue) )<$> fixed)

tableLoader :: Table -> Maybe Int -> Maybe Int -> [(Key,Order)] -> WherePredicate
    -> TransactionM (DBVar,Collection Key Showable)
tableLoader table  page size presort fixed
  -- Union Tables
  | not $ L.null $ rawUnion table  = do
    liftIO$ putStrLn $ "start loadTable " <> show (tableName table)
    li <- liftIO getCurrentTime
    inf <- ask
    i <- mapM (\t -> do
      l <- tableLoader t page size presort (rebaseKey inf t  fixed)
      return l
              )  (rawUnion table)
    let mvar = mvarMap inf
    mmap <- liftIO $ atomically $ readTMVar mvar
    let
        projunion :: TBData Key Showable -> TBData Key Showable
        projunion  i = res
            where
              res = liftTable' inf (tableName table ) .mapKey' keyValue $i
        o = foldr mergeDBRef  (M.empty,G.empty) (fmap (createUn (rawPK table).fmap projunion.G.toList) . snd <$>i )
    modify (M.insert (table,fixed) ( mapKey' keyFastUnique <$> snd o ))
    let mergeDBRefT  (ref1,j ,i,k) (ref2,m ,l,n) = (ref1 <> ref2 ,liftA2 (M.unionWith (\(a,b) (c,d) -> (a+c,b<>d)))  j  m , liftA2 (<>) i l ,unionWith mappend k n)
        dbvarMerge = foldr mergeDBRefT  ([],pure M.empty ,pure G.empty,never) (Le.over Le._3 (fmap (createUn (rawPK table).fmap projunion.G.toList)) .(\(DBVar2 e i j k ) -> ([e],i,j,k)). fst <$>i )
        dbvar (l,i,j,k) = DBVar2 (L.head l) i j k

    lf <- liftIO getCurrentTime
    liftIO $ putStrLn $ "finish loadTable" <> show  (tableName table) <> " - " <> show (diffUTCTime lf  li)
    return $ (dbvar dbvarMerge, o)
  -- (Scoped || Partitioned) Tables
  | not  (null $ _rawScope table ) && not (S.null (rawFKS table) )= do
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
  -- Primitive Tables
  | otherwise  =  do
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
                predicate (Nested (IProd b i) j ,Left _ ) = (\a -> (IProd b [a], Right (Not IsNull))) <$> i
                predicate i  = [i]
            tbf = tableView  (tableMap inf) table
          (res ,x ,o) <- (listEd $ schemaOps inf) (tableNonRef2 tbf) page size presort fixed (unestPred predtop)
          (evs,resFKS ,_)<- getFKS inf predtop table res
          let result = fmap resFKS   res
          liftIO $ when (not $ null (lefts result)) $ do
            print ("lefts",tableName table ,lefts result)
          return (rights  result,x,o )) table page size presort fixed
    lf <- liftIO getCurrentTime
    liftIO $ putStrLn $ "finish loadTable" <> show  (tableName table) <> " - " <> show (diffUTCTime lf  li)
    return o



joinSyncTable reflist  a b c d f e =
    ask >>= (\ inf -> pageTable True ((joinSyncEd $ schemaOps inf) reflist e ) a b c d f )



joinTable :: [(Table,TBData Key Showable,Path (S.Set Key ) SqlOperation )]-> Table -> Maybe Int -> Maybe Int -> [(Key,Order)] -> WherePredicate
    -> TransactionM (DBVar,Collection Key Showable)
joinTable reflist  a b c d e =
    ask >>= (\ inf -> pageTable False ((joinListEd $ schemaOps inf) reflist) a b c d e )



predNull (WherePredicate i) = L.null i

filterfixed table fixed v
  = if predNull fixed
       then v
       else G.queryCheck (fixed ,rawPK table) v




pageTable flag method table page size presort fixed = do
    inf <- ask
    let mvar = mvarMap inf
        tableU = mapTableK keyFastUnique table
        fixedU = mapPredicate keyFastUnique fixed
        defSort = fmap (,Desc) $  rawPK table
        sortList  = if L.null presort then defSort else  presort
        pagesize = maybe (opsPageSize $ schemaOps inf)id size
        ffixed = filterfixed  tableU fixedU
    mmap <- liftIO $ atomically $ readTMVar mvar
    let
      dbvar :: DBRef KeyUnique Showable
      dbvar =  justError ("cant find mvar" <> show table) (M.lookup (table) mmap )
    (reso ,nchan,iniVar) <- liftIO $ atomically $
      readState (fixedU ,rawPK tableU) dbvar

    ((fixedmap,fixedChan),idxVL)  <- liftIO $ atomically $
      liftA2 (,) (readIndex dbvar) (readTVar (idxVarLoad dbvar))
    iniT <- do

       loadmap <- get
       let pageidx = (fromMaybe 0 page +1) * pagesize
           freso =  fromMaybe fr (M.lookup (table ,fixed) loadmap )
              where fr = ffixed reso
           predreq = (fixedU,G.Contains (pageidx - pagesize,pageidx))
             {-diffpred'  i@(WherePredicate (AndColl [])) = Just i
           diffpred'  (WherePredicate f ) = WherePredicate <$> foldl (\i f -> i >>= (\a -> G.splitIndex a (rawPK table)f)  ) (Just  f)  (fmap snd $ G.getEntries freso)
           diffpred = diffpred' fixedU-}
           hasIndex = M.lookup fixedU fixedmap
           (sq ,_)= justError "no index" hasIndex

       i <-  if flag || ( (isNothing hasIndex|| (sq > G.size freso)) -- Tabela é maior que a tabela carregada
                && pageidx  > G.size freso ) -- O carregado é menor que a página
               && (isNothing (join $ fmap (M.lookup pageidx . snd) $ M.lookup fixedU fixedmap)  -- Ignora quando página já esta carregando
                                                                                       -- && isJust diffpred
                   )
             then do


               let pagetoken =  (join $ flip M.lookupLE  mp . (*pagesize) <$> page)
                   (_,mp) = fromMaybe (0,M.empty ) hasIndex
               liftIO$ putStrLn $ "new page " <> show (tableName table, pageidx, G.size freso,G.size reso,page, pagesize)
               (resK,nextToken ,s ) <- method table (liftA2 (-) (fmap (*pagesize) page) (fst <$> pagetoken)) (fmap snd pagetoken) size sortList fixed-- (justError "no pred" diffpred)
               let
                   res = fmap (mapKey' keyFastUnique ) resK
                   token =  nextToken
                   index = (estLength page pagesize (s + G.size freso) , maybe (M.insert pageidx HeadToken) (M.insert pageidx ) token $ mp)
               liftIO$ do
                 putIdx (idxChan dbvar ) (fixedU {-justError"no pred" diffpred-},estLength page pagesize s, pageidx ,fromMaybe HeadToken token)
                 putPatch (patchVar dbvar) (F.toList $ CreateRow <$> filter (\i -> isNothing $ G.lookup (G.getIndex i) reso  )   resK)
               return  (index,res <> G.toList freso)
             else do

               liftIO$ putStrLn $ "keep page " <> show (tableName table, pageidx, G.size freso,G.size reso,page, pagesize)
               return (fromMaybe (0,M.empty) hasIndex ,[])
       let nidx =  M.insert fixedU (fst i)
           ndata = snd i
       return (nidx fixedmap, if L.length ndata > 0 then createUn (rawPK tableU)  ndata <> freso else  freso )
    let iniFil = iniT
    modify (M.insert (table,fixed) ( snd $iniT))
    (vpt ,evpt)<- lift $ convertChanTidings0 inf tableU (fixedU ,rawPK tableU) (snd iniFil) iniVar nchan
    idxTds <- lift $ convertChanStepper0 inf (tableU) fixedmap fixedChan
    return (DBVar2 dbvar idxTds vpt evpt ,first (M.mapKeys (mapPredicate (recoverKey inf))).fmap (fmap (mapKey' (recoverKey inf)) )$iniFil)

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
      (TBPredicate k Showable, [k ])
     -> DBRef k v
     -> STM (TableIndex k v, TChan [RowPatch k v], TVar (TableIndex k v))
readState fixed dbvar = do
  var <-readTVar (collectionState dbvar)
  chan <- cloneTChan (patchVar dbvar)
  patches <- takeMany' chan
  let
      filterPred = nonEmpty . filter (\d -> splitMatch fixed (indexPK d) && indexFilterR (fst fixed) d )
      update = F.foldl' (flip (\p-> (flip apply p)))
  return (update var (concat patches),chan,collectionState dbvar)

indexPK (CreateRow i) = G.getIndex i
indexPK (PatchRow (_,i,_) ) = i

indexFilterR j (CreateRow i) = checkPred i j
indexFilterR j (PatchRow i) = indexFilterP j i

patchCheck (m,s,i) = if checkAllFilled then Right (m,s,i) else Left ("non nullable rows not filled " ++ show ( need `S.difference` available ))
  where
      checkAllFilled =  need `S.isSubsetOf`  available
      available = S.unions $ S.map _relOrigin . pattrKey <$> i
      need = S.fromList $ L.filter (\i -> not (isKOptional (keyType i) || isSerial (keyType i) || isJust (keyStatic i )) )  (kvAttrs m)

tableCheck (m,t) = if checkAllFilled then Right (m,t) else Left ("non nullable rows not filled " ++ show ( need `S.difference` available ))
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
            h a ) (\e -> atomically ( takeMany nchan ) >>= (\d ->  appendFile ("errors/data-" <> T.unpack ( tableName table )) $ show (e :: SomeException,d)<>"\n"))
        let conv (v,s,i,t) = (M.alter (\j -> fmap ((\(_,l) -> (s,M.insert i t l ))) j  <|> Just (s,M.singleton i t)) (mapPredicate (recoverKey inf) v) )
        bh <- accumB (M.mapKeys (mapPredicate (recoverKey inf))ini) ((\l i-> F.foldl' (flip conv) i l)<$> e)
        registerDynamic (killThread t)
        return (tidings bh ((\i l-> F.foldl' (flip conv) i l)<$> bh<@> e))

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
     -> Behavior (G.GiST (TBIndex Showable) a)
     -> TVar (G.GiST (TBIndex Showable) (TBData k Showable))
     -> TChan [RowPatch k Showable ]
     -> Dynamic
          (Event [RowPatch k Showable])
convertChanEvent table fixed bres inivar chan = do
  (e,h) <- newEvent
  t <- liftIO $ forkIO $ forever $ catchJust notException (do
    (ml,oldM) <- atomically $ (,) <$> takeMany chan <*> readTVar inivar
    v <- currentValue bres
    let
        m = concat ml
        newRows =  filter (\d -> splitMatch fixed (indexPK d) && indexFilterR (fst fixed) d && isNothing (G.lookup (indexPK d) v) ) m
        filterPred = nonEmpty . filter (\d -> splitMatch fixed (indexPK d) && indexFilterR (fst fixed) d )
        lookNew  d = fmap CreateRow $ G.lookup (indexPK d) oldM
        filterPredNot j = nonEmpty . catMaybes . map (\d -> if isJust ( G.lookup (indexPK d) j) && not (splitMatch fixed (indexPK d) && indexFilterR (fst fixed) d ) then Just (PatchRow (tableMeta table ,indexPK d,[])) else Nothing )
        newpatches = lookNew <$> newRows
        oldRows =  filterPredNot v m
        patches =  nonEmpty ( catMaybes newpatches )<> oldRows <> filterPred m

    traverse  h patches
    return () )(\e -> atomically ( takeMany chan ) >>= (\d ->  appendFile ("errors/data-" <> T.unpack ( tableName table )) $ show (e :: SomeException,d)<>"\n"))
  registerDynamic (killThread t)
  return e

convertChanTidings
 ::
  InformationSchema -> TableK KeyUnique
  -> (TBPredicate KeyUnique Showable, [KeyUnique ])
     -> DBRef KeyUnique Showable
     -> Dynamic
    (Tidings (G.GiST (TBIndex Showable) (TBData Key Showable)),Event [RowPatch Key Showable])
convertChanTidings inf table fixed dbvar = do
      (ini,nchan,inivar) <- liftIO $atomically $
        readState fixed  dbvar
      convertChanTidings0 inf table fixed ini inivar nchan


splitMatch (WherePredicate b,o) p = maybe True (\i -> G.match (mapPredicate (justError "no index" . flip L.elemIndex o ) $ WherePredicate i ) (Right p)  ) (G.splitIndexPK b o)

convertChanTidings0
  ::
  InformationSchema -> TableK KeyUnique
     -> (TBPredicate KeyUnique Showable, [KeyUnique])
     -> G.GiST (TBIndex Showable) (TBData KeyUnique Showable)
     -> TVar (G.GiST (TBIndex Showable) (TBData KeyUnique Showable))
     -> TChan
          [RowPatch KeyUnique Showable ]
          -> Dynamic (Tidings (G.GiST (TBIndex Showable) (TBData Key Showable)),Event [RowPatch Key Showable])
convertChanTidings0 inf table fixed ini iniVar nchan = mdo
    evdiffp <-  convertChanEvent table fixed bres iniVar nchan
    let
      evdiff = fmap (firstPatchRow (recoverKey inf)) <$> evdiffp
      update l = F.foldl' (flip (\p-> (flip apply p) )) l
    bres <- accumB (mapKey' (recoverKey inf) <$>ini) (flip update <$> evdiff)
    return $(tidings bres (update <$> bres <@> evdiff),evdiff)

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
fullInsert' ((k1,v1) )  = do
   inf <- ask
   let proj = _kvvalues . unTB
       tb  = (lookTable inf (_kvname k1))
   ret <-  (k1,) . _tb . KV <$>  Tra.traverse (\j -> _tb <$>  tbInsertEdit (unTB j) )  (proj v1)
   (_,(_,l)) <- tableLoader  tb Nothing Nothing [] (mempty)
   if  (isNothing $ flip G.lookup l $ tbpredM (_kvpk k1)  ret ) && rawTableType tb == ReadWrite
      then catchAll (do
        i@(Just (TableModification _ _ tb))  <- insertFrom  ret
        tell (maybeToList i)
        return $ createRow tb) (\e -> return ret)
      else do
        return ret

tellPatches :: [TableModification (RowPatch Key Showable)] -> TransactionM ()
tellPatches = tell

noInsert = Tra.traverse (noInsert' )

noInsert' :: TBData Key Showable -> TransactionM  (TBData Key Showable)
noInsert' (k1,v1)   = do
   let proj = _kvvalues . unTB
   (k1,) . _tb . KV <$>  Tra.sequence (fmap (\j -> _tb <$>  tbInsertEdit (unTB j) )  (proj v1))

transactionLog :: InformationSchema -> TransactionM a -> Dynamic [TableModification (RowPatch Key Showable)]
transactionLog inf log = do -- withTransaction (conn inf) $ do
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


transaction :: InformationSchema -> TransactionM a -> Dynamic a
transaction inf log = do -- withTransaction (conn inf) $ do
  (md,_,mods)  <- runRWST log inf M.empty
  let aggr = foldr (\tm@(TableModification id t f) m -> M.insertWith mappend t [tm] m) M.empty mods
  Tra.traverse (\(k,v) -> do
    ref <- prerefTable (if rawSchema k == schemaName inf then inf else justError "no schema" $ HM.lookup ((rawSchema k ))  (depschema inf) ) k
    nm <- mapM (logger (schemaOps inf) inf) v
    putPatch (patchVar ref ) $ (\(TableModification id t f)-> f) <$> nm
    ) (M.toList aggr)
  return md

fullDiffEditInsert :: TBData Key Showable -> TBData Key Showable -> TransactionM  (TBData Key Showable)
fullDiffEditInsert old@((k1,v1) ) (k2,v2) = do
   inf <- ask
   let proj = _kvvalues . unTB
   edn <- (k2,) . _tb . KV <$>  Tra.sequence (M.intersectionWith (\i j -> _tb <$>  tbDiffEditInsert (unTB i) (unTB j) ) (proj v1 ) (proj v2))
   when (isJust $ diff (tableNonRef' old) (tableNonRef' edn) ) $ do
      mod <- updateFrom   edn old
      tell (maybeToList mod)
   return edn


fullDiffEdit :: TBData Key Showable -> TBData Key Showable -> TransactionM  (TBData Key Showable)
fullDiffEdit old@((k1,v1) ) (k2,v2) = do
   inf <- ask
   let proj = _kvvalues . unTB
   edn <- (k2,) . _tb . KV <$>  Tra.sequence (M.intersectionWith (\i j -> _tb <$>  tbDiffEdit (unTB i) (unTB j) ) (proj v1 ) (proj v2))
   when (isJust $ diff (tableNonRef' old) (tableNonRef' edn) ) $ do
      mod <- updateFrom   edn old
      tell (maybeToList mod)
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
           local (\inf -> fromMaybe inf (HM.lookup (_kvschema m) (depschema inf))) ((\tb -> FKT ( kvlist $ fmap _tb $ backFKRef relTable  (keyAttr .unTB <$> unkvlist pk) (unTB1 tb)) rel2 tb ) . TB1  <$> fullDiffEdit o t)
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
           local (\inf -> fromMaybe inf (HM.lookup (_kvschema m) (depschema inf))) ((\tb -> FKT ( kvlist $ fmap _tb $ backFKRef relTable  (keyAttr .unTB <$> unkvlist pk) (unTB1 tb)) rel2 tb ) <$> fullInsert  t)
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

