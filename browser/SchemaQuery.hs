{-# LANGUAGE TypeFamilies,FlexibleContexts,OverloadedStrings,TupleSections #-}
module SchemaQuery
  (
  createUn
  ,takeMany
  ,convertChanEvent
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
  ,loadFKS
  ,fullDiffInsert
  ,fullDiffEdit
  ,fullDiffEditInsert
  ,transaction
  ,transactionLog
  ,transactionNoLog
  ,filterfixed
  )where
import Graphics.UI.Threepenny.Core (mapEventDyn)

import RuntimeTypes
import Step.Host
import Expression
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

prerefTable :: MonadIO m => InformationSchema -> Table -> m (DBRef Key Showable)
prerefTable  inf table  = do
  mmap <- liftIO$ atomically $ readTMVar (mvarMap inf)
  return $ justError ("cant find mvar" <> show table) (M.lookup (table) mmap )



refTable :: InformationSchema -> Table -> Dynamic DBVar
refTable  inf table  = do
  mmap <- liftIO$ atomically $ readTMVar (mvarMap inf)
  let ref = justError ("cant find mvar" <> show table) (M.lookup (table) mmap )
  idxTds<- convertChanStepper  (idxChan ref)(idxVar ref)
  dbTds <- convertChanTidings mempty  (patchVar ref) (collectionState ref)
  return (DBVar2 ref idxTds dbTds)


tbpredM un v = G.Idex . M.fromList $ justError "optional pk" $ (Tra.traverse (Tra.traverse unSOptional' ) $getUn un v)

createUn :: S.Set Key -> [TBData Key Showable] -> G.GiST (G.TBIndex Key Showable) (TBData Key Showable)
createUn un   =  G.fromList  transPred  .  filter (\i-> isJust $ Tra.traverse (Tra.traverse unSOptional' ) $ getUn un (tableNonRef' i) )
  where transPred v = G.Idex $ M.fromList $ justError "invalid pred" (Tra.traverse (Tra.traverse unSOptional' ) $getUn un (tableNonRef' v))


-- tableLoader :: InformationSchema -> Table -> TransactionM (Collection Key Showable)


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

  return (dbvar ,foldr mergeDBRef  (M.empty,G.empty) $ fmap snd $ ix )


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

getFKRef inf predtop rtable (me,old) v (Path r (FKInlineTable  j ) ) =  do
                let rinf = maybe inf id $ HM.lookup ((fst j))  (depschema inf)
                    table = lookTable rinf $ snd j
                    predicate predtop = case predtop of
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

                (joinFK,_) <- getFKS inf predtop table nextRef
                let
                    joined i = do
                      return $ editAttr joinFK i

                return (me >=> joined,old <> r)
    where
        getAtt i (m ,k ) = filter ((`S.isSubsetOf` i) . S.fromList . fmap _relOrigin. keyattr ) . F.toList . _kvvalues . unTB $ k

getFKRef inf predtop rtable (me,old) v (Path ref (FunctionField a b c)) = do
  let
    cl = c
    addAttr :: TBData Key Showable -> Either [Compose Identity (TB Identity)  Key Showable] (TBData Key Showable)
    addAttr (m,i) = maybe (Left []) (\r -> Right (m,mapComp (\(KV i) -> KV (M.insert (S.fromList $ keyattri r) (_tb r)   i) ) i)) r
      where
        r =  evaluate a b funmap cl (m,i)
  return (me >=> addAttr ,old <> ref )

getFKRef inf predtop rtable (me,old) v (Path _ (FKJoinTable i j ) ) =  do
                let rinf = maybe inf id $ HM.lookup ((fst j))  (depschema inf)
                    table = lookTable rinf $ snd j
                    predicate predtop = case predtop of
                                  WherePredicate l ->
                                    let
                                      go pred (AndColl l) = AndColl <$> nonEmpty (catMaybes $ go pred <$> l)
                                      go pred (OrColl l) = OrColl <$> nonEmpty (catMaybes $ go pred <$> l)
                                      go pred (PrimColl l) = PrimColl <$> pred l
                                      test f (Nested (IProd _ p) (Many[i] ),j)  = if p == f then Just (i ,j) else Nothing
                                      test f (Nested (IProd _ p) i ,j)  = if p == f then Just (i ,j) else Nothing
                                      test v f = Nothing
                                   in  fmap WherePredicate (go (test (_relOrigin <$> i)) l)
                liftIO $ putStrLn $ "loadForeign table" <> show (tableName table)
                let innerpred = fmap (\pred -> WherePredicate (AndColl pred)) $ traverse (\k -> (\v -> (PrimColl (IProd True [ _relTarget $ k], Left ( if L.length v == 1 then (L.head v, _relOperator k ) else (ArrayTB1 (Non.fromList v), Flip (AnyOp (_relOperator k ))))))) <$> ( nonEmpty $ L.nub $  concat $ catMaybes $   fmap (F.toList . unArray' ) . join . fmap (  unSOptional'. _tbattr .unTB) . M.lookup (S.singleton (Inline (_relOrigin k))) . unKV .snd <$> v ))  i
                (_,(_,tb2)) <- local (const rinf) (tableLoader table  Nothing (Just 1000) []  (fromMaybe mempty $ innerpred <> predicate predtop))
                let
                    tar = S.fromList $ fmap _relOrigin i
                    refl = S.fromList $ fmap _relOrigin $ filterReflexive i
                    inj = S.difference refl old
                    joinFK :: TBData Key Showable -> Either [Compose Identity (TB Identity)  Key Showable] (Column Key Showable)
                    joinFK m  = maybe (Left taratt) Right $ FKT (kvlist tarinj ) i <$> joinRel2 (tableMeta table ) i (fmap unTB $ taratt ) tb2
                      where
                        taratt = getAtt tar (tableNonRef' m)
                        tarinj = getAtt inj (tableNonRef' m)
                    addAttr :: Column Key Showable -> TBData Key Showable -> TBData Key Showable
                    addAttr r (m,i) = (m,mapComp (\(KV i) -> KV (M.insert (S.fromList $ keyattri r) (_tb r)  $ M.filterWithKey (\k _ -> not $ S.map _relOrigin k `S.isSubsetOf` refl && F.all isInlineRel k   ) i )) i )
                    joined i = do
                       fk <- joinFK i
                       return $ addAttr  fk i
                return (me >=> joined,old <> refl)
    where
        getAtt i (m ,k ) = filter ((`S.isSubsetOf` i) . S.fromList . fmap _relOrigin. keyattr ) . F.toList . _kvvalues . unTB $ k


getFKS inf predtop table v = F.foldl' (\m f  -> m >>= (\i -> getFKRef inf predtop  table i v f)) (return (return ,S.empty )) $ sorted -- first <> second
  where first =  filter (not .isFunction . pathRel )$ sorted
        second = filter (isFunction . pathRel )$ sorted
        sorted = P.sortBy (P.comparing pathRelRel)  (S.toList (rawFKS table))

rebaseKey inf t  (WherePredicate fixed ) = WherePredicate $ ( lookAccess inf (tableName t) . (Le.over Le._1 (fmap  keyValue) )<$> fixed)

tableLoader :: Table -> Maybe Int -> Maybe Int -> [(Key,Order)] -> WherePredicate
    -> TransactionM (DBVar,Collection Key Showable)
tableLoader table  page size presort fixed
  -- Union Tables
  | not $ L.null $ rawUnion table  = do
    liftIO$ putStrLn $ "start loadTable " <> show (tableName table,fixed)
    li <- liftIO getCurrentTime
    inf <- ask
    i <- mapM (\t -> do
      l <- tableLoader t page size presort (rebaseKey inf t  fixed)
      return l
              )  (rawUnion table)
    let mvar = mvarMap inf
    mmap <- liftIO $ atomically $ readTMVar mvar
    dbvar <- lift $ refTable   inf table
    let
        projunion :: TBData Key Showable -> TBData Key Showable
        projunion  i = res
            where
              res = liftTable' inf (tableName table ) .mapKey' keyValue $i
        o = foldr mergeDBRef  (M.empty,G.empty) (fmap (createUn (S.fromList$ rawPK table).fmap projunion.G.toList) . snd <$>i )
    modify (M.insert (table,fixed) ( snd o ))
    lf <- liftIO getCurrentTime
    liftIO $ putStrLn $ "finish loadTable" <> show  (tableName table) <> " - " <> show (diffUTCTime lf  li)
    return $ (dbvar, o)
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
    liftIO$ putStrLn $ "start loadTable " <> show (tableName table,fixed)
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

          (resFKS ,_)<- getFKS inf predtop table res
          return (rights $ fmap resFKS   res,x,o )) table page size presort fixed
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

filterfixed fixed v
  = if predNull fixed
       then v
       else G.queryCheck fixed v




pageTable flag method table page size presort fixed = do
    inf <- ask
    let mvar = mvarMap inf
        defSort = fmap (,Desc) $  rawPK table
        sortList  = if L.null presort then defSort else presort
        pagesize = maybe (opsPageSize $ schemaOps inf)id size
        ffixed = filterfixed  fixed
    mmap <- liftIO $ atomically $ readTMVar mvar
    let dbvar =  justError ("cant find mvar" <> show table) (M.lookup (table) mmap )
    (reso ,nchan) <- liftIO $ atomically $
      (,) <$> readTVar (collectionState dbvar)<*> cloneTChan (patchVar dbvar)

    (fixedmap,fixedChan)  <- liftIO $ atomically $
        liftA2 (,) (readTVar (idxVar dbvar)) (cloneTChan (idxChan dbvar))
    iniT <- do

       idxVL<- liftIO$ atomically $readTVar (idxVarLoad dbvar)
       loadmap <- get
       let pageidx = (fromMaybe 0 page +1) * pagesize
           freso =  fromMaybe fr (M.lookup (table ,fixed) loadmap )
              where fr = ffixed reso
           predreq = (fixed,G.Contains (pageidx - pagesize,pageidx))
           reqs = G.query predreq idxVL
           diffpred'  i@(WherePredicate (AndColl [])) = Just i
           diffpred'  (WherePredicate f ) = WherePredicate <$> foldl (\i f -> i >>= flip G.splitIndex f  ) (Just  f)  (fmap snd $ G.getEntries freso)
           diffpred = diffpred' fixed

       liftIO$ print ((fmap snd $ G.getEntries freso),diffpred)
       i <- case  fromMaybe (10000000,M.empty ) $  M.lookup fixed fixedmap of
          (sq,mp) -> do
             if flag || (sq > G.size freso -- Tabela é maior que a tabela carregada
                && pageidx  > G.size freso ) -- O carregado é menor que a página
               && (isNothing (join $ fmap (M.lookup pageidx . snd) $ M.lookup fixed fixedmap)  -- Ignora quando página já esta carregando
                && isJust diffpred
                   )
             then do
               liftIO $ atomically $ do
                 modifyTVar' (idxVarLoad dbvar) (G.insert ((),(fixed,G.Contains (pageidx - pagesize ,pageidx))) (3,6) )

               let pagetoken =  (join $ flip M.lookupLE  mp . (*pagesize) <$> page)
               liftIO$ putStrLn $ "new page " <> show (tableName table,sq, pageidx, G.size freso,G.size reso,page, pagesize,diffpred)
               (res,nextToken ,s ) <- method table (liftA2 (-) (fmap (*pagesize) page) (fst <$> pagetoken)) (fmap snd pagetoken) size sortList (justError "no pred" diffpred)
               let
                   token =  nextToken
                   index = (estLength page pagesize s, maybe (M.insert pageidx HeadToken) (M.insert pageidx ) token$ mp)
               liftIO$ do
                 putPatch (idxChan dbvar ) (fixed ,estLength page pagesize s, pageidx ,fromMaybe HeadToken token)
                 putPatch (patchVar dbvar) (F.toList $ patch  <$> res)
               return  (index,res)
             else do
               liftIO$ putStrLn $ "keep page " <> show (tableName table,sq, pageidx, G.size freso,G.size reso,page, pagesize)
               return ((sq,mp),[])
       let nidx =  M.insert fixed (fst i)
           ndata = snd i
       return (nidx fixedmap, if L.length ndata > 0 then createUn (S.fromList $ rawPK table)  ndata <> freso else  freso )
    let iniFil = iniT
    modify (M.insert (table,fixed) ( snd $iniT))
    vpt <- lift $ convertChanTidings0 fixed (snd iniFil) nchan
    idxTds <- lift $ convertChanStepper0 fixedmap fixedChan
    return (DBVar2 dbvar idxTds vpt ,iniFil)

convertChanStepper0  ini nchan = do
        (e,h) <- newEvent
        t <- liftIO $ forkIO  $ forever ( do
            a <- atomically $ readTChan nchan
            h a )
        let conv (v,s,i,t) = (M.alter (\j -> fmap ((\(_,l) -> (s,M.insert i t l ))) j  <|> Just (s,M.singleton i t)) v)
        bh <- accumB ini (conv <$> e)
        registerDynamic (killThread t)
        return (tidings bh (flip conv<$> bh<@> e))

convertChanStepper idxv idxref = do
        (ini,nchan) <- liftIO $atomically $
          (,) <$> readTVar idxref <*> cloneTChan idxv
        convertChanStepper0 ini nchan

convertChanEvent chan = do
  (e,h) <- newEvent
  t <- liftIO $ forkIO $ forever (do
    patches <- atomically $ readTChan chan
    h patches)
  registerDynamic (killThread t)
  return e

convertChanTidings fixed idxv idxref = do
      (ini,nchan) <- liftIO $atomically $
          (,) <$> readTVar idxref <*> cloneTChan idxv
      convertChanTidings0 fixed ini nchan


convertChanTidings0 fixed ini nchan = do
    evdiff <-  convertChanEvent nchan
    let
      filterPred :: [Index (TBData Key Showable)] -> Maybe [Index (TBData Key Showable)]
      filterPred = nonEmpty . filter (\d@(_,p,_) -> G.match fixed G.Exact p && indexFilterP fixed d )
      update = F.foldl' (flip (\p-> (flip apply p)))
      diffs = filterJust $ filterPred <$> evdiff
    bres <- accumB ini (flip update <$> diffs)
    return $tidings bres (update <$> bres <@> diffs)


takeMany :: TChan a -> STM [a]
takeMany mvar = go . (:[]) =<< readTChan mvar
  where
    go v = do
      i <- tryReadTChan mvar
      maybe (return (reverse v )) (go . (:v)) i






fullInsert = Tra.traverse (fullInsert')

fullInsert' :: TBData Key Showable -> TransactionM  (TBData Key Showable)
fullInsert' ((k1,v1) )  = do
   inf <- ask
   let proj = _kvvalues . unTB
       tb  = (lookTable inf (_kvname k1))
   ret <-  (k1,) . _tb . KV <$>  Tra.traverse (\j -> _tb <$>  tbInsertEdit (unTB j) )  (proj v1)
   (_,(_,l)) <- tableLoader  tb Nothing Nothing [] (mempty)
   if  (isNothing $ flip G.lookup l $ tbpredM (S.fromList $ _kvpk k1)  ret ) && rawTableType tb == ReadWrite
      then catchAll (do
        i@(Just (TableModification _ _ tb))  <- insertFrom  ret
        tell (maybeToList i)
        return $ create tb) (\e -> return ret)
      else do
        return ret


noInsert = Tra.traverse (noInsert' )

noInsert' :: TBData Key Showable -> TransactionM  (TBData Key Showable)
noInsert' (k1,v1)   = do
   let proj = _kvvalues . unTB
   (k1,) . _tb . KV <$>  Tra.sequence (fmap (\j -> _tb <$>  tbInsertEdit (unTB j) )  (proj v1))

transactionLog :: InformationSchema -> TransactionM a -> Dynamic [TableModification (TBIdx Key Showable)]
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

fullDiffInsert :: TBData Key Showable -> TransactionM  (Maybe (TableModification (TBIdx Key Showable)))
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
           local (\inf -> fromMaybe inf (HM.lookup (_kvschema m) (depschema inf))) ((\tb -> FKT ( kvlist $ fmap _tb $ backFKRef relTable  (keyAttr .unTB <$> unkvlist pk) (unTB1 tb)) rel2 tb ) <$> fullInsert ( t))
        LeftTB1 i ->
           maybe (return f ) ((fmap attrOptional) . tbInsertEdit ) (unLeftItens f)
        ArrayTB1 l ->
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
      fkref = joinRel  (tableMeta targetTable) rel tb  mtable
  return $ Just $ FKT (kvlist $ _tb <$> tb) rel   fkref
loadFK table (Path ori (FKInlineTable to ) )   = do
  runMaybeT $ do
    IT rel vt  <- MaybeT . return $ unTB <$> M.lookup (S.map Inline   ori) (unKV .snd $ table)
    loadVt <- lift $ Tra.traverse loadFKS vt
    return $ IT rel loadVt

loadFK  _ _ = return Nothing
