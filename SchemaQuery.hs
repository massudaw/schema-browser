{-# LANGUAGE FlexibleContexts,OverloadedStrings,TupleSections #-}
module SchemaQuery
  (eventTable
  ,createUn
  ,selectFromA
  ,selectFrom
  ,updateFrom
  ,patchFrom
  ,insertFrom
  ,syncFrom
  ,getFrom
  ,deleteFrom
  ,refTable
  ,loadFKS
  ,fullDiffInsert
  ,fullDiffEdit
  ,fullDiffEditInsert
  ,transaction
  ,transactionLog
  ,transactionNoLog
  )where
import Graphics.UI.Threepenny.Core (mapEventFin)

import RuntimeTypes
import Step.Host
import Step.Common

import Data.Time
import Data.Either
import Control.Concurrent.Async
import Control.Monad.Trans.Maybe
import qualified Data.Poset as P
import Debug.Trace
import Data.Ord
import GHC.Stack
import qualified NonEmpty as Non
import Data.Functor.Identity
import Control.Monad.Writer
import Control.Monad.Reader
import Control.Concurrent.STM
import Reactive.Threepenny
import Utils
import qualified Data.Map as M
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

estLength page size resL est = fromMaybe 0 page * size  +  est


refTable :: InformationSchema -> Table -> IO DBVar
refTable  inf table  = do
  mmap <- atomically $ readTMVar (mvarMap inf)
  return $ justError ("cant find mvar" <> show table) (M.lookup (tableMeta table) mmap )


tbpredM un v = G.Idex . M.fromList <$> (Tra.traverse (Tra.traverse unSOptional' ) $getUn un v)

createUn :: S.Set Key -> [TBData Key Showable] -> G.GiST (G.TBIndex Key Showable) (TBData Key Showable)
createUn un   =  G.fromList  transPred  .  filter (\i-> isJust $ Tra.traverse (Tra.traverse unSOptional' ) $ getUn un (tableNonRef' i) )
  where transPred v = G.Idex $ M.fromList $ L.sortBy ( comparing fst ) $ justError "invalid pred" (Tra.traverse (Tra.traverse unSOptional' ) $getUn un (tableNonRef' v))


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
  let dbvar =  justError ("cant find mvar" <> show table  ) (M.lookup (tableMeta table) mmap )
  let
      rinf = fromMaybe inf $ M.lookup (fst stable) (depschema inf)
      fromtable = (lookTable rinf $ snd stable)
      defSort = fmap (,Desc) $  rawPK t
  (l,i) <- local (const rinf) $ tableLoader fromtable Nothing Nothing []  (LegacyPredicate [])
  let
  ix <- mapM (\i -> do
      let
          fil = [("=", FKT ( kvlist $ _tb <$> backPathRef sref i) rel (TB1 i) )]
      (_,t) <- selectFrom "history" Nothing Nothing defSort (LegacyPredicate fil)
      let latest = fmap (("=",) . uncurry Attr). getPKM   $ ( L.maximumBy (comparing getPKM) $ G.toList $ snd t)
      (joinSyncTable  [(fromtable ,i,sref)] table page size presort (LegacyPredicate fil). F.toList ) (latest)
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

mapTEvent f x = fst <$> mapTEventFin f x

mapTEventFin f x = do
  i <- currentValue (facts x)
  mapT0EventFin i f x

mapT0EventFin i f x = do
  (e,fin) <- mapEventFin f (rumors x)
  be <-  liftIO $ f i
  t <- stepper be e
  return $ (tidings t e,fin)



rebaseKey inf t  (LegacyPredicate fixed ) = LegacyPredicate $ fmap (liftField inf (tableName t) . firstTB  keyValue)  <$> fixed
-- rebaseKey t  (WherePredicate fixed ) = fmap (liftField inf (tableName t) . firstTB  keyValue)  <$> fixed

tableLoader :: Table -> Maybe Int -> Maybe Int -> [(Key,Order)] -> WherePredicate
    -> TransactionM (DBVar,Collection Key Showable)
tableLoader table  page size presort fixed
  -- Union Tables
  | not $ L.null $ rawUnion table  = do
    inf <- ask
    i <- liftIO $ mapConcurrently (\t -> transactionNoLog inf $  tableLoader t page size presort (rebaseKey inf t  fixed))  (rawUnion table)
    let mvar = mvarMap inf
    mmap <- liftIO $ atomically $ readTMVar mvar
    let dbvar =  justError ("cant find mvar" <> show table  ) (M.lookup (tableMeta table) mmap )
        projunion :: TBData Key Showable -> TBData Key Showable
        projunion  = liftTable' inf (tableName table ) .mapKey' keyValue
    let o = foldr mergeDBRef  (M.empty,G.empty) (fmap (fmap projunion) . snd <$> i)
    return $ (dbvar,o)
  -- (Scoped || Partitioned) Tables
  | not  (null $ _rawScope table ) && not (S.null (rawFKS table) )= do
      inf <- ask
      let sref =  case filter (\(Path i _) -> S.isSubsetOf i (S.fromList $ _rawScope table)) (S.toList $ rawFKS table) of
                [sref] -> sref
                i ->  errorWithStackTrace ("no sref " <> show sref)
          Path kref (FKJoinTable rel stable ) =  sref
      let mvar = mvarMap inf
      mmap <- liftIO $ atomically $ readTMVar mvar
      let dbvar =  justError ("cant find mvar" <> show table  ) (M.lookup (tableMeta table) mmap )
      let
          rinf = fromMaybe inf $ M.lookup (fst stable) (depschema inf)
          fromtable = (lookTable rinf $ snd stable)
          defSort = fmap (,Desc) $  rawPK fromtable
      (l,i) <- local (const rinf) $ tableLoader  fromtable page  size defSort (LegacyPredicate [])
      let
          filtered ::  [TBData Key Showable]
          filtered =  (if L.null prefix then id else L.filter  (\i -> L.filter ((`S.member` kref).fst) (getAttr' (TB1 i)) == prefix )) $ F.toList (snd i)
            where prefix =  case fixed  of
                        LegacyPredicate fixed -> L.filter ((`S.member` kref) . fst ) (concat $ fmap (aattri. snd) fixed)
                        WherePredicate fixed -> errorWithStackTrace "not implemented" -- L.filter ((`S.member` kref) . fst ) (concat $ fmap (aattri. snd) fixed)
      ix <- mapM (\i -> do
          (l,v) <- joinTable [(fromtable ,i,sref)] table page size presort fixed
          return v ) $ F.toList (snd i)
      return (dbvar ,foldr mergeDBRef  (M.empty,G.empty) ix )
  -- Primitive Tables
  | otherwise  =  do
    inf <- ask
    let base (Path _ (FKJoinTable i j  ) ) = fst j == schemaName inf
        base i = True
        remoteFKS = S.filter (not .base )  (_rawFKSL table)
        getAtt i (m ,k ) = filter ((`S.isSubsetOf` i) . S.fromList . fmap _relOrigin. keyattr ) . F.toList . _kvvalues . unTB $ k
    liftIO$ putStrLn $ "start loadTable " <> show (tableName table)
    li <- liftIO getCurrentTime
    o <- pageTable False (\table page size presort fixed v -> do
          (res ,x ,o) <- (listEd $ schemaOps inf) (table {_rawFKSL = S.filter base  (_rawFKSL table)}) page size presort fixed v
          let getFKS  v = foldl (\m (Path _ (FKJoinTable i j ))  -> m >>= (\m -> do
                let rinf = justError "no schema" $ M.lookup ((fst j))  (depschema inf)
                    table = (lookTable rinf $ snd j)
                liftIO $ putStrLn $ "loadForeign table" <> show (tableName table)
                (db,(_,tb)) <- local (const rinf) (tableLoader table  Nothing Nothing [] (LegacyPredicate []))
                let
                    tar = S.fromList $ fmap _relOrigin i
                    joinFK :: TBData Key Showable -> Either [Compose Identity (TB Identity)  Key Showable] (Column Key Showable)
                    joinFK m  = maybe (Left taratt) Right $ FKT (kvlist taratt) i <$> joinRel2 (tableMeta table ) i (fmap unTB $ taratt ) tb
                      where
                            taratt = getAtt tar (tableNonRef' m)
                    addAttr :: Column Key Showable -> TBData Key Showable -> TBData Key Showable
                    addAttr r (m,i) = (m,mapComp (\(KV i) -> KV (M.insert (S.fromList $ keyattri r) (_tb r)  $ M.filterWithKey (\k _ -> not $ S.map _relOrigin k `S.isSubsetOf` tar && F.all isInlineRel k   ) i )) i )
                    joined = (\i -> do
                       fk <- joinFK i
                       return $ addAttr  fk i) <$> m
                liftIO $ putStrLn $ "reloadForeign table" <> show (tableName table) <> " - " <> show (lefts joined)
                fetched <-traverse (\pred -> local (const rinf) $  tableLoader table Nothing Nothing []  (WherePredicate (AndColl pred))) $ traverse (\k -> (\ v -> traceShowId $ (PrimColl (IProd True [ keyValue ._relOrigin  $ k], "IN", ArrayTB1 (Non.fromList v)))) <$> ( nonEmpty $ catMaybes $  fmap (_tbattr .unTB) . L.find ((== [k]) . keyattr ) <$> traceShowId (lefts joined) ))  i
                return (rights  joined)) )  (return v) $ P.sortBy (P.comparing pathRelRel)  (S.toList remoteFKS)
          resFKS <- getFKS res
          return (resFKS,x,o )) table page size presort fixed
    lf <- liftIO getCurrentTime

    liftIO $ putStrLn $ "finish loadTable" <> show  (tableName table) <> " - " <> show (diffUTCTime lf  li)
    return o



joinSyncTable reflist  a b c d f e =
    ask >>= (\ inf -> pageTable True ((joinSyncEd $ schemaOps inf) reflist e ) a b c d f )



joinTable :: [(Table,TBData Key Showable,Path (S.Set Key ) SqlOperation )]-> Table -> Maybe Int -> Maybe Int -> [(Key,Order)] -> WherePredicate
    -> TransactionM (DBVar,Collection Key Showable)
joinTable reflist  a b c d e =
    ask >>= (\ inf -> pageTable False ((joinListEd $ schemaOps inf) reflist) a b c d e )


eventTable = tableLoader

predNull (WherePredicate i) = L.null i
predNull (LegacyPredicate i) = L.null i

pageTable flag method table page size presort fixed = do
    inf <- ask
    let mvar = mvarMap inf
        defSort = fmap (,Desc) $  rawPK table
        sortList  = if L.null presort then defSort else presort
        fixidx = fixed
        pagesize = maybe defsize id size
        filterfixed
            = if predNull fixed
              then id
              else
                case fixed of
                  WherePredicate pred -> G.filter (\tb ->F.all  (\(a,e,v) -> indexPred  (a,T.unpack e ,v) tb) pred )
                  LegacyPredicate pred -> G.filter (\tb ->F.all id $ M.intersectionWith (\i j -> L.sort (nonRefTB (unTB i)) == L.sort ( nonRefTB (unTB j)) ) (mapFromTBList (fmap (_tb .snd) pred )) $ unKV (snd (tb)))
    mmap <- liftIO $ atomically $ readTMVar mvar
    let dbvar =  justError ("cant find mvar" <> show table) (M.lookup (tableMeta table) mmap )
    iniT <- do
       (fixedmap ,reso) <- liftIO $ currentValue (liftA2 (,) (facts (idxTid dbvar) ) (facts (collectionTid dbvar ) ))
       let pageidx = (fromMaybe 0 page +1) * pagesize
       i <- case  fromMaybe (10000000,M.empty ) $  M.lookup fixidx fixedmap of
          (sq,mp) -> do
             if flag || ( sq > G.size (filterfixed reso) -- Tabela é maior que a tabela carregada
                && sq > pagesize * (fromMaybe 0 page + 1) -- Tabela é maior que a página
                && pagesize * (fromMaybe 0 page +1) > G.size (filterfixed reso)  ) -- O carregado é menor que a página
             then do
               liftIO$ putStrLn $ "new page " <> show (tableName table)
               let pagetoken =  (join $ flip M.lookupLE  mp . (*pagesize) <$> page)
               (res,nextToken ,s ) <- method table (liftA2 (-) (fmap (*pagesize) page) (fst <$> pagetoken)) (fmap snd pagetoken) size sortList fixed
               let
                   token =  nextToken
                   index = (estLength page pagesize res s, maybe (M.insert pageidx HeadToken) (M.insert pageidx ) token$ mp)
               return  (index,res)
             else do
               return ((sq,mp),[])
       let nidx =  M.insert fixidx (fst i) fixedmap
           ndata = snd i
       liftIO $ atomically $ do
         writeTQueue (patchVar dbvar) (F.toList $ patch  <$> ndata )
         putTMVar (idxVar dbvar ) nidx
       return (nidx, createUn (S.fromList $ rawPK table) ndata <> reso)
    let tde = fmap filterfixed <$> rumors (liftA2 (,) (idxTid dbvar) (collectionTid dbvar ))
    let iniFil = fmap filterfixed iniT
    tdb  <- stepper iniFil tde
    return (dbvar {collectionTid  = fmap snd $ tidings tdb tde},iniFil)




fullInsert = Tra.traverse (fullInsert')

fullInsert' :: TBData Key Showable -> TransactionM  (TBData Key Showable)
fullInsert' ((k1,v1) )  = do
   inf <- ask
   let proj = _kvvalues . unTB
   ret <-  (k1,) . _tb . KV <$>  Tra.traverse (\j -> _tb <$>  tbInsertEdit (unTB j) )  (proj v1)
   (_,(_,l)) <- tableLoader (lookTable inf (_kvname k1)) Nothing Nothing [] (LegacyPredicate [])
   if  isJust $ join $ flip G.lookup l <$> tbpredM (S.fromList $ _kvpk k1)  ret
      then do
        return ret
      else do
        i@(Just (TableModification _ _ tb))  <- insertFrom  ret
        tell (maybeToList i)
        return $ create tb


noInsert = Tra.traverse (noInsert' )

noInsert' :: TBData Key Showable -> TransactionM  (TBData Key Showable)
noInsert' (k1,v1)   = do
   let proj = _kvvalues . unTB
   (k1,) . _tb . KV <$>  Tra.sequence (fmap (\j -> _tb <$>  tbInsertEdit (unTB j) )  (proj v1))

transactionLog :: InformationSchema -> TransactionM a -> IO [TableModification (TBIdx Key Showable)]
transactionLog inf log = do -- withTransaction (conn inf) $ do
  (md,mods)  <- runWriterT (runReaderT log inf )
  let aggr = foldr (\(TableModification id t f) m -> M.insertWith mappend t [TableModification id t f] m) M.empty mods
  agg2 <- Tra.traverse (\(k,v) -> do
    ref <- refTable (if rawSchema k == schemaName inf then inf else justError "no schema" $ M.lookup ((rawSchema k ))  (depschema inf) ) k
    nm <- mapM (logger (schemaOps inf) inf) v
    putPatch (patchVar ref ) $ (\(TableModification _ _ p) -> p) <$> nm
    return nm
    ) (M.toList aggr)
  return $ concat $ agg2



transactionNoLog :: InformationSchema -> TransactionM a -> IO a
transactionNoLog inf log = do -- withTransaction (conn inf) $ do
  (md,mods)  <- runWriterT (runReaderT log inf )
  let aggr = foldr (\tm@(TableModification id t f) m -> M.insertWith mappend t [tm] m) M.empty mods
  Tra.traverse (\(k,v) -> do
    ref <- refTable (if rawSchema k == schemaName inf then inf else justError "no schema" $ M.lookup ((rawSchema k ))  (depschema inf) ) k
    putPatch (patchVar ref ) $ (\(TableModification id t f)-> f) <$>v
    ) (M.toList aggr)
  return md


transaction :: InformationSchema -> TransactionM a -> IO a
transaction inf log = do -- withTransaction (conn inf) $ do
  (md,mods)  <- runWriterT (runReaderT log inf )
  let aggr = foldr (\tm@(TableModification id t f) m -> M.insertWith mappend t [tm] m) M.empty mods
  Tra.traverse (\(k,v) -> do
    ref <- refTable (if rawSchema k == schemaName inf then inf else justError "no schema" $ M.lookup ((rawSchema k ))  (depschema inf) ) k
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
tbEdit (Attr a1 a2) (Attr k1 k2)= return $ (Attr k1 k2)
tbEdit (IT a1 a2) (IT k2 t2) = IT k2 <$> noInsert t2
tbEdit g@(FKT apk arel2  a2) f@(FKT pk rel2  t2) =
   case (a2,t2) of
        (TB1 o@(om,ol),TB1 t@(m,l)) -> do
           let relTable = M.fromList $ fmap (\(Rel i _ j ) -> (j,i)) rel2
           local (\inf -> fromMaybe inf (M.lookup (_kvschema m) (depschema inf))) ((\tb -> FKT ( kvlist $ fmap _tb $ backFKRef relTable  (keyAttr .unTB <$> unkvlist pk) (unTB1 tb)) rel2 tb ) . TB1  <$> fullDiffEdit o t)
        (LeftTB1  _ ,LeftTB1 _) ->
           maybe (return f ) (fmap attrOptional) $ liftA2 tbEdit (unLeftItens g) (unLeftItens f)
        (ArrayTB1 o,ArrayTB1 l) ->
           (fmap (attrArray f .Non.fromList)) $  Tra.traverse (\ix ->   tbEdit ( justError ("cant find " <> show (ix,f)) $ unIndex ix g )( justError ("cant find " <> show (ix,f)) $ unIndex ix f ) )  [0.. Non.length l - 1 ]
        i -> errorWithStackTrace (show i)


tbInsertEdit :: Column Key Showable -> TransactionM (Column Key Showable)
tbInsertEdit j@(Attr k1 k2) = return $ (Attr k1 k2)
tbInsertEdit (IT k2 t2) = IT k2 <$> noInsert t2
tbInsertEdit f@(FKT pk rel2  t2) =
   case t2 of
        t@(TB1 (m,l)) -> do
           let relTable = M.fromList $ fmap (\(Rel i _ j ) -> (j,i)) rel2
           local (\inf -> fromMaybe inf (M.lookup (_kvschema m) (depschema inf))) ((\tb -> FKT ( kvlist $ fmap _tb $ backFKRef relTable  (keyAttr .unTB <$> unkvlist pk) (unTB1 tb)) rel2 tb ) <$> fullInsert ( t))
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
  (i,(_,mtable )) <- tableLoader targetTable Nothing Nothing [] (LegacyPredicate [])
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
