{-# LANGUAGE OverloadedStrings,TupleSections #-}
module SchemaQuery
  (eventTable
  ,selectFrom
  ,updateFrom
  ,patchFrom
  ,insertFrom
  ,getFrom
  ,deleteFrom
  ,refTable
  ,loadFKS
  ,fullDiffInsert
  ,fullDiffEdit
  ,transaction
  ,backFKRef
  )where

import RuntimeTypes
import Debug.Trace
import Data.Ord
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
import Prelude hiding (head)
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

tbpred un v = G.Idex $ justError "" $ (Tra.traverse (Tra.traverse unSOptional' ) $getUn un v)

createUn :: S.Set Key -> [TBData Key Showable] -> G.GiST (G.TBIndex Key Showable) (TBData Key Showable)
createUn un   =  G.fromList  transPred  .  filter (\i-> isJust $ Tra.traverse (Tra.traverse unSOptional' ) $ getUn un (tableNonRef' i) )
  where transPred v = G.Idex $ justError "invalid pred" (Tra.traverse (Tra.traverse unSOptional' ) $getUn un (tableNonRef' v))


-- tableLoader :: InformationSchema -> Table -> TransactionM (Collection Key Showable)
eventTable = tableLoader

selectFrom t a b c d = do
  inf <- ask
  eventTable (lookTable inf t) a b c d
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


tableLoader table  page size presort fixed
  | not $ L.null $ rawUnion table  = do
    i <- mapM (\t -> tableLoader t page size presort fixed)  (rawUnion table)
    inf <- ask
    let mvar = mvarMap inf
    mmap <- liftIO $ atomically $ readTMVar mvar
    let dbvar =  justError ("cant find mvar" <> show table  ) (M.lookup (tableMeta table) mmap )
        projunion :: TBData Key Showable -> TBData Key Showable
        projunion  = liftTable' inf (tableName table ) .mapKey' keyValue
    let o = foldr (\(j) (m) -> ((j <> m ))) (M.empty,G.empty) (fmap (fmap projunion) . snd <$> i)
    return $ (dbvar,o)
  | otherwise  =  do
    inf <- ask
    let base (Path _ (FKJoinTable i j  ) ) = fst j == schemaName inf
        base i = True
        remoteFKS = S.filter (not .base )  (_rawFKSL table)
        getAtt i (m ,k ) = filter (( `S.isSubsetOf` i) . S.fromList . fmap _relOrigin. keyattr ) . F.toList . _kvvalues . unTB $ k
    (db,o) <- eventTable' (table {_rawFKSL = S.filter base  (_rawFKSL table)}) page size presort fixed
    res <- foldl (\m (Path _ (FKJoinTable i j ))  -> m >>= (\m -> do
        let rinf = justError "no schema" $ M.lookup ((fst j))  (depschema inf)
            table = (lookTable rinf $ snd j)
        (db,(_,tb)) <- local (const rinf) (tableLoader table  page size presort fixed)
        let
            tar = S.fromList $ fmap _relOrigin i
            joinFK :: TBData Key Showable -> Column Key Showable
            joinFK m  = FKT taratt i (joinRel (tableMeta table ) i (fmap unTB $ taratt ) tb)
              where
                    taratt = getAtt tar m
            addAttr :: Column Key Showable -> TBData Key Showable -> TBData Key Showable
            addAttr r (m,i) = (m,mapComp (\(KV i) -> KV (M.insert (S.fromList $ keyattri r) (_tb r)  $ M.filterWithKey (\k _ -> not $ S.map _relOrigin k `S.isSubsetOf` tar   ) i )) i )
        return ((\i -> addAttr  (joinFK i) i) <$> m)) )  (return $ snd o) (S.toList remoteFKS)
    return $ (db,(fst o ,res))







eventTable' :: Table -> Maybe Int -> Maybe Int -> [(Key,Order)] -> [(T.Text, Column Key Showable)]
    -> TransactionM (DBVar,Collection Key Showable)
eventTable' table page size presort fixed = do
    inf <- ask
    let mvar = mvarMap inf
        defSort = fmap (,Desc) $  rawPK table
        sortList  = if L.null presort then defSort else presort
        fixidx = (L.sort $ snd <$> fixed )
        pagesize = maybe defsize id size
        filterfixed
            = if L.null fixed
              then id
              else
                G.filter (\ tb ->F.all id $ M.intersectionWith (\i j -> L.sort (nonRefTB (unTB i)) == L.sort ( nonRefTB (unTB j)) ) (mapFromTBList (fmap (_tb .snd) fixed)) $ unKV (snd (tableNonRef' tb)))
    mmap <- liftIO $ atomically $ readTMVar mvar
    let dbvar =  justError ("cant find mvar" <> show table) (M.lookup (tableMeta table) mmap )
    iniT <- do
       (fixedmap ,reso) <- liftIO $ currentValue (liftA2 (,) (facts (idxTid dbvar) ) (facts (collectionTid dbvar ) ))
       case M.lookup fixidx fixedmap of
          Just (sq,mp) -> do
             if ( sq > G.size (filterfixed reso) -- Tabela é maior que a tabela carregada
                && sq > pagesize * (fromMaybe 0 page + 1) -- Tabela é maior que a página
                && pagesize * (fromMaybe 0 page +1) > G.size (filterfixed reso)  ) -- O carregado é menor que a página
             then do
                   liftIO$ putStrLn $ "new page " <> show (tableName table)
                   let pagetoken =  (join $ flip M.lookupLE  mp . (*pagesize) <$> page)
                   (res,nextToken ,s ) <- (listEd $ schemaOps inf) table (liftA2 (-) (fmap (*pagesize) page) (fst <$> pagetoken)) (fmap snd pagetoken) size sortList fixed
                   let ini = (M.insert fixidx (estLength page pagesize res s  ,(\v -> M.insert ((fromMaybe 0 page +1 )*pagesize) v  mp) $ justError "no token"    nextToken) fixedmap , createUn (S.fromList $ rawPK table)  (fmap unTB1 res)<> reso )
                   liftIO $ atomically $ do
                     writeTQueue (patchVar dbvar ) (F.toList $ patch . unTB1 <$> res )
                     putTMVar (idxVar dbvar ) (fst ini)
                   return  ini
             else do
               liftIO$ putStrLn $ "existing page " <> show (tableName table)
               return (fixedmap ,reso)
          Nothing -> do
             liftIO$ putStrLn $ "new map " <> show (tableName table)
             (res,p,s) <- (listEd $ schemaOps inf ) table Nothing Nothing size sortList fixed
             let ini = (M.insert fixidx (estLength page pagesize res s ,maybe M.empty (M.singleton pagesize) p) fixedmap , createUn (S.fromList $ rawPK table)    (fmap (\i -> (unTB1 i)) res) <> reso)
             liftIO $ atomically $ do
               writeTQueue(patchVar dbvar ) (F.toList $ patch . unTB1 <$> res )
               putTMVar (idxVar dbvar ) (fst ini)
             return ini
    let tde = fmap filterfixed <$> rumors (liftA2 (,) (idxTid dbvar) (collectionTid dbvar ))
    let iniFil = fmap filterfixed iniT
    tdb  <- stepper iniFil tde
    return (dbvar {collectionTid  = fmap snd $ tidings tdb tde},iniFil)




fullInsert = Tra.traverse (fullInsert')

fullInsert' :: TBData Key Showable -> TransactionM  (TBData Key Showable)
fullInsert' ((k1,v1) )  = do
   inf <- ask
   let proj = _kvvalues . unTB
   ret <-  (k1,) . Compose . Identity . KV <$>  Tra.traverse (\j -> Compose <$>  tbInsertEdit (unTB j) )  (proj v1)
   (_,(_,l)) <- eventTable (lookTable inf (_kvname k1)) Nothing Nothing [] []
   if  isJust $ G.lookup (tbpred (S.fromList $ _kvpk k1)  ret) l
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
   (k1,) . Compose . Identity . KV <$>  Tra.sequence (fmap (\j -> Compose <$>  tbInsertEdit (unTB j) )  (proj v1))



transaction :: InformationSchema -> TransactionM a -> IO a
transaction inf log = do -- withTransaction (conn inf) $ do
  (md,mods)  <- runWriterT (runReaderT log inf )
  let aggr = foldr (\(TableModification id t f) m -> M.insertWith mappend t [f] m) M.empty mods
  Tra.traverse (\(k,v) -> do
    ref <- refTable (if rawSchema k == schemaName inf then inf else justError "no schema" $ M.lookup ((rawSchema k ))  (depschema inf) ) k
    putPatch (patchVar ref ) v
    ) (M.toList aggr)
  return md


fullDiffEdit :: TBData Key Showable -> TBData Key Showable -> TransactionM  (TBData Key Showable)
fullDiffEdit old@((k1,v1) ) (k2,v2) = do
   inf <- ask
   let proj = _kvvalues . unTB
   edn <- (k2,) . Compose . Identity . KV <$>  Tra.sequence (M.intersectionWith (\i j -> Compose <$>  tbDiffEdit (unTB i) (unTB j) ) (proj v1 ) (proj v2))
   mod <- updateFrom   edn old
   tell (maybeToList mod)
   return edn

fullDiffInsert :: TBData Key Showable -> TransactionM  (Maybe (TableModification (TBIdx Key Showable)))
fullDiffInsert (k2,v2) = do
   inf <- ask
   let proj = _kvvalues . unTB
   edn <- (k2,) . Compose . Identity . KV <$>  Tra.sequence ((\ j -> Compose <$>  tbInsertEdit (unTB j) ) <$>  (proj v2))
   mod <- insertFrom  edn
   tell (maybeToList mod)
   return mod



tbDiffEdit :: TB Identity Key Showable -> TB Identity Key Showable -> TransactionM (Identity (TB Identity Key  Showable))
tbDiffEdit i j
  | i == j =  return (Identity j)
  | otherwise = tbInsertEdit j

tbInsertEdit j@(Attr k1 k2) = return $ Identity  (Attr k1 k2)
tbInsertEdit (IT k2 t2) = Identity . IT k2 <$> noInsert t2
tbInsertEdit f@(FKT pk rel2  t2) =
   case t2 of
        t@(TB1 (m,l)) -> do
           let relTable = M.fromList $ fmap (\(Rel i _ j ) -> (j,i)) rel2
           local (\inf -> fromMaybe inf (M.lookup (_kvschema m) (depschema inf))) (Identity . (\tb -> FKT ( fmap _tb $ backFKRef relTable  (keyAttr .unTB <$> pk) (unTB1 tb)) rel2 tb ) <$> fullInsert t)
        LeftTB1 i ->
           maybe (return (Identity f) ) (fmap (fmap attrOptional) . tbInsertEdit ) (unLeftItens f)
        ArrayTB1 l ->
           fmap (fmap (attrArray f .Non.fromList)) $ fmap Tra.sequenceA $ Tra.traverse (\ix ->   tbInsertEdit $ justError ("cant find " <> show (ix,f)) $ unIndex ix f  )  [0.. Non.length l - 1 ]

loadFKS table = do
  inf <- ask
  let
    targetTable = lookTable inf (_kvname (fst table))
    fkSet:: S.Set Key
    fkSet =   S.unions . fmap (S.fromList . fmap _relOrigin . (\i -> if all isInlineRel i then i else filterReflexive i ) . S.toList . pathRelRel ) $ filter isReflexive  $ S.toList  (rawFKS targetTable)
    items = unKV . snd  $ table
    nonFKAttrs :: [(S.Set (Rel Key) ,Column Key Showable)]
    nonFKAttrs =  fmap (fmap unTB) $M.toList $  M.filterWithKey (\i a -> not $ S.isSubsetOf (S.map _relOrigin i) fkSet) items
  fks <- catMaybes <$> mapM (loadFK table ) (F.toList $ rawFKS targetTable)
  return  $ tblist' targetTable (fmap _tb $fmap snd nonFKAttrs <> fks )

loadFK :: TBData Key Showable -> Path (S.Set Key ) SqlOperation -> TransactionM (Maybe (Column Key Showable))
loadFK table (Path ori (FKJoinTable rel (st,tt) ) ) = do
  inf <- ask
  let targetTable = lookTable inf tt
  (i,(_,mtable )) <- eventTable targetTable Nothing Nothing [] []
  let
      relSet = S.fromList $ _relOrigin <$> rel
      tb  = unTB <$> F.toList (M.filterWithKey (\k l ->  not . S.null $ S.map _relOrigin  k `S.intersection` relSet)  (unKV . snd . tableNonRef' $ table))
      fkref = joinRel  (tableMeta targetTable) rel tb  mtable
  return $ Just $ FKT (_tb <$> tb) rel   fkref
loadFK table (Path ori (FKInlineTable to ) )   = do
  let IT rel vt = unTB $ justError "no inline" $ M.lookup (S.map Inline   ori) (unKV .snd $ table)
  loadVt <- Tra.traverse (loadFKS )  vt
  return (Just $ IT rel loadVt)

loadFK  _ _ = return Nothing
