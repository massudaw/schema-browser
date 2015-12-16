{-# LANGUAGE OverloadedStrings,TupleSections #-}
module SchemaQuery
  (eventTable
  ,refTable
  ,loadFKS
  ,fullDiffInsert
  ,fullDiffEdit
  ,transaction
  ,backFKRef
  )where

import RuntimeTypes
import Data.Ord
import qualified NonEmpty as Non
import Data.Functor.Identity
import Control.Monad.Writer
import Control.Concurrent
import Reactive.Threepenny
import Data.String
import Utils
import Patch
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Traversable as Tra
import qualified Data.List as L
import qualified Data.Foldable as F
import Debug.Trace
import GHC.Stack
import Types
import Query
import Data.Maybe
import Prelude hiding (head)
import Data.Foldable (foldl')
import Database.PostgreSQL.Simple
import Schema
import qualified Reactive.Threepenny as R
import System.Time.Extra
import qualified Data.Text as T

--
--  MultiTransaction Postgresql insertOperation
--

defsize = 200

estLength page size resL est = fromMaybe 0 page * size  +  est


refTable :: InformationSchema -> Table -> IO DBVar
refTable  inf table  = do
  mmap <- readMVar (mvarMap inf)
  return $ justError ("cant find mvar" <> show table) (M.lookup (tableMeta table) mmap )


eventTable :: InformationSchema -> Table -> Maybe Int -> Maybe Int -> [(Key,Order)] -> [(T.Text, Column Key Showable)]
    -> TransactionM (DBVar,Collection Key Showable)
eventTable inf table page size presort fixed = do
    let mvar = mvarMap inf
        defSort = fmap (,Desc) $  rawPK table
        sortList  = if L.null presort then defSort else presort
        fixidx = (L.sort $ snd <$> fixed )
        pagesize = maybe defsize id size
        filterfixed
            = if L.null fixed
              then id
              else
                M.filterWithKey  (\_ tb ->F.all id $ M.intersectionWith (\i j -> L.sort (nonRefTB (unTB i)) == L.sort ( nonRefTB (unTB j)) ) (mapFromTBList (fmap (_tb .snd) fixed)) $ unKV (snd (tableNonRef' tb)))
    mmap <- liftIO $ readMVar mvar
    let dbvar =  justError ("cant find mvar" <> show table) (M.lookup (tableMeta table) mmap )
    iniT <- do
       (fixedmap ,reso) <- liftIO $ currentValue (liftA2 (,) (facts (idxTid dbvar) ) (facts (collectionTid dbvar ) ))
       ini <- case M.lookup fixidx fixedmap of
          Just (sq,mp) -> do
             liftIO$ putStrLn $ "load existing filter map" <> show (M.size (filterfixed reso), pagesize * (fromMaybe 0 page + 1))
             liftIO$ print (M.keys mp )
             if (sq > M.size (filterfixed reso) -- Tabela é maior que a tabela carregada
                && M.size (filterfixed reso) < pagesize * (fromMaybe 0 page +1) -- O carregado é menor que a página
               )
             then do
                   liftIO$ putStrLn "load offseted new page"
                   let pagetoken =  (join $ flip M.lookupLE  mp . (*pagesize) <$> page)
                   (res,nextToken ,s ) <- (listEd $ schemaOps inf) inf table (liftA2 (-) (fmap (*pagesize) page) (fst <$> pagetoken)) (fmap snd pagetoken) size sortList fixed
                   let ini = (M.insert fixidx (estLength page pagesize res s  ,(\v -> M.insert ((fromMaybe 0 page +1 )*pagesize) v  mp) $ justError "no token"    nextToken) fixedmap , M.fromList (fmap (\i -> (getPK i,unTB1 i)) res)<> reso )
                   liftIO $ putMVar (patchVar dbvar ) (F.toList $ patch . unTB1 <$> res )
                   liftIO$ putMVar (idxVar dbvar ) (fst ini)
                   return  ini
                   --return (fixedmap,reso)
             else return (fixedmap ,reso)
          Nothing -> do
             liftIO$ putStrLn "create new filter map"
             (res,p,s) <- (listEd $ schemaOps inf ) inf table Nothing Nothing size sortList fixed
             let ini = (M.insert fixidx (estLength page pagesize res s ,maybe M.empty (M.singleton pagesize) p) fixedmap , M.fromList (fmap (\i -> (getPK i,unTB1 i)) res) <> reso)
             liftIO $ putMVar (patchVar dbvar ) (F.toList $ patch . unTB1 <$> res )
             liftIO$ putMVar (idxVar dbvar ) (fst ini)
             return ini
       return ini
    let tde = fmap filterfixed <$> rumors (liftA2 (,) (idxTid dbvar) (collectionTid dbvar ))
    let iniFil = fmap filterfixed iniT
    tdb  <- stepper iniFil tde
    return (dbvar {collectionTid  = fmap snd $ tidings tdb tde},iniFil)




fullInsert inf = Tra.traverse (fullInsert' inf )

fullInsert' :: InformationSchema -> TBData Key Showable -> TransactionM  (TBData Key Showable)
fullInsert' inf ((k1,v1) )  = do
   let proj = _kvvalues . unTB
   ret <-  (k1,) . Compose . Identity . KV <$>  Tra.traverse (\j -> Compose <$>  tbInsertEdit inf   (unTB j) )  (proj v1)
   (_,(_,l)) <- eventTable inf (lookTable inf (traceShow (k1,v1) $_kvname k1)) Nothing Nothing [] []
   if  isJust $ M.lookup (getPKM ret) l
      then do
        return ret
      else do
        i@(Just (TableModification _ _ tb))  <- (insertEd $ schemaOps inf) inf ret
        tell (maybeToList i)
        return $ create tb


noInsert inf = Tra.traverse (noInsert' inf)

noInsert' :: InformationSchema -> TBData Key Showable -> TransactionM  (TBData Key Showable)
noInsert' inf (k1,v1)   = do
   let proj = _kvvalues . unTB
   (k1,) . Compose . Identity . KV <$>  Tra.sequence (fmap (\j -> Compose <$>  tbInsertEdit inf   (unTB j) )  (proj v1))



transaction :: InformationSchema -> TransactionM a -> IO a
transaction inf log = {-withTransaction (conn inf) $-} do
  -- print "Transaction Run Log"
  (md,mods)  <- runWriterT log
  -- print "Transaction Update"
  let aggr = foldr (\(TableModification id t f) m -> M.insertWith mappend t [f] m) M.empty mods
  Tra.traverse (\(k,v) -> do
    -- print "GetTable"
    ref <- refTable inf k
    putMVar (patchVar ref ) v
    ) (M.toList aggr)
  --print "Transaction Finish"
  return md


fullDiffEdit :: InformationSchema -> TBData Key Showable -> TBData Key Showable -> TransactionM  (TBData Key Showable)
fullDiffEdit inf old@((k1,v1) ) (k2,v2) = do
   let proj = _kvvalues . unTB
   edn <- (k2,) . Compose . Identity . KV <$>  Tra.sequence (M.intersectionWith (\i j -> Compose <$>  tbDiffEdit inf  (unTB i) (unTB j) ) (proj v1 ) (proj v2))
   mod <- (editEd $ schemaOps inf)   inf edn old
   --tell (maybeToList mod)
   return edn

fullDiffInsert :: InformationSchema -> TBData Key Showable -> TransactionM  (Maybe (TableModification (TBIdx Key Showable)))
fullDiffInsert inf  (k2,v2) = do
   let proj = _kvvalues . unTB
   edn <- (k2,) . Compose . Identity . KV <$>  Tra.sequence ((\ j -> Compose <$>  tbInsertEdit inf   (unTB j) ) <$>  (proj v2))
   mod <- (insertEd $ schemaOps inf) inf edn
   -- tell (maybeToList mod)
   return mod



tbDiffEdit :: InformationSchema -> TB Identity Key Showable -> TB Identity Key Showable -> TransactionM (Identity (TB Identity Key  Showable))
tbDiffEdit inf i j
  | i == j =  return (Identity j)
  | otherwise = tbInsertEdit inf  j

tbInsertEdit inf  j@(Attr k1 k2) = return $ Identity  (Attr k1 k2)
tbInsertEdit inf  (IT k2 t2) = Identity . IT k2 <$> noInsert inf t2
tbInsertEdit inf  f@(FKT pk rel2  t2) =
   case t2 of
        t@(TB1 (_,l)) -> do
           let relTable = M.fromList $ fmap (\(Rel i _ j ) -> (j,i)) rel2
           Identity . (\tb -> FKT ( backFKRef relTable  (keyAttr .unTB <$> pk) (unTB1 tb)) rel2 tb ) <$> fullInsert inf t
        LeftTB1 i ->
           maybe (return (Identity f) ) (fmap (fmap attrOptional) . tbInsertEdit inf) (unLeftItens f)
        ArrayTB1 l ->
           fmap (fmap (attrArray f .Non.fromList)) $ fmap Tra.sequenceA $ Tra.traverse (\ix ->   tbInsertEdit inf $ justError ("cant find " <> show (ix,f)) $ unIndex ix f  )  [0.. Non.length l - 1 ]

loadFKS inf table = do
  let
    targetTable = lookTable inf (_kvname (fst table))
    fkSet:: S.Set Key
    fkSet =   S.unions . fmap (S.fromList . fmap _relOrigin . (\i -> if all isInlineRel i then i else filterReflexive i ) . S.toList . pathRelRel ) $ filter isReflexive  $ S.toList  (rawFKS targetTable)
    items = unKV . snd  $ table
    nonFKAttrs :: [(S.Set (Rel Key) ,Column Key Showable)]
    nonFKAttrs =  fmap (fmap unTB) $M.toList $  M.filterWithKey (\i a -> not $ S.isSubsetOf (S.map _relOrigin i) fkSet) items
  fks <- catMaybes <$> mapM (loadFK inf table ) (F.toList $ rawFKS targetTable)
  return  $ tblist' targetTable (fmap _tb $fmap snd nonFKAttrs <> fks )

loadFK :: InformationSchema -> TBData Key Showable -> Path (S.Set Key ) SqlOperation -> TransactionM (Maybe (Column Key Showable))
loadFK inf table (Path ori (FKJoinTable to rel tt ) tar) = do
  let targetTable = lookTable inf tt
  (i,(_,mtable )) <- eventTable inf targetTable Nothing Nothing [] []
  let
      relSet = S.fromList $ _relOrigin <$> rel
      tb  = unTB <$> F.toList (M.filterWithKey (\k l ->  not . S.null $ S.map _relOrigin  k `S.intersection` relSet)  (unKV . snd . tableNonRef' $ table))
      fkref = joinRel  (tableMeta targetTable) rel tb  (F.toList mtable)
  return $ Just $ FKT (_tb <$> tb) rel   fkref
loadFK inf table (Path ori (FKInlineTable to ) tar)   = do
  let IT rel vt = unTB $ justError "no inline" $ M.lookup (S.map Inline   ori) (unKV .snd $ table)
  loadVt <- Tra.traverse (loadFKS inf )  vt
  return (Just $ IT rel loadVt)

loadFK _ _ _ = return Nothing
