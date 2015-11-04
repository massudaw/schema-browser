{-# LANGUAGE OverloadedStrings,TupleSections #-}
module SchemaQuery
  (deleteMod
  ,insertMod
  ,updateMod
  ,postgresOps
  ,selectAll
  ,eventTable
  ,fullDiffInsert
  ,fullDiffEdit
  ,transaction
  ,backFKRef
  )where

import RuntimeTypes
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
import Postgresql
import PostgresQuery
import Data.Maybe
import Prelude hiding (head)
import Data.Foldable (foldl')
import Database.PostgreSQL.Simple
import Schema
import qualified Reactive.Threepenny as R
import System.Time.Extra
import qualified Data.Text.Lazy as T

--
--  MultiTransaction Postgresql insertOperation
--

deleteMod :: InformationSchema ->  TBData Key Showable -> Table -> IO (Maybe (TableModification (TBIdx Key Showable)))
deleteMod inf j@(meta,_) table = do
  let patch =  (tableMeta table, getPKM j,[])
  deletePatch (conn inf)  patch table
  Just <$> logTableModification inf (TableModification Nothing table patch)

selectAll inf table = liftIO $ do
      let
          tb =  tableView (tableMap inf) table
          tbf = tb -- forceDesc True (markDelayed True tb)
      print (tableName table,selectQuery tbf )
      (t,v) <- duration  $ queryWith_  (fromAttr (unTlabel tbf)) (conn inf)(fromString $ T.unpack $ selectQuery $ tbf)
      print (tableName table,t)
      return v

eventTable inf table = do
    let mvar = mvarMap inf
    mmap <- takeMVar mvar
    (mtable,td) <- case (M.lookup (tableMeta table) mmap ) of
         Just (i,td) -> do
           putMVar mvar mmap
           return (i,td)
         Nothing -> do
           res <- (listEd $ schemaOps inf ) inf table
           mnew <- newMVar (fmap unTB1 res)
           (e,h) <- R.newEvent
           ini <- readMVar mnew
           forkIO $ forever $ do
              h =<< takeMVar mnew
           bh <- R.stepper ini e
           let td = (R.tidings bh e)
           -- Dont
           if True -- (rawTableType table == ReadWrite)
              then  putMVar mvar (M.insert (tableMeta table) (mnew,td) mmap)
              else putMVar mvar  mmap

           return (mnew,td)
    return (mtable,fmap TB1 <$> td)



postgresOps = SchemaEditor fullDiffEdit fullDiffInsert deleteMod selectAll (\inf table -> loadDelayed inf (unTB1 $ unTlabel $ tableView (tableMap inf) table ))

fullInsert inf = Tra.traverse (fullInsert' inf )

fullInsert' :: InformationSchema -> TBData Key Showable -> TransactionM  (TBData Key Showable)
fullInsert' inf ((k1,v1) )  = do
   let proj = _kvvalues . unTB
   ret <-  (k1,) . Compose . Identity . KV <$>  Tra.traverse (\j -> Compose <$>  tbInsertEdit inf   (unTB j) )  (proj v1)
   (m,t) <- liftIO $ eventTable inf (lookTable inf (_kvname k1))
   l <- currentValue (facts t)
   if  isJust $ L.find ((==tbPK (tableNonRef (TB1 ret))). tbPK . tableNonRef ) l
      then do
        return ret
      else do
        i@(Just (TableModification _ _ tb))  <- liftIO $ insertMod inf ret (lookTable inf (_kvname k1))
        tell (maybeToList i)
        return $ createTB1 tb


noInsert inf = Tra.traverse (noInsert' inf)

noInsert' :: InformationSchema -> TBData Key Showable -> TransactionM  (TBData Key Showable)
noInsert' inf (k1,v1)   = do
   let proj = _kvvalues . unTB
   (k1,) . Compose . Identity . KV <$>  Tra.sequence (fmap (\j -> Compose <$>  tbInsertEdit inf   (unTB j) )  (proj v1))


insertMod :: InformationSchema ->  TBData Key Showable -> Table -> IO (Maybe (TableModification (TBIdx Key Showable)))
insertMod inf j  table = do
  let patch = patchTB1 j
  kvn <- insertPatch fromRecord (conn  inf) patch table
  let mod =  TableModification Nothing table kvn
  Just <$> logTableModification inf mod


transaction :: InformationSchema -> TransactionM a -> IO a
transaction inf log = withTransaction (conn inf) $ do
  (md,mods)  <- runWriterT log
  let aggr = foldr (\(TableModification id t f) m -> M.insertWith mappend t [f] m) M.empty mods
  Tra.traverse (\(k,v) -> do
    (m,t) <- eventTable inf k
    l <- currentValue (facts t)
    let lf = foldl' (\i p -> applyTable  i (PAtom p)) l v
    putMVar m (fmap unTB1 lf)
    ) (M.toList aggr)
  return md


fullDiffEdit :: InformationSchema -> TBData Key Showable -> TBData Key Showable -> TransactionM  (TBData Key Showable)
fullDiffEdit inf old@((k1,v1) ) (k2,v2) = do
   let proj = _kvvalues . unTB
   edn <- (k2,) . Compose . Identity . KV <$>  Tra.sequence (M.intersectionWith (\i j -> Compose <$>  tbDiffEdit inf  (unTB i) (unTB j) ) (proj v1 ) (proj v2))
   mod <- liftIO $ updateMod inf edn old (lookTable inf (_kvname k2))
   --tell (maybeToList mod)
   return edn

fullDiffInsert :: InformationSchema -> TBData Key Showable -> TransactionM  (Maybe (TableModification (TBIdx Key Showable)))
fullDiffInsert inf  (k2,v2) = do
   let proj = _kvvalues . unTB
   edn <- (k2,) . Compose . Identity . KV <$>  Tra.sequence ((\ j -> Compose <$>  tbInsertEdit inf   (unTB j) ) <$>  (proj v2))
   mod <- liftIO $ insertMod inf edn (lookTable inf (_kvname k2))
   -- tell (maybeToList mod)
   return mod


updateMod :: InformationSchema -> TBData Key Showable -> TBData Key Showable -> Table -> IO (Maybe (TableModification (TBIdx Key Showable)))
updateMod inf kv old table = do
  patch <- updatePatch (conn  inf) kv  old  table
  let mod =  TableModification Nothing table patch
  Just <$> logTableModification inf mod


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
           Identity . (\tb -> FKT ( backFKRef relTable  (keyAttr .unTB <$> pk) tb) rel2 tb ) <$> fullInsert inf t
        LeftTB1 i ->
           maybe (return (Identity f) ) (fmap (fmap attrOptional) . tbInsertEdit inf) (unLeftItens f)
        ArrayTB1 l ->
           fmap (fmap (attrArray f)) $ fmap Tra.sequenceA $ Tra.traverse (\ix ->   tbInsertEdit inf $ justError ("cant find " <> show (ix,f)) $ unIndex ix f  )  [0.. length l - 1 ]

loadDelayed :: InformationSchema -> TBData Key () -> TBData Key Showable -> IO (Maybe (TBIdx Key Showable))
loadDelayed inf t@(k,v) values@(ks,vs)
  | S.null $ _kvdelayed k = return Nothing
  | L.null delayedattrs  = return Nothing
  | otherwise = do
       let
           whr = T.intercalate " AND " ((\i-> (keyValue i) <>  " = ?") <$> S.toList (_kvpk k) )
           table = justError "no table" $ M.lookup (_kvpk k) (pkMap inf)
           delayedTB1 =  (ks,) . _tb $ KV ( filteredAttrs)
           delayed =  mapKey' (kOptional . ifDelayed . ifOptional) (mapValue' (const ()) delayedTB1)
           str = "SELECT " <> explodeRecord (relabelT' runIdentity Unlabeled delayed) <> " FROM " <> showTable table <> " WHERE " <> whr
       print str
       is <- queryWith (fromRecord delayed) (conn inf) (fromString $ T.unpack str) (fmap unTB $ F.toList $ _kvvalues $  runIdentity $ getCompose $ tbPK' (tableNonRef' values))
       case is of
            [] -> errorWithStackTrace "empty query"
            [i] ->return $ fmap (\(i,j,a) -> (i,getPKM (ks,vs),a)) $ difftable delayedTB1(mapKey' (kOptional.kDelayed.unKOptional) . mapFValue' (LeftTB1 . Just . DelayedTB1 .  unSOptional ) $ i  )
            _ -> errorWithStackTrace "multiple result query"
  where
    delayedattrs = concat $ fmap (keyValue . (\(Inline i ) -> i)) .  F.toList <$> M.keys filteredAttrs
    filteredAttrs = M.filterWithKey (\key v -> S.isSubsetOf (S.map _relOrigin key) (_kvdelayed k) && (all (maybe False id) $ fmap (fmap (isNothing .unSDelayed)) $ fmap unSOptional $ kattr $ v)  ) (_kvvalues $ unTB vs)


