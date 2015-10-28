{-# LANGUAGE TupleSections #-}
module SchemaQuery
  (deleteMod
  ,insertMod
  ,updateMod
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
import qualified Data.Traversable as Tra
import qualified Data.List as L
import Types
import Query
import Postgresql
import PostgresQuery
import Data.Maybe
import Prelude hiding (head)
import Schema
import qualified Data.Foldable as F
import Data.Foldable (foldl')
import Database.PostgreSQL.Simple

--
--  MultiTransaction Postgresql insertOperation
--

deleteMod :: InformationSchema ->  TBData Key Showable -> Table -> IO (Maybe (TableModification (TBIdx Key Showable)))
deleteMod inf j@(meta,_) table = do
  let patch =  (tableMeta table, getPKM j,[])
  deletePatch (conn inf)  patch table
  Just <$> logTableModification inf (TableModification Nothing table patch)


type TransactionM = WriterT [TableModification (TBIdx Key Showable)] IO

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
   tell (maybeToList mod)
   return edn

fullDiffInsert :: InformationSchema -> TBData Key Showable -> TransactionM  (Maybe (TableModification (TBIdx Key Showable)))
fullDiffInsert inf  (k2,v2) = do
   let proj = _kvvalues . unTB
   edn <- (k2,) . Compose . Identity . KV <$>  Tra.sequence ((\ j -> Compose <$>  tbInsertEdit inf   (unTB j) ) <$>  (proj v2))
   mod <- liftIO $ insertMod inf edn (lookTable inf (_kvname k2))
   tell (maybeToList mod)
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



