{-# LANGUAGE RecordWildCards, Arrows, RankNTypes, RecursiveDo,
  TypeFamilies, FlexibleContexts, OverloadedStrings, TupleSections
  #-}
module SchemaQuery
  (
    module SchemaQuery.Edit
  , module SchemaQuery.Read
  , module SchemaQuery.Arrow
  , module SchemaQuery.Store
  , revertModification
  ) where

import SchemaQuery.Store
import SchemaQuery.Edit
import SchemaQuery.Read
import SchemaQuery.Arrow
import RuntimeTypes
import Types.Patch
import Types.Common
import Types.Primitive
import qualified Types.Index as G
import qualified Data.Foldable as F
import Control.Monad.IO.Class
import Step.Common
import Utils
import Serializer
import qualified Data.Text as T

getRow (Idex ix) table =  do
  liftIO . putStrLn $ "Load complete row table : " ++ show (ix,table)
  inf <- askInf
  let pred = AndColl $ zipWith (\v i -> PrimColl (i ,[(i,Left (v,Equals))])) ix (rawPK table)
  (ref,(nidx,rep)) <-  tableLoaderAll table  Nothing (WherePredicate pred) Nothing
  return $safeHead (G.toList $ primary rep)

revertModification :: Int ->  TransactionM ()
revertModification idx = do
  inf <- askInf
  let table = lookTable (meta inf) "undo_modification_table"
      pred = [(keyRef "modification_id",Left (int idx,Equals))]
  (ref,(nidx,TableRep (_,_,ndata))) <- localInf (const (meta inf)) $ tableLoaderAll table  (Just 0) (tablePredicate (meta inf) (tableName table) pred) Nothing
  let
    mod :: RevertModification (T.Text,T.Text) (RowPatch T.Text Showable)
    mod@(RevertModification source delta)  = decodeT (mapKey' keyValue $ justError "row not found" $ safeHead $ F.toList ndata)
    targetName = snd (tableObj source)
    targetTable = lookTable inf targetName

  let op = unRowPatch $ liftRowPatch inf targetName  delta
  r <- getRow (fst op) targetTable
  traverse (\r ->
    case  snd op of
      DropRow -> do
        deleteFrom (tableMeta targetTable) r
      PatchRow p -> do
        fullEdit (tableMeta targetTable) r p
      CreateRow p -> do
        fullInsert (tableMeta targetTable) r
          ) r
  return ()


