{-# LANGUAGE RecordWildCards, Arrows, RankNTypes, RecursiveDo,
  TypeFamilies, FlexibleContexts, OverloadedStrings, TupleSections
  #-}
module SchemaQuery.Edit
  (
  -- Database Mutable Operations
    matchInsert
  , matchUpdate
  , matchDelete
  , fullInsert
  , fullEdit
  , patchFrom
  , deleteFrom
  ) where

import Control.Exception (throw)
import Control.Monad.Catch
import Control.Monad.RWS
import qualified Data.Foldable as F
import qualified Data.HashMap.Strict as HM
import qualified Data.List as L
import qualified Data.Map as M
import Data.Maybe
import Data.Time
import qualified NonEmpty as Non
import Debug.Trace
import Query
import Reactive.Threepenny hiding (apply)
import RuntimeTypes
import SchemaQuery.Read
import Types
import qualified Types.Index as G
import Types.Patch


matchUpdate inf m a =
 let
    overloaded  = M.lookup (_kvschema m ,_kvname m) overloadedRules
    overloadedRules = (rules $ schemaOps inf)
    isUpdate (i,UpdateRule _ ) =  i (mapKey' keyValue a)
    isUpdate _ = False
 in L.find isUpdate  =<< overloaded


updateFrom m a pk b = do
  inf <- askInf
  v <- case matchUpdate inf m a  of
    Just (_,UpdateRule i) -> do
      liftIO . putStrLn $ "Triggered update rule: " ++ show (_kvschema m,_kvname m)
      v <- i a b
      tellPatches m (pure v)
      return v
    Nothing -> do
      let bf = filter (\k -> F.any (L.elem FWrite . keyModifier ._relOrigin) (index k)) b
      patchFrom m ((pk ,PatchRow bf))
  return v

patchFrom m  r   = do
  liftIO $ print r
  let l = RowPatch r
  asyncPatches m (pure l)
  return l

fullInsert :: KVMetadata Key ->TBData Key Showable -> TransactionM  (RowPatch Key Showable)
fullInsert k1 v1 = createRow' k1 <$> recInsert k1 v1

fullEdit ::  KVMetadata Key -> TBData Key Showable -> TBData Key Showable -> TransactionM (RowPatch Key Showable)
fullEdit k1 old v2 =
  patchRow' k1 old <$> fullDiffEdit k1 old v2

matchInsert inf m a =
  let
    overloaded  = M.lookup (_kvschema m ,_kvname m) overloadedRules
    overloadedRules = (rules $ schemaOps inf)
    isCreate (i,CreateRule _ ) = i (mapKey' keyValue a)
    isCreate _ = False
  in L.find isCreate  =<< overloaded

insertFrom  m a   = do
  inf <- askInf
  v <- case matchInsert inf m a  of
    Just (s,CreateRule l) -> do
      liftIO . putStrLn $ "Triggered create rule: " ++ show (_kvschema m,_kvname m)
      l a
    Nothing -> (insertEd $ schemaOps inf)  m a
  tellPatches m (pure v)
  return  v

matchDelete inf m a =
 let
    overloaded  = M.lookup (_kvschema m ,_kvname m) overloadedRules
    overloadedRules = (rules $ schemaOps inf)
    isDelete (i,DropRule _ ) =  i (mapKey' keyValue a)
    isDelete _ = False
 in L.find isDelete =<< overloaded


deleteFrom  m a   = do
  inf <- askInf
  log <- case matchDelete inf m a  of
    Nothing -> (deleteEd $ schemaOps inf) m a
    Just (_,DropRule i) -> do
      liftIO . putStrLn $ "Triggered drop rule: " ++ show (_kvschema m,_kvname m)
      i a
  tellPatches m (pure log)
  return log


createRow (RowPatch (_,CreateRow i)) = i
createRow (RowPatch (_,PatchRow i)) = create i


recInsert :: KVMetadata Key -> TBData Key Showable -> TransactionM  (TBData Key Showable)
recInsert k1  v1 = do
   inf <- askInf
   ret <- traverseKV (tbInsertEdit k1) v1
   let tb  = lookTable inf (_kvname k1)
       overloadedRules = (rules $ schemaOps inf)
   (_,(_,TableRep(_,_,l))) <- tableLoaderAll  tb Nothing mempty (Just (recPK inf k1 (allFields inf tb)))
   if  (isNothing $ (flip G.lookup l) =<< G.tbpredM k1  ret) && (rawTableType tb == ReadWrite || isJust (M.lookup (_kvschema k1 ,_kvname k1) overloadedRules))
      then catchAll (do
        tb  <- insertFrom k1 ret
        return $ createRow tb) (\e -> liftIO $ do
          throw e
          putStrLn $ "Failed insertion: "  ++ (show (e :: SomeException))
          return ret)
      else do
        return ret


itRefFun :: RelOperations (KV Key Showable)
itRefFun = (id,id,noEdit,noInsert)
  where
    noInsert k1 v1   = do
      traverseKV (tbInsertEdit k1)  v1
    noEdit k1 v1 v2  = do
      trazipWithKV (tbDiffEditInsert k1) v1 v2

fullDiffEdit :: KVMetadata Key -> TBData Key Showable -> TBData Key Showable -> TransactionM (TBData Key Showable)
fullDiffEdit k1 old v2 = do
   edn <-  trazipWithKV (tbDiffEditInsert k1)  old v2
   when (isJust $ diff (tableNonRef old) (tableNonRef edn)) . void $do
     traverse (updateFrom k1 old (G.getIndex k1 edn))  (diff old edn)
   return edn

tbDiffEditInsert :: KVMetadata Key ->  Column Key Showable -> Column Key Showable -> TransactionM (Column Key  Showable)
tbDiffEditInsert k1 i j
  | isJust (diff i  j) = tbEdit k1 i j
  | otherwise =  return j


tbEdit :: KVMetadata Key -> Column Key Showable -> Column Key Showable -> TransactionM (Column Key Showable)
tbEdit m (Fun _ _ _ ) (Fun k1 rel k2)= return $ (Fun k1 rel k2)
tbEdit m (Attr _ _ ) (Attr k1 k2)= return $ (Attr k1 k2)
tbEdit m (IT a1 a2) (IT k2 t2) = do
  inf <- askInf
  let r = _keyAtom $ keyType k2
      m2 = lookSMeta inf r
  IT k2 <$> tbEditRef itRefFun m2  a2 t2
tbEdit m g@(FKT apk arel2  a2) f@(FKT pk rel2  t2) = do
  inf <- askInf
  let
    ptable = lookTable inf $ _kvname m
    m2 = lookSMeta inf  $ RecordPrim $ findRefTableKey ptable rel2
    pkrel = fmap (_relOrigin. head. F.toList) $ kvkeys pk
  recoverFK pkrel rel2 <$> (tbEditRef (tbRefFun rel2) m2 (liftFK g) (liftFK f))

type RelOperations b
  = (b -> TBData Key Showable
    , TBData Key Showable -> b
    , KVMetadata Key -> KV Key Showable -> KV Key Showable -> TransactionM (KV Key Showable)
    , KVMetadata Key -> KV Key Showable -> TransactionM (KV Key Showable) )


-- TODO: How to encode a common root merge and conflicts
-- | TBMerge a a a
--  | TBConflict (TBOperation a) a

operationTree :: (a -> a -> TBOperation a) -> FTB a -> FTB a -> FTB (TBOperation a)
operationTree f (TB1 i) (TB1 j) = TB1 (f i j)
operationTree f (LeftTB1 i) (LeftTB1 j ) = LeftTB1 $ (liftA2 (operationTree f) i j) <|> (fmap TBInsert <$> j)
operationTree f (ArrayTB1 i) (ArrayTB1 j) = (\i a -> ArrayTB1 . Non.fromList $ F.toList i ++ a)  (Non.zipWith (operationTree f) i j)  (fmap TBInsert <$> Non.drop (Non.length i) j)

tbEditRef :: Show b => RelOperations b -> KVMetadata Key ->  FTB b -> FTB b -> TransactionM (FTB b)
tbEditRef fun@(funi,funo,edit,insert) m2 v1 v2 = mapInf m2 (traverse (fmap funo  . (interp <=< recheck) . fmap funi) $operationTree comparison v1 v2)
  where
    recheck (TBInsert l ) = do
      inf <- askInf
      let
        tb  = lookTable inf (_kvname m2)
        overloadedRules = (rules $ schemaOps inf)
      (_,(_,TableRep(_,_,g))) <- tableLoaderAll  tb Nothing mempty (Just (recPK inf m2 (allFields inf tb)))
      if (isNothing $ (flip G.lookup g) =<< G.tbpredM m2 l) && (rawTableType tb == ReadWrite || isJust (M.lookup (_kvschema m2 ,_kvname m2) overloadedRules))
         then return (TBInsert l)
         else return (TBNoop l)
    recheck l = return l

    interp (TBNoop l) = return l
    interp (TBInsert l) = insert m2  l
    interp (TBUpdate ol l) = edit m2  ol l
    comparison ol l = if G.getIndex m2 inol  == G.getIndex m2 inl then TBUpdate ol l else TBInsert l
      where
        inol = funi ol
        inl = funi l


tbInsertEdit :: KVMetadata Key -> Column Key Showable -> TransactionM (Column Key Showable)
tbInsertEdit m (Attr k1 k2) = return $ (Attr k1 k2)
tbInsertEdit m (Fun k1 rel k2) = return $ (Fun k1 rel k2)
tbInsertEdit m (IT k2 t2) = do
  inf <- askInf
  let RecordPrim r = _keyAtom $ keyType k2
  IT k2 <$> tbInsertRef itRefFun (tableMeta $ lookSTable inf r)   t2
tbInsertEdit m f@(FKT pk rel2 t2) = do
  inf <- askInf
  let
    ptable = lookTable inf $ _kvname m
    m2 = lookSMeta inf  $ RecordPrim $ findRefTableKey ptable rel2
    pkrel = fmap (_relOrigin. head. F.toList) . kvkeys  $ pk
  recoverFK  pkrel rel2 <$> tbInsertRef (tbRefFun rel2) m2 (liftFK f)

tbRefFun :: [Rel Key ] -> RelOperations (TBRef Key Showable)
tbRefFun rel2 = (snd.unTBRef,(\tb -> TBRef (fromMaybe (kvlist []) $ reflectFK rel2 tb,tb)),fullDiffEdit,recInsert)

tbInsertRef ::Show b => RelOperations b -> KVMetadata Key ->  FTB b -> TransactionM (FTB b)
tbInsertRef (funi,funo,edit,insert) m2 = mapInf m2 . traverse (fmap funo . insert m2 .funi)

mapInf m2 = localInf (\inf -> fromMaybe inf (HM.lookup (_kvschema m2) (depschema inf)))


asyncModification m a = do
  inf <- askInf
  now <- liftIO getCurrentTime
  AsyncTableModification  (lookTable inf (_kvname m) )<$>  return a


asyncPatches :: KVMetadata Key ->  [RowPatch Key Showable] -> TransactionM ()
asyncPatches m i =
  modifyTable m [] =<< mapM (asyncModification m) i

tellPatches :: KVMetadata Key ->  [RowPatch Key Showable] -> TransactionM ()
tellPatches m i =
  modifyTable m [] =<< mapM (wrapModification m ) i
