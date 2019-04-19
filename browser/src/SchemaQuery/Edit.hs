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
import qualified Data.Sequence.NonEmpty as NonS
import Query
import Reactive.Threepenny hiding (apply)
import RuntimeTypes
import SchemaQuery.Read
import SchemaQuery.Store
import Types
import qualified Types.Index as G
import Types.Patch


isCreate a (i,CreateRule _) = i (mapKey' keyValue a)
isCreate _ _ = False

isDeleteRule a (i,DropRule _) =  i (mapKey' keyValue a)
isDeleteRule _ _ = False

isUpdate a (i,UpdateRule _) =  i (mapKey' keyValue a)
isUpdate _ _ = False

matchInsert = matchRule isCreate
matchDelete = matchRule isDeleteRule
matchUpdate = matchRule isUpdate

matchRule cond inf m a =
  let
    overloaded  = M.lookup (_kvschema m ,_kvname m) overloadedRules
    overloadedRules = (rules $ schemaOps inf)
  in L.find (cond  a) =<< overloaded

insertFrom  m a   = do
  inf <- askInf
  v <- case matchInsert inf m a  of
    Just (s,CreateRule l) -> do
      liftIO . putStrLn $ "Triggered create rule: " ++ show (_kvschema m,_kvname m)
      l a
    Nothing -> (insertEd $ schemaOps inf)  m a
  tellPatches m (pure v)
  return  v

updateFrom m a pk b = do
  inf <- askInf
  v <- case matchUpdate inf m a  of
    Just (_,UpdateRule i) -> do
      liftIO . putStrLn $ "Triggered update rule: " ++ show (_kvschema m,_kvname m)
      v <- i a b
      tellPatches m (pure v)
      return v
    Nothing -> do
      patchFrom m (pk ,PatchRow b)
  return v

patchFrom m  r   = do
  let l = RowPatch r
  asyncPatches m (pure l)
  return l

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

fullInsert :: KVMetadata Key ->TBData Key Showable -> TransactionM  (RowPatch Key Showable)
fullInsert k1 v1 = createRow' k1 <$> recInsert k1 v1

fullEdit :: KVMetadata Key -> TBData Key Showable -> TBIdx Key Showable -> TransactionM (RowPatch Key Showable)
fullEdit k1 old v2 =
  patchRow k1 old <$> fullDiffEdit k1 old v2



recInsert :: KVMetadata Key -> TBData Key Showable -> TransactionM  (TBData Key Showable)
recInsert k1  v1 = do
   inf <- askInf
   ret <- noInsert k1 v1
   let tb  = lookTable inf (_kvname k1)
       overloadedRules = (rules $ schemaOps inf)
   (_,(_,TableRep(_,_,l))) <- tableLoaderAll  tb Nothing mempty (Just (recPK inf k1 (allFields inf tb)))
   if  (isNothing $ (flip G.lookup l) =<< G.primaryKeyM k1  ret) && (rawTableType tb == ReadWrite || isJust (M.lookup (_kvschema k1 ,_kvname k1) overloadedRules))
      then catchAll (do
        tb  <- insertFrom k1 ret
        return $ createRow tb) (\e -> liftIO $ do
          throw e
          putStrLn $ "Failed insertion: "  ++ (show (e :: SomeException))
          return ret)
      else do
        return ret


itRefFun :: RelOperations (KV Key Showable)
itRefFun = (id,id,id,id,noEdit,noInsert)


noInsert :: KVMetadata Key  -> KV Key Showable -> TransactionM (KV Key Showable)
noInsert k1 = traverseKV (tbInsertEdit k1)

noEdit :: KVMetadata Key  -> KV Key Showable -> TBIdx Key Showable -> TransactionM (TBIdx Key Showable)
noEdit k1 = trazipWithKVP (tbEdit k1) 

trazipWithKVP ::  (Column Key Showable -> Index (Column Key Showable) -> TransactionM (Index (Column Key Showable)) )
              -> KV Key Showable -> TBIdx Key Showable -> TransactionM (TBIdx Key Showable)
trazipWithKVP f v j = concat <$> traverse editAValue (unkvlist v)
  where
    editAValue vi =
        let edits = L.find ((key ==). index) j 
            key = index vi
        in maybe (return []) (fmap pure <$> f vi ) edits


fullDiffEdit :: KVMetadata Key -> TBData Key Showable -> TBIdx Key Showable -> TransactionM (TBIdx Key Showable)
fullDiffEdit k1 old v2 = do
   edn <-  noEdit k1 old v2
   when (not $ L.null $ patchNoRef edn) . void $do
     updateFrom k1 old (G.getIndex k1 old) edn 
   return edn


tbEdit :: KVMetadata Key -> Column Key Showable -> Index (Column Key Showable) -> TransactionM (Index (Column Key Showable))
tbEdit m (Fun _ _ _ ) (PFun k1 rel k2)= return $ (PFun k1 rel k2)
tbEdit m (Attr _ _ ) (PAttr k1 k2)= return $ (PAttr k1 k2)
tbEdit m (IT a1 a2) (PInline k2 t2) = do
  inf <- askInf
  let r = _keyAtom $ keyType k2
      m2 = lookSMeta inf r
  PInline k2 <$> tbEditRef itRefFun m2  a2 t2
    
tbEdit m g@(FKT apk arel2  a2) f@(PFK rel2 pk  t2) = do
  inf <- askInf
  let
    ptable = lookTable inf $ _kvname m
    m2 = lookSMeta inf  $ RecordPrim $ findRefTableKey ptable rel2
    pkrel =  _relOrigin <$> kvkeys apk 
  fromMaybe (error "not empty") . recoverPFK pkrel rel2 <$> (tbEditRef (tbRefFun rel2) m2 (liftFK g) (liftPFK f))


type RelOperations b
  = (b -> TBData Key Showable
    , Index b -> TBIdx Key Showable
    , TBIdx Key Showable -> Index b
    , TBData Key Showable -> b
    , KVMetadata Key -> KV Key Showable -> TBIdx Key Showable -> TransactionM (TBIdx Key Showable)
    , KVMetadata Key -> KV Key Showable -> TransactionM (KV Key Showable) )


-- TODO: How to encode a common root merge and conflicts
-- | TBMerge a a a
--  | TBConflict (TBOperation a) a

operationTree :: Patch a => (a -> Index a -> TBOperation a) -> FTB a -> PathFTB (Index a) -> PathFTB (TBOperation a)
operationTree f (TB1 i) (PAtom j) = PAtom (f i j)
operationTree f (LeftTB1 i) (POpt j ) = POpt $ (liftA2 (operationTree f) i j) <|> (fmap (TBInsert . create) <$> j)
operationTree f (ArrayTB1 i) (PIdx ix jm) = PIdx ix $ (\ j ->  if ix >= L.length i then (TBInsert . create <$> j) else operationTree f  ( (NonS.!!)  i ix )  j ) <$> jm 
operationTree f i (PatchSet l ) = PatchSet $ fmap (operationTree  f i) l 

opmap :: (a -> b) -> (Index a -> Index b) -> TBOperation a -> TBOperation b
opmap f d (TBInsert i ) = TBInsert $ f i 
opmap f d (TBNoop i) = TBNoop (f i)
opmap f d (TBUpdate i j ) = TBUpdate (f i )  (d j )

tbEditRef :: (Patch b ,Show b) => RelOperations b -> KVMetadata Key ->  FTB b -> PathFTB (Index b) -> TransactionM (PathFTB (Index b))
tbEditRef fun@(funi,funid,funod,funo,edit,insert) m2 v1 v2 = mapInf m2 (traverse ((interp <=< recheck) . opmap funi funid) $operationTree comparison v1 v2)
  where
    recheck (TBInsert l ) = do
      inf <- askInf
      let
        tb  = lookTable inf (_kvname m2)
        overloadedRules = (rules $ schemaOps inf)
      (_,(_,TableRep(_,_,g))) <- tableLoaderAll  tb Nothing mempty (Just (recPK inf m2 (allFields inf tb)))
      if (isNothing $ (flip G.lookup g) =<< G.primaryKeyM m2 l) && (rawTableType tb == ReadWrite || isJust (M.lookup (_kvschema m2 ,_kvname m2) overloadedRules))
         then return (TBInsert l)
         else return (TBNoop l)
    recheck l = return l

    interp (TBNoop l) = return (patch $ funo l)
    interp (TBInsert l) = patch . funo <$> insert m2  l
    interp (TBUpdate ol l) = funod <$> edit m2  ol l
    comparison ol l = if G.getIndex m2 inol  == G.getIndex m2 inl then TBUpdate ol l else TBInsert (apply ol l ) 
      where
        inol = funi ol
        inl = apply inol (funid l)


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
    pkrel = fmap (_relOrigin ) . kvkeys  $ pk
  recoverFK  pkrel rel2 <$> tbInsertRef (tbRefFun rel2) m2 (liftFK f)

tbRefFun :: [Rel Key ] -> RelOperations (TBRef Key Showable)
tbRefFun rel2 = (snd.unTBRef,(\(PTBRef i j k)  -> compact (j <> k) ),(\i -> PTBRef [] i [] ), (\tb -> TBRef (fromMaybe (kvlist []) $ reflectFK rel2 tb,tb)),fullDiffEdit,recInsert)

tbInsertRef ::Show b => RelOperations b -> KVMetadata Key ->  FTB b -> TransactionM (FTB b)
tbInsertRef (funi,_ ,_,funo,edit,insert) m2 = mapInf m2 . traverse (fmap funo . insert m2 .funi)

mapInf m2 = localInf (\inf -> fromMaybe inf (HM.lookup (_kvschema m2) (depschema inf)))

