{-# LANGUAGE RecordWildCards, Arrows, RankNTypes, RecursiveDo,
  FlexibleInstances,TypeSynonymInstances,TypeFamilies, FlexibleContexts, OverloadedStrings, TupleSections
  #-}
module SchemaQuery.Read
  (
  -- Create fresh variables
   createFresh
  -- Database Read Only Operations
  , select
  , selectFrom
  , selectFromProj
  , getFrom
  , listenFrom
  , listenLogTable
  , refTable
  , refTables
  , refTablesDesc
  , refTablesProj
  , tableLoaderAll
  , selectFromTable
  , fromTable
  , fromTableS
  , fkPredicate
  , fkPredicateIx
  , refTables'
  -- Cache Only Operations
  , loadFKS
  -- Constraint Checking
  , tableCheck
  -- SQL Arrow API
  ) where

import Control.Arrow
import TP.Widgets(calmT)
import Reactive.Threepenny.PStream
import SchemaQuery.Store
import Serializer
import Text
import Control.Concurrent.STM
import qualified Control.Lens as Le
import Control.Monad.Catch
import Debug.Trace
import Control.Monad.RWS
import Control.Monad.Trans.Maybe
import Data.Either
import qualified Data.Foldable as F
import qualified Data.HashMap.Strict as HM
import qualified Data.Interval as Interval
import qualified Data.List as L
import qualified Data.Map as M
import Data.Maybe
import qualified Data.Set as S
import qualified Data.Text as T
import Data.Time
import qualified Data.Traversable as Tra
import Expression
import Query
import Reactive.Threepenny hiding (apply)
import RuntimeTypes
import Step.Common
import Types
import qualified Types.Index as G
import Types.Patch
import Utils


estLength page size est = fromMaybe 0 page * size  +  est

projunionMeta :: InformationSchema -> Table -> KVMeta Key  -> KVMeta Key
projunionMeta inf table = res
  where
    res =  liftTable' inf (tableName table) . mapKey' keyValue. transformTable
    transformTable = mapKV transformAttr . kvFilter (\k -> S.isSubsetOf (S.map keyString $ relOutputSet k) attrs)
      where
        attrs = S.fromList $ keyValue <$> rawAttrs table
        transformAttr (Fun k l i) = Fun k l (keyType nk) 
          where nk = lkKey table (keyValue k)
        transformAttr (Attr k i ) = Attr k (keyType nk)
          where nk = lkKey table (keyValue k)
        transformAttr (IT k i ) = IT k i
          where nk = lkKey table (keyValue k)
        transformAttr (FKT r rel v) = FKT (transformTable r ) rel v
          where ok = mergeFKRef (keyType. _relOrigin <$> rel)
                nk = mergeFKRef (keyType. lkKey table . keyValue . _relOrigin <$> rel)


projunion :: Show a=>InformationSchema -> Table -> KV Key  a -> KV Key  a
projunion inf table = res
  where
    res =  liftTable' inf (tableName table) . mapKey' keyValue. transformTable
    transformTable = mapKV transformAttr . kvFilter (\k -> S.isSubsetOf (S.map keyString $ relOutputSet k) attrs)
      where
        attrs = S.fromList $ keyValue <$> rawAttrs table
        transformAttr (Fun k l i) = Fun k l (transformKey (keyType k) (keyType nk) i)
          where nk = lkKey table (keyValue k)
        transformAttr (Attr k i ) = Attr k (transformKey (keyType k) (keyType nk) i)
          where nk = lkKey table (keyValue k)
        transformAttr (IT k i ) = IT k (transformKey (keyType k) (keyType nk) i)
          where nk = lkKey table (keyValue k)
        transformAttr (FKT r rel v) = FKT (transformTable r ) rel (transformKeyList ok nk  v)
          where ok = mergeFKRef (keyType. _relOrigin <$> rel)
                nk = mergeFKRef (keyType. lkKey table . keyValue . _relOrigin <$> rel)

mapIndex :: InformationSchema  -> Table -> IndexMetadata Key Showable -> IndexMetadata Key Showable
mapIndex inf table (IndexMetadata i)  = IndexMetadata $ M.mapKeys (liftPredicateF (lookupKeyName) inf (tableName table) . mapPredicate (fmap keyValue)) . filterPredicate $ i
  where
    filterPredicate  = M.filterWithKey (\k _ -> isJust $ traPredicate  check  $ k)
    check i = if S.member (keyValue i) attrs  then Just i else Nothing
    attrs = S.fromList $ keyValue <$> rawAttrs table

lookIndexMetadata pred (IndexMetadata i ) = M.lookup pred i

mapIndexMetadata f (IndexMetadata v ) = IndexMetadata $ M.mapKeys (mapPredicate (fmap f) )  v
mapIndexMetadataPatch f (i,j,k,l) = (mapPredicate (fmap f) i,j,k,l)

mapDBVar :: InformationSchema -> Table -> DBVar2 Showable -> ([DBRef Key Showable],Tidings (IndexMetadata Key Showable),Tidings (M.Map [Rel Key] (SecondaryIndex Key Showable),TableIndex Key Showable ))
mapDBVar inf table (DBVar2 e i l  )
  = ([e], mapIndex inf table <$> i,  (\(TableRep (_,i,j)) -> (i,createUn (tableMeta table)  (rawPK table) . fmap (projunion inf table) . G.toList $ j)) <$> l)

mergeDBRef  (IndexMetadata j,i) (IndexMetadata m,l) = (IndexMetadata $ M.unionWith (\(a,b) (c,d) -> (a+c,M.unionWith mergeToken b d))  j  m , i <>  l )

mergeDBRefT  (ref1,j ,i) (ref2,m ,l) = (ref1 <> ref2 ,liftA2 (\(IndexMetadata a) (IndexMetadata b) -> IndexMetadata $ M.unionWith (\(a,b) (c,d) -> (a+c,M.unionWith mergeToken  b d)) a b)  j  m , liftA2 (\(i,j) (i2,j2)-> (M.intersectionWith (<>)i i2 ,  j <> j2))  i l   )

refTable :: InformationSchema -> Table -> Dynamic DBVar
refTable  inf table  = do
  mmap <- liftIO$ atomically $ readTVar (mvarMap inf)
  ref <- liftIO $ lookDBVar inf mmap (tableMeta table)
  (idxTds,dbTds ) <- convertChan inf table mempty (allFields inf table) ref
  return (DBVar2 ref idxTds  dbTds )


selectFromTable
 :: T.Text
 -> Maybe Int
 -> [(Rel T.Text , AccessOp Showable )]
 -> TransactionM DBVar
selectFromTable t a p = do
  inf  <- askInf
  selectFrom t a (tablePredicate inf t p)


selectFromProj t a d p = do
  inf <- askInf
  let tb = lookTable inf t
  tableLoader tb a d p


selectFrom t a d = do
  inf <- askInf
  let tb = lookTable inf t
  tableLoader tb a d (allFields inf tb)

pkPred  m b =  pred
  where
    attrs = justError "missing attr" $ traverse (\ i-> (i, ) <$> kvLookup (simplifyRel i)   (tableNonRef b)) ( _kvpk m)
    pred = WherePredicate . andColl $ 
        (\(i,v) -> PrimColl . (simplifyRel i ,) .  pure . (simplifyRel i,). Left . (,Equals) . _tbattr $ v ) <$> attrs

getFrom :: Table -> KVMeta Key -> KV Key Showable -> TransactionM (DBRef Key Showable,Maybe (TBIdx Key Showable))
getFrom table allFields b = {-(\i -> traverse (\i -> liftIO$ putStrLn $ "delta \n " ++ ident (render i)) (snd i) >> return i) =<<-}  do
  inf <- askInf
  let
    m = tableMeta table
    pred = pkPred m b
    comp = recComplement inf m allFields pred b
  ((IndexMetadata fixedmap,TableRep (_,sidx,reso)),dbvar)
      <- createTable pred (tableMeta table)
  r <- maybe (do
    liftIO . putStrLn $  "getFrom: "<> show (tableName table) <> " row is complete " <> renderPredicateWhere pred 
    return Nothing) (\comp -> debugTime ("getFrom: " <> show (tableName table)) $ do
    let n = recComplement inf m  allFields pred  =<< new
        new = G.lookup (G.getIndex m b) reso
        delta = diff b =<< new
    --liftIO . putStrLn $ ident (render b)
    --liftIO . putStrLn $ ident (render comp)
    (maybe (do
      liftIO . putStrLn $ "Local storage: get " <> T.unpack (tableName table) <>  " where "  <> (renderPredicateWhere pred) -- , new ,G.keys reso )
      return delta )  (\comp -> do
      -- liftIO . putStrLn $ "Loading complement\n"  <> (ident . render $ comp)
      v <- (getEd $ schemaOps inf) table (restrictTable nonFK comp) (G.getIndex m b)
      let newRow = apply (apply b (fromMaybe mempty delta)) v
      resFKS  <- getFKS inf pred table  [newRow] comp
      let
        output = resFKS newRow
        result = either (const Nothing) (Just. patch )  output
      traverse (fetchPatches m [] . pure . (RowPatch . (G.getIndex m b,).PatchRow)) result
      --traverse (\i -> do
        --liftIO . putStrLn $ "Pred\n" <> show pred
        --liftIO . putStrLn $ "Old\n" <> show b
        --liftIO . putStrLn $ "Delta\n" <> (maybe ("") show delta)
        --liftIO . putStrLn $ "Get\n" <> (show v)
        --liftIO . putStrLn $ "Result\n" <> (either show (ident.render) output)
        --liftIO . putStrLn $ "DiffResult\n" <> (maybe "" show  result)
        -- liftIO . putStrLn $ "Remaining complement\n"  <> (ident .render $ i)) $ (recComplement inf m allFields pred ) =<< (applyIfChange (apply b  (fromMaybe mempty delta) ) =<< result )
      return result) n)) comp
  return (dbvar,r)



expandOperation (PatchRow i ) = Diff i
expandOperation (CreateRow j ) = Diff (patch j)
expandOperation (DropRow  ) =  Delete 

expandPatch (RowPatch (i,j)) = expandOperation j  
expandPatch (BatchPatch i j) = expandOperation j  

listenFrom table allFields b = mdo
  inf <- askInf
  let
    m = tableMeta table
    pred = WherePredicate . andColl $ catMaybes $ fmap PrimColl . (\i -> (i ,) .  pure . (i,). Left . (,Equals) . _tbattr <$> kvLookup (i )  (tableNonRef b) )<$> _kvpk m
  (dbref,r) <- getFrom table allFields b
  let result = fromMaybe b $ applyIfChange b =<< r
  e <- lift $ convertChanEvent inf table (pred,rawPK table)  allFields  (pure (apply (TableRep (m,M.empty,G.empty)) (createRow' m  result)))  (patchVar dbref)
  lift $ accumT (Just result) ((\e i -> either error fst . foldUndo i . fmap expandPatch  $  e  )  <$> e)



paginateTable table pred tbf = do
  inf <- askInf
  (ref,(nidx,TableRep (_,_,ndata))) <-  tableLoaderAll table (Just 0) pred (Just tbf)
  let
    check ix (i,tb2) = do
        let
          iempty = (IndexMetadata M.empty,G.empty)
          next = ix +1
          -- Check if estimated size exist and if is bigger then the next page size (next * pagesize)
          -- or the current is already bigger or euqals the estimated
          cond = maybe False (\i -> fst i >= G.size tb2 && fst i >= next * (opsPageSize $ schemaOps inf))  (lookIndexMetadata pred i)
        output <- if cond
            then  do
              liftIO $ putStrLn $ "Loading table " ++ show (tableName table) ++ " page " ++ show ix
              (_,(nidx,TableRep(_,_,ndata))) <- tableLoaderAll table (Just next) pred (Just tbf)
              -- Check if nothing has changed  or no more data to load
              if G.size ndata == G.size tb2
                 then return iempty
                 else check next (nidx,ndata)
            else return iempty
        return $ mergeDBRef (i,tb2) output
  snd <$> check 0 (nidx,ndata)

predicate
  :: Show a1 => [Rel (FKey (KType a1))]
     -> TBPredicate (FKey (KType a1)) a
     -> Maybe (TBPredicate (FKey (KType a1)) a)
predicate i (WherePredicate l ) =
   fmap WherePredicate (go (test (relComp i)) l)
  where
    go pred (AndColl l) = andColl <$> nonEmpty (catMaybes $ go pred <$> l)
    go pred (OrColl l) = orColl <$> nonEmpty (catMaybes $ go pred <$> l)
    go pred (PrimColl l) = PrimColl <$> pred l
    test f (RelAccess p i ,j)  = if p == f then Just ( i ,fmap (mapLeft (fmap (removeArray (_keyFunc $ relType  p)))) <$> j) else Nothing
    test v f = Nothing
    removeArray (KOptional :i)  o = removeArray i o
    removeArray (KArray : i)  (AnyOp o) = o
    removeArray i  o = o

getFKRef inf predtop (me,old) set (FKInlineTable  r j ) tbf =  do
    let
      rinf = maybe inf id $ HM.lookup (fst j) (depschema inf)
      table = lookTable rinf $ snd j
      nextRef :: [FTB (TBData Key Showable)]
      nextRef = catMaybes $ fmap (\i -> _fkttable  <$> kvLookup (Inline r) i ) set
    case nonEmpty (concat $ fmap F.toList nextRef) of
      Just refs -> do
        joinFK <- getFKS rinf predtop table  refs tbf
        let joined = alterAtF (Inline r) (traverse joinFK)
        return (me >=> joined,old <> S.singleton r)
      Nothing ->
        return (me ,old <> S.singleton r)

getFKRef inf predtop (me,old) v f@(FunctionField a b c) tbf
  | L.any isRelAccess c = do
    let
      evalFun :: TBData Key Showable -> Either ([TB Key Showable],[Rel Key]) (TBData Key Showable)
      evalFun i = maybe (Left $( [],S.toList  $ pathRelRel f)  )  (Right . flip addAttr i) (evaluate  a b funmap c i)
    return (me >=> evalFun ,old <> S.singleton a )
  | otherwise = return (me,old)
getFKRef  inf predtop (me,old) v f@(PluginField (ix,FPlugins s t  c)) tbf =  do
  let
    evalPlugin (PurePlugin a) v = if isJust (checkPredFull inf t (fst $ staticP a) v) then Right (maybe v (apply v)  (diff v =<<  (liftTable' inf t <$> (dynPure a $ mapKey' keyValue v)))) else Right v
    evalPlugin (DiffPurePlugin a) v = if isJust (checkPredFull inf t (fst $ staticP a) v) then Right (maybe v (apply v) (liftPatch inf t <$> (dynPure a $ mapKey' keyValue v))) else Right v
    evalPlugin (StatefullPlugin j) v = F.foldl' (\i j -> evalPlugin j =<< i) (Right v) (snd <$> j)
    evalPlugin i v = Right v
  return (me >=> evalPlugin c ,old)

getFKRef inf predtop (me,old) set (RecJoin i j) tbf = getFKRef inf predtop (me,old) set j tbf

getFKRef inf predtop (me,old) set (FKJoinTable i j) tbf =  do
    let
      nonRefRel (Rel i _ _ ) = i
      nonRefRel i@(Inline _ ) = i
      nonRefRel i = i
      unComp =  fmap nonRefRel . concat . fmap relUnComp  
      tar = S.fromList $ fmap _relOrigin (unComp i)
      refl = S.fromList $ fmap _relOrigin $ filterReflexive i
      rinf = maybe inf id $ HM.lookup (fst j)  (depschema inf)
      table = lookTable rinf $ snd j
      refs = fkPredicate i set 
      predm = refs <> predicate i predtop
    tb2 <-  case predm of
      Just pred -> do
        localInf (const rinf) $ paginateTable table pred tbf
      Nothing -> return (G.empty)
    let
      inj = S.difference refl old
      joinFK :: TBData Key Showable -> Either ([TB Key Showable],[Rel Key]) (Column Key Showable)
      joinFK m  = maybe (Left (atttar,i))  Right $ FKT (kvlist attinj) i <$> joinRel2 (tableMeta table ) targetAttr tb2
        where
          targetAttr= (fmap (replaceRel i )$ atttar ) 
          replaceRel rel (Attr k v) = (justError "no rel" $ L.find ((==k) ._relOrigin) rel,v)
          nonRef = tableNonRef m
          atttar = getAtt tar nonRef
          attinj = getAtt inj nonRef
      add :: Column Key Showable -> TBData Key Showable -> TBData Key Showable
      add r = addAttr r  . kvFilter (\k ->  not $ relOutputSet k `S.isSubsetOf` refl && isInlineRel k)
      joined i = do
         fk <- joinFK i
         return $ add fk i
    return $ (me >=> joined,old <> refl)

traceIfFalse i False = traceShow i  False
traceIfFalse i True = True

mapLeft f (Left i ) = Left (f i)
mapLeft f (Right i ) = (Right i)


-- fkPredicateIx rel l | traceShow ("fkPredicateIx" , renderRel rel,head l) False = undefined
fkPredicateIx rel set =  refs
  where 
    genpredicate o = primPredicate o rel 
    primPredicate o (RelAccess ref tar) 
      =  join $ fmap orColl . nonEmpty . catMaybes . fmap (flip primPredicate tar) <$> nonEmpty i 
      where i = concat $ fmap F.toList $ F.toList $ refLookup ref o  
    primPredicate o (RelComposite l ) =  fmap andColl . allMaybes .  fmap (primPredicate o ) $ l
    primPredicate o (Rel ori op tar)  = do
      let attr = lkAttr ori o
      i <- unSOptional ._tbattr $ attr 
      return $ PrimColl (tar,[(tar,Left (i,Flip op))])
    primPredicate _ i = error (show i)
    lkAttr k v =  justError ("noAttr " <> show (k,v,rel) )$ kvLookup k v <|> kvLookup k (tableNonRef v) <|> kvLookup (Inline $ _relOrigin k) (tableNonRef v)
    refs = fmap (WherePredicate .orColl. L.nub) $ nonEmpty $ catMaybes $  genpredicate <$> set


-- fkPredicateIx rel l | traceShow ("fkPredicate" , renderRel rel,head l) False = undefined
fkPredicate i set =  refs
  where 
    genpredicate o = fmap andColl . allMaybes . fmap (primPredicate o)  $ i
    primPredicate o k  = do
      let a  = justError ("No Attr: " ++ show (k,L.intercalate ", " $ fmap renderRel $ kvkeys o,i)) $ lkAttr k o
      case a of 
        Attr _ v -> (\i -> PrimColl (_relTarget k ,[(_relTarget k,Left (i,Flip $ _relOperator k))])) <$>  unSOptional v 
        FKT i l _ -> primPredicate (mappend i (kvlist $ catMaybes $ flip kvLookup o <$>  (concatMap (fmap relAccessSafe .relUnComp )  l)))  k 
        i -> error ("not a attr " ++ show i)
    lkAttr k v 
      = kvLookup k v <|> kvLookup k (tableNonRef v) <|>  (kvLookup (Inline $ _relOrigin k) (tableNonRef v))
    refs = fmap (WherePredicate .orColl. L.nub) $ nonEmpty $ catMaybes $  genpredicate <$> set

getFKS
  :: InformationSchemaKV Key Showable
     -> TBPredicate Key Showable
     -> TableK Key
     -> [TBData Key Showable]
     -> KVMeta Key 
     -> TransactionM
        (TBData Key Showable -> Either
              ([TB Key Showable],[Rel Key])
              (TBData Key Showable))
getFKS inf predtop table v tbf = fmap fst $ F.foldl' (\m f  -> m >>= (\i -> maybe (return i) (getFKRef inf predtop i v f  . head . F.toList )  (pluginCheck  f tbf) )) (return (return ,S.empty )) sorted
  where
    pluginCheck i@(PluginField _) tbf = Just (Primitive [] mempty) 
    pluginCheck i tbf  = refLookup (relComp $ pathRelRel i) tbf
    sorted =  sortValues (relComp . pathRelInputs inf (tableName table)) $ rawFKS table <> functionRefs table <> pluginFKS table

rebaseKey inf t  (WherePredicate fixed ) = WherePredicate $ lookAccess inf (tableName t) . (Le.over Le._1 (fmap  keyValue) ) . fmap (fmap (first (fmap keyValue)))  <$> fixed

mergeToken (pi,TableRef i)  (pj,TableRef j) = (pi <> pj,TableRef $ Interval.hull i  j)

type TableChannels k v =  (TChan (IndexMetadataPatch k v), TChan [TableModificationU k v])

tableLoader
    :: Table
    -> Maybe Int
    -> WherePredicate
    -> KVMeta Key 
    -> TransactionM DBVar
tableLoader (Project table  (Union l)) page fixed  tbf = do
  liftIO . putStrLn $ "start loadTable " <> show (tableName table)
  inf <- askInf
  let
    m = tableMeta table
    dbvarMerge i = foldr mergeDBRefT  ([],pure (IndexMetadata M.empty)  ,pure ( M.fromList $ (,G.empty)<$> _kvuniques m,G.empty )) (mapDBVar inf table <$>i )
    dbvar (l,i,j) = DBVar2 (justError "head5" $ safeHead l) i ((\(i,j) -> TableRep (m, i,j) :: TableRep Key Showable) <$> j)
  i <- mapM (\t -> tableLoader t page (rebaseKey inf t  fixed) (projunionMeta inf t tbf)) l
  return $ dbvar (dbvarMerge i)
tableLoader  table page fixed tbf = do
  liftIO . putStrLn $ "start loadTable " <> show (tableName table)
  (ref,(nidx,rep)) <- tableLoader' table page fixed tbf
  inf <- askInf
  vpt <- lift $ convertChanTidings0 inf table (fixed ,rawPK table) tbf rep  (patchVar ref)
  idxTds <- lift $ convertChanStepper0 inf table nidx (idxChan ref) 
  return (DBVar2 ref idxTds vpt)

tableLoader'
  :: Table
   -> Maybe Int
   -> WherePredicate
   -> KVMeta Key 
   -> TransactionM (DBRef Key Showable,(IndexMetadata Key Showable,TableRep Key Showable ))
tableLoader' = do
  pageTable (\table page token size presort predicate tbf reso -> do
    inf <- askInf
    let
      unestPred (WherePredicate l) = WherePredicate $ go predicate l
        where
          go pred (AndColl l) = AndColl (go pred <$> l)
          go pred (OrColl l) = OrColl (go pred <$> l)
          go pred (PrimColl l) = PrimColl $ pred l
          predicate (RelAccess i j ,_ ) = (i, ((\a -> (a,Right (Not IsNull)))<$>) $ relUnComp i)
          predicate (NInline i j ,r)   = (Inline j ,r)
          predicate i = i
    (res ,x ,o) <- (listEd $ schemaOps inf) (tableMeta table) (restrictTable nonFK tbf) page token size presort (unestPred predicate)

    let preresult =  mapResult <$> res
        mapResult i = do
            case G.lookup (G.getIndex (tableMeta table) i) reso of
                Just orig ->  case recComplement inf (tableMeta table) tbf predicate orig   of
                    Just d -> Left (apply orig (patch i))
                    Nothing -> Right  orig
                Nothing -> Left i
    result <- if L.any isLeft preresult
      then do
        resFKS <- getFKS inf predicate table (lefts preresult) tbf
        return (either resFKS Right <$> preresult)
      else return (either (error  "") Right <$> preresult)
    liftIO $ when (not $ null (lefts result)) $ do
      putStrLn . T.unpack $ "Missing references: "  <> tableName table
      --putStrLn $ "Filters: \n"  <> renderPredicateWhere predicate
      --putStrLn $ "Fields: \n"  <> show tbf
      putStrLn $ "Errors: \n" <>  (unlines $ show . fmap (fmap renderRel) <$> lefts result)
      --putStrLn $ "PreResult: \n" <>  show preresult
      --putStrLn $ "Result: \n" <>  show res 
    liftIO $ putStrLn $ "Size "  <> show (tableName table) <> " " <> show (L.length (rights result))
    return (rights  result,x,o - L.length (lefts result )))


-- TODO: Could we derive completeness information from bounds
-- or have some negative information about explored empty bounds
pageTable method table page fixed tbf = debugTime ("pageTable: " <> T.unpack (tableName table)) $ do
    inf <- askInf
    let
      m = tableMeta table
      sortList = fmap (,Desc) $  rawPK table
      pagesize = (opsPageSize $ schemaOps inf)
    ((IndexMetadata fixedmap,TableRep (_,sidx,reso)),dbvar)
      <- createTable fixed (tableMeta table)
    let
      pageidx =  (fromMaybe 0 page +1) * pagesize
      hasIndex = M.lookup fixed fixedmap
      readNew sq tbf  =  do
         let pagetoken = flip M.lookupLE  mp . (*pagesize)  =<< page
             (indexSize ,mp) = fromMaybe (maxBound,M.empty) hasIndex
             pageStart = liftA2 (-) (fmap (*pagesize) page) (fst <$> pagetoken)
             token = fmap (snd.snd) pagetoken
         (resOut,token ,s ) <- method table  pageStart (fmap (snd.snd) pagetoken) (Just pagesize) sortList fixed tbf reso
         let
             -- # postFilter fetched results
             resK = if predNull fixed then resOut else resOut -- G.filterRows fixed resOut
             -- # removeAlready fetched results
             diffNew i
                -- FIXME: When we have a partially loaded filter this code
                -- can generate wrong createRow', we should diff against the
                --  main index instead of a filtered view
                = case G.lookup (G.getIndex m i) reso of
                   Just v -> case recComplement inf m tbf fixed v of
                      Just _ ->  patchRowM' m v i
                      Nothing -> Nothing
                   Nothing -> Just $ createRow' m  i
             newRes = catMaybes $ fmap diffNew resK
         -- Only trigger the channel with new entries
         fetchPatches (tableMeta table) [(fixed, estLength page pagesize s, pageidx, tbf,token)]  newRes
         let nidx = maybe (estLength page pagesize s,M.singleton pageidx (tbf,token) ) (\(s0,v) -> (estLength page pagesize  s, M.insert pageidx (tbf,token) v)) hasIndex
             ini = (TableRep (m,sidx,reso))
         if L.null newRes
            then do
              liftIO . putStrLn $ "No new fields " <> show (tableName table)  <> show (L.length resK, G.size reso) -- <> show (G.getIndex m <$> resK )
              return (nidx,(sidx,reso))
            else do
              let final = either error ((\(TableRep (_,i,j)) -> (i,j)).fst) $ foldUndo ini  newRes
              liftIO . putStrLn $ "New fields " <> show (tableName table) <> " --------  " <> show (L.length resK, L.length newRes , G.size reso, G.size (snd final)) 
              -- liftIO .putStrLn $ ident $ render (tableNonRef tbf)
              return (nidx,final)

    (nidx,(sidx2,ndata)) <- case hasIndex of
      Just (sq,idx) ->
        if (sq > G.size reso)
        then case  M.lookup pageidx idx of
          Just v -> case recComplement inf (tableMeta table)  tbf fixed (fst v) of
            Just i -> do
              liftIO . putStrLn $ "Load complement from existing page " <> show pageidx
                 -- <> "\n"<> ident (render  i )
                 -- TODO: Investigate if we can optimize Read only complement
              readNew sq tbf -- i 
            Nothing -> do
              -- Check if interval is inside the current interval in case is not complete
              if (sq  ==  G.size reso || G.size reso >= pageidx )
                then do
                  liftIO . putStrLn $ "Empty complement: " <> show (tableName table,G.size reso, pageidx,sq) 
                  return ((sq,idx), (sidx,reso))
                else do
                  -- BUG: DEBUG why this is happening
                  liftIO . putStrLn $ "WARNING: Load missing filter: " <> show (tableName table,sq, G.size reso,pageidx) -- <> (ident . render $ tbf)
                  readNew sq tbf 
          Nothing -> do
            liftIO . putStrLn $ "New page requested: " <> show pageidx
            readNew sq tbf
        else  do
          let
            pagetoken = M.lookupLE pageidx idx
            existingProjection = fmap (fst .snd) pagetoken
            projection = recComplement inf m tbf fixed =<< existingProjection
          when (sq < G.size reso) $ do
            fetchPatches (tableMeta table) [(fixed, G.size reso, pageidx, tbf,TableRef $ G.getBounds (tableMeta table) (G.toList reso))] []
          case projection of
            Just remain -> do
              liftIO . putStrLn $ "Current table is partially complete: " <> show (tableName table, sq,G.size reso)
              -- liftIO . putStrLn $ "Remain " ++ (ident $ render remain)
              -- liftIO . putStrLn $ "Existing " ++ (maybe "" (ident . render) existingProjection )
              -- TODO : Investigate if we can optimize just loading complements
              readNew  sq tbf
            Nothing -> do
              case pagetoken of 
                Nothing ->  
                  if F.any (isJust . recComplement inf (tableMeta table) tbf fixed ) reso
                    then do
                      liftIO . putStrLn $ "New pagetoken missing complement" <> show (tableName table, sq, G.size reso, pageidx)
                      readNew sq tbf
                    else  do
                      liftIO . putStrLn $ "New pagetoken but current table is complete  : " <> show (tableName table, sq, G.size reso, pageidx)
                      return ((max (G.size reso) sq,idx), (sidx,reso))
                Just (_,(proj,_)) -> do
                  case (recComplement inf (tableMeta table) tbf fixed proj ) of
                    Just comp -> do
                      liftIO $ putStrLn $ "Existing token with remaining complement " <> show (tableName table, sq,G.size reso)
                      -- ++  maybe ""  (ident . render ) (recComplement inf (tableMeta table) tbf fixed proj )
                      -- TODO : Investigate if we can optimize just loading complements
                      readNew sq tbf 
                    Nothing -> do 
                      liftIO . putStrLn $ "Existing token current table is complete: " <> show (tableName table, sq,G.size reso)
                      -- liftIO $ putStrLn $ "Old proj \n" ++ ( ident $ render  proj)
                      -- liftIO $ putStrLn $ "New proj \n" ++ ( ident $ render  tbf)
                      return ((max (G.size reso) sq,idx), (sidx,reso))
      Nothing -> do
        liftIO $ putStrLn $ "No index: "  <> T.unpack (tableName table)
        let m = rawPK table
            isComplete (WherePredicate i) = match i
              where
                match (AndColl l) = product $ match <$> l
                match (OrColl l) =  sum $ match <$> l
                match (PrimColl (i,_)) = if L.elem i m then 1 else 0
            complements = catMaybes $ (recComplement inf (tableMeta table) tbf fixed ) <$> G.toList reso
            -- TODO: there are some wrong matchings in the reso filter
            size = L.length $ G.filterRows fixed  (G.toList reso)
        if fixed /= mempty && isComplete fixed == size && size /= 0
           then
            case L.null complements of
              True -> do
                liftIO $ putStrLn $ "Reusing existing complete predicate : " <> show (tableName table) <> " - " <>  renderPredicateWhere fixed
                --readNew maxBound tbf
                return ((G.size reso ,M.empty), (sidx,reso))
              False -> do
                liftIO $ putStrLn $ "Loading not null complement : " <> show (tableName table, G.size reso)
                readNew maxBound tbf -- (foldr1 kvMerge complements)
           else do
             liftIO $ putStrLn $ "Loading predicate: "  
                  <> renderPredicateWhere fixed 
                  <> (if isComplete fixed  == size && (size /= 0) then " is Complete " else "" )
             readNew maxBound tbf
    return (dbvar,(IndexMetadata (M.insert fixed nidx fixedmap),TableRep (tableMeta table,sidx2, ndata)))



tableCheck
  :: (Show t, Show a) =>
     KVMetadata (FKey (KType t))
     -> KV (FKey (KType t)) a
     -> Either [Char] (KV (FKey (KType t)) a)
tableCheck m t = if checkAllFilled then Right t else Left ("tableCheck: non nullable rows not filled " ++ show ( need `S.difference` available ,_kvname m,t))
  where
    checkAllFilled =  need `S.isSubsetOf`  available
    available = S.unions $ relOutputSet . keyattr <$> unkvlist t
    need = S.fromList $ L.filter (\i -> not (isKOptional (keyType i) || isSerial (keyType i) || isJust (keyStatic i )) )  (_kvattrs m)


convertChanEventIndex inf table nchan = do
    (e,h) <- newEvent
    dynFork $ forever $ catchJust notException ( do
      h =<<  atomically (takeMany nchan)
      ) (\e -> atomically (takeMany nchan) >>= (\d ->  putStrLn $ show ("error convertChanStep"  ,e :: SomeException,d)<>"\n"))
    return e

listenLogTable :: InformationSchema -> Table -> Dynamic (Tidings [String]) 
listenLogTable inf t  = do 
  ref <- liftIO $ prerefTable inf t  
  convertEventChan (dblogger ref)

convertEventChan 
  :: TEvent s 
  -> Dynamic (Tidings [s])
convertEventChan (v,c) = do
    (e,h) <- newEvent
    (cc,ini) <- liftIO $ atomically $ do
      (,) <$> cloneTChan c <*> readTVar v
    dynFork . forever $  do
      h =<<  atomically (takeMany cc)
    accumT ini ((++)<$> e)


convertChanStepper0
  :: Show v =>
    InformationSchema
    -> TableK Key
    -> IndexMetadata Key v
    -> TChan (IndexMetadataPatch Key v)
    -> Dynamic
        (Tidings (IndexMetadata Key v ))
convertChanStepper0  inf table ini nchan = do
    e <- convertChanEventIndex inf table nchan
    accumT ini (flip apply <$> e)

convertChan
  :: InformationSchema
  -> TableK Key
     -> (TBPredicate Key Showable, [Rel Key])
     -> KVMeta Key 
     -> DBRef Key Showable
     -> Dynamic
      (Tidings (IndexMetadata Key Showable ),Tidings (TableRep Key Showable))
convertChan inf table fixed tbf dbvar = do
  ((ini,result),cloneddbvar) <- liftIO $ atomically $
    cloneDBVar  fixed dbvar
  (,) <$> convertChanStepper0 inf table ini (idxChan cloneddbvar)
      <*> convertChanTidings0 inf table fixed tbf result (patchVar cloneddbvar)

restrictAttr :: TBMeta Key -> TB Key Showable -> Maybe (TB Key Showable)
restrictAttr (Attr _ _ ) i@(Attr _ _) =  Just i  
restrictAttr (Fun _ _ _ ) i@(Fun _ _ _ ) =  Just i  
restrictAttr (IT l n ) (IT i k) = fmap (IT i ) $ traverse (restrictRow t) k 
  where t = head (F.toList n)
restrictAttr (FKT l m n ) (FKT i j k) = fmap (FKT i j ) $ traverse (restrictRow t) k 
  where t = head (F.toList n)

restrictPAttr :: TBMeta Key -> PathAttr Key Showable -> Maybe (PathAttr Key Showable)
restrictPAttr (Attr _ _ ) a@(PAttr _ _) =  Just a 
restrictPAttr (Fun _ _ _ ) a@(PFun _ _ _ ) =  Just a 
restrictPAttr (IT l n ) (PInline i k) = fmap (PInline i ) $ traverse (restrictPatch t) k 
  where t = head (F.toList n)
restrictPAttr (FKT l m n ) (PFK i j k) = fmap (PFK i j ) $ traverse (restrictPatch t) k 
  where t = head (F.toList n)

restrictPatch :: KVMeta Key -> TBIdx Key Showable -> Maybe (TBIdx Key Showable)
restrictPatch v = fmap kvlistp . nonEmpty . mapMaybe (\i -> flip restrictPAttr i =<<  kvLookup (index i) v ) . unkvlistp


-- NOTE : When we have a foreign key and only want the field we need to restrict the fields by using tableNonRef
restrictRow :: KVMeta Key -> KV Key Showable -> Maybe (KV Key Showable)
restrictRow v n = kvNonEmpty (directMatch <> nonRefMatch )  -- (\i -> F.foldl' (<|> ) (restrictField i) (restrictField <$> nonRefTB i) )
    where restrictField i = flip restrictAttr i =<< kvLookup (index i) v
          directMatch = mapKVMaybe restrictField  n 
          nonRefMatch = mapKVMaybe restrictField (tableNonRef $ kvFilterWith (\k _ -> isNothing (kvLookup k directMatch) ) $ n )

restrictOp :: KVMeta Key -> RowOperation Key Showable -> Maybe (RowOperation Key Showable)
restrictOp tbf v = case v of
    CreateRow j -> CreateRow <$> restrictRow tbf j
    PatchRow j -> PatchRow <$> restrictPatch tbf j
    i-> Just i  

restrict :: KVMeta Key -> RowPatch Key Showable -> Maybe (RowPatch Key Showable)
restrict tbf (RowPatch (i,v)) = RowPatch . (i,) <$> restrictOp tbf v  
restrict tbf (BatchPatch i v) =  BatchPatch  i <$> (restrictOp tbf v)
    

traceNothing f Nothing = traceShow ("Filtered:  ",f) Nothing 
traceNothing f i = traceShow ("Passed:   ",f) i 

convertChanEvent
  ::
    InformationSchema -> TableK Key
     -> (TBPredicate Key Showable, [Rel Key])
     -> KVMeta Key
     -> Behavior (TableRep Key Showable)
     -> TChan [TableModificationU Key Showable]
     -> Dynamic
          (Event [RowPatch Key Showable])
convertChanEvent inf table fixed select bres chan = do
  (e,h) <- newEvent
  dynFork . forever $ catchJust notException (do
    ml <- atomically $ takeMany chan
    TableRep (_,_,v) <- currentValue bres
    let
      
      meta = tableMeta table
      check r j  = if G.checkPred i (fst fixed) 
                  then do
                    case recComplement inf meta select (pkPred meta i) i  of
                      Just c ->  do 
                        -- when ( tableName table == "table_description" )$  do
                          -- liftIO $ putStrLn $ "match raw:\n" ++ show c
                        -- reload <-  Just . maybeToList . snd <$> getFrom  table c i
                        --liftIO $ putStrLn $ "!!! WARNING !!!! match pretty "
                        --      ++ show (tableName table)
                        --      ++ show (L.length (concat ml ))
                        --      ++ renderPredicateWhere (fst fixed)
                        --      ++ "\n" ++ ident (render (tableNonRef c) )
                        --      ++ "\nCurrent\n" ++ ident (render i)
                        --      ++ "\nOld\n" ++ ident (render r)
                        --      ++ "\nDelta\n" ++ ident (render j)
                        --      ++ "\nLoad\n" ++ maybe "" (concatMap (ident .render))  reload
                          -- TODO: Fetch missing columns from patch
                        return $ Nothing -- Just [] -- reload
                      Nothing -> return $ Just mempty 
                  else  return Nothing
            where 
                i = apply r j 
      deltas  =  tableDiff <$> compact (concat  ml)
      match :: RowPatch Key Showable -> TransactionM (Maybe [RowPatch Key Showable])
      match r@(RowPatch (i,PatchRow j)) 
            = case G.lookup i v  of
              Just r ->  do
                 delta <- check r j 
                 return $ pure. (\ d -> RowPatch (i,PatchRow (head $ compact (j :d)  )))  <$> delta
              Nothing -> return Nothing 
      match (RowPatch (i,CreateRow j)) = do
                  if G.checkPred j  (fst fixed) 
                  then return $ Just [RowPatch (i,CreateRow j ) ]
                  else return Nothing
      match (BatchPatch i j) = nonEmpty . concat . catMaybes <$>  mapM (\ix -> match (RowPatch (ix,j)) ) i 
      match i = return $ Just  [i]
      --  TODO : Recover this code for cases where the Patch removes a item from the predicate
      -- filterPredNot j = nonEmpty . catMaybes . map (\d -> if L.any (\i -> isJust (G.lookup i j) ) (index d) && not (match d) then Just (rebuild (index d) DropRow )  else Nothing )
    (newRows,_) <- runDynamic .transactionNoLog inf $ concat .catMaybes <$> mapM match deltas 
      -- oldRows = filterPredNot v deltas 
    let
      patches = join $ nonEmpty . catMaybes . fmap (restrict select) <$> ({-oldRows <> -} nonEmpty newRows)
    --when (tableName table == "clients") . void $do
    --  (\v -> do
    --    putStrLn $ "Logging new patches: " ++ renderPredicateWhere (fst fixed)
    --    mapM_ (putStrLn . ident . render ) v) deltas
    --  maybe
    --    (putStrLn $ "WARNING: All patches filtered :" ++ renderPredicateWhere (fst fixed))

    --    (\v -> do
    --      putStrLn $ "Logging new filtered patches: " ++ renderPredicateWhere (fst fixed)
    --      mapM_ (putStrLn . ident . render ) v) patches

    traverse h patches
    
    return ()) (\e -> atomically (takeMany chan) >>= (\d -> putStrLn $  show ("error convertChanEvent"  ,e :: SomeException,d)<>"\n"))
  return e

patchType (PatchRow _ ) = "PatchRow"
patchType (CreateRow _ ) = "CreateRow"
patchType (DropRow  ) = "DropRowRow"

mapTableRep f (TableRep (m,i,j))= TableRep (f <$> m, mapSecondary f i, mapPrimary f j)
mapSecondary f = M.mapKeys (fmap (fmap f)) . fmap (fmap (fmap (fmap (G.mapAttributePath f))))
mapPrimary  f = fmap (mapKey' f)


convertChanTidings0
  :: InformationSchema
  -> TableK Key
  -> (TBPredicate Key Showable, [Rel Key])
  -> (KVMeta Key)
  -> TableRep Key Showable
  -> TChan [TableModificationU Key Showable]
  -> Dynamic (Tidings (TableRep Key Showable))
convertChanTidings0 inf table fixed select ini nchan = mdo
    evdiff <-  convertChanEvent inf table  fixed select (snd <$> facts t) nchan
    ti <- liftIO getCurrentTime
    let projection (TableRep (a,b,i)) =  TableRep (a,b , restrict <$>   i)
        restrict i = justError ("empty restriction projection: \n"  ++ ident (render select) ++ "\n" ++ ident (render i) ). restrictRow select  $ i
    t <- accumT (0,projection ini) ((\i (ix,j) -> (ix+1,either error fst $ foldUndo j i )) <$> evdiff)
    return  (snd <$> t)

tryTakeMany :: TChan a -> STM [a]
tryTakeMany mvar = maybe (return[]) (go . (:[])) =<< tryReadTChan mvar
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


tableLoaderAll table  page fixed tbf = do
  inf <- askInf
  tableLoader'  table page fixed (fromMaybe (allFields inf table ) tbf)

loadFKS targetTable table = do
  inf <- askInf
  let
    fkSet:: S.Set Key
    fkSet =   S.unions . fmap (S.fromList . fmap _relOrigin . (\i -> if all isInlineRel i then i else filterReflexive i ) . S.toList . pathRelRel ) $ filter isReflexive  $  (rawFKS targetTable)
    items = table
  fks <- catMaybes <$> mapM (loadFK ( table )) (rawFKS targetTable)
  let
    nonFKAttrs :: [Column Key Showable]
    nonFKAttrs = filter ((\ i -> not $ S.isSubsetOf (relOutputSet i) fkSet).keyattr) (unkvlist items)
  return  $ kvlist (nonFKAttrs <> fks )

loadFK :: TBData Key Showable -> SqlOperation -> TransactionM (Maybe (Column Key Showable))
loadFK table (FKJoinTable rel (st,tt) )  = do
  inf <- askInf
  let targetTable = lookTable inf tt
  (i,(_,TableRep (_,_,mtable ))) <- tableLoaderAll targetTable Nothing mempty Nothing
  let
    relSet = S.fromList $ _relOrigin <$> rel
    tb  = F.toList (M.filterWithKey (\k l ->  not . S.null $ relOutputSet k `S.intersection` relSet)  (unKV . tableNonRef $ table))
    fkref = joinRel2  (tableMeta targetTable) (fmap (replaceRel rel) tb ) mtable
  return $ FKT (kvlist  tb) rel   <$> fkref
loadFK table (FKInlineTable ori to )   = do
  inf <- askInf
  runMaybeT $ do
    let targetTable = lookSTable inf to
    IT rel vt  <- MaybeT . return $ M.lookup (Inline   ori) (unKV $ table)
    loadVt <- lift $ Tra.traverse (loadFKS targetTable) vt
    return $ IT rel loadVt

loadFK  _ _ = return Nothing

refTablesProj inf table page pred proj = do
  ref  <-  transactionNoLog inf $ tableLoader table page pred proj
  return (idxTid ref,collectionTid ref,patchVar $ iniRef ref)

refTablesDesc inf table page pred = do
  ref  <-  transactionNoLog inf $ tableLoader table page pred (recPKDesc inf (tableMeta table) $ allFields inf table)
  return (idxTid ref,collectionTid ref,patchVar $ iniRef ref)

refTables' inf table page pred = do
  ref  <-  transactionNoLog inf $ tableLoader table page pred (allFields inf  table)
  return (idxTid ref,collectionTid ref,patchVar $ iniRef ref)

refTables inf table = refTables' inf table Nothing mempty

projectRec :: T.Text
 -> Maybe Int
 -> [(Rel T.Text , AccessOp Showable )]
 -> TransactionM
      DBVar
projectRec t a p = do
  inf  <- askInf
  selectFrom t a (tablePredicate inf t p)


tableDiffs (BatchedAsyncTableModification _ i) = concat $ tableDiffs <$> i
tableDiffs i = [tableDiff i]

printException :: Show a => SomeException -> a -> IO ()
printException e d = do
  putStrLn $ "Failed applying patch: " <> show d
  putStrLn   "================================="
  putStrLn $ show (e :: SomeException)

fromTableS origin whr = mdo
  inf <- askInf
  let table = lookTable inf origin
  (inipred ,iniproj) <- currentValue (psvalue whr)
  liftIO . putStrLn $ "Load fromTableS:  " <> show origin
  (ref,(_,rep)) <- tableLoaderAll table Nothing  (liftPredicateF lookupKeyName inf origin inipred) (Just iniproj)
  (e,h) <- lift newEvent 
  (_,ini) <- liftIO . runDynamic $ do 
    ev <- convertChanEvent inf table (liftPredicateF lookupKeyName inf origin inipred, rawPK table) iniproj (psvalue t)  (patchVar ref)
    onEventIO ev (mapM h.compact)
  t0 <- liftIO getCurrentTime
  let filtered = filterJust $ (\i j -> let r = apply i j in if (fst i ==  fst r) then Nothing else traceShow (fst i,fst r) $ Just  r)   <$> psvalue whr <@> psevent whr
  lift $ onEventDynIni ini  filtered (\(pred ,proj) -> do
    liftIO . putStrLn $ "Listen fromTableS:  " <> show origin <> "\n" <> show (t0, L.length (renderPredicateWhere pred))
    ev <- convertChanEvent inf table (liftPredicateF lookupKeyName inf origin pred, rawPK table) proj  (psvalue t)  (patchVar ref)
    onEventIO ev (mapM h.compact))
  t <- lift $ accumS rep e
  return (t,ref)

instance (Eq v,Show v) => Patch (WherePredicateK v) where
  type Index (WherePredicateK v) = WherePredicateK v
  applyUndo (WherePredicate (AndColl i)) (WherePredicate (AndColl j)) = Right $ (WherePredicate (AndColl (L.nub $ i <> j)),WherePredicate (AndColl i))
  applyUndo (WherePredicate (OrColl i)) (WherePredicate (OrColl j)) = Right $ (WherePredicate (OrColl (L.nub $ i <> j)), WherePredicate (OrColl (i )))
  applyUndo (WherePredicate (OrColl i)) (WherePredicate j )= Right $ (WherePredicate (OrColl (L.nub $  i <> [j] )), WherePredicate (OrColl (i )))
  applyUndo (WherePredicate (AndColl i)) (WherePredicate j) = Right $ (WherePredicate (AndColl (L.nub $ i <> [j] )), WherePredicate (AndColl (i )))
  applyUndo i j = Right ( i <> j  , i )
  applyUndo i j = error (show (i,j))
  diff i j = Nothing
  patch i = i


fromTable origin whr proj = mdo
  inf <- askInf
  let table = lookTable inf origin
      pred = liftPredicateF lookupKeyName inf origin whr
  -- liftIO $ putStrLn (show (whr,pred))
  (ref,(n,rep)) <- tableLoaderAll table Nothing  pred (Just proj) 
  ev <- lift $ convertChanEvent inf table (pred,rawPK table) (allFields inf table) (psvalue t) (patchVar ref)
  t <- lift $ accumS rep  (head <$> ev)
  return (t,ref)

select table  = do
  inf <-askInf
  (_,(_,TableRep (_,_,evMap ))) <- tableLoaderAll (lookTable inf table) Nothing mempty Nothing
  return (decodeT . mapKey' keyValue <$> evMap)


--- Plugins Interface Methods
createFresh :: T.Text -> InformationSchema -> T.Text -> KType CorePrim -> IO InformationSchema
createFresh  tname inf i ty@(Primitive l  atom)  =
  case atom of
    AtomicPrim _  -> do
      let k = newKey tableO i ty
      return $ inf
          Le.& keyMapL Le.%~ (HM.insert (tname,i) k )
    RecordPrim (s,t) -> do
      let k = newKey tableO i ty
          path =  FKInlineTable k $ inlineName ty
          alterTable (Project r i) = r
                    Le.& rawAttrsR Le.%~  (k:)
                    Le.& _inlineFKS Le.%~  (path:)
          alterTable r  = r
                    Le.& rawAttrsR Le.%~  (k:)
                    Le.& _inlineFKS Le.%~  (path:)
      let newinf =  inf
            Le.& tableMapL . Le.ix tname Le.%~ alterTable
            Le.& keyMapL Le.%~ HM.insert (tname,i) k
      return newinf
  where tableO = lookTable inf tname
