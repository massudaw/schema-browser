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
import Data.Ord
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
import qualified Data.Text as T

--
--  MultiTransaction Postgresql insertOperation
--

deleteMod :: InformationSchema ->  TBData Key Showable -> Table -> IO (Maybe (TableModification (TBIdx Key Showable)))
deleteMod inf j@(meta,_) table = do
  let patch =  (tableMeta table, getPKM j,[])
  deletePatch (conn inf)  patch table
  Just <$> logTableModification inf (TableModification Nothing table patch)

selectAll
  ::
     InformationSchema
     -> TableK Key
     -> Maybe PageToken
     -> Maybe Int
     -> [(Key, Order)]
     -> [(T.Text, Column Key Showable)]
     -> TransactionM  (Int,
           [(KVMetadata Key,
             Compose
               Identity (KV (Compose Identity (TB Identity))) Key Showable)])
selectAll inf table i  j k st = do
      let
          unref (TableRef i) = i
          tbf =  tableView (tableMap inf) table
      liftIO $ print (tableName table,selectQuery tbf )
      let m = unTB1 tbf
      (t,v) <- liftIO$ duration  $ paginate (conn inf) m k 0 (maybe 20 id j) (fmap unref i) (nonEmpty st)
      mapM_ (tellRefs inf  ) (snd v)
      liftIO$ print (tableName table,t)
      return v

tellRefs  ::  InformationSchema ->TBData Key Showable ->  TransactionM ()
tellRefs  inf (m,k) = mapM_ (tellRefsAttr . unTB ) $ F.toList  (_kvvalues $ unTB k)
  where tellRefsAttr (FKT l k t) = void $ do
            tell ((\m@(k,v) -> TableModification Nothing (lookTable inf (_kvname k)) . patchTB1 $ m) <$> F.toList t)
            mapM_ (tellRefs inf) $ F.toList t
        tellRefsAttr (Attr _ _ ) = return ()
        tellRefsAttr (IT _ t ) = void $ mapM (tellRefs inf) $ F.toList t


estLength page size resL est = fromMaybe 0 page * fromMaybe 20 size  +  est

eventTable :: InformationSchema -> Table -> Maybe Int -> Maybe Int -> [(Key,Order)] -> [(T.Text, Column Key Showable)]
    -> TransactionM (DBVar,Collection Key Showable)
eventTable inf table page size presort fixed = do
    let mvar = mvarMap inf
        defSort = fmap (,Desc) $ S.toList $ rawPK table
        sortList  = if L.null presort then defSort else presort
        fixidx = (L.sort $ snd <$> fixed )
        filterfixed = filter (\(m,k)->F.all id $ M.intersectionWith (\i j -> L.sort (nonRefTB (unTB i)) == L.sort ( nonRefTB (unTB j)) ) (mapFromTBList (fmap (_tb .snd) fixed)) $ unKV k)
    -- print "Take MVar"
    mmap <- liftIO$ takeMVar mvar
    -- print "Look MVar"
    (mtable,td,ini) <- case (M.lookup (tableMeta table) mmap ) of
         Just (i,td) -> do
           liftIO $ putMVar mvar mmap
           -- print "Put MVar"
           (fixedmap ,reso) <- liftIO$ currentValue (facts td)
           let (sq,mp)  = justError "" $ M.lookup fixidx  fixedmap

           ini <- if (isJust (M.lookup fixidx  fixedmap )&& maybe False (\p->not $ M.member (p+1) mp) page  && sq >  L.length (filterfixed reso ) && isJust (join $ flip M.lookup mp <$> page ))
             then  do
               (res,nextToken ,s ) <- (listEd $ schemaOps inf ) inf table (join $ flip M.lookup mp <$> page ) size sortList fixed
               let ini = (M.insert fixidx (estLength page size res s  ,maybe mp (\v -> M.insert (fromMaybe 0 page +1 ) v  mp)  nextToken) fixedmap ,reso <> (unTB1 <$> res))
               liftIO$ putMVar i ini
               return $ Just ini
             else return Nothing
           ini2 <- if (isNothing (M.lookup fixidx  fixedmap ))
             then do
               (res,p,s) <- (listEd $ schemaOps inf ) inf table Nothing size sortList fixed
               let ini = (M.insert fixidx (estLength page size res s ,maybe M.empty (M.singleton (1 :: Int)) p) fixedmap ,L.nub  $ fmap unTB1 res <> reso)
               liftIO $ putMVar i ini
               return $ Just ini
             else return Nothing
             -- liftIO $ print (fst ini)
           return (i,td,ini <> ini2)
         Nothing -> do
           (res,p,s) <- (listEd $ schemaOps inf ) inf table Nothing size sortList fixed
           -- liftIO $ print "New MVar"
           let ini = (M.singleton fixidx (estLength page size res s ,maybe M.empty (M.singleton (1 :: Int)) p) ,fmap unTB1 res)
           mnew <- liftIO$ newMVar ini
           (e,h) <- liftIO $R.newEvent
           bh <- liftIO$ R.stepper ini  e
           let td = (R.tidings bh e)
           liftIO$ putMVar mvar (M.insert (tableMeta table) (mnew,td) mmap)
           liftIO$ forkIO $ forever $ do
              (h =<< takeMVar mnew ) -- >> print "Take MVar"
           -- Dont
           -- print "Put MVar"
           return (mnew,td,Just ini)
    iniT <- fromMaybe (liftIO $ currentValue (facts td)) (return <$> ini)
    return ((mtable, fmap filterfixed <$> td),fmap filterfixed iniT)



postgresOps = SchemaEditor fullDiffEdit fullDiffInsert deleteMod (\i j p g s o-> (\(l,i) -> (fmap TB1 i,Just $ TableRef  (filter (flip L.elem (fmap fst s) . fst ) $  getPK $ TB1 $ last i) ,l)) <$> selectAll i j p g s o ) (\_ _ _ _ _ -> return ([],Nothing,0)) (\inf table -> liftIO . loadDelayed inf (unTB1 $ unTlabel $ tableView (tableMap inf) table ))

fullInsert inf = Tra.traverse (fullInsert' inf )

fullInsert' :: InformationSchema -> TBData Key Showable -> TransactionM  (TBData Key Showable)
fullInsert' inf ((k1,v1) )  = do
   let proj = _kvvalues . unTB
   ret <-  (k1,) . Compose . Identity . KV <$>  Tra.traverse (\j -> Compose <$>  tbInsertEdit inf   (unTB j) )  (proj v1)
   ((m,t),_) <- eventTable inf (lookTable inf (_kvname k1)) Nothing Nothing [] []
   (_,l) <- currentValue (facts t)
   if  isJust $ L.find ((==tbPK (tableNonRef (TB1  ret))). tbPK . tableNonRef . TB1  ) l
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
transaction inf log = {-withTransaction (conn inf) $-} do
  -- print "Transaction Run Log"
  (md,mods)  <- runWriterT log
  -- print "Transaction Update"
  let aggr = foldr (\(TableModification id t f) m -> M.insertWith mappend t [f] m) M.empty mods
  Tra.traverse (\(k,v) -> do
    -- print "GetTable"
    ((m,t),_) <- transaction inf $  eventTable inf k Nothing Nothing [] []
    -- print "ReadValue"
    (mp,l) <- currentValue (facts t)
    let lf = foldl' (\i p -> applyTable  i (PAtom p)) (fmap TB1 l) v
    -- print "PutValue"
    putMVar m (mp,fmap unTB1 lf)
    ) (M.toList aggr)
  --print "Transaction Finish"
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


