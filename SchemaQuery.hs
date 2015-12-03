{-# LANGUAGE OverloadedStrings,TupleSections #-}
module SchemaQuery
  (eventTable
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

estLength page size resL est = fromMaybe 0 page * fromMaybe 200 size  +  est

eventTable :: InformationSchema -> Table -> Maybe Int -> Maybe Int -> [(Key,Order)] -> [(T.Text, Column Key Showable)]
    -> TransactionM (DBVar,Collection Key Showable)
eventTable inf table page size presort fixed = do
    let mvar = mvarMap inf
        defSort = fmap (,Desc) $  rawPK table
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




fullInsert inf = Tra.traverse (fullInsert' inf )

fullInsert' :: InformationSchema -> TBData Key Showable -> TransactionM  (TBData Key Showable)
fullInsert' inf ((k1,v1) )  = do
   let proj = _kvvalues . unTB
   ret <-  (k1,) . Compose . Identity . KV <$>  Tra.traverse (\j -> Compose <$>  tbInsertEdit inf   (unTB j) )  (proj v1)
   ((m,t),(_,l)) <- eventTable inf (lookTable inf (_kvname k1)) Nothing Nothing [] []
   if  isJust $ L.find ((==tbPK (tableNonRef (TB1  ret))). tbPK . tableNonRef . TB1  ) l
      then do
        return ret
      else do
        i@(Just (TableModification _ _ tb))  <- (insertEd $ schemaOps inf) inf ret
        tell (maybeToList i)
        return $ createTB1 tb


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
    ((m,t),(mp,l)) <- transaction inf $  eventTable inf k Nothing Nothing [] []
    -- print "ReadValue"
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
           Identity . (\tb -> FKT ( backFKRef relTable  (keyAttr .unTB <$> pk) tb) rel2 tb ) <$> fullInsert inf t
        LeftTB1 i ->
           maybe (return (Identity f) ) (fmap (fmap attrOptional) . tbInsertEdit inf) (unLeftItens f)
        ArrayTB1 l ->
           fmap (fmap (attrArray f)) $ fmap Tra.sequenceA $ Tra.traverse (\ix ->   tbInsertEdit inf $ justError ("cant find " <> show (ix,f)) $ unIndex ix f  )  [0.. length l - 1 ]


