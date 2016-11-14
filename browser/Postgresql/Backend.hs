{-# LANGUAGE FlexibleContexts,TypeFamilies ,NoMonomorphismRestriction,OverloadedStrings ,TupleSections #-}
module Postgresql.Backend (connRoot,postgresOps) where

import Types
import qualified Types.Index as G
import Step.Common
import Step.Host
import Data.Functor.Apply
import System.Environment
import Safe
import Control.Monad
import Postgresql.Printer
import Postgresql.Parser
import Utils
import Control.Monad.Reader
import GHC.Stack
import Schema
import RuntimeTypes
import Data.Bifunctor
import Query
import Control.Monad.Writer hiding (pass)
import System.Time.Extra
import Types.Patch
import Debug.Trace
import Data.Ord
import Data.Functor.Identity
import qualified  Data.Map as M

import Data.Tuple
import Data.String

import Control.Applicative
import Data.Maybe
import qualified Data.List as L

import Prelude hiding (takeWhile,head)

import qualified Data.Foldable as F
import qualified Data.Text as T
import Data.Text (Text)
import qualified Data.Set as S
import qualified Database.PostgreSQL.Simple.FromRow as FR
import Database.PostgreSQL.Simple

insertPatch
  :: (MonadIO m ,Functor m )
     => (TBData PGKey () -> FR.RowParser (TBData PGKey Showable ))
     -> Connection
     -> TBIdx PGKey Showable
     -> TableK PGKey
     -> m (TBIdx PGKey Showable )
insertPatch f conn path@(m ,s,i ) t =  liftIO$ if not $ L.null serialAttr
      then do
        let
          iquery :: String
          iquery = T.unpack $ prequery <> " RETURNING ROW(" <>  T.intercalate "," (projKey serialAttr) <> ")"
        out <-  fmap safeHead $ liftIO $ queryWith (f (mapValue' (const ()) serialTB )) conn (fromString  iquery ) directAttr
        let Just (_,_ ,gen) =  join $ diff serialTB <$> out
            comp = compact (i <> gen)
        return (m, G.getIndex (justError "no out insert" out) ,comp )
      else do
        let
          iquery = T.unpack prequery
        print iquery
        execute  conn (fromString  iquery ) directAttr
        return path
    where
      prequery =  "INSERT INTO " <> rawFullName t <>" ( " <> T.intercalate "," (escapeReserved <$> projKey directAttr ) <> ") VALUES (" <> T.intercalate "," (fmap (const "?") $ projKey directAttr)  <> ")"
      attrs =  concat $ nonRefTB . create <$> i
      testSerial (k,v ) = (isSerial .keyType $ k) && (isNothing. unSSerial $ v)
      serial f =  filter (all1 testSerial  .f)
      direct f = filter (not.all1 testSerial .f)
      serialAttr = serial aattri attrs
      directAttr = direct aattri attrs
      projKey = fmap (keyValue ._relOrigin) . concat . fmap keyattri
      serialTB = tblist' t (fmap _tb  serialAttr)
      all1 f [] = False
      all1 f i = all f i



deletePatch
  ::
     Connection ->  TBIdx PGKey Showable -> Table -> IO (TBIdx PGKey Showable)
deletePatch conn patch@(m ,G.Idex kold ,_) t = do
    execute conn (fromString $ traceShowId $ T.unpack del) koldPk
    return patch
  where
    equality k = attrValueName k <> "="  <> "?"
    koldPk = uncurry Attr <$> M.toList kold
    pred   =" WHERE " <> T.intercalate " AND " (fmap  equality koldPk)
    del = "DELETE FROM " <> rawFullName t <>   pred

applyPatch
  ::
     Connection -> TBIdx PGKey Showable -> IO (TBIdx PGKey Showable)
applyPatch conn patch@(m,G.Idex kold,skv)  =
    execute conn (fromString $ traceShowId $ T.unpack up)  (fmap attrPatchValue skv <> koldPk ) >> return patch
  where
    equality k = k <> "="  <> "?"
    koldPk = uncurry Attr <$> M.toList kold
    attrPatchName (PAttr k p ) = escapeReserved (keyValue k) <> "=" <> nestP(keyValue k) p
      where nestP k (PInter True (b,j)) = "lowerI(" <> k <> "," <> "?" <>" ," <> (T.pack $show j)<> ")"
            nestP k (PInter False (b,j)) = "upperI(" <> k <> "," <> "?" <> "," <> (T.pack (show j )) <> ")"
            nestP k (PatchSet l) = F.foldl' nestP k  l
            nestP k i = "?"
    attrPatchValue (PAttr  k v) = Attr k (create v) :: TB Identity PGKey Showable
    pred   =" WHERE " <> T.intercalate " AND " (equality . escapeReserved . keyValue . fst <$> M.toList kold)
    setter = " SET " <> T.intercalate "," (   attrPatchName <$> skv   )
    up = "UPDATE " <> kvMetaFullName m <> setter <>  pred


updatePatch
  ::
     Connection -> TBData PGKey Showable -> TBData PGKey Showable -> Table -> IO (TBIdx PGKey Showable)
updatePatch conn kv old  t =
    execute conn (fromString $ traceShowId $ T.unpack up)  (skv <> koldPk ) >> return patch
  where
    patch  = justError ("cant diff states" <> (concat $ zipWith differ (show kv) (show old))) $ diff old kv
    kold = M.toList $ getPKM old
    equality k = k <> "="  <> "?"
    koldPk = uncurry Attr <$> kold
    pred   =" WHERE " <> T.intercalate " AND " (equality . escapeReserved . keyValue . fst <$> kold)
    setter = " SET " <> T.intercalate "," (equality .   escapeReserved . attrValueName <$> skv   )
    up = "UPDATE " <> rawFullName t <> setter <>  pred
    skv = unTB <$> F.toList  (_kvvalues $ unTB tbskv)
    tbskv = snd isM
    isM :: TBData PGKey  Showable
    isM =  justError ("cant diff befor update" <> show (kv,old)) $ diffUpdateAttr kv old

diffUpdateAttr :: (Ord k , Ord a) => TBData k a -> TBData k a -> Maybe (TBData k a )
diffUpdateAttr  kv kold@(t,_ )  =  fmap ((t,) . _tb . KV ) .  allMaybesMap  $ liftF2 (\i j -> if i == j then Nothing else Just i) (unKV . snd . tableNonRef'  $ kv ) (unKV . snd . tableNonRef' $ kold )

differ = (\i j  -> if i == j then [i]  else "(" <> [i] <> "|" <> [j] <> ")" )

paginate inf t order off size koldpre wherepred = do
    let (que,attr) = selectQuery t koldpre order wherepred
    i <- lookupEnv "POSTGRESQL_DECODER"
    let
      jsonDecode =  do
        let quec = fromString $ T.unpack $ "SELECT row_to_json(q),count(*) over () FROM (" <> que <> ") as q " <> offsetQ <> limitQ
        print quec
        logLoadTimeTable inf (lookTable inf $ _kvname (fst t)) wherepred "JSON" $
            uncurry (queryWith (withCount (fromRecordJSON t) ) (conn inf ) ) (quec, maybe [] (fmap (firstTB (recoverFields inf)))  attr)
      textDecode = do
        let quec = fromString $ T.unpack $ "SELECT *,count(*) over () FROM (" <> que <> ") as q " <> offsetQ <> limitQ
        print quec
        logLoadTimeTable inf (lookTable inf $ _kvname (fst t)) wherepred "TEXT" $
            uncurry (queryWith (withCount (fromRecord (unTlabel' t)) ) (conn inf ) ) (quec, maybe [] (fmap (firstTB (recoverFields inf)))  attr)

    v <- case i of
           Just "JSON" ->  jsonDecode
           Just "TEXT" ->    textDecode
           Nothing -> jsonDecode
    let estimateSize = maybe 0 (\c-> c - off ) $ safeHead ( fmap snd v :: [Int])
    print estimateSize
    return (estimateSize, fmap fst v)
  where

        offsetQ = " OFFSET " <> T.pack (show off)
        limitQ = " LIMIT " <> T.pack (show size)



-- High level db operations

insertMod :: TBData Key Showable -> TransactionM (Maybe (TableModification (TBIdx Key Showable)))
insertMod j  = do
  inf <- ask
  liftIO $ do
    let
      table = lookTable inf (_kvname (fst  j))
    kvn <- insertPatch (fmap (mapKey' (recoverFields inf)) . fromRecord . (mapKey' (typeTrans inf))) (conn  inf) (patch $ mapKey' (recoverFields inf) j) (mapTableK (recoverFields inf ) table)
    let mod =  TableModification Nothing table (firstPatch (typeTrans inf) $ kvn)
    return $ Just  mod


deleteMod :: TBData Key Showable -> TransactionM (Maybe (TableModification (TBIdx Key Showable)))
deleteMod j@(meta,_) = do
  inf <- ask
  log <- liftIO $  do
    let
      patch =  (tableMeta table, G.getIndex  j,[])
      table = lookTable inf (_kvname (fst  j))
    deletePatch (conn inf)  (firstPatch (recoverFields inf) patch) table
    return (TableModification Nothing table  patch)
  tell  (maybeToList $ Just log)
  return $ Just log

updateMod :: TBData Key Showable -> TBData Key Showable -> TransactionM (Maybe (TableModification (TBIdx Key Showable)))
updateMod kv old = do
  inf <- ask
  liftIO$ do
    let table = lookTable inf (_kvname (fst  old ))
    patch <- updatePatch (conn  inf) (mapKey' (recoverFields inf) kv )(mapKey' (recoverFields inf) old ) table
    let mod =  TableModification Nothing table (firstPatch (typeTrans inf) patch)
    return $ Just mod

patchMod :: TBIdx Key Showable -> TransactionM (Maybe (TableModification (TBIdx Key Showable)))
patchMod patch@(m,_,_) = do
  inf <- ask
  liftIO $ do
    let table = lookTable inf (_kvname m )
    patch <- applyPatch (conn  inf) (firstPatch (recoverFields inf ) patch )
    let mod =  TableModification Nothing table (firstPatch (typeTrans inf) patch)
    -- Just <$> logTableModification inf mod
    return (Just mod)



selectAll
  ::
     TBF (Labeled Text) Key ()
     -> Int
     -> Maybe PageToken
     -> Int
     -> [(Key, Order)]
     -> WherePredicate
     -> TransactionM  (Int,
           [(KVMetadata Key,
             Compose
               Identity (KV (Compose Identity (TB Identity))) Key Showable)])
selectAll m offset i  j k st = do
      inf <- ask
      let
          unref (TableRef i) = Just i
          unref (HeadToken ) = Nothing
          -- tbf =  tableView (tableMap inf) table
          -- let m = tbf

      v <- liftIO$ paginate inf m k offset j (join $ fmap unref i) st
      mapM_ (tellRefs ) (snd v)
      return v

tellRefs  ::  TBData Key Showable ->  TransactionM ()
tellRefs  (m,k) = do
    inf <- ask
    let
        tellRefsAttr (FKT l k t) = void $ do
            tell ((\m@(k,v) -> TableModification Nothing (lookTable inf (_kvname k)) . patch $ m) <$> F.toList t)
            mapM_ (tellRefs ) $ F.toList t
        tellRefsAttr (Attr _ _ ) = return ()
        tellRefsAttr (Fun _ _ _ ) = return ()
        tellRefsAttr (IT _ t ) = void $ mapM (tellRefs ) $ F.toList t
    mapM_ (tellRefsAttr . unTB ) $ F.toList  (_kvvalues $ unTB k)

loadDelayed :: InformationSchema -> TB3Data (Labeled Text) Key () -> TBData Key Showable -> IO (Maybe (TBIdx Key Showable))
loadDelayed inf t@(k,v) values@(ks,vs)
  | L.null $ _kvdelayed k = return Nothing
  | L.null delayedattrs  = return Nothing
  | otherwise = do
       let
           whr = T.intercalate " AND " ((\i-> justError ("no key" <> show i <> show labelMap)  (M.lookup (S.singleton $ Inline i) labelMap) <>  " = ?") <$> (_kvpk k) )
           labelMap = fmap (label .getCompose) $  _kvvalues $ head $ F.toList $ getCompose (snd $ tableNonRef2 (k,v))
           table = justError "no table" $ M.lookup (S.fromList $ _kvpk k) (pkMap inf)
           delayedTB1 =  fmap (mapComp (\(KV i ) -> KV (M.filterWithKey  (\i _ -> isJust $ M.lookup i filteredAttrs )  i )))
           delayed =  mapKey' (kOptional . ifDelayed . ifOptional) (mapValue' (const ()) (delayedTB1 t))
           str = "select row_to_json(q)  FROM (SELECT " <> explodeRecord delayed <> " FROM " <> expandBaseTable (TB1 t) <> " WHERE " <> whr <> ") as q "
           pk = (fmap (firstTB (recoverFields inf) .unTB) $ fmap snd $ L.sortBy (comparing (\(i,_) -> L.findIndex (\ix -> (S.singleton . Inline) ix == i ) $ _kvpk k)   ) $ M.toList $ _kvvalues $  unTB $ snd $ tbPK (tableNonRef' values))
       print (T.unpack str,show pk )
       is <- queryWith (fromRecordJSON delayed) (conn inf) (fromString $ T.unpack str) pk
       res <- case is of
            [] -> errorWithStackTrace "empty query"
            [i] ->return $ fmap (\(i,j,a) -> (i,G.getIndex (ks,vs),a)) $ diff (ks , _tb $ KV filteredAttrs) (mapKey' (kOptional.kDelayed.unKOptional) . mapFValue' (LeftTB1 . Just . DelayedTB1 .  unSOptional ) $ i  )
            _ -> errorWithStackTrace "multiple result query"
       return res
  where
    delayedattrs = concat $ fmap (keyValue . (\(Inline i ) -> i)) .  F.toList <$> M.keys filteredAttrs
    filteredAttrs = M.filterWithKey (\key v -> S.isSubsetOf (S.map _relOrigin key) (S.fromList $ _kvdelayed k) && (all (maybe False id) $ fmap (fmap (isNothing .unSDelayed)) $ fmap unSOptional $ kattr $ v)  ) (_kvvalues $ unTB vs)

connRoot dname = (fromString $ "host=" <> host dname <> " port=" <> port dname  <> " user=" <> user dname <> " dbname=" <> dbn  dname <> " password=" <> pass dname ) -- <> " sslmode= require" )



postgresOps = SchemaEditor updateMod patchMod insertMod deleteMod (\ j off p g s o-> (\(l,i) -> (i,(TableRef . G.Idex . M.filterWithKey (\k _ -> L.elem k (fmap fst s) ) .   getPKM <$> lastMay i) ,l)) <$> selectAll  j (fromMaybe 0 off) p (fromMaybe 200 g) s o )  (\table j -> do
    inf <- ask
    liftIO . loadDelayed inf (tableView (tableMap inf) table ) $ j ) mapKeyType undefined undefined (\ a -> liftIO . logTableModification a) 200
