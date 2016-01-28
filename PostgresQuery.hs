{-# LANGUAGE TypeFamilies ,NoMonomorphismRestriction,OverloadedStrings ,TupleSections #-}
module PostgresQuery where

import Types
import Safe
import Control.Monad
import Postgresql.Printer
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

import Postgresql
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
insertPatch f conn path@(m ,s,i ) t =  if not $ L.null serialAttr
      then do
        let
          iquery :: String
          iquery = T.unpack $ prequery <> " RETURNING ROW(" <>  T.intercalate "," (projKey serialAttr) <> ")"
        liftIO $ print iquery
        out <-  fmap head $ liftIO $ queryWith (f (mapRecord (const ()) serialTB )) conn (fromString  iquery ) directAttr
        let Just (_,_ ,gen) = diff serialTB out
        return (m,getPKM out ,compact (i <> gen ) )
      else do
        let
          iquery = T.unpack prequery
        liftIO $ print iquery
        liftIO $ execute  conn (fromString  iquery ) directAttr
        return path
    where
      prequery =  "INSERT INTO " <> rawFullName t <>" ( " <> T.intercalate "," (projKey directAttr ) <> ") VALUES (" <> T.intercalate "," (fmap (const "?") $ projKey directAttr)  <> ")"
      attrs =  concat $ nonRefTB . create <$> i
      testSerial (k,v ) = (isSerial .keyType $ k) && (isNothing. unSSerial $ v)
      serial f =  filter (all1 testSerial  .f)
      direct f = filter (not.all1 testSerial .f)
      serialAttr = serial aattri attrs
      directAttr = direct aattri attrs
      projKey = fmap (keyValue ._relOrigin) . concat . fmap keyattri
      serialTB = reclist' t (fmap _tb  serialAttr)
      all1 f [] = False
      all1 f i = all f i



deletePatch
  ::
     Connection ->  TBIdx PGKey Showable -> Table -> IO (TBIdx PGKey Showable)
deletePatch conn patch@(m ,kold ,_) t = do
    execute conn (fromString $ traceShowId $ T.unpack del) koldPk
    return patch
  where
    equality k = attrValueName k <> "="  <> "?"
    koldPk = uncurry Attr <$> F.toList kold
    pred   =" WHERE " <> T.intercalate " AND " (fmap  equality koldPk)
    del = "DELETE FROM " <> rawFullName t <>   pred

applyPatch
  ::
     Connection -> TBIdx PGKey Showable -> IO (TBIdx PGKey Showable)
applyPatch conn patch@(m,kold,skv)  =
    execute conn (fromString $ traceShowId $ T.unpack up)  (fmap attrPatchValue skv <> koldPk ) >> return patch
  where
    equality k = k <> "="  <> "?"
    koldPk = uncurry Attr <$> F.toList kold
    attrPatchName (PAttr k _) = keyValue k
    attrPatchValue (PAttr  k v) = Attr k (create v) :: TB Identity PGKey Showable
    pred   =" WHERE " <> T.intercalate " AND " (equality . keyValue . fst <$> F.toList kold)
    setter = " SET " <> T.intercalate "," (equality .   attrPatchName <$> skv   )
    up = "UPDATE " <> kvfullname m <> setter <>  pred


updatePatch
  ::
     Connection -> TBData PGKey Showable -> TBData PGKey Showable -> Table -> IO (TBIdx PGKey Showable)
updatePatch conn kv old  t =
    execute conn (fromString $ traceShowId $ T.unpack up)  (skv <> koldPk ) >> return patch
  where
    patch  = justError ("cant diff states" <> (concat $ zipWith differ (show kv) (show old))) $ diff old kv
    kold = getPKM old
    equality k = k <> "="  <> "?"
    koldPk = uncurry Attr <$> F.toList kold
    pred   =" WHERE " <> T.intercalate " AND " (equality . keyValue . fst <$> F.toList kold)
    setter = " SET " <> T.intercalate "," (equality .   attrValueName <$> skv   )
    up = "UPDATE " <> rawFullName t <> setter <>  pred
    skv = unTB <$> F.toList  (_kvvalues $ unTB tbskv)
    tbskv = snd isM
    isM :: TBData PGKey  Showable
    isM =  justError ("cant diff befor update" <> show (kv,old)) $ diffUpdateAttr kv old

differ = (\i j  -> if i == j then [i]  else "(" <> [i] <> "|" <> [j] <> ")" )

paginate inf t order off size k eqpred = do
    let (que,attr) = case k of
          (Just koldpre) ->
            let
              que =  selectQuery t <> pred <> orderQ
              koldPk :: [TB Identity Key Showable]
              koldPk =  uncurry Attr <$> L.sortBy (comparing ((`L.elemIndex` (fmap fst order)).fst)) koldpre
            in (que,koldPk <> tail (reverse koldPk) <> eqpk )
          Nothing ->
            let
              que =  selectQuery t <> pred <> orderQ
            in (que,eqpk)
    let quec = fromString $ T.unpack $ "SELECT *,count(*) over () FROM (" <> que <> ") as q " <> offsetQ <> limitQ
    print (quec,attr)
    v <- uncurry (queryWith (withCount (fromRecord (unTlabel' t)) ) (conn inf ) ) (quec, fmap (firstTB (recoverFields inf)) attr)
    print (maybe 0 (\c-> c - off ) $ safeHead ( fmap snd v :: [Int]))
    return ((maybe 0 (\c-> c - off ) $ safeHead ( fmap snd v :: [Int])), fmap fst v)
  where pred = maybe "" (const " WHERE ") (fmap (fmap snd)   k <> fmap (concat . fmap  (fmap TB1 .F.toList . snd)) eqspred) <> T.intercalate " AND " (maybe [] (const $ pure $ generateComparison (first (justLabel t) <$> order)) k <> (maybe [] pure $ eqquery <$> eqspred))
        equality (pred,k) = " ? " <> pred <> inattr k
        eqquery :: [(Text,TB Identity Key a)] -> Text
        eqquery eqpred = T.intercalate " AND " (equality . second (firstTB (justLabel t)) <$> eqpred)
        eqspred = L.sortBy (comparing ((`L.elemIndex` (fmap fst order)). inattr .snd) )  <$> eqpred
        eqpk :: [TB Identity Key Showable]
        eqpk =  maybe [] id   (fmap snd <$> eqspred)
        offsetQ = " OFFSET " <> T.pack (show off)
        limitQ = " LIMIT " <> T.pack (show size)
        orderQ = " ORDER BY " <> T.intercalate "," ((\(l,j)  -> l <> " " <> showOrder j ) . first (justLabel t) <$> order)



data View
  = View
  { tree :: TB3Data (Labeled Text) Key ()
  , viewOrder :: [(Key,Order)]
  , viewProjection :: [Key]
  , pagination :: (Int,Int,Int,Maybe [(Key,FTB Showable)])
  }

justLabel :: TB3Data (Labeled Text ) Key () -> Key -> Text
justLabel t k =  justError ("cant find label"  <> show k <> " - " <> show t).getLabels t $ k

-- tableType :: TB1 () -> Text


getLabels t k =  M.lookup  k (mapLabels label' t)
    where label' (Labeled l (Attr k _)) =  (k,l )
          label' (Labeled l (IT k tb )) = (k, l <> " :: " <> tableType tb)
          label' (Unlabeled (Attr k _)) = (k,keyValue k)
          label' (Unlabeled (IT k v)) = (k, label $ getCompose $ snd (head (F.toList v))  )
          lattr =_tbattrkey . labelValue .getCompose


mapLabels label' t =  M.fromList $ fmap (label'. getCompose.labelValue.getCompose) (getAttr $ joinNonRef' t)


-- Generate SORT Order

generateSort v = T.intercalate "," (generateSort' <$> v)
generateSort' (k,v) =  k <> " " <>   showOrder v

-- Generate Comparison Operator

generateComparison ((k,v):[]) = k <>  dir v <> "?"
  where dir Asc = ">"
        dir Desc = "<"
generateComparison ((k,v):xs) = "case when " <> k <>  "=" <> "? OR "<> k <> " is null  then " <>  generateComparison xs <> " else " <> k <>  dir v <> "?" <>" end"
  where dir Asc = ">"
        dir Desc = "<"

-- High level db operations

insertMod :: TBData Key Showable -> TransactionM (Maybe (TableModification (TBIdx Key Showable)))
insertMod j  = do
  inf <- ask
  liftIO $ do
    let
      table = lookTable inf (_kvname (fst  j))
    kvn <- insertPatch (fmap (mapKey' (recoverFields inf)) . fromRecord . (mapKey' (typeTrans inf))) (conn  inf) (patch $ mapKey' (recoverFields inf) j) (mapTableK (recoverFields inf ) table)
    let mod =  TableModification Nothing table (firstPatch (typeTrans inf) kvn)
    Just <$> logTableModification inf mod


deleteMod :: TBData Key Showable -> TransactionM (Maybe (TableModification (TBIdx Key Showable)))
deleteMod j@(meta,_) = do
  inf <- ask
  log <- liftIO $  do
    let
      patch =  (tableMeta table, getPKM j,[])
      table = lookTable inf (_kvname (fst  j))
    deletePatch (conn inf)  (firstPatch (recoverFields inf) patch) table
    Just <$> logTableModification inf (TableModification Nothing table  patch)
  tell  (maybeToList log)
  return log

updateMod :: TBData Key Showable -> TBData Key Showable -> TransactionM (Maybe (TableModification (TBIdx Key Showable)))
updateMod kv old = do
  inf <- ask
  liftIO$ do
    let table = lookTable inf (_kvname (fst  old ))
    patch <- updatePatch (conn  inf) (mapKey' (recoverFields inf) kv )(mapKey' (recoverFields inf) old ) table
    let mod =  TableModification Nothing table (firstPatch (typeTrans inf) patch)
    Just <$> logTableModification inf mod

patchMod :: TBIdx Key Showable -> TransactionM (Maybe (TableModification (TBIdx Key Showable)))
patchMod patch@(m,_,_) = do
  inf <- ask
  liftIO $ do
    let table = lookTable inf (_kvname m )
    patch <- applyPatch (conn  inf) (firstPatch (recoverFields inf ) patch )
    let mod =  TableModification Nothing table (firstPatch (typeTrans inf) patch)
    Just <$> logTableModification inf mod


selectAll
  ::
     TableK Key
     -> Int
     -> Maybe PageToken
     -> Int
     -> [(Key, Order)]
     -> [(T.Text, Column Key Showable)]
     -> TransactionM  (Int,
           [(KVMetadata Key,
             Compose
               Identity (KV (Compose Identity (TB Identity))) Key Showable)])
selectAll table offset i  j k st = do
      inf <- ask
      let
          unref (TableRef i) = i
          tbf =  tableView (tableMap inf) table
      let m = tbf
      (t,v) <- liftIO$ duration  $ paginate inf m k offset j (fmap unref i) (nonEmpty st)
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
        tellRefsAttr (IT _ t ) = void $ mapM (tellRefs ) $ F.toList t
    mapM_ (tellRefsAttr . unTB ) $ F.toList  (_kvvalues $ unTB k)

loadDelayed :: InformationSchema -> TBData Key () -> TBData Key Showable -> IO (Maybe (TBIdx Key Showable))
loadDelayed inf t@(k,v) values@(ks,vs)
  | L.null $ _kvdelayed k = return Nothing
  | L.null delayedattrs  = return Nothing
  | otherwise = do
       let
           whr = T.intercalate " AND " ((\i-> (keyValue i) <>  " = ?") <$> (_kvpk k) )
           table = justError "no table" $ M.lookup (S.fromList $ _kvpk k) (pkMap inf)
           delayedTB1 =  (ks,) . _tb $ KV ( filteredAttrs)
           delayed =  mapKey' (kOptional . ifDelayed . ifOptional) (mapValue' (const ()) delayedTB1)
           str = "SELECT " <> explodeRecord (relabelT' runIdentity Unlabeled delayed) <> " FROM " <> showTable table <> " WHERE " <> whr
       print str
       is <- queryWith (fromRecord delayed) (conn inf) (fromString $ T.unpack str) (fmap (firstTB (recoverFields inf) .unTB) $ F.toList $ _kvvalues $  runIdentity $ getCompose $ tbPK' (tableNonRef' values))
       case is of
            [] -> errorWithStackTrace "empty query"
            [i] ->return $ fmap (\(i,j,a) -> (i,getPKM (ks,vs),a)) $ diff delayedTB1(mapKey' (kOptional.kDelayed.unKOptional) . mapFValue' (LeftTB1 . Just . DelayedTB1 .  unSOptional ) $ i  )
            _ -> errorWithStackTrace "multiple result query"
  where
    delayedattrs = concat $ fmap (keyValue . (\(Inline i ) -> i)) .  F.toList <$> M.keys filteredAttrs
    filteredAttrs = M.filterWithKey (\key v -> S.isSubsetOf (S.map _relOrigin key) (S.fromList $ _kvdelayed k) && (all (maybe False id) $ fmap (fmap (isNothing .unSDelayed)) $ fmap unSOptional $ kattr $ v)  ) (_kvvalues $ unTB vs)

connRoot dname = (fromString $ "host=" <> host dname <> " port=" <> port dname  <> " user=" <> user dname <> " dbname=" <> dbn  dname <> " password=" <> pass dname ) -- <> " sslmode= require" )



postgresOps = SchemaEditor updateMod patchMod insertMod deleteMod (\ j off p g s o-> (\(l,i) -> (fmap TB1 i,(TableRef . filter (flip L.elem (fmap fst s) . fst ) .  getPK . TB1 <$> lastMay i) ,l)) <$> selectAll  j (fromMaybe 0 off) p (fromMaybe 200 g) s o ) (\ _ _ _ _ -> return ([],Nothing,0)) (\table j -> do
    inf <- ask
    liftIO . loadDelayed inf (unTlabel' $ tableView (tableMap inf) table ) $ j ) mapKeyType undefined
