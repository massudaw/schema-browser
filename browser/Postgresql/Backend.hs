{-# LANGUAGE Arrows,FlexibleContexts,TypeFamilies ,NoMonomorphismRestriction,OverloadedStrings ,TupleSections #-}
module Postgresql.Backend (postgresqlRules,connRoot,postgresOps) where

import Types
import Step.Client
import Data.Time
import qualified Types.Index as G
import Control.Arrow hiding(first)
import SchemaQuery
import GHC.Int
import Control.Monad.RWS hiding(pass)
import qualified Data.ByteString.Char8 as BS
import Environment
import Postgresql.Types
import Default
import Step.Common
import qualified Data.Poset as P
import Postgresql.Printer
import Step.Host
import Postgresql.Sql.Printer
import Data.Interval (Extended(..),upperBound)
import Data.Either
import Data.Functor.Apply
import System.Environment
import Control.Concurrent.STM
import Safe
import Control.Monad
import Postgresql.Printer
import Postgresql.Parser
import Utils
import Text
import Control.Monad.Reader
import Control.Lens as Le
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
import qualified  Data.HashMap.Strict as HM

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

filterFun  = M.filter (\ v-> not $ isFun v )
  where isFun (Fun _ _ _ ) = True
        isFun i = False

overloadedRules = M.fromListWith (++) (translate <$> postgresqlRules)
postgresqlRules  = [dropSchema,createSchema,alterSchema,createTableCatalog, dropTableCatalog,createColumnCatalog,dropColumnCatalog]

schema_name  s
  = iforeign [(Rel s Equals "name")] (irecord $ ifield "name" (ivalue (readV PText)))

column_type
  = isum [iinline "primitive" . iopt . irecord $
             iforeign [(Rel "schema_name" Equals "nspname"),(Rel "data_name" Equals "typname")]
               (irecord ((,) <$> ifield "nspname" (ivalue (readV PText)) <*> ifield "typname" (ivalue (readV PText))))
         ,iinline "composite" . iopt . irecord $
             iforeign [(Rel "schema_name" Equals "schema_name"),(Rel "data_name" Equals "table_name")]
               (irecord ((,) <$> ifield "schema_name" (ivalue (readV PText)) <*> ifield "table_name" (ivalue (readV PText))))]

createColumnCatalog  =
  aschema "metadata" $
    atable "catalog_columns" $
      arow RowCreate $
        proc _ -> do
          c <- ifield "column_name" (ivalue (readV PText)) -< ()
          (s,t) <- iforeign [(Rel "table_name" Equals "table_name"),(Rel "table_schema" Equals "schema_name")]
                      (irecord ((,) <$> schema_name "schema_name"  <*>  ifield "table_name" (ivalue (readV PText)))) -< ()
          (sty,ty) <-  iinline "col_type"  . iftb PIdOpt .irecord$ column_type -< ()
          act (\(s,t,c,sty,ty) -> do
            inf <- lift askInf
            let sqr = "ALTER TABLE ?.? ADD COLUMN ? ?.? "
                args = (DoubleQuoted s ,DoubleQuoted t,DoubleQuoted c ,DoubleQuoted  sty ,DoubleQuoted ty )
            executeLogged (rootconn inf)  sqr args
            return ()) -< (s,t,c,sty,ty)

dropColumnCatalog  = do
  aschema "metadata" $
    atable "catalog_columns" $
      arow RowDrop $
        proc _ -> do
          c <- ifield "column_name"
              (ivalue (readV PText)) -< ()
          s <- iforeign [(Rel "table_schema" Equals "name")]
              (irecord (ifield "name" (ivalue (readV PText) ))) -< ()
          t <- iforeign [(Rel "table_name" Equals "table_name"),(Rel "table_schema" Equals "schema_name")]
              (irecord (ifield "table_name" (ivalue (readV PText)))) -< ()
          act (\(t,s,c) -> do
            inf <- lift askInf
            executeLogged (rootconn inf) "ALTER TABLE ?.? DROP COLUMN ? "(DoubleQuoted  s ,DoubleQuoted  t, DoubleQuoted c)) -< (t,s,c)
          returnA -< ()


createTableCatalog :: PluginM (Namespace Text Text RowModifier Text)  (Atom (TBData  Text Showable)) TransactionM  i ()
createTableCatalog = do
  aschema "metadata" $
    atable "catalog_tables" $
      arow RowCreate $
        proc _ -> do
          t <- ifield "table_name"
             (ivalue (readV PText)) -< ()
          s <- schema_name "schema_name"  -< ()
          oid <- act (\(sc ,n) -> do
              inf <- lift askInf
              liftIO $ executeLogged (rootconn inf) "CREATE TABLE ?.? ()"(DoubleQuoted sc ,DoubleQuoted  n)
              [Only i] <- liftIO $ query (rootconn inf) "select oid from metadata.catalog_tables where table_name =? and schema_name = ? " ((renderShowable n),(renderShowable sc))
              return i) -< (TB1 s,TB1 t)
          ifield "oid" (iftb PIdOpt (ivalue (writeV (PInt 8)))) -< SNumeric oid
          returnA -< ()

dropTableCatalog :: PluginM (Namespace Text Text RowModifier Text)  (Atom (TBData  Text Showable)) TransactionM  i ()
dropTableCatalog = do
  aschema "metadata" $
    atable "catalog_tables" $
      arow RowDrop $
        proc _ -> do
          t <- ifield "table_name"
              (ivalue (readV PText)) -< ()
          (SText ty) <- ifield "table_type"
              (ivalue (readV  PText))-< ()
          s <- schema_name "schema_name"  -< ()
          act (\(ty,sc ,n) ->  do
              inf <- lift askInf
              let tys = case ty of
                    "BASE TABLE" -> "TABLE"
                    "VIEW" -> "VIEW"
              liftIO$ executeLogged (rootconn inf) ("DROP " <> tys <> " ?.?") (DoubleQuoted sc ,DoubleQuoted n)
              ) -< (ty,TB1 s,TB1 t)
          returnA -< ()


createSchema  = do
  aschema "metadata" $
    atable "catalog_schema" $
      arow RowCreate $
        proc _ -> do
          s <- ifield "name"
              (ivalue (readV  PText))-< ()
          o <- fmap join $ iforeign [(Rel "owner" Equals "oid")]
              (iopt $ irecord (ifield "usename" (iopt $ ivalue (readV PText)) )) -< ()
          oid <- act (\(n,onewm) ->  do
            inf <- lift askInf
            maybe
              (executeLogged (rootconn inf) "CREATE SCHEMA ? "(Only $ DoubleQuoted n))
              (\o -> executeLogged (rootconn inf) "CREATE SCHEMA ? AUTHORIZATION ? "(DoubleQuoted n, DoubleQuoted o)) onewm
            liftIO $ print =<< formatQuery  (rootconn inf) "select oid from metadata.catalog_schema where name =? " (Only $ (renderShowable n))
            [Only i] <- liftIO$ query (rootconn inf) "select oid from metadata.catalog_schema where name =? " (Only $ (renderShowable n))
            return i) -< (TB1 s,fmap TB1 o)
          ifield "oid" (ivalue (writeV (PInt 8))) -< SNumeric oid
          returnA -< ()

alterSchema = do
  aschema "metadata" $
    atable "catalog_schema" $
      arow RowUpdate $
        proc _ -> do
          (n,nnewm) <- ifield "name"
              (ivalue (changeV PText)) -< ()
          Just (o,onewm) <- fmap join $ iforeign [(Rel "owner" Equals "oid")]
              (iopt $ irecord (ifield "usename" (iopt (ivalue (changeV PText))) )) -< ()
          act (\(n,o,onewm,nnewm) -> do
            inf <- lift askInf
            when (onewm /= o) . void $
              executeLogged (rootconn inf) "ALTER SCHEMA ? OWNER TO ?" (DoubleQuoted n, DoubleQuoted onewm)
            when (nnewm /= n) . void $
              executeLogged (rootconn inf) "ALTER SCHEMA ? RENAME TO ?" (DoubleQuoted n, DoubleQuoted nnewm) ) -< (n,o,onewm,nnewm)
          returnA -< ()

dropSchema = do
  aschema "metadata" $
    atable "catalog_schema" $
      arow RowDrop $
        proc _ -> do
          s <- ifield "name" (ivalue (readV  PText))-< ()
          act (\n->  do
            inf <- lift askInf
            liftIO$ executeLogged (rootconn inf) "DROP SCHEMA ?"(Only $ DoubleQuoted n)
            return ()) -< TB1 s
          returnA -< ()




insertPatch
  :: (MonadIO m ,Functor m )
     => InformationSchema
     -> Connection
     -> TBData Key Showable
     -> TableK Key
     -> m (TBIdx Key Showable)
insertPatch  inf conn i  t = either error (\i ->  liftIO $ if not $ L.null serialAttr
      then do
        let
          iquery :: String
          (iquery ,namemap)= codegen $ do
            j <- explodeRecord inf (tableMeta t) (kvlist serialAttr)
            return $ T.unpack $ prequery <> " RETURNING (SELECT row_to_json(q) FROM (" <> selectRow "p0" j <> ") as q)"
        print  =<< formatQuery conn (fromString iquery) directAttr
        [out] <- queryWith (fromRecordJSON inf (tableMeta t) serialTB namemap ) conn (fromString  iquery) directAttr
        let gen =  patch out
        return (patch out)
      else do
        let
          iquery = T.unpack prequery
        executeLogged  conn (fromString  iquery ) directAttr
        return []) checkAllFilled
    where
      checkAllFilled = tableCheck  (tableMeta t) i
      prequery =  "INSERT INTO " <> rawFullName t <>" ( " <> T.intercalate "," (escapeReserved .keyValue<$> projKey directAttr ) <> ") VALUES (" <> T.intercalate "," (value <$> projKey directAttr)  <> ")"
      attrs =  concat $L.nub $ nonRefTB  <$> F.toList (filterFun $ unKV i)
      testSerial (k,v ) = (isSerial .keyType $ k) && (isNothing. unSSerial $ v)
      direct f = filter (not.all1 testSerial .f)
      serialAttr = flip Attr (LeftTB1 Nothing)<$> filter (isSerial .keyType) ( rawPK t <> F.toList (rawAttrs t))
      directAttr :: [TB Key Showable]
      directAttr = direct aattr attrs
      projKey :: [TB Key a ] -> [Key]
      projKey = fmap _relOrigin . concat . fmap keyattr
      serialTB = kvlist serialAttr
      all1 f [] = False
      all1 f i = all f i

value i = "?"  <> fromMaybe ""  (inlineType (keyType i))

attrValueName ::  TB (FKey k) a -> Text
attrValueName (Attr i _ )= keyValue i
attrValueName (IT i  _) = keyValue i


deletePatch
  ::
     Connection ->  KVMetadata PGKey -> TBIndex Showable -> Table -> IO ()
deletePatch conn m ix@(G.Idex kold) t = do
    executeLogged conn qstr qargs
    return ()
  where
    qstr = fromString $ T.unpack del
    qargs = koldPk
    equality k = escapeReserved (attrValueName k) <> "="  <> "?"
    koldPk = uncurry Attr <$> zip (_kvpk m) (F.toList kold)
    pred   =" WHERE " <> T.intercalate " AND " (fmap  equality koldPk)
    del = "DELETE FROM " <> rawFullName t <>   pred

type SetterGen c = (Text
                -> (Text -> Text)
                -> KType (Prim PGType (Text, Text))
                -> PathFTB c
                -> Writer [(Maybe (KType (Prim PGType (Text, Text)), FTB Showable), Text)] ())
applyPatch
  ::
     Connection -> KVMetadata PGKey ->(TBIndex Showable ,TBIdx PGKey Showable) -> IO ()
applyPatch conn m patch@(G.Idex kold,skv)  = do
    executeLogged conn qstr qargs
    return ()
  where
    qstr = fromString $ T.unpack up
    qargs = ((first (fmap textToPrim) <$> (catMaybes $ fst <$> inputs)) <> koldPk )
    equality k = k <> "="  <> "?"
    koldPk = zip (fmap textToPrim . keyType <$> _kvpk m) (F.toList kold)
    pred   = " WHERE " <> T.intercalate " AND " (equality . escapeReserved . keyValue . fst <$> zip (_kvpk m) (F.toList kold))
    inputs = execWriter $ mapM (attrPatchName Nothing) skv
    setter = " SET " <> T.intercalate "," (snd <$> inputs)
    up = "UPDATE " <> kvMetaFullName m <> setter <>  pred


attrPatchName :: Maybe Text -> PathAttr PGKey Showable -> Writer [(Maybe (KType (Prim PGType (Text, Text)) , FTB Showable), Text)] ()
attrPatchName pre (PAttr k p ) = nestP atom (maybe "" (\i -> i <> ".") pre <> escapeReserved ( keyValue k)) id (keyType k) p
      where
        atom k c ty i  = inp $ ((ty,create i) , k <> "=" <> c "?")
attrPatchName pre (PInline k p ) = nestP atom (maybe "" (\i -> i <> ".") pre <> escapeReserved ( keyValue k)) id (keyType k) p
      where
        atom k c ty (PAtom i)  = mapM_ (attrPatchName (Just k)) i

six ix = "[" <> T.pack (show ix) <> "]"
sixUp ix = "[" <> T.pack (show ix) <> ":]"
sixDown ix = "[:" <> T.pack (show ix) <> "]"
inp (i,j) = tell [(Just i,j)]
inpStatic j = tell [(Nothing,j)]

nestP :: Show c => SetterGen c ->SetterGen c
nestP f k call (Primitive (KOptional:xs) c) (POpt (Just j)) = do
  nestP f k call (Primitive xs c) j
nestP f k call (Primitive (KOptional:xs) c) (POpt (Just j)) = do
  nestP f k call (Primitive xs c) j
nestP f k _ (Primitive (KOptional:xs) c) (POpt Nothing) = do
  inpStatic $  (k <> "=" <>   "null" )
nestP f k ca (Primitive (KArray:xs) c) (PIdx ix (Just j)) = do
  nestP f (k <> six ix ) ca (Primitive xs c) j
nestP f k _ (Primitive (KArray :xs) c) (PIdx ix Nothing) = do
  inpStatic $ (k <> " = " <>  k <> sixDown (ix -1) <> " || " <> k <> sixUp (ix + 1)  )
nestP f k ca (Primitive (KInterval:xs) c) (PInter True (NegInf,j)) =
  inpStatic (k <> " = " <> "lowerI(" <>  k <> ",null," <> (T.pack (show j )) <> ")")
nestP f k ca (Primitive (KInterval:xs) c) (PInter True (Finite b,j)) =
  nestP f k ((\i ->"lowerI(" <> k <> "," <> i <> "," <> (T.pack (show j )) <> ")") . ca) (Primitive xs c) b
nestP f k ca (Primitive (KInterval:xs) c) (PInter False (PosInf,j)) =
  inpStatic (k <> " = " <> "upperI(" <>  k <> ",null," <> (T.pack (show j )) <> ")")
nestP f k ca (Primitive (KInterval:xs) c) (PInter False (Finite b,j)) =
  nestP f k ((\i -> "upperI(" <>  k <> "," <> i <> "," <> (T.pack (show j )) <> ")") . ca ) (Primitive xs c) b
nestP f k c ty (PatchSet b) = mapM_ (nestP f k c ty) b
nestP f k c ty i@(PAtom _) = f k c ty i
nestP _ k  _ ty i = error $ show (k,ty,i)

updatePatch
  ::
     Connection -> KVMetadata PGKey -> TBData PGKey Showable -> TBData PGKey Showable -> Table -> IO ()
updatePatch conn m kv old  t = do
    executeLogged conn qstr qargs
    return ()
  where
    qstr = fromString $ T.unpack up
    qargs = skv <> koldPk
    kold = M.toList $ getPKM m old
    equality  k =escapeReserved  (keyValue k) <> "="  <> value k
    koldPk = uncurry Attr <$> kold
    pred   =" WHERE " <> T.intercalate " AND " (equality  . fst <$> kold)
    setter = " SET " <> T.intercalate "," (equality  . _tbattrkey <$> skv   )
    up = "UPDATE " <> rawFullName t <> setter <>  pred
    skv = F.toList  (_kvvalues $ tbskv)
    tbskv = isM
    isM :: TBData PGKey  Showable
    isM =  justError ("cant diff befor update: " <> show (tableNonRef kv) <> "\n" <> show (tableNonRef old) <> "\n"  <> show kv) $ diffUpdateAttr kv old

diffUpdateAttr :: (Ord k , Ord a) => TBData k a -> TBData k a -> Maybe (TBData k a )
diffUpdateAttr  kv kold  =  fmap KV  .  allMaybesMap  $ liftF2 (\i j -> if i == j then Nothing else Just i) (unKV . tableNonRef  $ kv ) (unKV . tableNonRef $ kold )

paginate
  :: InformationSchema
  -> KVMetadata Key
  -> TBData Key ()
  -> [(Key, Order)]
  -> Int
  -> Int
  -> Maybe [FTB Showable]
  -> WherePredicate
  -> IO (Int, [TBData Key Showable])
paginate inf meta t order off size koldpre wherepred = do
  let ((que,attr),name) = selectQuery inf meta t koldpre order wherepred
  v <- do
      let quec = fromString $ T.unpack $ "SELECT row_to_json(q),count(*) over () FROM (" <> que <> ") as q " <> offsetQ <> limitQ
      print  =<< formatQuery (conn  inf) quec (fromMaybe [] attr)
      queryWith (withCount (fromRecordJSON inf meta t name )) (conn inf) quec (fromMaybe [] attr)
  let estimateSize = maybe 0 (\c-> c - off ) $ safeHead ( fmap snd v :: [Int])
  print estimateSize
  return (estimateSize, fmap fst v)
  where
        offsetQ = " OFFSET " <> T.pack (show off)
        limitQ = " LIMIT " <> T.pack (show size)



-- High level db operations


insertMod :: KVMetadata Key -> TBData Key Showable -> TransactionM (((RowPatch Key Showable)))
insertMod m j  = do
  inf <- askInf
  liftIO $ do
      let
        table = lookTable inf (_kvname m)
        ini = defaultTable inf table j ++  patch j
      d <- insertPatch  inf (conn  inf) (create ini) table
      l <- liftIO getCurrentTime
      return    $ either (error . unlines ) (createRow' m) (typecheck (typeCheckTable (_rawSchemaL table, _rawNameL table)) (create $ ini ++ d))


deleteMod :: KVMetadata Key -> TBData Key Showable -> TransactionM (((RowPatch Key Showable)))
deleteMod m t = do
  inf <- askInf
  liftIO $  do
      let table = lookTable inf (_kvname m)
          idx = G.getIndex m t
      deletePatch (conn inf) (recoverFields inf <$> m) idx  table
      l <- liftIO getCurrentTime
      return $  RowPatch (idx,DropRow )

updateMod :: KVMetadata Key -> TBData Key Showable -> TBIndex Showable -> TBIdx Key Showable -> TransactionM (((RowPatch Key Showable)))
updateMod m old pk p = do
  inf <- askInf
  liftIO$ do
      let table = lookTable inf (_kvname m)
          ini = either (error . unlines ) id (typecheck (typeCheckTable (_rawSchemaL table, _rawNameL table)) $ create $ defaultTable inf table kv ++  patch kv)
          kv = apply old  p
      updatePatch (conn  inf) (recoverFields inf <$>  m) (mapKey' (recoverFields inf) ini )(mapKey' (recoverFields inf) old ) table
      l <- liftIO getCurrentTime
      let mod =   RowPatch (G.notOptional pk  ,PatchRow p)
      return $ mod

patchMod :: KVMetadata Key -> TBIndex Showable -> TBIdx Key Showable-> TransactionM (((RowPatch Key Showable)))
patchMod m pk patch = do
  inf <- askInf
  liftIO $ do
    let table = lookTable inf (_kvname m)
    applyPatch (conn inf) (recoverFields inf <$>m )(pk,firstPatch (recoverFields inf ) patch)
    l <- liftIO getCurrentTime
    let mod =   RowPatch (G.notOptional pk,PatchRow patch)
    return (mod)

loadDelayed :: Table -> TBData Key Showable -> TransactionM (Maybe (TBIdx Key Showable))
loadDelayed table  values = do
  inf <- askInf
  liftIO $ check inf
  where
    check inf
      | L.null $ _kvdelayed m = return Nothing
      | L.null delayedattrs  = return Nothing
      | otherwise = do
           let
               delayedTB1 :: TBData Key () -> TBData Key ()
               delayedTB1 (KV i ) = KV $ M.filterWithKey  (\i _ -> isJust $ M.lookup i filteredAttrs ) i
               delayed =  mapKey' unKDelayed (mapFValue (fmap (const ())) (delayedTB1 v))
               (str,namemap) = codegen (loadDelayedQuery inf m v delayed)
               pk = fmap (firstTB (recoverFields inf) . snd) . L.sortBy (comparing (\(i,_) -> L.findIndex (\ix -> (S.singleton . Inline) ix == i ) $ _kvpk m)) . M.toList . _kvvalues $ tbPK m(tableNonRef values)
               qstr = (fromString $ T.unpack str)
           print  =<< formatQuery (conn  inf) qstr pk
           is <- queryWith (fromRecordJSON inf m delayed namemap) (conn inf) qstr pk
           res <- case is of
                [i] ->return $ diff (KV filteredAttrs) (makeDelayed i)
                [] -> error "empty query"
                _ -> error "multiple result query"
           return res
      where
        v=  allRec' (tableMap inf) table
        m = tableMeta table
        makeDelayed = mapKey' makeDelayedK . mapFValue makeDelayedV
        makeDelayedV i = join $ (LeftTB1 . Just . TB1) <$>  i
        makeDelayedK = Le.over (keyTypes.keyFunc) (++[KDelayed])
        split (KOptional:xs) (LeftTB1 i) = maybe False (split xs) i
        split (KDelayed:xs) (LeftTB1 i) = isNothing i
        split [] _ = False
        checkDelayed (Attr k i ) =split (_keyFunc $ keyType k) i
        checkDelayed i = False
        delayedattrs = concat $ fmap (keyValue . _relOrigin ) .  F.toList <$> M.keys filteredAttrs
        filteredAttrs = M.filterWithKey (\key v -> S.isSubsetOf (S.map _relOrigin key) (S.fromList $ _kvdelayed m) && (checkDelayed  v)  ) (_kvvalues $ values)



selectAll
  ::
     KVMetadata Key
     -> TBData Key ()
     -> Maybe Int
     -> Maybe PageToken
     -> Maybe Int
     -> [(Key, Order)]
     -> WherePredicate
     -> TransactionM ([KV Key Showable],PageToken,Int)
selectAll meta m offset i  j k st = do
      inf <- askInf
      let
          unIndex (Idex i) = i
          unref (TableRef i) = fmap unIndex $ unFin $ upperBound i
      (l,i) <- liftIO$ paginate inf meta m k (fromMaybe 0 offset) (fromMaybe tSize j) ( join $ fmap unref i) st
      return (i,(TableRef $ G.getBounds meta i) ,l)

connRoot dname = (fromString $ "host=" <> host dname <> " port=" <> port dname  <> " user=" <> user dname <> " dbname=" <> dbn  dname <> " password=" <> pass dname   )

tSize = 400

postgresOps = SchemaEditor updateMod patchMod insertMod deleteMod   selectAll loadDelayed mapKeyType (\ a -> liftIO . logTableModification a) tSize (\inf -> withTransaction (conn inf))  overloadedRules
