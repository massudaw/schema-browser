{-# LANGUAGE Arrows,FlexibleContexts,TypeFamilies ,NoMonomorphismRestriction,OverloadedStrings ,TupleSections #-}
module Postgresql.Backend (connRoot,postgresOps) where

import Types
import Step.Client
import Control.Exception
import Data.Time
import qualified Types.Index as G
import Control.Arrow hiding(first)
import SchemaQuery
import GHC.Int
import Control.Monad.RWS hiding(pass)
import Environment
import Postgresql.Types
import Default
import Postgresql.Printer
import Data.Interval (Extended(..),upperBound)
import Data.Either
import Data.Functor.Apply
import Postgresql.Parser
import Utils
import Text
import Control.Lens as Le
import Schema
import RuntimeTypes
import Data.Bifunctor
import Query
import Control.Monad.Writer hiding (pass)
import Types.Patch
import Data.Ord
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
import Database.PostgreSQL.Simple

filterFun  = M.filter (\ v-> not $ isFun v )
  where isFun (Fun _ _ _ ) = True
        isFun i = False

overloadedRules = M.fromListWith (++) (translate <$> postgresqlRules)
postgresqlRules  = [dropSchema,createSchema,alterSchema,createTableCatalog, dropTableCatalog,createColumnCatalog,dropColumnCatalog]

schema_name
  :: Monad m => Text -> PluginM (G.AttributePath Text  MutationTy) (Atom (TBData Text Showable))   m i (Showable)
schema_name  s
  = iforeign [(Rel s Equals "name")] (ivalue . irecord $ ifield "name" (ivalue (readV PText)))

column_type
  :: (Monad m ) =>
    PluginM (G.PathIndex PathTID (Union (G.AttributePath Text  MutationTy))) (Atom (FTB (TBData Text Showable)))   m i (Showable,Showable)
column_type
  = ivalue $ isum [iinline "primitive" . iopt . ivalue . irecord $
             iforeign [(Rel "schema_name" Equals "nspname"),(Rel "data_name" Equals "typname")]
               (ivalue $ irecord ((,) <$> ifield "nspname" (ivalue (readV PText)) <*> ifield "typname" (ivalue (readV PText))))
         ,iinline "composite" . iopt . ivalue . irecord $
             iforeign [(Rel "schema_name" Equals "schema_name"),(Rel "data_name" Equals "table_name")]
               (ivalue $ irecord ((,) <$> ifield "schema_name" (ivalue (readV PText)) <*> ifield "table_name" (ivalue (readV PText))))]

createColumnCatalog
  :: PluginM  (Namespace Text Text RowModifier Text) (Atom (TBData Text Showable)) TransactionM i ()
createColumnCatalog  =
  aschema "metadata" $
    atable "catalog_columns" $
      arow RowCreate  $
        proc _ -> do
          c <- ifield "column_name" (ivalue (readV PText)) -< ()
          (s,t) <- iforeign [(Rel "table_name" Equals "table_name"),(Rel "table_schema" Equals "schema_name")]
                      (ivalue $ irecord ((,) <$> schema_name "schema_name"  <*>  ifield "table_name" (ivalue (readV PText)))) -< ()
          (sty,ty) <-  iinline "col_type"  . iftb PIdOpt $ column_type -< ()
          act (\(s,t,c,sty,ty) -> do
            inf <- lift askInf
            let sqr = "ALTER TABLE ?.? ADD COLUMN ? ?.? "
                args = (DoubleQuoted s ,DoubleQuoted t,DoubleQuoted c ,DoubleQuoted  sty ,DoubleQuoted ty )
            executeLogged (rootconn inf)  sqr args
            return ()) -< (s,t,c,sty,ty)

dropColumnCatalog
  :: PluginM  (Namespace Text Text RowModifier Text) (Atom (TBData Text Showable)) TransactionM i ()
dropColumnCatalog  = do
  aschema "metadata" $
    atable "catalog_columns" $
      arow RowDrop $
        proc _ -> do
          c <- ifield "column_name"
              (ivalue (readV PText)) -< ()
          s <- iforeign [(Rel "table_schema" Equals "name")]
              (ivalue $ irecord (ifield "name" (ivalue (readV PText) ))) -< ()
          t <- iforeign [(Rel "table_name" Equals "table_name"),(Rel "table_schema" Equals "schema_name")]
              (ivalue $ irecord (ifield "table_name" (ivalue (readV PText)))) -< ()
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


createSchema
  :: PluginM  (Namespace Text Text RowModifier Text) (Atom (TBData Text Showable)) TransactionM i ()
createSchema  = do
  aschema "metadata" $
    atable "catalog_schema" $
      arow RowCreate $
        proc _ -> do
          s <- ifield "name"
              (ivalue (readV  PText))-< ()
          o <- fmap join $ iforeign [(Rel "owner" Equals "oid")]
              (iopt $ ivalue $ irecord (ifield "usename" (iopt $ ivalue (readV PText)) )) -< ()
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

alterSchema
  :: PluginM  (Namespace Text Text RowModifier Text) (Atom (TBData Text Showable)) TransactionM i ()
alterSchema = do
  aschema "metadata" $
    atable "catalog_schema" $
      arow RowUpdate $
        proc _ -> do
          (n,nnewm) <- ifield "name"
              (ivalue (changeV PText)) -< ()
          Just (o,onewm) <- fmap join $ iforeign [(Rel "owner" Equals "oid")]
              (iopt $ ivalue $ irecord (ifield "usename" (iopt (ivalue (changeV PText))) )) -< ()
          act (\(n,o,onewm,nnewm) -> do
            inf <- lift askInf
            when (onewm /= o) . void $
              executeLogged (rootconn inf) "ALTER SCHEMA ? OWNER TO ?" (DoubleQuoted n, DoubleQuoted onewm)
            when (nnewm /= n) . void $
              executeLogged (rootconn inf) "ALTER SCHEMA ? RENAME TO ?" (DoubleQuoted n, DoubleQuoted nnewm) ) -< (n,o,onewm,nnewm)
          returnA -< ()

dropSchema
  :: PluginM  (Namespace Text Text RowModifier Text) (Atom (TBData Text Showable)) TransactionM i ()
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


deleteIdx
  ::
     Connection ->  KVMetadata PGKey -> TBIndex Showable -> Table -> IO ()
deleteIdx conn m ix@(G.Idex kold) t = do
    executeLogged conn qstr qargs
    return ()
  where
    qstr = fromString $ T.unpack del
    qargs = koldPk
    equality k = escapeReserved (attrValueName k) <> "="  <> "?"
    koldPk = uncurry Attr <$> zip (_kvpk m) (F.toList kold)
    pred   =" WHERE " <> T.intercalate " AND " (fmap  equality koldPk)
    del = "DELETE FROM " <> rawFullName t <>   pred

applyPatch
  ::
     Connection -> KVMetadata PGKey ->([TBIndex Showable] ,TBIdx PGKey Showable) -> IO ()
applyPatch conn m patch@(pks,skv)  = do
    executeLogged conn qstr qargs
    return ()
  where
    qstr = fromString $ T.unpack up
    qargs = (first (fmap textToPrim) <$> (catMaybes $ fst <$> inputs)) <> concat ( fmap koldPk pks)
    equality k = k <> "="  <> "?"
    koldPk (G.Idex kold) = zip (fmap textToPrim . keyType <$> _kvpk m) (F.toList kold)
    pred   (G.Idex kold) =  T.intercalate " AND " (equality . escapeReserved . keyValue . fst <$> zip (_kvpk m) (F.toList kold))
    inputs = execWriter $ mapM (attrPatchName Nothing) skv
    setter = " SET " <> T.intercalate "," (snd <$> inputs)
    paren i = "(" <> i <> ")"
    up = "UPDATE " <> kvMetaFullName m <> setter <> " WHERE " <> T.intercalate " OR " ( paren . pred  <$> pks)


attrPatchName :: Maybe Text -> PathAttr PGKey Showable -> Writer [(Maybe (KType (Prim PGType (Text, Text)) , FTB Showable), Text)] ()
attrPatchName pre (PAttr k p ) = sqlPatchFTB atom (maybe "" (\i -> i <> ".") pre <> escapeReserved ( keyValue k)) id (keyType k) p
  where
    atom k c ty (PAtom (SDelta (DSInt i))) = inpVariable  (ty,TB1 $ SNumeric i) ( k <> "=" <> c  (k <> " + ?"))
    atom k c ty i  = inpVariable  (ty,create i) ( k <> "=" <> c "?")
attrPatchName pre (PInline k p ) = sqlPatchFTB atom (maybe "" (\i -> i <> ".") pre <> escapeReserved ( keyValue k)) id (keyType k) p
  where
    atom k c ty (PAtom i)  = mapM_ (attrPatchName (Just k)) i
attrPatchName pre i = error $ show (pre,i)


inpVariable :: (KType (Prim PGType (Text, Text)), FTB Showable) -> Text -> UpdateOperations
inpVariable i j = tell [(Just i,j)]

inpStatic :: Text -> UpdateOperations
inpStatic j = tell [(Nothing,j)]

type UpdateOperations =  Writer [(Maybe (KType (Prim PGType (Text, Text)), FTB Showable), Text)] ()
type SetterGen c = (Text
                -> (Text -> Text)
                -> KType (Prim PGType (Text, Text))
                -> PathFTB c
                -> UpdateOperations)

sqlPatchFTB :: Show c => SetterGen c ->SetterGen c
sqlPatchFTB f k call (Primitive l c ) s = go k call l s
  where
    go  k call (KSerial:xs)  (POpt o) = do
      case o of
        Just j ->go  k call xs  j
        Nothing -> inpStatic $  (k <> "=" <>   "null" )
    go  k call (KOptional:xs)  (POpt o) = do
      case o of
        Just j ->go  k call xs  j
        Nothing -> inpStatic $  (k <> "=" <>   "null" )
    go  k ca (KArray:xs)  (PIdx ix o) = do
      case o of
        Just j -> go  (k <> six ix ) ca xs  j
        Nothing -> inpStatic $ (k <> " = " <>  k <> sixDown (ix -1) <> " || " <> k <> sixUp (ix + 1)  )
      where
        six ix = "[" <> T.pack (show ix) <> "]"
        sixUp ix = "[" <> T.pack (show ix) <> ":]"
        sixDown ix = "[:" <> T.pack (show ix) <> "]"
    go  k ca (KInterval:xs) b@(PatchSet _ ) =
      f k ca (Primitive (KInterval:xs) c ) b
    go  k ca (KInterval:xs)  (PInter s (v,j)) =
      case (s,v) of
        (True,NegInf) ->   inpStatic (k <> " = " <> "lowerI(" <>  k <> ",null," <> (T.pack (show j )) <> ")")
        (True,Finite b) -> go  k ((\i ->"lowerI(" <> k <> "," <> i <> "," <> (T.pack (show j )) <> ")") . ca) xs  b
        (False,PosInf) -> inpStatic (k <> " = " <> "upperI(" <>  k <> ",null," <> (T.pack (show j )) <> ")")
        (False ,Finite b) -> go  k ((\i -> "upperI(" <>  k <> "," <> i <> "," <> (T.pack (show j )) <> ")") . ca ) xs  b
    go  k c ty (PatchSet b) = mapM_ (go  k c ty) b
    go  k ca ty i@(PAtom _) = f k ca (Primitive ty c) i
    go  k  _ ty i = error $ show (k,ty,i)

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
  let quec = fromString $ T.unpack $ "SELECT row_to_json(q),(case WHEN ROW_NUMBER() over () = 1 then count(*) over () else null end) as count FROM (" <> que <> ") as q " <> offsetQ <> limitQ
  print  =<< formatQuery (conn  inf) quec (fromMaybe [] attr)
  v <- queryWith (withCount (fromRecordJSON inf meta t name )) (conn inf) quec (fromMaybe [] attr) `catch` (\e -> print (t,wherepred ) >> throw (e :: SomeException))
  let estimateSize = maybe 0 (\c-> c - off ) $ join $ safeHead ( fmap snd v :: [Maybe Int])
  print estimateSize
  return (estimateSize, fmap fst v)
  where
    offsetQ = " OFFSET " <> T.pack (show off)
    limitQ = " LIMIT " <> T.pack (show size)


insertMod :: KVMetadata Key -> TBData Key Showable -> TransactionM (((RowPatch Key Showable)))
insertMod m j  = do
  inf <- askInf
  liftIO $ do
      let
        table = lookTable inf (_kvname m)
        ini = defaultTableData inf table j ++  patch j
      d <- insertPatch  inf (conn  inf) (create ini) table
      l <- liftIO getCurrentTime
      return    $ either (error . unlines ) (createRow' m) (typecheck (typeCheckTable (_rawSchemaL table, _rawNameL table)) (create $ ini ++ d))


deleteMod :: KVMetadata Key -> TBData Key Showable -> TransactionM (((RowPatch Key Showable)))
deleteMod m t = do
  inf <- askInf
  liftIO $  do
      let table = lookTable inf (_kvname m)
          idx = G.getIndex m t
      deleteIdx (conn inf) (recoverFields inf <$> m) idx  table
      l <- liftIO getCurrentTime
      return $  RowPatch (idx,DropRow )

updateMod :: KVMetadata Key -> TBData Key Showable -> TBIndex Showable -> TBIdx Key Showable -> TransactionM (((RowPatch Key Showable)))
updateMod m old pk p = do
  inf <- askInf
  liftIO$ do
      let table = lookTable inf (_kvname m)
          ini = either (error . unlines ) id (typecheck (typeCheckTable (_rawSchemaL table, _rawNameL table)) $ create $ defaultTableData inf table kv ++  patch kv)
          kv = apply old  p
      updatePatch (conn  inf) (recoverFields inf <$>  m) (mapKey' (recoverFields inf) ini )(mapKey' (recoverFields inf) old ) table
      l <- liftIO getCurrentTime
      let mod =   RowPatch (G.notOptional pk  ,PatchRow p)
      return $ mod

patchMod :: KVMetadata Key -> [TBIndex Showable] -> TBIdx Key Showable-> TransactionM (((RowPatch Key Showable)))
patchMod m pk patch = do
  inf <- askInf
  liftIO $ do
    applyPatch (conn inf) (recoverFields inf <$> m) (pk,patchNoRef $ firstPatch (recoverFields inf) patch)
    return $ rebuild  pk (PatchRow patch)

loadDelayed :: Table -> TBData Key Showable -> TransactionM (Maybe (RowPatch Key Showable))
loadDelayed table  values = do
  inf <- askInf
  let
    v = tableNonRef $ allRec' (tableMap inf) table
    nonRefV = tableNonRef values
    delayed =  recComplement inf m nonRefV v
  -- liftIO $ print delayed
  liftIO $ fmap join $ traverse (check inf nonRefV )  delayed
  where
    m = tableMeta table
    check inf values delayed = do
           let
               (str,namemap) = codegen (loadDelayedQuery inf m delayed)
               pk = fmap (firstTB (recoverFields inf) . snd) . L.sortBy (comparing (\(i,_) -> L.findIndex (\ix -> (S.singleton . Inline) ix == i ) $ _kvpk m)) . M.toList . _kvvalues $ tbPK m values
               qstr = (fromString $ T.unpack str)
           print  =<< formatQuery (conn  inf) qstr pk
           is <- queryWith (fromRecordJSON inf m delayed namemap) (conn inf) qstr pk
           res <- case is of
                    [i] ->return $ RowPatch . (G.getIndex m i,).PatchRow <$> diff values i
                    [] -> error "empty query"
                    _ -> error "multiple result query"
           return res

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


postgresOps = SchemaEditor updateMod patchMod insertMod deleteMod   selectAll loadDelayed mapKeyType (\ a -> liftIO . logTableModification a) (\a -> liftIO . logUndoModification a) tSize (\inf -> withTransaction (conn inf))  overloadedRules
