{-# LANGUAGE TypeOperators,DeriveFunctor,FlexibleInstances ,ScopedTypeVariables,FlexibleContexts,ConstraintKinds,TypeFamilies,RankNTypes, TupleSections,BangPatterns,OverloadedStrings #-}
module Schema where

import Data.String
import Serializer
import Query
import System.Environment
import Data.Either
import qualified Data.Aeson as A
import Postgresql.Sql.Parser
import Postgresql.Sql.Types
import qualified Data.Poset as P
import qualified Data.Binary as B
import qualified Data.ByteString.Char8 as BS
import qualified Data.ByteString.Lazy.Char8 as BSL
import Postgresql.Types
import Data.Word
import Data.Int
import Control.Monad.State
import Step.Host
import Types
import Expression
import Data.Tuple
import Control.Concurrent.STM.TVar
import Control.Concurrent.STM
import Types.Patch
import Control.Monad.RWS
import qualified Types.Index as G
import SchemaQuery
import qualified Data.Foldable as F
import Data.Maybe
import Data.Bifunctor(second,first)
import Utils
import Control.Exception
import qualified Control.Lens as Le
import Control.Lens ((&),(%~))
import Database.PostgreSQL.Simple
import Database.PostgreSQL.Simple.ToField (ToField)
import Database.PostgreSQL.Simple.FromField (FromField)
import Data.Time
import RuntimeTypes
import Data.Vector (Vector)
import qualified Data.Vector as V
import qualified Data.List as L
import qualified Data.HashMap.Strict as HM
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Map (Map)
import Data.Set (Set)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Reactive.Threepenny as R
import Postgresql.Parser


createType :: (Bool,Bool,Bool,Bool,Bool,Text,Text,Maybe Int32) -> KType (Prim (Text,Text,Maybe Word32) (Text,Text))
createType  (isNull,isArray,isRange,isDef,isComp,tysch,tyname,typmod)
  =  Primitive comp base
  where
    add i v = if i then (v:) else id
    comp = add isNull KOptional . add isArray KArray . add isRange KInterval . add isDef KSerial  $ []
    base
      | isComp =  RecordPrim (tysch ,tyname)
      | otherwise = AtomicPrim (tysch ,tyname,fromIntegral <$> typmod)


queryAuthorization :: Connection -> Int -> Int -> IO (Map Int [Text])
queryAuthorization conn schema user = do
    sq <- query conn aq (schema,user)
    let convert (tname,authorizations) = (tname ,V.toList authorizations)
    return $ M.fromList $ convert <$> sq
  where aq = "select \"table\",authorizations from metadata.authorization where schema= ? and grantee = ? "

tableSizes = "SELECT c.relname,c.reltuples::bigint AS estimate FROM   pg_class c JOIN   pg_namespace n ON c.relkind = 'r' and n.oid = c.relnamespace WHERE n.nspname = ? "

fromShowable2 i v = join (traverse (parseDefValue i) <$> parseExpr v)

testSerial = (=="nextval"). fst . T.break(=='(')

readFModifier :: Text -> FieldModifier
readFModifier "read" = FRead
readFModifier "edit" = FPatch
readFModifier "write" = FWrite

readTableType :: Text ->  TableType
readTableType "BASE TABLE" = ReadWrite
readTableType "VIEW" = ReadOnly

keyTables ,keyTablesInit :: TVar DatabaseSchema ->  (Text ,AuthCookie User) -> (Text -> SchemaEditor) ->  R.Dynamic InformationSchema
keyTables schemaVar (schema ,user) authMap =  maybe (keyTablesInit schemaVar (schema,user) authMap ) return.  HM.lookup schema  =<< liftIO (atomically $ readTVar .globalRef =<< readTVar schemaVar )

schemaPropsQuery conn schema = do
  [(schemaId, color)] <- query conn
    "SELECT oid , color \
    \ FROM metadata.schema \
    \ LEFT JOIN metadata.schema_style st ON st.schema = schema.oid \
    \ WHERE name = ?" (Only schema)
  return $ SchemaProperties schemaId schema color

tablePropsQuery conn schema = do
	tables <-  query conn  "SELECT t.table_name,t.oid,t.table_type,d.description,tr.translation,pks,scopes,s.table_name is not null\
    \ FROM metadata.tables t \ 
    \ LEFT JOIN metadata.table_description d on table_schema = t.schema_name and d.table_name = t.table_name \
    \ LEFT JOIN metadata.table_name_translation tr on tr.\"table\" = t.oid\
    \ LEFT JOIN metadata.pks p on p.schema_name = t.schema_name and p.table_name = t.table_name \ 
    \ LEFT JOIN metadata.sum_table s on s.schema_name = t.schema_name and t.table_name = s.table_name \ 
    \ WHERE t.schema_name = ?" (Only schema)
	return . HM.fromList $ (\(name,oid,ty,desc,trans,pks,scopes,is_sum) -> (name,(oid,readTableType ty,maybe [] V.toList  desc,trans,maybe [] V.toList pks,maybe [] V.toList scopes,is_sum))) <$> tables

tableColumnsQuery
  :: (ToField a1,
      FromField a2, 
      Ord a2) 
     => Connection
     -> a1
     -> IO
          [(a2, FKey (KType (Prim (Text, Text, Maybe Word32) (Text, Text))))]
tableColumnsQuery conn schema= do
   let 
    convertColumns (toid,t,c,op,mod) = ((t,c), (\def ->  Key c (V.toList $ fmap readFModifier mod) op def toid ))
    tableColumns =
          " SELECT\
          \   \"table\",\
          \   table_name,\
          \   column_name,\
          \   ordinal_position,\
          \   field_modifiers\
          \ FROM metadata.columns2 \
          \ WHERE table_schema = ?"
   uniqueMap <- fmap  convertColumns <$>  query conn tableColumns (Only schema)
   let convertColumnsType i@(t,c,j,k,l,m,d,z,b,typ) = (t, key defty ty )
          where 
            defty = do 
              i <- m 
              def <- listToMaybe. T.splitOn "::" $ i
              if testSerial def 
                then Nothing 
                else fromShowable2 (mapKType ty) .  BS.pack . T.unpack $ def
            key = justError "no key" $ M.lookup (t,c) (M.fromList uniqueMap)
            ty = createType (j,k,l,maybe False testSerial m,d,z,b,typ)
   fmap convertColumnsType <$>  query conn "select table_name,column_name,is_nullable,is_array,is_range,col_def,is_composite,type_schema,type_name ,atttypmod from metadata.column_types where table_schema = ?"  (Only schema)

buildTMap schema keyMap rsch = HM.singleton schema keyMap <> foldr mappend mempty (tableMap <$> F.toList  rsch)

keyTablesInit schemaRef  (schema,user) authMap = do
       liftIO $ putStrLn $ "Loading Schema: " <> T.unpack schema
       schemaVar <- liftIO$ readTVarIO schemaRef
       let conn = schemaConn schemaVar
       let ops  = authMap schema
       tableMap0 <- liftIO $ tablePropsQuery conn schema 
       schemaProps <- liftIO $ schemaPropsQuery conn schema
       columns <- liftIO $ tableColumnsQuery conn schema
       
       let
        keyList = (\(t,k)-> ((t,keyValue k),k)) <$> columns 
        tableKeys = buildMap  (\(t,k) -> (t,[k]))  columns

       plugs <- if notElem schema ["code","metadata"]
          then do
             code <- liftIO$ indexSchema schemaRef "code"
             allPlugs <- loadPlugins' code
             let plugs = concat $ newFields . snd <$> L.filter (\i-> isJust $ HM.lookup (_pluginTable $ snd i) tableMap0) allPlugs
                 newFields (FPlugins  _ t (StatefullPlugin l))= concat $ mapKeys . fst <$> l
                   where
                     (oid,_,_,_,_,_,_) = justError "no key" $ HM.lookup t tableMap0
                     max = maximum (keyPosition <$> justLook t tableKeys)
                     mapKeys (i,o) = zipWith (\un (name,ty) -> let k = newKey' [] oid un name ty  in ((t,name),k)) [max + 1 ..] (i <> o)
                 newFields _ = []
             return (plugs,allPlugs)
          else return ([],[])

       let
          keyMap = HM.fromList $ (fmap (typeTransform ops) <$> keyList) <> fst plugs
          backendKeys = M.fromList $ (\k -> (keyFastUnique k ,k)) . snd   <$>  keyList
          lookupKey' map t c = justError ("nokey" <> show (t,c)) $ HM.lookup (t,c) map
          lookupKey ::  Text -> Text ->  Key
          lookupKey = lookupKey' keyMap



       let
        schemaForeign :: Query
        schemaForeign = "select target_schema_name from metadata.fks where origin_schema_name = ? and target_schema_name <> origin_schema_name"
       rslist <- liftIO $ query conn  schemaForeign (Only schema)
       rsch <- HM.fromList <$> mapM (\(Only s) -> (s,) <$> keyTables  schemaRef (s,user) authMap ) rslist
       let
           lookupFKey s t k =  lookupKey' (sKeyMap s) t k
            where
              sKeyMap s
                | s == schema = keyMap
                | otherwise = _keyMapL (justError "no schema" $ HM.lookup s rsch)

       let
          foreignKeys, functionKeys, uniqueIndexes :: Query
          foreignKeys = "SELECT origin_table_name,target_schema_name,target_table_name,origin_fks,target_fks,rel_fks FROM metadata.fks WHERE origin_schema_name = ?"
          functionKeys = "SELECT table_name,column_name,cols,fun FROM metadata.function_keys WHERE schema_name = ?"
          uniqueIndexes = "SELECT table_name,pks FROM metadata.unique_sets WHERE schema_name = ?"
          indexes = "SELECT table_name,columns FROM metadata.catalog_indexes WHERE schema_name = ?" 
          convertFK (tp,sc,tc,kp,kc,rel) = (tp, pure (FKJoinTable (zipWith3 Rel (Inline . lookupKey tp <$> V.toList kp) (readBinaryOp <$> V.toList rel) (Inline . lookupFKey sc tc <$> V.toList kc)) (sc,tc)))
          convertFunction (tp,tc,cols,fun) = (tp, pure (FunctionField tc (readFun fun) (indexerRel <$> V.toList cols )))
          convertUnique (c,v) = (c,pure $ fmap (lookupKey c) . V.toList $ v)
          convertIndexes (c,v) = (c,[V.toList v])

       fks <- liftIO $ buildMap convertFK <$> query conn foreignKeys (Only schema)
       functionsRefs <- liftIO $ buildMap convertFunction <$> query conn functionKeys (Only schema) 
       uniqueConstrMap <- liftIO $ buildMap convertUnique <$> query conn uniqueIndexes  (Only schema)
       indexMap <- liftIO $ buildMap convertIndexes  <$> query conn indexes (Only schema)
       let
           allKeys :: Map Text [Key]
           allKeys =  buildMap (\((t,_),k) -> (t,pure $ lookupKey t (keyValue k))) $ HM.toList keyMap
           createTable c (un,tableType,desc,translation,pksl,scpv,is_sum) 
             = (Raw un schema tableType translation is_sum c constraints indexes scp pks (lookupKey c . T.pack <$> desc) inlineFK [] (PluginField <$> filter ((==c) . _pluginTable.snd ) (snd plugs)) allfks attr)
            where
              pks = lookupKey c <$> pksl
              scp = lookupKey c <$> scpv
              isInline (Primitive _ (RecordPrim _)) = True
              isInline _ = False
              inlineFK = (\k -> (FKInlineTable k . inlineName ) $ keyType k ) <$>  filter (isInline .keyType ) attr
              attr = justLook c allKeys
              constraints = fromMaybe [] $ M.lookup c uniqueConstrMap 
              indexes = maybe []  (fmap (fmap (justError "no col" . flip M.lookup attrMap ))) $  M.lookup c indexMap
                where attrMap = M.fromList $ (\i -> (keyPosition i,i)) <$> attr
              allfks = maybe [] computeRelReferences $ M.lookup c fks
           tableMap1 = HM.mapWithKey createTable tableMap0 
           tableMapPre = buildTMap  schema tableMap1  rsch
           addRefs table = maybe table (\r -> Le.over _functionRefs (mappend (P.sortBy (P.comparing (relSort . pathRelRel))  $ fmap liftFun r)) table) ref
             where
               ref =  M.lookup tn functionsRefs
               liftFun (FunctionField k s a) = FunctionField (lookupFKey ts tn k) s (liftASch (lookKeyNested tableMapPre) ts tn <$> a)
               tn = tableName table
               ts = rawSchema table
           i3l = addRefs <$> tableMap1
       ures <- fmap rights $ liftIO $ decodeViews conn schema
       let
           i3 =  addRecInit (buildTMap schema i3l rsch) <$>  i3l
           unionT (s,n ,_ ,SQLRSelect{}) = (n,id)
           unionT (s,n,_,SQLRUnion (SQLRSelect _ (Just (SQLRReference _ i)) _)  (SQLRSelect _ (Just (SQLRReference _ j)) _ ))
             = (n ,\t -> Project t ( Union ((\t -> justError "no key" $ HM.lookup t i3) <$>  [i,j] )))
           i3u = foldr (uncurry HM.adjust. swap ) i3 (unionT <$> ures)

       metaschema <- if schema /= "metadata"
          then Just <$> keyTables  schemaRef ("metadata",user) authMap
          else return Nothing
       mvar <- liftIO $ atomically $ newTVar M.empty
       let inf = InformationSchema schemaProps user keyMap backendKeys i3u mvar conn metaschema rsch ops schemaRef
       var <- liftIO $ atomically $ modifyTVar (globalRef schemaVar) (HM.insert schema inf)
       return inf

computeRelReferences l = fst $ foldl transform  ([],M.empty)  $ P.sortBy (P.comparing (S.map _relOrigin . pathRelRel)) l
  where
    transform (l, s) (FKJoinTable rels j)
          = let
             r = alterRel <$> rels
            in (FKJoinTable (fst <$> r) j: l ,foldr mappend s (snd <$> r))
           where 
             alterRel rel@(Rel i j k) =  case M.lookup i s of
                Just r -> (Rel (RelAccess  (RelComposite r) i ) j k ,M.empty)
                Nothing -> (rel, M.singleton i rels)

isUnion (Project _ (Union _ )) = True
isUnion _ = False


-- Search for recursive cycles and tag the tables
addRecInit :: HM.HashMap Text (HM.HashMap Text Table) -> Table -> Table
addRecInit inf t = t & (rawFKSL %~ map path) . (_inlineFKS %~ map path)
  where
    path :: SqlOperation -> SqlOperation
    path pini
      = if L.null recurse then (if tname pini == tableName t then RecJoin (MutRec [] ) pini else pini) else RecJoin (MutRec recurse) pini
      where
        recurse = L.filter (not .L.null) $ openPath S.empty [] pini
        sname :: SqlOperation -> (Text,Text)
        sname (FKInlineTable _ nt) = nt
        sname (FKJoinTable _ nt) = nt
        tname = snd . sname
        openPath :: S.Set SqlOperation -> [[Rel Key]] -> SqlOperation -> [[[Rel Key]]]
        openPath ts p pa
          | tname pa == tableName t = [p]
          | S.member pa ts =  []
          | otherwise = openTable (S.insert pa ts) p (sname pa)
        openTable :: Set SqlOperation -> [[Rel Key]] -> (Text,Text) -> [[[Rel Key]]]
        openTable t p (st,nt) =
          join $ fmap (\pa-> openPath t (cons pa) (unRecRel pa)) fks
          where
            cons pa = p <> [F.toList (pathRelRel $unRecRel pa)]
            tb = justError ("no table" <> show nt) $ HM.lookup nt =<< HM.lookup st inf
            fks = rawFKS tb



catchPluginException :: InformationSchema -> Int -> Int -> Map Key ( FTB Showable) -> IO a -> IO (Either Int a)
catchPluginException inf pname tname  idx i =
  (Right <$> i) `catch` (\e  -> do
              t <- getCurrentTime
              print (t,idx,e :: SomeException)
              id  <- query (rootconn inf) "INSERT INTO metadata.plugin_exception (\"user\",\"schema\",\"table\",\"plugin\",exception,data_index2,instant) values(?,?,?,?,?,? :: metadata.key_value[] ,?) returning id" (usernameId inf , schemaId inf,pname,tname,Binary (B.encode $ show (e :: SomeException)) ,V.fromList (fmap (TBRecord2  ("metadata","key_value"). second (Binary . B.encode) . first keyValue) (M.toList idx)) , t )
              return (Left ((\(Only i) -> i)$ head $id)))

logUndoModification
  :: InformationSchema
  -> RevertModification Table (RowPatch Key Showable)  -> IO ()
logUndoModification inf (RevertModification id ip) = do
  time <- getCurrentTime
  env <- lookupEnv "ROOT"
  let mod = modificationEnv env
      ltime =  utcToLocalTime utc time
  liftIO $ executeLogged (rootconn inf) (fromString $ T.unpack $ "INSERT INTO metadata.undo_" <> mod <> " (modification_id,data_index,modification_data) VALUES (?,? :: row_index ,? :: row_operation)" ) (justError "empty tableId" . tableId $ id, Binary . B.encode $    index ip , Binary  . B.encode . content $ firstPatchRow keyValue ip)
  let modt = lookTable (meta inf)  mod
  return ()

logTableModification
  :: InformationSchema
     -> TableModification (RowPatch Key Showable)  -> IO (TableModification (RowPatch Key Showable))
logTableModification inf i@(BatchedAsyncTableModification o l) =
  BatchedAsyncTableModification o <$> mapM (logTableModification inf) l
logTableModification inf i@(FetchData _ ip) =
  return i
logTableModification inf (TableModification Nothing ts u table ip) = do
  time <- getCurrentTime
  env <- lookupEnv "ROOT"
  let mod = modificationEnv env
  let ltime =  utcToLocalTime utc time

  [Only id] <- queryLogged (rootconn inf) (fromString $ T.unpack $ "INSERT INTO metadata." <> mod <> " (\"user_name\",modification_time,\"table_name\",data_index,modification_data  ,\"schema_name\") VALUES (?,?,? ,?:: row_index,? :: row_operation ,?) returning modification_id ") (username inf ,ltime,tableName table,  Binary . B.encode $    index ip , Binary  . B.encode . content $ firstPatchRow keyValue ip, schemaName inf)
  let modt = lookTable (meta inf)  mod
  dbref  <- prerefTable (meta inf) modt

  putPatch (patchVar dbref) [FetchData modt $ createRow' (tableMeta table) $ liftTable' (meta inf)  (modificationEnv env)   $ encodeT (TableModification (Just id) ts u (schemaName inf,tableName table ) (firstPatchRow keyValue ip ) )]
  return (TableModification (Just id) ts u table ip )


modificationEnv env = "modification_table" -- if isJust env then "master_modification_table" else "modification_table"


lookDesc
  :: InformationSchemaKV Key Showable
     -> TableK k
     -> G.GiST (TBIndex Showable) (TBData Key Showable)
     -> T.Text
lookDesc inf j i = maybe (rawName j)  (\(Attr _ (TB1 (SText v)))-> v) row
  where
    pk = [("schema" ,int $ schemaId inf),("table",int (tableUnique j))]
    row = lookupAccess  (meta inf) pk "translation"  ("table_name_translation", i)

tableOrder
  ::
     InformationSchemaKV Key Showable
     -> TableK k
     -> G.GiST (TBIndex Showable) (TBData Key Showable)
     -> FTB Showable
tableOrder inf table orderMap =  maybe (int 0) _tbattr row
  where
    pk = [("table",int . tableUnique $ table ), ("schema",int (schemaId inf))]
    row = lookupAccess (meta inf) pk  "usage" ("ordering",orderMap)

lookupAccess inf l f c = join $ fmap (indexField (IProd  notNull (lookKey inf (fst c) f) )) . G.lookup (idex inf (fst c) l) $ snd c

idex inf t v = Idex $ fmap snd $ L.sortOn (((`L.elemIndex` (rawPK $ lookTable inf t)).fst)) $ first (lookKey inf t  ) <$> v


recoverFields :: InformationSchema -> FKey (KType (Prim KPrim  (Text,Text))) -> FKey (KType (Prim PGType PGRecord))
recoverFields inf v = map
  where map = justError ("notype" <> T.unpack (showKey v)) $  backendsKey inf (keyFastUnique v)

loadPlugins' :: InformationSchema -> R.Dynamic [Plugins]
loadPlugins' code =
  F.toList <$> transactionNoLog  code (SchemaQuery.select "plugin_code")

loadPlugins :: InformationSchema -> R.Dynamic [Plugins]
loadPlugins inf =  do
  code <- liftIO$ indexSchema  (rootRef inf) "code"
  loadPlugins' code





