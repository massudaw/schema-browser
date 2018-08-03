{-# LANGUAGE TypeOperators,DeriveFunctor,FlexibleInstances ,ScopedTypeVariables,FlexibleContexts,ConstraintKinds,TypeFamilies,RankNTypes, TupleSections,BangPatterns,OverloadedStrings #-}
module Schema where

import Data.String
import Serializer
import System.Environment
import Data.Either
import qualified Data.Aeson as A
import Postgresql.Sql.Parser
import Postgresql.Sql.Types
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

fromShowable2 i v = case  parseValue v of
            Left v -> Nothing
            Right v ->toExpr v
  where toExpr v =  case v of
              Lit v -> ConstantExpr . fromShowable i <$>  (A.decode $ BSL.pack $ T.unpack v)
              ApplyFun t l -> Function t <$> (traverse toExpr l)
              Cast i j -> toExpr i
              i -> error (show i)


testSerial  =(=="nextval"). fst . T.break(=='(')

readFModifier :: Text -> FieldModifier
readFModifier "read" = FRead
readFModifier "edit" = FPatch
readFModifier "write" = FWrite


keyTables ,keyTablesInit :: TVar DatabaseSchema ->  (Text ,AuthCookie User) -> (Text -> SchemaEditor) -> [Plugins] ->  R.Dynamic InformationSchema
keyTables schemaVar (schema ,user) authMap pluglist =  maybe (keyTablesInit schemaVar (schema,user) authMap pluglist ) return.  HM.lookup schema  =<< liftIO (atomically $ readTVar .globalRef =<< readTVar schemaVar )


keyTablesInit schemaRef  (schema,user) authMap pluglist = do
       schemaVar <- liftIO$ readTVarIO schemaRef
       let conn = schemaConn schemaVar
           -- schemaId = justLookH schema (schemaNameMap schemaVar)
       let ops  = authMap schema
       [Only schemaId] <- liftIO $ query  conn "SELECT oid FROM metadata.schema where name = ?" (Only schema)
       color <- liftIO$ query conn "SELECT color FROM metadata.schema_style where schema = ? " (Only schemaId)
       uniqueMap <- liftIO$ fmap (\(toid,t,c,op,mod,tr) -> ((t,c), (\def ->  Key c tr (V.toList $ fmap readFModifier mod) op def toid ))) <$>  query conn "select t.oid ,o.table_name,o.column_name,ordinal_position,field_modifiers,translation from  metadata.columns o join metadata.tables t on o.table_name = t.table_name and o.table_schema = t.schema_name  left join metadata.table_translation tr on o.column_name = tr.column_name   where table_schema = ? "(Only schema)
       res2 <- liftIO$ fmap (\i@(t,c,j,k,l,m,d,z,b,typ)-> (t,) $ (\ty -> (justError ("no unique" <> show (t,c,fmap fst uniqueMap)) $  M.lookup (t,c) (M.fromList uniqueMap) )  (join$ fromShowable2 (mapKType ty) .  BS.pack . T.unpack <$> join (fmap (\v -> if testSerial v then Nothing else Just v) (join $ listToMaybe. T.splitOn "::" <$> m) )) ty )  (createType  (j,k,l,maybe False testSerial m,d,z,b,typ))) <$>  query conn "select table_name,column_name,is_nullable,is_array,is_range,col_def,is_composite,type_schema,type_name ,atttypmod from metadata.column_types where table_schema = ?"  (Only schema)
       let
          keyList =  fmap (\(t,k)-> ((t,keyValue k),k)) res2
          keyMap = typeTransform ops <$> HM.fromList keyList

          lookupKey' map t c = justError ("nokey" <> show (t,c)) $ HM.lookup (t,c) map
          lookupKey ::  Text -> Text ->  Key
          lookupKey = lookupKey' keyMap

          lookupPK :: Functor f => f (Int,Text,Maybe (Vector Text),Maybe (Vector Text),Bool) -> f (Text,(Int,Vector Key,Vector Key,Bool))
          lookupPK = fmap  (\(o,t,c,s,b)-> (t,(o,vector  t c,vector t s,b)) )
            where vector t = maybe V.empty (fmap (lookupKey t))
          lookFk t k = V.toList $ fmap (lookupKey t) k
          readTT :: Text ->  TableType
          readTT "BASE TABLE" = ReadWrite
          readTT "VIEW" = ReadOnly
          readTT i =  error  $ T.unpack i

       descMap <- liftIO$ M.fromList . fmap  (\(t,cs)-> (t,fmap (\c -> justError (show (t,c)) $ HM.lookup (t,c) keyMap) (V.toList cs)) ) <$> query conn "SELECT table_name,description FROM metadata.table_description WHERE table_schema = ? " (Only schema)
       transMap <- liftIO$ M.fromList   <$> query conn "SELECT \"table\",translation FROM metadata.table_name_translation WHERE schema = ? " (Only schemaId )
       uniqueConstrMap <- liftIO$ M.fromListWith (++) . fmap (fmap pure)   <$> query conn "SELECT table_name,pks FROM metadata.unique_sets WHERE schema_name = ? " (Only schema)
       indexMap <- liftIO$ M.fromListWith (++) . fmap (fmap pure)   <$> query conn "SELECT table_name,columns FROM metadata.catalog_indexes WHERE schema_name = ? " (Only schema)

       res <- liftIO$ lookupPK <$> query conn "SELECT oid,t.table_name,pks,scopes,s.table_name is not null FROM metadata.tables t left join metadata.pks  p on p.schema_name = t.schema_name and p.table_name = t.table_name left join metadata.sum_table s on s.schema_name = t.schema_name and t.table_name = s.table_name where t.schema_name = ?" (Only schema)

       resTT <- liftIO$ fmap readTT . M.fromList <$> query conn "SELECT table_name,table_type FROM metadata.tables where schema_name = ? " (Only schema)
       let
        schemaForeign :: Query
        schemaForeign = "select target_schema_name from metadata.fks where origin_schema_name = ? and target_schema_name <> origin_schema_name"
       rslist <- liftIO $ query conn  schemaForeign (Only schema)
       rsch <- HM.fromList <$> mapM (\(Only s) -> (s,) <$> keyTables  schemaRef (s,user) authMap pluglist) rslist
       let
           sKeyMap s
              | s == schema = keyMap
              | otherwise = _keyMapL (justError "no schema" $ HM.lookup s rsch)
           lookRFk s t k = V.toList $ fmap  (lookupKey' (sKeyMap s) t) k

       let
          foreignKeys :: Query
          foreignKeys = "select origin_table_name,target_schema_name,target_table_name,origin_fks,target_fks,rel_fks from metadata.fks where origin_schema_name = ?"
          functionKeys :: Query
          functionKeys = "select table_name,schema_name,column_name,cols,fun from metadata.function_keys where schema_name = ?"

       fks <- liftIO$ M.fromListWith mappend . fmap (\(tp,sc,tc,kp,kc,rel) -> (tp,  pure (FKJoinTable (zipWith3 Rel (Inline <$> lookFk tp kp) (readBinaryOp <$> V.toList rel) (lookRFk sc tc kc)) (sc,tc)))) <$> query conn foreignKeys (Only schema)

       functionsRefs <- liftIO$ M.fromListWith mappend . fmap (\i@(tp,sc::Text,tc,cols,fun) -> (tp,  pure (FunctionField tc ( readFun fun) (indexerRel <$> V.toList cols ) ) )) <$> query conn functionKeys (Only schema):: R.Dynamic (Map Text [SqlOperationK Text] )

       let
           allKeys :: Map Text [Key]
           allKeys =  M.fromListWith mappend  $ (\((t,_),k) -> (t,pure $ lookupKey t (keyValue k))) <$> HM.toList keyMap
           createTable (c,(un,pksl,scpv,is_sum)) = (c ,Raw un schema tableType translation is_sum c constraints indexes  scp pks desc inlineFK [] allfks attr)
            where
              pks = F.toList pksl
              scp = F.toList scpv
              isInline (Primitive _ (RecordPrim _)) = True
              isInline _ = False
              inlineFK =  (\k -> (FKInlineTable k . inlineName ) $ keyType k ) <$>  filter (isInline .keyType ) attr
              attr =  justLook c allKeys
              indexes = fromMaybe [] (fmap ( fmap (justError "no key" . flip M.lookup  attrMap)  . V.toList) <$> M.lookup c indexMap)
                where attrMap = M.fromList $ (\i -> (keyPosition i,i)) <$> attr
              translation = M.lookup un transMap
              constraints = fromMaybe [] (fmap ( fmap (lookupKey c )  . V.toList) <$> M.lookup c uniqueConstrMap)
              desc = fromMaybe [] $ M.lookup  c descMap
              tableType = justLook c resTT
              allfks = fromMaybe []  $ M.lookup c fks
           i3lnoFun = fmap createTable res :: [(Text,Table)]
           tableMapPre = HM.singleton schema (HM.fromList i3lnoFun)
           addRefs table = maybe table (\r -> Le.over _functionRefs (mappend (fmap liftFun r)) table) ref
             where
               ref =  M.lookup (tableName table) functionsRefs
               liftFun (FunctionField k s a) = FunctionField (lookupKey' (sKeyMap ts) tn k) s (liftASch (lookKeyNested tableMapPre) ts tn <$> a)
               tn = tableName table
               ts = rawSchema table

           i3l =fmap addRefs <$> i3lnoFun
       ures <- fmap rights $ liftIO $ decodeViews conn schema
       let
           i3 =  addRecInit (HM.singleton schema (HM.fromList i3l ) <> foldr mappend mempty (tableMap <$> F.toList  rsch)) <$>  HM.fromList i3l
           pks = M.fromList $ (\(_,t)-> (S.fromList$ rawPK t ,t)) <$> HM.toList i3
           i2 =    M.filterWithKey (\k _ -> not.S.null $ k )  pks
           unionT (s,n ,_ ,SQLRSelect{}) = (n,id)
           unionT (s,n,_,SQLRUnion (SQLRSelect _ (Just (SQLRReference _ i)) _)  (SQLRSelect _ (Just (SQLRReference _ j)) _ )  )
             = (n ,\t -> Project t ( Union ((\t -> justError "no key" $ HM.lookup t i3 )<$>  [i,j] )))
       let
           i3u = foldr (uncurry HM.adjust. swap ) i3 (unionT <$> ures)
           i2u = foldr (uncurry M.adjust. swap) i2 (first (\tn -> justError ("no union table" ++ show tn ). fmap (\(_,i,_,_) ->S.fromList $ F.toList i)  $ M.lookup tn (M.fromList res)) . unionT <$> ures)

       metaschema <- if schema /= "metadata"
          then Just <$> keyTables  schemaRef ("metadata",user) authMap pluglist
          else return Nothing

       mvar <- liftIO$ atomically $ newTVar  M.empty
       let inf = InformationSchema (SchemaProperties schemaId schema ((\(Only i ) -> i)<$> listToMaybe color)) user  keyMap backendKeys  (M.fromList $ (\i -> (keyFastUnique i,i)) <$> F.toList keyMap) (M.filterWithKey (\k v -> notElem (tableName v ) convert) i2u )  i3u mvar  conn metaschema  rsch ops pluglist schemaRef
           backendKeys = M.fromList $ (\k -> (keyFastUnique k ,k)) . snd   <$>  keyList
           convert = concatMap (\(_,_,_,n) -> deps  n) ures
           deps (SQLRUnion (SQLRSelect _ (Just (SQLRReference _ i)) _ )  (SQLRSelect _ (Just (SQLRReference _ j)) _ ) ) =  [i,j]
           deps SQLRSelect{} = []


       var <- liftIO$ atomically $ modifyTVar (globalRef schemaVar  ) (HM.insert schema inf )
       return inf

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
        openTable :: Set (SqlOperation) -> [[Rel Key]] -> (Text,Text) -> [[[Rel Key]]]
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
  (dbref ,_) <-R.runDynamic $ prerefTable (meta inf) modt

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

idex inf t v = G.Idex $  fmap snd $ L.sortOn (((`L.elemIndex` (rawPK $ lookTable inf t)).fst)) $ first (lookKey inf t  ) <$> v

{-
addStats schema = do
  let metaschema = meta schema
  varmap <- liftIO$ atomically $ readTVar ( mvarMap schema)
  let stats = "table_stats"
  (dbpol,(_,polling))<- transactionNoLog metaschema $ selectFrom stats  Nothing Nothing [] mempty
  let
    row t s ls = tblist  $ [Attr "schema" (int (schemaId schema ) ), Attr "table" (int t) , Attr "size" (TB1 (SNumeric s)), Attr "loadedsize" (TB1 (SNumeric ls)) ]
    lrow t dyn st = liftTable' metaschema "table_stats" . row t (maybe (G.size dyn) (maximum .fmap fst ) $  nonEmpty $  F.toList st) $ (G.size dyn)
    lookdiff tb row =  maybe (Just $ patch row ) (\old ->  diff old row ) (G.lookup (G.getIndex row) tb)
  mapM_ (\(m,_)-> do
    var <- refTable schema (m)
    let event = R.filterJust $ lookdiff <$> R.facts (collectionTid dbpol ) R.<@> (flip (lrow (tableUnique $ (m))) <$>  R.facts (idxTid var ) R.<@> R.rumors (collectionTid  var ) )
    R.onEventIO event (\i -> do
      putPatch (patchVar $ iniRef dbpol) . pure  .PatchRow $ i
      )) (M.toList  varmap)
  return  schema
-}

recoverFields :: InformationSchema -> FKey (KType (Prim KPrim  (Text,Text))) -> FKey (KType (Prim PGType PGRecord))
recoverFields inf v = map
  where map = justError ("notype" <> T.unpack (showKey v)) $  backendsKey inf (keyFastUnique v)



