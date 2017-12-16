{-# LANGUAGE TypeOperators,DeriveFunctor,FlexibleInstances ,ScopedTypeVariables,FlexibleContexts,ConstraintKinds,TypeFamilies,RankNTypes, TupleSections,BangPatterns,OverloadedStrings #-}
module Schema where

import Data.String
import Serializer
import System.Environment
import Data.Either
import qualified Data.Aeson as A
import Postgresql.Sql
import qualified Data.Binary as B
import qualified Data.ByteString.Char8 as BS
import qualified Data.ByteString.Lazy as BSL
import qualified Data.IntMap as IM
import Postgresql.Types
import Data.Word
import Data.Int
import Control.Monad.State
import Query
import Step.Host
import Data.Ord
import Types
import Expression
import Data.Tuple
import Control.Concurrent.STM.TVar
import Control.Concurrent.STM
import Types.Patch
import Control.Monad.RWS
import qualified Types.Index as G
import SchemaQuery
import Prelude hiding (head)
import Data.Unique
import qualified Data.Foldable as F
import Data.Maybe
import Data.Bifunctor(second,first)
import Utils
import Control.Exception
import qualified Control.Lens as Le
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


createType :: (Bool,Bool,Bool,Bool,Bool,Bool,Text,Text,Maybe Int32) -> KType (Prim (Text,Text,Maybe Word32) (Text,Text))
createType  (isNull,isArray,isDelayed,isRange,isDef,isComp,tysch,tyname,typmod)
  = Primitive comp base
  where
    add i v = if i then (v:) else id
    comp = add isNull KOptional . add isArray KArray . add isRange KInterval . add isDef KSerial . add isDelayed KDelayed $ []
    base
      | isComp =  RecordPrim (tysch ,tyname)
      | otherwise = AtomicPrim (tysch ,tyname,fromIntegral <$> typmod)


meta inf = maybe inf id (metaschema inf)




queryAuthorization :: Connection -> Int -> Int -> IO (Map Int [Text])
queryAuthorization conn schema user = do
    sq <- query conn aq (schema,user)
    let convert (tname,authorizations) = (tname ,V.toList authorizations)
    return $ M.fromList $ convert <$> sq
  where aq = "select \"table\",authorizations from metadata.authorization where schema= ? and grantee = ? "

tableSizes = "SELECT c.relname,c.reltuples::bigint AS estimate FROM   pg_class c JOIN   pg_namespace n ON c.relkind = 'r' and n.oid = c.relnamespace WHERE n.nspname = ? "

-- fromShowable2 i j | traceShow (i,j) False = error ""
fromShowable2 i v = fromShowable i  <$> A.decode (BSL.fromStrict v)

testSerial  =((=="nextval"). fst . T.break(=='('))

readFModifier :: Text -> FieldModifier
readFModifier "read" = FRead
readFModifier "edit" = FPatch
readFModifier "write" = FWrite


keyTables ,keyTablesInit :: TVar DatabaseSchema ->  (Text ,Text) -> (Text -> IO (Auth , SchemaEditor)) -> [Plugins] ->  R.Dynamic InformationSchema
keyTables schemaVar (schema ,user) authMap pluglist =  maybe (keyTablesInit schemaVar (schema,user) authMap pluglist ) return.  HM.lookup schema  =<< liftIO (atomically $ readTVar .globalRef =<< readTVar schemaVar )

extendedRel :: HM.HashMap (Text,Text) Key -> Text -> Text -> Text -> Key -> Rel Key
extendedRel inf t a b c =  snd access $ (lrel (fst access))

    where path :: [Text]
          path = T.splitOn "->" a
          lrel :: Text -> Rel Key
          lrel t =  Rel (justError "no key" $ HM.lookup (t ,  last path) inf ) (readBinaryOp b) c
          access :: (Text, Rel Key -> Rel Key)
          access = F.foldl' cons  (t,id) (init path)
            where
              cons (t,j) i = (snd $ inlineName $ keyType  k ,j . RelAccess k )
                where
                  k :: Key
                  k = justError "no key" $HM.lookup (t,i) inf

keyTablesInit schemaRef  (schema,user) authMap pluglist = do
       schemaVar <- liftIO$ atomically $ readTVar schemaRef
       let conn = schemaConn schemaVar
           schemaId = justLookH schema (schemaNameMap schemaVar)
       (oauth,ops ) <- liftIO$ authMap schema
       color <- liftIO$ query conn "SELECT color FROM metadata.schema_style where schema = ? " (Only schemaId )
       [Only uid] <- liftIO$ query conn "select oid from metadata.\"user\" where usename = ?" (Only user)
       uniqueMap <- liftIO$join $ mapM (\(t,c,op,mod,tr) -> ((t,c),) .(\ un -> (\def ->  Key c tr (V.toList $ fmap readFModifier mod) op def un )) <$> newUnique) <$>  query conn "select o.table_name,o.column_name,ordinal_position,field_modifiers,translation from  metadata.columns o left join metadata.table_translation t on o.column_name = t.column_name   where table_schema = ? "(Only schema)
       res2 <- liftIO$ fmap ( (\i@(t,c,j,k,del,l,m,d,z,b,typ)-> (t,) $ (\ty -> (justError ("no unique" <> show (t,c,fmap fst uniqueMap)) $  M.lookup (t,c) (M.fromList uniqueMap) )  (join$ fromShowable2 (mapKType ty) .  BS.pack . T.unpack <$> join (fmap (\v -> if testSerial v then Nothing else Just v) (join $ listToMaybe. T.splitOn "::" <$> m) )) ty )  (createType  (j,k,del,l,maybe False testSerial m,d,z,b,typ)) )) <$>  query conn "select table_name,column_name,is_nullable,is_array,is_delayed,is_range,col_def,is_composite,type_schema,type_name ,atttypmod from metadata.column_types where table_schema = ?"  (Only schema)
       let
          keyList =  fmap (\(t,k)-> ((t,keyValue k),k)) res2
          backendkeyMap = M.fromList keyList
          keyMap = fmap (typeTransform ops ) $ HM.fromList keyList

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

       authorization <- liftIO$ queryAuthorization conn schemaId uid
       descMap <- liftIO$ M.fromList . fmap  (\(t,cs)-> (t,fmap (\c -> justError (show (t,c)) $ HM.lookup (t,c) keyMap) (V.toList cs)) ) <$> query conn "SELECT table_name,description FROM metadata.table_description WHERE table_schema = ? " (Only schema)
       transMap <- liftIO$ M.fromList   <$> query conn "SELECT \"table\",translation FROM metadata.table_name_translation WHERE schema = ? " (Only schemaId )
       uniqueConstrMap <- liftIO$ M.fromListWith (++) . fmap (fmap pure)   <$> query conn "SELECT table_name,pks FROM metadata.unique_sets WHERE schema_name = ? " (Only schema)
       indexMap <- liftIO$ M.fromListWith (++) . fmap (fmap pure)   <$> query conn "SELECT table_name,columns FROM metadata.catalog_indexes WHERE schema_name = ? " (Only schema)

       res <- liftIO$ lookupPK <$> query conn "SELECT oid,t.table_name,pks,scopes,s.table_name is not null FROM metadata.tables t left join metadata.pks  p on p.schema_name = t.schema_name and p.table_name = t.table_name left join metadata.sum_table s on s.schema_name = t.schema_name and t.table_name = s.table_name where t.schema_name = ?" (Only schema)

       resTT <- liftIO$ fmap readTT . M.fromList <$> query conn "SELECT table_name,table_type FROM metadata.tables where schema_name = ? " (Only schema)

       let
        schemaForeign :: Query
        schemaForeign = "select target_schema_name from metadata.fks where origin_schema_name = ? and target_schema_name <> origin_schema_name"
       rslist <- liftIO$query conn  schemaForeign (Only schema)
       rsch <- HM.fromList <$> mapM (\(Only s) -> (s,) <$> keyTables  schemaRef (s,user) authMap pluglist) rslist
       let
           map s
              | s == schema = keyMap
              | otherwise = _keyMapL (justError "no schema" $ HM.lookup s rsch)
           lookRFk s t k = V.toList $ fmap  (lookupKey' (map s) t) k

       let
          foreignKeys :: Query
          foreignKeys = "select origin_table_name,target_schema_name,target_table_name,origin_fks,target_fks,rel_fks from metadata.fks where origin_schema_name = ?"
          functionKeys :: Query
          functionKeys = "select table_name,schema_name,column_name,cols,fun from metadata.function_keys where schema_name = ?"
          exforeignKeys :: Query
          exforeignKeys = "select origin_table_name,target_schema_name,target_table_name,origin_fks,target_fks,rel_fks from metadata.extended_view_fks where origin_schema_name = ?"

       fks <- liftIO$ M.fromListWith mappend . fmap (\i@(tp,sc,tc,kp,kc,rel) -> (tp,  pure ( FKJoinTable (zipWith3 (\a b c -> Rel a (readBinaryOp b) c) (lookFk tp kp ) (V.toList rel) (lookRFk sc tc kc)) (sc,tc)) )) <$> query conn foreignKeys (Only schema)
       efks <- liftIO$ M.fromListWith mappend . fmap (\i@(tp,sc,tc,kp,kc,rel) -> (tp, pure ( FKJoinTable (zipWith3 (\a b c -> extendedRel keyMap tp a b c)  (V.toList kp ) (V.toList rel) (lookRFk sc tc kc)) (sc,tc)) )) <$> query conn exforeignKeys (Only schema) :: R.Dynamic (Map Text [SqlOperation ])


       functionsRefs <- liftIO$ M.fromListWith mappend . fmap (\i@(tp,sc::Text,tc,cols,fun) -> (tp,  pure( FunctionField tc (readFun fun) (head . indexer <$> V.toList cols ) ) )) <$> query conn functionKeys (Only schema):: R.Dynamic (Map Text [SqlOperationK Text] )
       let all =  M.fromList $ fmap (\(c,l)-> (c,S.fromList $ fmap (\(t,n)-> (\(Just i) -> i) $ HM.lookup (t,keyValue n) keyMap ) l )) $ groupSplit (\(t,_)-> t)  $ (fmap (\((t,_),k) -> (t,k))) $  HM.toList keyMap :: Map Text (Set Key)
       let i3lnoFun = fmap (\(c,(un,pksl,scp,is_sum))->
                               let
                                  pks = F.toList pksl
                                  inlineFK =  fmap (\k -> (\t ->  (  FKInlineTable k $ inlineName t) ) $ keyType k ) .  filter (isInline .keyType ) .  S.toList <$> M.lookup c all
                                  attrMap =  M.fromList $ fmap (\i -> (keyPosition i,i)) $ S.toList $ justError "no attr" $ M.lookup c (all)
                                  attr = S.toList $ S.difference (justError ("no collumn" <> show c) $ M.lookup c all) ( S.fromList $ (maybe [] id $ M.lookup c descMap) <>  pks)
                               in (c ,Raw un schema  (justLook c resTT) (M.lookup un transMap) (filter (isKDelayed.keyType)  attr) is_sum c (fromMaybe [] (fmap ( fmap (lookupKey c )  . V.toList) <$> M.lookup c uniqueConstrMap)) (fromMaybe [] (fmap ( fmap (justError "no key" . flip M.lookup  attrMap)  . V.toList) <$> M.lookup c indexMap))   (F.toList scp) pks (maybe [] id $ M.lookup  c descMap) (fromMaybe []  $ (M.lookup c efks )<>(M.lookup c fks )<>  inlineFK  ) attr )) res :: [(Text,Table)]
       let
           unionQ = "select schema_name,table_name,inputs from metadata.table_union where schema_name = ?"

           tableMapPre = HM.singleton schema (HM.fromList i3lnoFun)
           addRefs table = maybe table (\r -> Le.over rawFKSL (mappend (fmap liftFun r)) table) ref
             where ref =  M.lookup (tableName table) functionsRefs
                   liftFun ( (FunctionField k s a) ) =   (FunctionField (lookupKey' (map ts) tn k) s (liftASch tableMapPre ts tn <$> a))
                   tn = tableName table
                   ts = rawSchema table

           i3l =fmap addRefs <$> i3lnoFun
       ures <- fmap rights $ liftIO $ decodeViews conn schema
       let
           i3 =  addRecInit (HM.singleton schema (HM.fromList i3l ) <> foldr mappend mempty (tableMap <$> F.toList  rsch)) $  HM.fromList i3l
           pks = M.fromList $ fmap (\(_,t)-> (S.fromList$ rawPK t ,t)) $ HM.toList i3
           i2 =    M.filterWithKey (\k _ -> not.S.null $ k )  pks
           unionT (s,n ,_ ,Select _ _ _) = (n,id)
           unionT (s,n,_,SqlUnion (Select _ (FromRaw _ i) _ )  (Select _ (FromRaw _ j) _) )
             = (n ,(\t -> Project t ( Union ((\t -> justError "no key" $ HM.lookup (T.pack . BS.unpack $ t) i3 )<$>  [i,j] )) ))
       let
           i3u = foldr (uncurry HM.adjust. swap ) i3 (unionT <$> ures)
           i2u = foldr (uncurry M.adjust. swap) i2 (first (\tn -> justError ("no union table" ++ show tn ). fmap (\(_,i,_,_) ->S.fromList $ F.toList i)  $ M.lookup tn (M.fromList res)) . unionT <$> ures)
       sizeMapt <- liftIO$ M.fromList . catMaybes . fmap  (\(t,cs)-> (,cs) <$>  HM.lookup t i3u ) <$> query conn tableSizes (Only schema)

       metaschema <- if (schema /= "metadata")
          then Just <$> keyTables  schemaRef ("metadata",user) authMap pluglist
          else return Nothing

       mvar <- liftIO$ atomically $ newTVar  M.empty
       let colMap =  fmap IM.fromList $ HM.fromListWith mappend $ (\((t,_),k) -> (t,[(keyPosition k,k)])) <$>  HM.toList keyMap
       let inf = InformationSchema schemaId schema (fmap unOnly $ listToMaybe color) (uid,user) oauth keyMap colMap (M.fromList $ (\k -> (keyFastUnique k ,k))  <$>  F.toList backendkeyMap  )  (M.fromList $ fmap (\i -> (keyFastUnique i,i)) $ F.toList keyMap) (M.filterWithKey (\k v -> not $ L.elem (tableName v )  convert) $ i2u )  i3u sizeMapt mvar  conn metaschema  rsch ops pluglist schemaRef
           convert = (concat $ fmap (\(_,_,_,n) -> deps  n) ures)
           deps (SqlUnion (Select _ (FromRaw _ i) _)  (Select _ (FromRaw _ j) _)) = fmap (T.pack.BS.unpack) [i,j]
           deps (Select _ _ _ ) = []


       liftIO $print (schema,keyMap)
       var <- liftIO$ atomically $ modifyTVar (globalRef schemaVar  ) (HM.insert schema inf )
       -- addStats inf
         {-
       traverse (\ req -> do
         r <- liftIO$ forkIO $ forever $
           R.runDynamic $ do
             liftIO$ threadDelay $60*10^6
             transaction inf  req
         R.registerDynamic (killThread r)) $ historySync ops
-}

       return inf

isUnion (Project _ (Union _ )) = True
isUnion _ = False


-- Search for recursive cycles and tag the tables
addRecInit :: HM.HashMap Text (HM.HashMap Text Table) -> HM.HashMap Text Table -> HM.HashMap Text Table
addRecInit inf m = fmap recOverFKS m
  where
        recOverFKS t  = t Le.& rawFKSL Le.%~ map path
          where
                path :: SqlOperation -> SqlOperation
                path i@(FunctionField _ _ _ ) = i
                path pini = case  L.filter (not .L.null) $ openPath S.empty [] pini of
                              [] -> if (tname pini) == tableName t then  RecJoin (MutRec []) pini else pini
                              e -> RecJoin (MutRec e) pini
                    where
                      tname :: SqlOperation -> Text
                      tname (FKInlineTable _ nt) = snd nt
                      tname (FKJoinTable _ nt) = snd nt
                      openPath :: S.Set SqlOperation -> [[Rel Key]] -> SqlOperation -> [[[Rel Key]]]
                      openPath ts p pa@(FKInlineTable _ nt )
                        | snd nt == tableName t = [p]
                        | S.member pa ts =  []
                        | otherwise = openTable (S.insert pa ts) p nt
                      openPath ts p pa@((FKJoinTable  _ nt) )
                        | snd nt == tableName t  = [p]
                        | S.member pa ts =  []
                        | otherwise = openTable (S.insert pa ts)  p nt
                      openPath ts p (FunctionField _ _ _) = []
                      -- openTable :: Set (SqlOperation) -> [[Rel Key]] -> a -> [[[Rel Key]]]
                      openTable t p (st,nt)  =  do
                                let
                                    cons :: SqlOperation -> [[Rel Key]]
                                    cons pa
                                      -- | pa == pini = p
                                      | otherwise = p <> [F.toList (pathRelRel $unRecRel pa)]
                                ix <- fmap (\pa-> openPath t (cons pa ) (unRecRel pa)) fsk
                                return (concat (L.filter (not.L.null) ix))
                        where tb = justError ("no table" <> show (nt,m)) $ join $ HM.lookup nt <$> (HM.lookup st inf)
                              fsk :: [SqlOperation]
                              fsk = F.toList $ rawFKS tb




newKey name ty p = do
  un <- newUnique
  return $ Key name Nothing    [FRead,FWrite] p Nothing un ty


catchPluginException :: InformationSchema -> Int -> Int -> Map Key ( FTB Showable) -> IO a -> IO (Either Int a)
catchPluginException inf pname tname  idx i = do
  (Right <$> i) `catch` (\e  -> do
                t <- getCurrentTime
                print (t,e :: SomeException)
                id  <- query (rootconn inf) "INSERT INTO metadata.plugin_exception (\"user\",\"schema\",\"table\",\"plugin\",exception,data_index2,instant) values(?,?,?,?,?,? :: metadata.key_value[] ,?) returning id" (fst $ username inf , schemaId inf,pname,tname,Binary (B.encode $ show (e :: SomeException)) ,V.fromList (  (fmap (TBRecord2  . second (Binary . B.encode) . first keyValue) (M.toList idx)) ) , t )
                return (Left (unOnly $ head $id)))


logTableModification
  ::
     InformationSchema
     -> TableModification (RowPatch Key Showable)  -> IO (TableModification (RowPatch Key Showable))
logTableModification inf (TableModification Nothing ts u table ip) = do
  let i = fmap patchNoRef $ case ip of
            PatchRow i -> i
            DropRow i -> (G.Idex mempty,patch i)
            CreateRow i -> (G.Idex mempty,patch i)
  time <- getCurrentTime
  env <- lookupEnv "ROOT"
  let mod = modificationEnv env
  let ltime =  utcToLocalTime utc $ time
      (G.Idex pidx,pdata) = firstPatch keyValue  <$> i

  [Only id] <- liftIO $ query (rootconn inf) (fromString $ T.unpack $ "INSERT INTO metadata." <> mod <> " (\"user_name\",modification_time,\"table_name\",data_index,modification_data  ,\"schema_name\") VALUES (?,?,?,?::bytea[],? ,?) returning modification_id " ) (snd $ username inf ,ltime,tableName table, V.fromList $ (  fmap  (Binary . B.encode)   pidx ) , Binary  . B.encode $firstPatchRow keyValue ip, schemaName inf)
  let modt = lookTable (meta inf)  mod
  (dbref ,_)<- R.runDynamic $ prerefTable (meta inf) modt

  putPatch (patchVar dbref) [liftPatchRow (meta inf) (modificationEnv env)  $ CreateRow $ encodeT (TableModification (Just id) ts u (schemaName inf,tableName table ) (firstPatchRow keyValue ip ) )]
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

idex inf t v = G.Idex $  fmap snd $ L.sortBy (comparing ((`L.elemIndex` (rawPK $ lookTable inf t)).fst)) $ first (lookKey inf t  ) <$> v

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
  where map = justError ("notype" <> T.unpack (showKey v)) $ M.lookup (keyFastUnique v)  (backendsKey inf )


liftASch :: TableMap  -> Text -> Text -> Access Text  -> Access Key
liftASch inf s tname (IProd b l) = IProd b $ lookKey  l
  where
    tb = lookup tname $  lookup s inf
    lookup i m = justError ("no look" <> show i) $ HM.lookup i m
    lookKey c = justError "no attr" $ L.find ((==c).keyValue ) (tableAttrs tb)

liftASch inf s tname (Nested i c) = Nested ref (liftASch inf sch st <$> c)
  where
    ref = liftASch inf s tname <$> i
    lookup i m = justError ("no look" <> show i) $ HM.lookup i m
    tb = lookup tname $  lookup s inf
    rel  = justError "no fk" $ L.find (\i -> S.fromList (iprodRef <$> ref )== (S.map _relOrigin $ pathRelRel i) ) (rawFKS tb)
    (sch,st) = case rel of
          FKJoinTable  _ l -> l
          FKInlineTable  _ l -> l



