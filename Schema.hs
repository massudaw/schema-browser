{-# LANGUAGE FlexibleContexts,ConstraintKinds,TypeFamilies,RankNTypes, TupleSections,BangPatterns,OverloadedStrings #-}


module Schema where

import Data.String
import Types
import Codec.Compression.GZip
import Step.Common
import Data.Tuple
import Control.Concurrent.STM.TQueue
import Control.Concurrent.STM
import Types.Patch
import System.Directory
import qualified Types.Index as G

import SchemaQuery
import qualified NonEmpty as Non
import Control.Monad.Writer
import Debug.Trace
import Prelude hiding (head)
import Data.Unique
import qualified Data.Foldable as F
import Data.Maybe
import qualified Data.Binary as B
import GHC.Stack
import Data.Bifunctor(second,first)
import Utils
import Control.Exception
import Control.Monad.Reader
import qualified Control.Lens as Le

import Data.Functor.Identity
import Database.PostgreSQL.Simple
import Data.Time
import RuntimeTypes

import Data.Traversable(sequenceA,traverse)
import Data.Vector (Vector)
import qualified Data.Vector as V

import Control.Applicative
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Map (Map)
import Data.Set (Set)
import Control.Concurrent

import Data.Text (Text)
import qualified Data.Text as T

import qualified Reactive.Threepenny as R

import Query
import Postgresql.Parser
import qualified Data.ByteString.Char8 as BS
import qualified Data.ByteString.Lazy as BSL


createType :: (Bool,Bool,Bool,Bool,Bool,Bool,Text,Text) -> KType (Prim (Text,Text) (Text,Text))
createType  (isNull,isArray,isDelayed,isRange,isDef,isComp,tysch,tyname)
  = comp (Primitive base)
  where
    add i v = if i then v else id
    comp = add isNull KOptional . add isArray KArray . add isRange KInterval . add isDef KSerial . add isDelayed KDelayed
    base
      | isComp =  RecordPrim (tysch ,tyname)
      | otherwise = AtomicPrim (tysch ,tyname)


recoverFields :: InformationSchema -> FKey (KType (Prim KPrim  (Text,Text))) -> FKey (KType (Prim PGType PGRecord))
recoverFields inf v = map
  where map = justError ("notype" <> T.unpack (showKey v)) $ M.lookup (keyFastUnique v)  (backendsKey inf )

meta inf = maybe inf id (metaschema inf)




queryAuthorization :: Connection -> Text -> Text -> IO (Map Text [Text])
queryAuthorization conn schema user = do
    sq <- query conn aq (schema,user)
    let convert (tname,authorizations) = (tname ,V.toList authorizations)
    return $ M.fromList $ convert <$> sq
  where aq = "select table_name,authorizations from metadata.authorization where table_schema = ? and grantee = ? "

tableSizes = "SELECT c.relname,c.reltuples::bigint AS estimate FROM   pg_class c JOIN   pg_namespace n ON c.relkind = 'r' and n.oid = c.relnamespace WHERE n.nspname = ? "

-- fromShowable2 i j | traceShow (i,j) False = errorWithStackTrace ""
fromShowable2 i@(Primitive (AtomicPrim PText )) v = fromShowable i $  BS.drop 1 (BS.init v)
fromShowable2 i v = fromShowable i v

testSerial  =((=="nextval"). fst . T.break(=='('))

readFModifier :: Text -> FieldModifier
readFModifier "read" = FRead
readFModifier "edit" = FPatch
readFModifier "write" = FWrite


keyTables ,keyTablesInit :: MVar (Map Text InformationSchema )->  Connection -> (Text ,Text) -> (Text -> IO (Auth , SchemaEditor)) -> [Plugins] ->  IO InformationSchema
keyTables schemaVar conn (schema ,user) authMap pluglist = maybe (keyTablesInit schemaVar conn (schema,user) authMap pluglist ) return  . (M.lookup schema ) =<< readMVar schemaVar


extendedRel :: Map (Text,Text) Key -> Text -> Text -> Text -> Key -> Rel Key
extendedRel inf t a b c =  snd access $ (lrel (fst access))

    where path :: [Text]
          path = T.splitOn "->" a
          lrel :: Text -> Rel Key
          lrel t =  Rel (justLook (t ,  last path) inf ) b c
          access :: (Text, Rel Key -> Rel Key)
          access = foldl cons  (t,id) (init path)
            where
              cons (t,j) i = (snd $ inlineName $ keyType  k ,j . RelAccess k )
                where
                  k :: Key
                  k = justLook (t,i) inf

keyTablesInit schemaVar conn (schema,user) authMap pluglist = do
       (oauth,ops ) <- authMap schema
       uniqueMap <- join $ mapM (\(t,c,op,mod,tr) -> ((t,c),) .(\ un -> (\def ->  Key c tr (V.toList $ fmap readFModifier mod) op def un )) <$> newUnique) <$>  query conn "select o.table_name,o.column_name,ordinal_position,field_modifiers,translation from  metadata.columns o left join metadata.table_translation t on o.column_name = t.column_name   where table_schema = ? "(Only schema)
       res2 <- fmap ( (\i@(t,c,j,k,del,l,m,d,z,b)-> (t,) $ (\ty -> (justError ("no unique" <> show (t,c,fmap fst uniqueMap)) $  M.lookup (t,c) (M.fromList uniqueMap) )  (join $ fromShowable2 (mapKType ty) .  BS.pack . T.unpack <$> join (fmap (\v -> if testSerial v then Nothing else Just v) (join $ listToMaybe. T.splitOn "::" <$> m) )) ty )  (createType  (j,k,del,l,maybe False testSerial m,d,z,b)) )) <$>  query conn "select table_name,column_name,is_nullable,is_array,is_delayed,is_range,col_def,is_composite,type_schema,type_name from metadata.column_types where table_schema = ?"  (Only schema)
       let
          keyList =  fmap (\(t,k)-> ((t,keyValue k),k)) res2
          backendkeyMap = M.fromList keyList
          keyMap = fmap (typeTransform ops ) $ M.fromList keyList
          lookupKey3 :: (Functor f) => f (Text,Maybe (Vector Text),Maybe (Vector Text),Bool) -> f (Text,(Vector Key,Vector Key,Bool))
          lookupKey3 = fmap  (\(t,c,s,b)-> (t,(maybe V.empty (fmap (\ci -> justError ("no key " <> T.unpack ci <> " " <> T.unpack t ) $ M.lookup (t,ci) keyMap)) c,maybe V.empty (fmap (\ci -> justError ("no key " <> T.unpack ci) $ M.lookup (t,ci) keyMap)) s,b)) )
          lookupKey2 :: Functor f => f (Text,Text) -> f Key
          lookupKey2 = fmap  (\(t,c)-> justError ("nokey" <> show (t,c)) $ M.lookup ( (t,c)) keyMap )
          lookupKey ::  (Text,Text) ->  Key
          lookupKey = (\(t,c)-> justError ("nokey" <> show (t,c)) $ M.lookup ( (t,c)) keyMap )
          readTT :: Text ->  TableType
          readTT "BASE TABLE" = ReadWrite
          readTT "VIEW" = ReadOnly
          readTT i =  errorWithStackTrace  $ T.unpack i
       authorization <- queryAuthorization conn schema user
       descMap <- M.fromList . fmap  (\(t,cs)-> (t,fmap (\c -> (\(Just i) -> i) $ M.lookup (t,c) keyMap) (V.toList cs)) ) <$> query conn "SELECT table_name,description FROM metadata.table_description WHERE table_schema = ? " (Only schema)
       transMap <- M.fromList   <$> query conn "SELECT table_name,translation FROM metadata.table_name_translation WHERE schema_name = ? " (Only schema)
       uniqueConstrMap <- M.fromListWith (++) . fmap (fmap pure)   <$> query conn "SELECT table_name,pks FROM metadata.unique_sets WHERE schema_name = ? " (Only schema)

       res <- lookupKey3 <$> query conn "SELECT t.table_name,pks,scopes,s.table_name is not null FROM metadata.tables t left join metadata.pks  p on p.schema_name = t.schema_name and p.table_name = t.table_name left join metadata.sum_table s on s.schema_name = t.schema_name and t.table_name = s.table_name where t.schema_name = ?" (Only schema)
       resTT <- fmap readTT . M.fromList <$> query conn "SELECT table_name,table_type FROM metadata.tables where schema_name = ? " (Only schema) :: IO (Map Text TableType)

       let
        schemaForeign :: Query
        schemaForeign = "select target_schema_name from metadata.fks where origin_schema_name = ? and target_schema_name <> origin_schema_name"
       rslist <- query conn  schemaForeign (Only schema)
       rsch <- M.fromList <$> mapM (\(Only s) -> (s,) <$> keyTables  schemaVar conn (s,user) authMap pluglist) rslist
       let lookFk t k = V.toList $ lookupKey2 (fmap (t,) k)
           lookRFk s t k = V.toList $ lookupKey2 (fmap (t,) k)
            where
              lookupKey2 :: Functor f => f (Text,Text) -> f Key
              lookupKey2 = fmap  (\(t,c)-> justError ("nokey" <> show (t,c)) $ M.lookup ( (t,c)) map)
                where map
                        | s == schema = keyMap
                        | otherwise = _keyMapL (justError "no schema" $ M.lookup s rsch)
       let
          foreignKeys :: Query
          foreignKeys = "select origin_table_name,target_schema_name,target_table_name,origin_fks,target_fks,rel_fks from metadata.fks where origin_schema_name = ?"
          exforeignKeys :: Query
          exforeignKeys = "select origin_table_name,target_schema_name,target_table_name,origin_fks,target_fks,rel_fks from metadata.extended_view_fks where origin_schema_name = ?"
       fks <- M.fromListWith S.union . fmap (\i@(tp,sc,tc,kp,kc,rel) -> (tp,S.singleton $ Path (S.fromList $ lookFk tp kp) ( FKJoinTable (zipWith3 (\a b c -> Rel a b c) (lookFk tp kp ) (V.toList rel) (lookRFk sc tc kc)) (sc,tc)) )) <$> query conn foreignKeys (Only schema) :: IO (Map Text (Set (Path (Set Key) (SqlOperation ) )))
       efks <- M.fromListWith S.union . fmap (\i@(tp,sc,tc,kp,kc,rel) -> (tp,S.singleton $ Path (S.fromList $ lookFk tp (head . T.splitOn "->" <$> kp)) ( FKJoinTable (zipWith3 (\a b c -> extendedRel keyMap tp a b c)  (V.toList kp ) (V.toList rel) (lookRFk sc tc kc)) (sc,tc)) )) <$> query conn exforeignKeys (Only schema) :: IO (Map Text (Set (Path (Set Key) (SqlOperation ) )))


       let all =  M.fromList $ fmap (\(c,l)-> (c,S.fromList $ fmap (\(t,n)-> (\(Just i) -> i) $ M.lookup (t,keyValue n) keyMap ) l )) $ groupSplit (\(t,_)-> t)  $ (fmap (\((t,_),k) -> (t,k))) $  M.toList keyMap :: Map Text (Set Key)
           i3l =  (\(c,(pksl,scp,is_sum))-> let
                                  pks = F.toList pksl
                                  inlineFK =  fmap (\k -> (\t -> Path (S.singleton k ) (  FKInlineTable $ inlineName t) ) $ keyType k ) .  filter (isInline .keyType ) .  S.toList <$> M.lookup c all
                                  attr = S.difference ((\(Just i) -> i) $ M.lookup c all) ((S.fromList $ (maybe [] id $ M.lookup c descMap) )<> S.fromList pks)
                                in (c ,Raw schema  ((\(Just i) -> i) $ M.lookup c resTT) (M.lookup c transMap) (S.filter (isKDelayed.keyType)  attr) is_sum c (fromMaybe [] (fmap (S.fromList . fmap (lookupKey .(c,) )  . V.toList) <$> M.lookup c uniqueConstrMap)) (maybe [] id $ M.lookup c authorization)  (F.toList scp) pks (maybe [] id $ M.lookup  c descMap) (fromMaybe S.empty $ (M.lookup c efks )<>(M.lookup c fks )<> fmap S.fromList inlineFK ) S.empty attr [])) <$> res :: [(Text,Table)]
           unionQ = "select schema_name,table_name,inputs from metadata.table_union where schema_name = ?"
       ures <- query conn unionQ (Only schema) :: IO [(Text,Text,Vector Text)]
       let
           i3 = addRecInit (M.singleton schema (M.fromList i3l ) <> foldr mappend mempty (tableMap <$> F.toList  rsch)) $  M.fromList i3l
           pks = M.fromList $ fmap (\(_,t)-> (S.fromList$ rawPK t ,t)) $ M.toList i3
           i2 =   M.filterWithKey (\k _ -> not.S.null $ k )  pks
           unionT (s,n,l) = (n ,(\t -> t { rawUnion =  ((\t -> justLook t i3 )<$>  F.toList l )} ))
       let
           i3u = foldr (uncurry M.adjust. swap ) i3 (unionT <$> ures)
           i2u = foldr (uncurry M.adjust. swap) i2 (first (justError "no union table" . fmap (\(i,_,_) ->S.fromList $ F.toList i) . flip M.lookup (M.fromList res)) . unionT <$> ures)
       sizeMapt <- M.fromList . catMaybes . fmap  (\(t,cs)-> (,cs) <$>  M.lookup t i3u ) <$> query conn tableSizes (Only schema)

       metaschema <- if (schema /= "metadata")
          then Just <$> keyTables  schemaVar conn ("metadata",user) authMap pluglist
          else return Nothing

       mvar <- atomically $ newTMVar  M.empty
       let inf = InformationSchema schema user oauth keyMap (M.fromList $ (\k -> (keyFastUnique k ,k))  <$>  F.toList backendkeyMap  )  (M.filterWithKey (\k v -> not $ L.elem (tableName v ) (concat $ fmap (\(_,_,n) -> F.toList n) ures)) $ i2u)  i3u sizeMapt mvar  conn metaschema  rsch ops pluglist
       varmap <- mapM (createTableRefs inf) (filter (L.null . rawUnion) $ F.toList i2u)
       let preinf = InformationSchema schema user oauth keyMap (M.fromList $ (\k -> (keyFastUnique k ,k))  <$>  F.toList backendkeyMap  )  i2u  i3u sizeMapt undefined conn undefined rsch ops pluglist
       varmapU <- mapM (createTableRefsUnion preinf (M.fromList varmap)) (filter (not . L.null . rawUnion) $ F.toList i2u)
       atomically $ takeTMVar mvar >> putTMVar mvar  (M.fromList $ varmap <> varmapU)
       var <- modifyMVar_  schemaVar   (return . M.insert schema inf )
       addStats inf
       return inf


takeMany mvar = go . (:[]) =<< readTQueue mvar
  where
    go v = do
      i <- tryReadTQueue mvar
      maybe (return (reverse v )) (go . (:v)) i

createTableRefsUnion inf m i  = do
  t <- getCurrentTime
  let
      diffIni :: [TBIdx Key Showable]
      diffIni = []
  mdiff <-  atomically $ newTQueue
  (iv,v) <- readTable inf "dump" (schemaName inf) (i)
  (patch,hdiff) <- R.newEvent
  let
      patchUni = fmap concat $ R.unions $ R.rumors . patchTid .(justError "no table union" . flip M.lookup m) . tableMeta <$>  (rawUnion i)
      patch =  fmap patchunion <$> patchUni
      patchunion  = liftPatch inf (tableName i ) .firstPatch keyValue
  R.onEventIO patch (hdiff)
  midx <-  atomically$ newTMVar iv
  bh <- R.accumB v (flip (L.foldl' apply) <$> patch )
  let bh2 = (R.tidings bh (L.foldl' apply  <$> bh R.<@> patch ))
  bhdiff <- R.stepper diffIni patch
  (eidx ,hidx) <- R.newEvent
  bhidx <- R.stepper M.empty eidx

  forkIO $ forever $ (do
      forkIO . hidx =<< atomically (takeTMVar midx)
      return () ) `catch` (\e -> print ("block index",tableName i ,e :: SomeException))
  forkIO $ forever $ (do
      patches <- atomically $ takeMany mdiff
      when (not $ L.null $ concat patches) $ do
        (void $ hdiff (concat patches))) `catch` (\e -> print ("block data",tableName i ,e :: SomeException))
  return (tableMeta i,  DBVar2  mdiff midx (R.tidings bhdiff patch) (R.tidings bhidx eidx) bh2 )


createTableRefs :: InformationSchema -> Table -> IO (KVMetadata Key,DBVar)
createTableRefs inf i = do
  t <- getCurrentTime
  let
      diffIni :: [TBIdx Key Showable]
      diffIni = []
  mdiff <-  atomically $ newTQueue
  (ediff,hdiff) <- R.newEvent
  (iv,v) <- readTable inf "dump" (schemaName inf) (i)
  midx <-  atomically$ newTMVar iv
  bh <- R.accumB v (flip (L.foldl' apply) <$> ediff )
  let bh2 = (R.tidings bh (L.foldl' apply  <$> bh R.<@> ediff ))
  bhdiff <- R.stepper diffIni ediff
  (eidx ,hidx) <- R.newEvent
  bhidx <- R.stepper (M.singleton (LegacyPredicate []) (G.size v,M.empty)) eidx
  forkIO $ forever $ (do
      forkIO . hidx =<< atomically (takeTMVar midx)
      return () ) `catch` (\e -> print ("block index",tableName i ,e :: SomeException))
  forkIO $ forever $ (do
      patches <- atomically $ takeMany mdiff
      when (not $ L.null $ concat patches) $ do
        (void $ hdiff (concat patches))) `catch` (\e -> print ("block data ",tableName i ,e :: SomeException))
  return (tableMeta i,  DBVar2  mdiff midx (R.tidings bhdiff ediff) (R.tidings bhidx eidx) bh2 )


-- Search for recursive cycles and tag the tables
addRecInit :: Map Text (Map Text Table) -> Map Text Table -> Map Text Table
addRecInit inf m = fmap recOverFKS m
  where
        recOverFKS t  = t Le.& rawFKSL Le.%~ S.map path
          where
                path pini@(Path k rel ) =
                    Path k (case rel of
                      FKInlineTable nt  -> case  L.filter (not .L.null) $ openPath S.empty [] pini of
                              [] -> if snd nt == tableName t then  RecJoin (MutRec []) (FKInlineTable nt) else FKInlineTable nt
                              e -> RecJoin (MutRec e) (FKInlineTable nt)
                      FKJoinTable b nt -> case L.filter (not .L.null) $  openPath S.empty [] pini of
                              [] -> if snd nt == tableName t then  RecJoin (MutRec []) (FKJoinTable  b nt) else FKJoinTable  b nt
                              e -> RecJoin (MutRec e) (FKJoinTable  b nt)
                      )
                    where
                      openPath ts p pa@(Path _(FKInlineTable nt) )
                        | snd nt == tableName t = [p]
                        | S.member pa ts =  []
                        | otherwise = openTable (S.insert pa ts) p nt
                      openPath ts p pa@(Path _(FKJoinTable  _ nt) )
                        | snd nt == tableName t  = [p]
                        | S.member pa ts =  []
                        | otherwise = openTable (S.insert pa ts)  p nt
                      openPath ts p pa = errorWithStackTrace (show (ts,p,pa))
                      openTable t p (st,nt)  =  do
                              let cons pa
                                    | pa == pini = p
                                    | otherwise = p <> [F.toList (pathRelRel (fmap unRecRel pa))]
                              ix <- fmap (\pa-> openPath t ( cons pa ) (fmap unRecRel pa)) fsk
                              return (concat (L.filter (not.L.null) ix))
                        where tb = justError ("no table" <> show (nt,m)) $ join $ M.lookup nt <$> (M.lookup st inf)
                              fsk = F.toList $ rawFKS tb




newKey name ty p = do
  un <- newUnique
  return $ Key name Nothing    [FRead,FWrite] p Nothing un ty


catchPluginException :: InformationSchema -> Text -> Text -> [(Key, FTB Showable)] -> IO (a) -> IO (Either Int (a))
catchPluginException inf pname tname idx i = do
  (Right <$> i) `catch` (\e  -> do
                t <- getCurrentTime
                print (t,e)
                id  <- query (rootconn inf) "INSERT INTO metadata.plugin_exception (username,schema_name,table_name,plugin_name,exception,data_index2,instant) values(?,?,?,?,?,?,?) returning id" (username inf , schemaName inf,pname,tname,Binary (B.encode $ show (e :: SomeException)) ,V.fromList (  (fmap (TBRecord2 "metadata.key_value" . second (Binary . B.encode) . first keyValue) idx) ), t )
                return (Left (unOnly $ head $id)))


logTableModification
  :: (B.Binary a ,Ord a, Ord (Index a)) =>
     InformationSchema
     -> TableModification (TBIdx Key a)  -> IO (TableModification (TBIdx Key a))
logTableModification inf (TableModification Nothing table i) = do
  time <- getCurrentTime

  let ltime =  utcToLocalTime utc $ time
      (_,pidx,pdata) = firstPatch keyValue  i
  [Only id] <- liftIO $ query (rootconn inf) "INSERT INTO metadata.modification_table (username,modification_time,table_name,data_index2,modification_data  ,schema_name) VALUES (?,?,?,?,? :: bytea[],?) returning modification_id "  (username inf ,ltime,rawName table, V.fromList <$> nonEmpty (  (fmap (TBRecord2 "metadata.key_value"  . second (Binary . B.encode) ) pidx )) , fmap (Binary  . B.encode ) . V.fromList <$> nonEmpty pdata , schemaName inf)
  return (TableModification (Just id) table i )



dbTable mvar table = do
    mmap <- atomically $readTMVar mvar
    return . justError ("no mvar " <> show table) . M.lookup table $ mmap


mergeCreate (Just i) (Just j) = Just $ mergeTB1 i j
mergeCreate Nothing (Just i) = Just i
mergeCreate (Just i)  Nothing = Just i
mergeCreate Nothing Nothing = Nothing

mergeTB1 ((m,Compose k) ) ((m2,Compose k2) )
  | m == m2 = (m,Compose $ liftA2 (<>) k k2)
  | otherwise = (m,Compose $ liftA2 (<>) k k2) -- errorWithStackTrace (show (m,m2))

ifOptional i = if isKOptional (keyType i) then unKOptional i else i
ifDelayed i = if isKDelayed (keyType i) then unKDelayed i else i





-- Load optional not  loaded delayed values
-- and merge to older values
applyAttr' :: (Patch a,Show a,Ord a ,Show (Index a),G.Predicates (G.TBIndex Key a))  =>  Column Key a  -> PathAttr Key (Index a) -> DBM Key a (Column Key a)
applyAttr' (Attr k i) (PAttr _ p)  = return $ Attr k (apply i p)
applyAttr' sfkt@(FKT iref rel i) (PFK _ p m b )  =  do
                            let ref =  M.mapWithKey (\key vi -> foldl  (\i j ->  edit key j i ) vi p ) (_kvvalues iref)
                                edit  key  k@(PAttr  s _) v = if (_relOrigin $ head $ F.toList $ key) == s then  mapComp (  flip apply k  ) v else v
                            tbs <- atTableS (_kvschema m) m
                            return $ FKT (KV ref ) rel (maybe (joinRel m rel (fmap unTB $ F.toList ref) ( tbs)) id (Just $ create b))
applyAttr' (IT k i) (PInline _   p)  = IT k <$> (applyFTBM (fmap pure $ create) applyRecord' i p)
-- applyAttr' i j = errorWithStackTrace (show ("applyAttr'" :: String,i,j))

applyRecord'
  :: (Patch a,Show a ,Show (Index a), Ord a ,G.Predicates (G.TBIndex Key a)) =>
    TBData Key a
     -> TBIdx Key (Index a)
     -> DBM Key a (TBData Key a)
applyRecord' t@((m, v)) (_ ,_  , k)  = fmap (m,) $ traComp (fmap KV . sequenceA . M.mapWithKey (\key vi -> foldl  (\i j -> i >>= edit key j ) (return vi) k  ) . _kvvalues ) v
  where edit  key  k@(PAttr  s _) v = if (head $ F.toList $ key) == Inline s then  traComp (flip applyAttr' k ) v else return v
        edit  key  k@(PInline s _ ) v = if (head $ F.toList $ key) == Inline s then  traComp (flip applyAttr' k ) v else return v
        edit  key  k@(PFK rel s _ _ ) v = if  key == S.fromList rel then  traComp (flip applyAttr' k ) v else return v

applyTB1'
  :: (Patch a,Index a~ a ,Show a , Ord a,G.Predicates (G.TBIndex Key a) ) =>
    TB2 Key a
     -> PathFTB (TBIdx Key a)
     -> DBM Key a (TB2 Key a)
applyTB1' = applyFTBM (fmap pure $ create) applyRecord'

createAttr' :: (Patch a,Ord a ,Show a ,G.Predicates (G.TBIndex Key a)) => PathAttr Key (Index a) -> DBM Key a (Column Key a)
createAttr' (PAttr  k s  ) = return $ Attr k  (create s)
createAttr' (PInline k s ) = return $ IT k (create s)
createAttr' (PFK rel k s b ) = do
      let ref = (_tb . create <$> k)
      tbs <- atTableS (_kvschema s) s
      return $ FKT (kvlist ref) rel (maybe (joinRel s rel (fmap unTB ref) ( tbs)) id (Just $ create b))
-- createAttr' i = errorWithStackTrace (show i)

createTB1'
  :: (Patch a,Index a~ a ,Show a , Ord a,G.Predicates (G.TBIndex Key a)  ) =>
     (Index (TBData Key a )) ->
     DBM Key a (KVMetadata Key , Compose Identity  (KV (Compose Identity  (TB Identity))) Key  a)
createTB1' (m ,s ,k)  = fmap (m ,)  $ fmap (_tb .KV . mapFromTBList ) . traverse (fmap _tb . createAttr') $  k



type Database k v = InformationSchemaKV k v
type DBM k v = ReaderT (Database k v) IO

atTableS s  k = do
  i <- ask
  k <- liftIO$ dbTable (mvarMap $ fromMaybe i (M.lookup s (depschema i))) k
  (\(DBVar2 _ _   _ _ c)-> liftIO $ R.currentValue (R.facts c)) k


atTable k = do
  i <- ask
  k <- liftIO$ dbTable (mvarMap i) k
  (\(DBVar2 _ _   _ _ c)-> liftIO $ R.currentValue (R.facts c)) k

joinRelT ::  [Rel Key] -> [Column Key Showable] -> Table ->  G.GiST (G.TBIndex Key Showable) (TBData Key Showable) -> TransactionM ( FTB (TBData Key Showable))
joinRelT rel ref tb table
  | L.all (isOptional .keyType) origin = fmap LeftTB1 $ traverse (\ref->  joinRelT (Le.over relOri unKOptional <$> rel ) ref  tb table) (traverse unLeftItens ref )
  | L.any (isArray.keyType) origin = fmap (ArrayTB1 .Non.fromList)$ traverse (\ref -> joinRelT (Le.over relOri unKArray <$> rel ) ref  tb table ) (fmap (\i -> pure $ justError ("cant index  " <> show (i,head ref)). unIndex i $ (head ref)) [0..(Non.length (unArray $ unAttr $ head ref) - 1)])
  | otherwise = maybe (tell (TableModification Nothing tb . patch <$> F.toList tbcreate) >> return tbcreate ) (return .TB1) tbel
      where origin = fmap _relOrigin rel
            tbcreate = TB1 $ tblist' tb (_tb . firstTB (\k -> fromMaybe k  $ M.lookup k relMap ) <$> ref )
            relMap = M.fromList $ (\r ->  (_relOrigin r,_relTarget r) )<$>  rel
            invrelMap = M.fromList $ (\r ->  (_relTarget r,_relOrigin r) )<$>  rel
            tbel = searchGist  invrelMap (tableMeta tb) table (Just ref)

addStats schema = do
  let metaschema = meta schema
  varmap <- atomically $ readTMVar ( mvarMap schema)
  let stats = lookTable metaschema "table_stats"
  (dbpol,(_,polling))<- transactionNoLog metaschema $ eventTable stats  Nothing Nothing [] (LegacyPredicate [])
  let
    row t s ls = tblist . fmap _tb $ [Attr "schema_name" (TB1 (SText (schemaName schema ) )), Attr "table_name" (TB1 (SText t)) , Attr "size" (TB1 (SNumeric s)), Attr "loadedsize" (TB1 (SNumeric ls)) ]
    lrow t dyn st = liftTable' metaschema "table_stats" . row t (maybe (G.size dyn) (maximum .fmap fst ) $  nonEmpty $  F.toList st) $ (G.size dyn)
    lookdiff tb row =  maybe (Just $ patch row ) (\old ->  diff old row ) (G.lookup (G.Idex (M.fromList $ getPKM row)) tb)
  mapM_ (\(m,var)-> do
    let event = R.filterJust $ lookdiff <$> R.facts (collectionTid dbpol ) R.<@> (flip (lrow (_kvname m)) <$>  R.facts (idxTid var ) R.<@> R.rumors (collectionTid  var ) )
    R.onEventIO event (\i -> do
      putPatch (patchVar dbpol) . pure  $ i
      )) (M.toList  varmap)
  return  schema



runDBM inf m = do
    runReaderT m inf


lookPK :: InformationSchema -> (Set Key) -> Table
lookPK inf pk =
      case  M.lookup pk  (pkMap inf) of
           Just table -> table
           i -> errorWithStackTrace (show pk)


dumpSnapshot :: MVar (M.Map T.Text InformationSchema ) -> IO ()
dumpSnapshot smvar = do
  smap <- readMVar smvar
  mapM (uncurry writeSchema) (M.toList smap)
  return ()

writeSchema s v = do
  tmap <- atomically $ readTMVar $ mvarMap v
  let sdir = "dump/"<> (fromString $ T.unpack s)
  hasDir <- doesDirectoryExist sdir
  when (not hasDir ) $  createDirectory sdir
  mapM (uncurry (writeTable sdir) )(M.toList tmap)

writeTable s t v = do
  let tname = s <> "/" <> (fromString $ T.unpack (_kvname t))
  iv <- R.currentValue $ R.facts $ collectionTid v
  iidx <- R.currentValue $ R.facts $ idxTid v
  {-
  let sidx = first (fmap (firstTB keyValue)) . fmap (fmap (fmap (pageFirst keyValue))) <$> M.toList iidx
      sdata = fmap (mapKey' keyValue) $ G.toList $ iv
  when (not (L.null sdata) )$
      BSL.writeFile tname (compress $ B.encode $ (sidx,sdata))
      -}
  return ()

readTable :: InformationSchema -> Text -> Text -> Table -> IO (Collection Key Showable)
readTable inf r s t  = do
  let tname = fromString $ T.unpack $ r <> "/" <> s <> "/" <> tableName t
  has <- doesFileExist tname
  if has
    then do
      return (M.empty ,G.empty)
  --     f <- (Right . decompress . BSL.fromStrict <$> BS.readFile tname ) `catch` (\e -> return $ Left (show (e :: SomeException )))
--        return $  either (const (M.empty ,G.empty)) (\f -> either (const (M.empty,G.empty)) (\(_,_,(m,g)) -> (M.mapKeys (fmap (liftField inf (tableName t) )) $ fmap (fmap ((pageFirst (lookKey inf (tableName t))))) <$> m,createUn (S.fromList $ rawPK t) . fmap (liftTable' inf (tableName t)) $ g )) $ B.decodeOrFail f) f
    else
      return (M.empty ,G.empty)


