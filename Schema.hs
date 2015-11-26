{-# LANGUAGE FlexibleContexts,ConstraintKinds,TypeFamilies,RankNTypes, TupleSections,BangPatterns,OverloadedStrings #-}


module Schema where

import Types
import Control.Monad.Writer
import Debug.Trace
import Prelude hiding (head)
import Data.Unique
import qualified Data.Foldable as F
import Data.Maybe
import Data.String
import Control.Monad.IO.Class
import qualified Data.Binary as B
import GHC.Stack
import Data.Monoid
import Data.Bifunctor(second,first)
import Utils
import Control.Exception
import System.Time.Extra
import Control.Monad.Reader
import qualified Control.Lens as Le

import Data.Functor.Identity
import Database.PostgreSQL.Simple
import Data.Time
import RuntimeTypes

import Data.Traversable(sequenceA,traverse)
import Data.Vector (Vector)
import qualified Data.Vector as V
import Data.IORef
import Network.Google.OAuth2

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
import Postgresql
import Patch
import qualified Data.ByteString.Char8 as BS


createType :: (Bool,Bool,Bool,Bool,Bool,Bool,Text,Text) -> KType (Prim (Text,Text) (Text,Text))
createType  (isNull,isArray,isDelayed,isRange,isDef,isComp,tysch,tyname)
  = comp (Primitive base)
  where
    add i v = if i then v else id
    comp = add isNull KOptional . add isArray KArray . add isRange KInterval . add isDef KSerial . add isDelayed KDelayed
    base
      | isComp =  RecordPrim (tysch ,tyname)
      | otherwise = AtomicPrim (tysch ,tyname)


recoverFields :: InformationSchema -> Table -> FKey (KType (Prim KPrim  (Text,Text))) -> FKey (KType (Prim PGType PGRecord))
recoverFields inf t v = map
  where map = justError "notype" $ M.lookup (rawName t ,keyValue v)  (keyMap inf)

meta inf = maybe inf id (metaschema inf)



foreignKeys :: Query
foreignKeys = "select origin_table_name,target_table_name,origin_fks,target_fks,rel_fks from metadata.fks where origin_schema_name = target_schema_name  and  target_schema_name = ?"


queryAuthorization :: Connection -> Text -> Text -> IO (Map Text [Text])
queryAuthorization conn schema user = do
    sq <- query conn aq (schema,user)
    let convert (tname,authorizations) = (tname ,V.toList authorizations)
    return $ M.fromList $ convert <$> sq
  where aq = "select table_name,authorizations from metadata.authorization where table_schema = ? and grantee = ? "

tableSizes = "SELECT c.relname,c.reltuples::bigint AS estimate FROM   pg_class c JOIN   pg_namespace n ON c.relkind = 'r' and n.oid = c.relnamespace WHERE n.nspname = ? "

fromShowable2 i@(Primitive (AtomicPrim (_, "character varying"))) v = fromShowable i $  BS.drop 1 (BS.init v)
fromShowable2 i@(Primitive (AtomicPrim (_,"text"))) v = fromShowable i $  BS.drop 1 (BS.init v)
fromShowable2 i v = fromShowable i v

testSerial  =((=="nextval"). fst . T.break(=='('))

readFModifier :: Text -> FieldModifier
readFModifier "read" = FRead
readFModifier "edit" = FPatch
readFModifier "write" = FWrite

keyTables :: MVar (Map Text InformationSchema )-> MVar (Map (KVMetadata Key) DBVar ) -> Connection -> Connection -> (Text ,Text)-> Maybe (Text,IORef OAuth2Tokens) -> SchemaEditor ->  IO InformationSchema
keyTables schemaVar mvar conn userconn (schema ,user) oauth ops = maybe (do
       uniqueMap <- join $ mapM (\(t,c,op,mod,tr) -> ((t,c),) .(\ un -> (\def ->  Key c tr (V.toList $ fmap readFModifier mod) op def un )) <$> newUnique) <$>  query conn "select o.table_name,o.column_name,ordinal_position,field_modifiers,translation from  metadata.columns o left join metadata.table_translation t on o.column_name = t.column_name   where table_schema = ? "(Only schema)
       res2 <- fmap ( (\i@(t,c,j,k,del,l,m,d,z,b)-> (t,) $ (\ty -> (justError ("no unique" <> show (t,c,fmap fst uniqueMap)) $  M.lookup (t,c) (M.fromList uniqueMap) )  ( join $ fromShowable2 ty .  BS.pack . T.unpack <$> join (fmap (\v -> if testSerial v then Nothing else Just v) (join $ listToMaybe. T.splitOn "::" <$> m) )) ty )  (createType  (j,k,del,l,maybe False testSerial m,d,z,b)) )) <$>  query conn "select table_name,column_name,is_nullable,is_array,is_delayed,is_range,col_def,is_composite,type_schema,type_name from metadata.column_types where table_schema = ?"  (Only schema)
       let
          keyList =  fmap (\(t,k)-> ((t,keyValue k),k)) res2
          keyMap = M.fromList keyList
          lookupKey3 :: (Functor f) => f (Text,Maybe (Vector Text),Bool) -> f (Text,(Vector Key,Bool))
          lookupKey3 = fmap  (\(t,c,b)-> (t,(maybe V.empty (fmap (\ci -> justError ("no key " <> T.unpack ci) $ M.lookup (t,ci) keyMap)) c,b)) )
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

       res <- lookupKey3 <$> query conn "SELECT t.table_name,pks,is_sum FROM metadata.tables t left join metadata.pks  p on p.schema_name = t.schema_name and p.table_name = t.table_name where t.schema_name = ?" (Only schema)
       resTT <- fmap readTT . M.fromList <$> query conn "SELECT table_name,table_type FROM metadata.tables where schema_name = ? " (Only schema) :: IO (Map Text TableType)
       let lookFk t k =V.toList $ lookupKey2 (fmap (t,) k)
       fks <- M.fromListWith S.union . fmap (\i@(tp,tc,kp,kc,rel) -> (tp,S.singleton $ Path (S.fromList $ lookFk tp kp) ( FKJoinTable tp (zipWith3 (\a b c -> Rel a b c) (lookFk tp kp ) (V.toList rel) (lookFk tc kc)) tc) (S.fromList $ F.toList $ fst $ justError "no pk found" $ M.lookup tc (M.fromList res) ))) <$> query conn foreignKeys (Only schema) :: IO (Map Text (Set (Path (Set Key) (SqlOperation ) )))
       let all =  M.fromList $ fmap (\(c,l)-> (c,S.fromList $ fmap (\(t,n)-> (\(Just i) -> i) $ M.lookup (t,keyValue n) keyMap ) l )) $ groupSplit (\(t,_)-> t)  $ (fmap (\((t,_),k) -> (t,k))) $  M.toList keyMap :: Map Text (Set Key)
           i3l =  (\(c,(pksl,is_sum))-> let
                                  pks = S.fromList $ F.toList pksl
                                  inlineFK =  fmap (\k -> (\t -> Path (S.singleton k ) (  FKInlineTable $ inlineName t) S.empty ) $ keyType k ) .  filter (isInline .keyType ) .  S.toList <$> M.lookup c all
                                  attr = S.difference ((\(Just i) -> i) $ M.lookup c all) ((S.fromList $ (maybe [] id $ M.lookup c descMap) )<> pks)
                                in (c ,Raw schema  ((\(Just i) -> i) $ M.lookup c resTT) (M.lookup c transMap) (S.filter (isKDelayed.keyType)  attr) is_sum c (fromMaybe [] (fmap (S.fromList . fmap (lookupKey .(c,) )  . V.toList) <$> M.lookup c uniqueConstrMap)) (maybe [] id $ M.lookup c authorization)  pks (maybe [] id $ M.lookup  c descMap) (fromMaybe S.empty $ M.lookup c fks    <> fmap S.fromList inlineFK ) S.empty attr )) <$> res :: [(Text,Table)]
       let
           i3 = addRecInit $ M.fromList i3l
           (i1,pks) = (keyMap, M.fromList $ fmap (\(_,t)-> (rawPK t ,t)) $ M.toList i3 )
           i2 =  M.filterWithKey (\k _ -> not.S.null $ k )  pks
       sizeMapt <- M.fromList . catMaybes . fmap  (\(t,cs)-> (,cs) <$>  M.lookup t  i3 ) <$> query conn tableSizes (Only schema)
       metaschema <- if (schema /= "metadata")
          then Just <$> keyTables  schemaVar mvar conn userconn ("metadata",user) oauth ops
          else return Nothing
       let inf = InformationSchema schema user oauth i1 i2  i3 sizeMapt mvar  userconn conn metaschema ops
       var <- takeMVar schemaVar
       putMVar schemaVar (M.insert schema inf var)
       return inf
       ) (return ) . (M.lookup schema ) =<< readMVar schemaVar

-- Search for recursive cycles and tag the tables
addRecInit :: Map Text Table -> Map Text Table
addRecInit m = fmap recOverFKS m
  where
        recOverFKS t  = t Le.& rawFKSL Le.%~ S.map path
          where
                path pini@(Path k rel tr) =
                    Path k (case rel of
                      FKInlineTable nt  -> case  L.filter (not .L.null) $ openPath S.empty [] pini of
                              [] -> if nt == tableName t then  RecJoin (MutRec []) (FKInlineTable nt) else FKInlineTable nt
                              e -> RecJoin (MutRec e) (FKInlineTable nt)
                      FKJoinTable a b nt -> case L.filter (not .L.null) $  openPath S.empty [] pini of
                              [] -> if nt == tableName t then  RecJoin (MutRec []) (FKJoinTable a b nt) else FKJoinTable a b nt
                              e -> RecJoin (MutRec e) (FKJoinTable a b nt)
                      ) tr
                    where
                      openPath ts p pa@(Path _(FKInlineTable nt) l)
                        | nt == tableName t = [p]
                        | S.member pa ts =  []
                        | otherwise = openTable (S.insert pa ts) p nt
                      openPath ts p pa@(Path _(FKJoinTable _ _ nt) _)
                        | nt == tableName t  = [p]
                        | S.member pa ts =  []
                        | otherwise = openTable (S.insert pa ts)  p nt
                      openTable t p nt  =  do
                              let cons pa
                                    | pa == pini = p
                                    | otherwise = p <> [F.toList (pathRelRel pa)]
                              ix <- fmap (\pa-> openPath t ( cons pa ) pa) fsk
                              return (concat (L.filter (not.L.null) ix))
                        where tb = justError ("no table" <> show (nt,m)) $ M.lookup nt m
                              fsk = F.toList $ rawFKS tb



liftTable' :: InformationSchema -> Text -> TBData Text a -> TBData Key a
liftTable' inf tname (_,v)   = (tableMeta ta,) $ mapComp (\(KV i) -> KV $ mapComp (liftField inf tname) <$> (M.mapKeys (S.map (fmap (lookKey inf tname))) i)) v
            where
                  ta = lookTable inf tname

fixPatch :: a ~ Index a => InformationSchema -> Text -> Index (TBData Key a) -> Index (TBData Key a)
fixPatch inf t (i , k ,p) = (i,k,fmap (fixPatchAttr inf t) p)

unRecRel (RecJoin _ l) = l
unRecRel l = l

fixPatchAttr :: a ~ Index a => InformationSchema -> Text -> Index (Column Key a) -> Index (Column Key a)
fixPatchAttr inf t p@(PAttr _ _ ) =  p
fixPatchAttr inf tname p@(PInline rel e ) =  PInline rel (fmap (\(_,o,v)-> (tableMeta $ lookTable inf tname2,o,fmap (fixPatchAttr  inf tname2 )v)) e)
    where Just (FKInlineTable tname2) = fmap (unRecRel.pathRel) $ L.find (\r@(Path i _ _)->  S.map (fmap keyValue ) (pathRelRel r) == S.singleton (Inline (keyValue rel)) )  (F.toList$ rawFKS  ta)
          ta = lookTable inf tname
fixPatchAttr inf tname p@(PFK rel2 pa t b ) =  PFK rel2 (fmap (fixPatchAttr inf tname) pa) (tableMeta $ lookTable inf tname2) b
    where (FKJoinTable _ _ tname2 )  = (unRecRel.pathRel) $ justError (show (rel2 ,rawFKS ta)) $ L.find (\(Path i _ _)->  i == S.fromList (_relOrigin <$> rel2))  (F.toList$ rawFKS  ta)
          ta = lookTable inf tname

liftKeys
  :: InformationSchema
     -> Text
     -> FTB1 Identity Text a
     -> FTB1 Identity Key a
liftKeys inf tname = fmap (liftTable' inf tname)


liftField :: InformationSchema -> Text -> Column Text a -> Column Key a
liftField inf tname (Attr t v) = Attr (lookKey inf tname t) v
liftField inf tname (FKT ref  rel2 tb) = FKT (mapComp (liftField inf tname) <$> ref)   ( rel) (liftKeys inf tname2 tb)
    where FKJoinTable _ rel tname2  = unRecRel $ pathRel $ justError (show (rel2 ,rawFKS ta)) $ L.find (\(Path i _ _)->  S.map keyValue i == S.fromList (_relOrigin <$> rel2))  (F.toList$ rawFKS  ta)
          ta = lookTable inf tname
liftField inf tname (IT rel tb) = IT (mapComp (liftField inf tname ) rel) (liftKeys inf tname2 tb)
    where FKInlineTable tname2  = unRecRel.pathRel  $ justError (show (rel ,rawFKS ta)) $ L.find (\r@(Path i _ _)->  S.map (fmap keyValue ) (pathRelRel r) == S.fromList (keyattr rel))  (F.toList$ rawFKS  ta)
          ta = lookTable inf tname



lookTable :: InformationSchema -> Text -> Table
lookTable inf t = justError ("no table: " <> T.unpack t) $ M.lookup t (tableMap inf)

lookKey :: InformationSchema -> Text -> Text -> Key
lookKey inf t k = justError ("table " <> T.unpack t <> " has no key " <> T.unpack k ) $ M.lookup (t,k) (keyMap inf)


newKey name ty p = do
  un <- newUnique
  return $ Key name Nothing    [FRead,FWrite] p Nothing un ty


catchPluginException :: InformationSchema -> Text -> Text -> [(Key, FTB Showable)] -> IO (Maybe a) -> IO (Maybe a)
catchPluginException inf pname tname idx i = do
  i `catch` (\e  -> do
                t <- getCurrentTime
                print (t,e)
                execute (rootconn inf) "INSERT INTO metadata.plugin_exception (username,schema_name,table_name,plugin_name,exception,data_index2,instant) values(?,?,?,?,?,?,?)" (username inf , schemaName inf,pname,tname,show (e :: SomeException) ,V.fromList (  (fmap (TBRecord2 "metadata.key_value"  . second (Binary . B.encode) . first keyValue) idx) ), t )
                return Nothing )


logTableModification
  :: (B.Binary a ,Ord a) =>
     InformationSchema
     -> TableModification (TBIdx Key a)  -> IO (TableModification (TBIdx Key a))
logTableModification inf (TableModification Nothing table i) = do
  time <- getCurrentTime
  let ltime =  utcToLocalTime utc $ time
      (_,pidx,pdata) = firstPatch keyValue  i
  [Only id] <- liftIO $ query (rootconn inf) "INSERT INTO metadata.modification_table (username,modification_time,table_name,data_index2,modification_data  ,schema_name) VALUES (?,?,?,?,? :: bytea[],?) returning modification_id "  (username inf ,ltime,rawName table, V.fromList (  (fmap (TBRecord2 "metadata.key_value"  . second (Binary . B.encode) ) pidx )) , Binary  .B.encode <$> V.fromList pdata , schemaName inf)
  return (TableModification (Just id) table i )


keyTables' con rcon s i j = do
  sch <- newMVar M.empty
  tables <- newMVar M.empty
  keyTables sch tables con rcon s i j
withInf d s f = withConn d (f <=< (\conn -> keyTables' conn conn (s,"postgres") Nothing undefined ))

withConnInf d s f = withConn d (\conn ->  f =<< liftIO ( keyTables'  conn conn (s,"postgres") Nothing undefined ) )

withTestConnInf d s f = withTestConn d (\conn ->  f =<< liftIO ( keyTables'  conn conn (s,"postgres") Nothing undefined ) )

testParse' db sch q = withTestConnInf db sch (\inf -> do
                                       let rp = tableView (tableMap inf) (fromJust $ M.lookup q (tableMap inf))
                                           rpd = rp -- forceDesc True (markDelayed True rp)
                                           rpq = selectQuery rpd
                                       print $ tableMeta $ lookTable inf q
                                       print rp
                                       print rpq
                                       q <- queryWith_ (fromRecord (unTB1 $ unTlabel rpd) ) (conn  inf) (fromString $ T.unpack $ rpq)
                                       return $ q
                                           )


testParse db sch q = withConnInf db sch (\inf -> do
                                       let rp = tableView (tableMap inf) (fromJust $ M.lookup q (tableMap inf))
                                           rpd = rp -- forceDesc True (markDelayed True rp)
                                           rpq = selectQuery rpd
                                       -- print $ tableMeta $ lookTable inf q
                                       -- print rp
                                       -- print rpq
                                       q <- queryWith_ (fromRecord (unTB1 $ unTlabel rpd) ) (conn  inf) (fromString $ T.unpack $ rpq)
                                       return $ q
                                           )

testMetaQuery q = testParse' "test" "metadata"  q
testFireMetaQuery q = testParse "incendio" "metadata"  q
testFireQuery q = testParse "incendio" "incendio"  q
testNutrition q = testParse "incendio" "nutrition"  q
testAcademia q = testParse "academia" "academia"  q



dbTable mvar table = do
    mmapm <- tryTakeMVar mvar
    case mmapm of
        Just mmap ->
          case (M.lookup table mmap ) of
               Just (i,td) -> do
                  putMVar mvar mmap
                  return $ Just (i,td)
               Nothing -> do
                  putMVar mvar mmap
                  return Nothing
        Nothing -> return Nothing


mergeCreate (Just i) (Just j) = Just $ mergeTB1 i j
mergeCreate Nothing (Just i) = Just i
mergeCreate (Just i)  Nothing = Just i
mergeCreate Nothing Nothing = Nothing

mergeTB1 (TB1  (m,Compose k) ) (TB1  (m2,Compose k2) )
  | m == m2 = TB1  (m,Compose $ liftA2 (<>) k k2)
  | otherwise = TB1  (m,Compose $ liftA2 (<>) k k2) -- errorWithStackTrace (show (m,m2))

ifOptional i = if isKOptional (keyType i) then unKOptional i else i
ifDelayed i = if isKDelayed (keyType i) then unKDelayed i else i



-- Load optional not  loaded delayed values
-- and merge to older values
applyAttr' :: (Show a,Ord a ,a~ Index a)  =>  Column Key a  -> PathAttr Key a -> DBM Key a (Column Key a)
applyAttr' (Attr k i) (PAttr _ p)  = return $ Attr k (applyShowable i p)
applyAttr' sfkt@(FKT iref rel i) (PFK _ p m b )  =  do
                            let ref =  F.toList $ M.mapWithKey (\key vi -> foldl  (\i j ->  edit key j i ) vi p ) (mapFromTBList iref)
                                edit  key  k@(PAttr  s _) v = if (_relOrigin $ head $ F.toList $ key) == s then  mapComp (  flip applyAttr k  ) v else v
                            tbs <- atTable m
                            return $ FKT ref rel (maybe (joinRel rel (fmap unTB ref) tbs) id b)
applyAttr' (IT k i) (PInline _   p)  = IT k <$> (applyFTBM (fmap pure $ createTB1) applyRecord' i p)
applyAttr' i j = errorWithStackTrace (show ("applyAttr'" :: String,i,j))

applyRecord'
  :: (Index a~ a ,Show a , Ord a ) =>
    TBData Key a
     -> TBIdx Key a
     -> DBM Key a (TBData Key a)
applyRecord' t@((m, v)) (_ ,_  , k)  = fmap (m,) $ traComp (fmap KV . sequenceA . M.mapWithKey (\key vi -> foldl  (\i j -> i >>= edit key j ) (return vi) k  ) . _kvvalues ) v
  where edit  key  k@(PAttr  s _) v = if (head $ F.toList $ key) == Inline s then  traComp (flip applyAttr' k ) v else return v
        edit  key  k@(PInline s _ ) v = if (head $ F.toList $ key) == Inline s then  traComp (flip applyAttr' k ) v else return v
        edit  key  k@(PFK rel s _ _ ) v = if  key == S.fromList rel then  traComp (flip applyAttr' k ) v else return v

applyTB1'
  :: (Index a~ a ,Show a , Ord a ) =>
    TB2 Key a
     -> PathFTB (TBIdx Key a)
     -> DBM Key a (TB2 Key a)
applyTB1' = applyFTBM (fmap pure $ createTB1) applyRecord'

createAttr' :: (Ord a ,Show a ,Index a ~ a) => PathAttr Key a -> DBM Key a (Column Key a)
createAttr' (PAttr  k s  ) = return $ Attr k  (createShowable s)
createAttr' (PInline k s ) = return $ IT (_tb $ Attr k (TB1 ())) (createFTB createTB1 s)
createAttr' (PFK rel k s b ) = do
      let ref = (_tb . createAttr <$> k)
      tbs <- atTable s
      return $ FKT ref rel (maybe (joinRel rel (fmap unTB ref) tbs) id b)
createAttr' i = errorWithStackTrace (show i)

createTB1'
  :: (Index a~ a ,Show a , Ord a  ) =>
     (Index (TBData Key a )) ->
     DBM Key a (KVMetadata Key , Compose Identity  (KV (Compose Identity  (TB Identity))) Key  a)
createTB1' (m ,s ,k)  = fmap (m ,)  $ fmap (_tb .KV . mapFromTBList ) . traverse (fmap _tb . createAttr') $  k



type Database k v = MVar (Map (KVMetadata k) (DBVar2 k v) )
type DBM k v = ReaderT (Database k v) IO

atTable ::  KVMetadata Key -> DBM Key v [TBData Key v]
atTable k = do
  i <- ask
  k <- liftIO$ dbTable i k
  maybe (return []) (\(m,c)-> fmap snd $ liftIO $ R.currentValue (R.facts c)) k

joinRelT ::  [Rel Key] -> [Column Key Showable] -> Table ->  [TBData Key Showable] -> TransactionM ( FTB (TBData Key Showable))
joinRelT rel ref tb table
  | L.all (isOptional .keyType) origin = fmap LeftTB1 $ traverse (\ref->  joinRelT (Le.over relOrigin unKOptional <$> rel ) ref  tb table) (traverse unLeftItens ref )
  | L.any (isArray.keyType) origin = fmap ArrayTB1 $ traverse (\ref -> joinRelT (Le.over relOrigin unKArray <$> rel ) ref  tb table ) (fmap (\i -> pure $ justError ("cant index  " <> show (i,head ref)). unIndex i $ (head ref)) [0..(L.length (unArray $ unAttr $ head ref) - 1)])
  | otherwise = maybe (tell (TableModification Nothing tb . patchTB1 <$> F.toList tbcreate) >> return tbcreate ) (return .TB1) tbel
      where origin = fmap _relOrigin rel
            tbcreate = tblist' tb (_tb . firstTB (\k -> justError "no rel key" $ M.lookup k relMap ) <$> ref )
            relMap = M.fromList $ (\r ->  (_relOrigin r,_relTarget r) )<$>  rel
            tbel = L.find (\(_,i)-> interPointPost rel ref (nonRefAttr  $ F.toList $ _kvvalues $ unTB  i) ) table


joinRel :: (Ord a ,Show a) => [Rel Key] -> [Column Key a] -> [TBData Key a] -> FTB (TBData Key a)
joinRel rel ref table
  | L.all (isOptional .keyType) origin = LeftTB1 $ fmap (flip (joinRel (Le.over relOrigin unKOptional <$> rel ) ) table) (traverse unLeftItens ref )
  | L.any (isArray.keyType) origin = ArrayTB1 $ fmap (flip (joinRel (Le.over relOrigin unKArray <$> rel ) ) table . pure ) (fmap (\i -> justError ("cant index  " <> show (i,head ref)). unIndex i $ (head ref)) [0..(L.length (unArray $ unAttr $ head ref) - 1)])
  | otherwise = maybe (tblist (_tb . firstTB (\k -> justError "no rel key" $ M.lookup k relMap ) <$> ref )) TB1 tbel
      where origin = fmap _relOrigin rel
            relMap = M.fromList $ (\r ->  (_relOrigin r,_relTarget r) )<$>  rel
            tbel = L.find (\(_,i)-> interPointPost rel ref (nonRefAttr  $ F.toList $ _kvvalues $ unTB  i) ) table


-- test inf i j = runDBM inf (applyTB1' i j)
runDBM inf m = do
    runReaderT m (mvarMap inf)


lookPK :: InformationSchema -> (Set Key) -> Table
lookPK inf pk =
      case  M.lookup pk  (pkMap inf) of
           Just table -> table
           i -> errorWithStackTrace (show pk)


