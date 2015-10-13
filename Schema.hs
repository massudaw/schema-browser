{-# LANGUAGE FlexibleContexts,ConstraintKinds,TypeFamilies,RankNTypes, TupleSections,BangPatterns,OverloadedStrings #-}


module Schema where

import Types
import Debug.Trace
import Data.Unique
import qualified Data.Foldable as F
-- import Step
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

import Data.Functor.Identity
import Database.PostgreSQL.Simple
import Data.Time
import RuntimeTypes

import Data.Traversable(sequenceA,traverse)
import Data.Vector (Vector)
import qualified Data.Vector as V

import Control.Monad
import Control.Applicative
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Map (Map)
import Data.Set (Set)
import Control.Concurrent

import Data.Text.Lazy(Text)
import qualified Data.Text.Lazy as T

import qualified Reactive.Threepenny as R


import Query
import Postgresql
import Patch
import qualified Data.ByteString.Char8 as BS


createType :: Text ->  (Text,Text,Text,Text,Text,Text,Maybe Text,Maybe Text,Maybe Text,Bool) -> KType Text
createType _ (t,c,"tsrange",_,_,n,def,_,_,_) =  (nullable n $ KInterval $ Primitive "timestamp without time zone")
createType _ (t,c,"tstzrange",_,_,n,def,_,_,_) =  (nullable n $ KInterval $ Primitive "timestamp with time zone")
createType _ (t,c,"daterange",_,_,n,def,_,_,_) =  (nullable n $ KInterval $ Primitive "date")
createType _ (t,c,"int4range",_,_,n,def,_,_,_) = (nullable n $ KInterval $ Primitive "int4")
createType _ (t,c,"numrange",_,_,n,def,_,_,_) =  (nullable n $ KInterval $ Primitive "numeric")
createType _ (t,c,"USER-DEFINED",_,"floatrange",n,def,_,_,_) =  (nullable n $ KInterval $ Primitive "double precision")
createType _ (t,c,"USER-DEFINED",_,"trange",n,def,_,_,_) =  (nullable n $ KInterval $ Primitive "time")
-- Table columns Primitive
createType s (t,c,"USER-DEFINED",udtschema ,udtname,n,def,_,_,False) |  udtschema == s = (nullable n $ InlineTable  udtschema udtname )
createType s (t,c,"USER-DEFINED",udtschema ,udtname,n,def,_,_,True) |  udtschema == s = (nullable n $ KEither udtschema udtname )
createType s (t,c,"ARRAY",udtschema ,udtname,n,def,_,_,False) | udtschema == s = (nullable n $ KArray $ InlineTable  udtschema $T.drop 1 udtname )
createType s (t,c,"ARRAY",udtschema ,udtname,n,def,_,_,True) | udtschema == s = (nullable n $ KArray $ KEither udtschema $T.drop 1 udtname )
createType _ (t,c,"ARRAY",_,i,n,def,p,_,_) = (nullable n $ KArray $ (Primitive (T.tail i)))
createType _ (t,c,_,_,"geometry",n,def,p,_,_) =  (nullable n $ Primitive $ (\(Just i) -> i) p)
createType _ (t,c,_,_,"box3d",n,def,p,_,_) =  (nullable n $ Primitive $  "box3d")
createType _ (t,c,ty,_,_,n,def,_,Just "pdf" ,_) =(serial def . nullable n $ KDelayed $ Primitive "pdf" )
createType _ (t,c,ty,_,_,n,def,_,Just "jpg" ,_) = (serial def . nullable n $ KDelayed $ Primitive "jpg" )
createType _ (t,c,ty,_,_,n,def,_,Just "ofx" ,_) = (serial def . nullable n $ KDelayed $ Primitive "ofx" )
createType _ (t,c,ty,_,_,n,def,_,Just dom ,_) = (serial def . nullable n $ Primitive dom)
createType _ (t,c,ty,_,_,n,def,_,_,_) =(serial def . nullable n $ Primitive ty)
--createType un v = error $ show v

serial (Just xs ) t = if T.isPrefixOf  "nextval" xs then KSerial t else t
serial Nothing t = t

nullable "YES" t = KOptional t
nullable "NO" t = t



meta inf = maybe inf id (metaschema inf)


type TableSchema = (Map (Text,Text) Key,Map (Set Key) Table,Map Text Table)

foreignKeys :: Query
foreignKeys = "select origin_table_name,target_table_name,origin_fks,target_fks,rel_fks from metadata.fks where origin_schema_name = target_schema_name  and  target_schema_name = ?"


queryAuthorization :: Connection -> Text -> Text -> IO (Map Text [Text])
queryAuthorization conn schema user = do
    sq <- query conn aq (schema,user)
    let convert (tname,authorizations) = (tname ,V.toList authorizations)
    return $ M.fromList $ convert <$> sq
  where aq = "select table_name,authorizations from metadata.authorization where table_schema = ? and grantee = ? "

tableSizes = "SELECT c.relname,c.reltuples::bigint AS estimate FROM   pg_class c JOIN   pg_namespace n ON c.relkind = 'r' and n.oid = c.relnamespace WHERE n.nspname = ? "

fromShowable2 i@(Primitive "character varying") v = fromShowable i $  BS.drop 1 (BS.init v)
fromShowable2 i@(Primitive "text") v = fromShowable i $  BS.drop 1 (BS.init v)
fromShowable2 i v = fromShowable i v

keyTables :: Connection -> Connection -> (Text ,Text)-> IO InformationSchema
keyTables conn userconn (schema ,user) = do
       uniqueMap <- join $ mapM (\(t,c,op,tr) -> ((t,c),) .(\ un -> (\def ->  Key c tr op def un )) <$> newUnique) <$>  query conn "select o.table_name,o.column_name,ordinal_position,translation from information_schema.tables natural join metadata.columns o left join metadata.table_translation t on o.column_name = t.column_name   where table_schema = ? "(Only schema)
       -- res2 <- fmap ( (\i@(t,c,j,k,l,m,n,d,z,b)-> (t,) $ (\ty -> (justError "no unique" $  M.lookup (t,c) (M.fromList uniqueMap) )  ( join $ fromShowable2 ty . BS.pack . T.unpack <$>  (join $ listToMaybe. T.splitOn "::" <$> n) ) ty )  (createType  schema (t,c,j,k,l,m,n,d,z,b)) )) <$>  query conn "select ta.table_name,o.column_name,data_type,udt_schema,udt_name,is_nullable,column_default, type,domain_name , st.table_name is not null from information_schema.tables ta natural join information_schema.columns  o left join metadata.table_translation t on o.column_name = t.column_name    left join   public.geometry_columns on o.table_schema = f_table_schema  and o.column_name = f_geometry_column left join metadata.sum_table st on st.schema_name = udt_schema and ('_' || st.table_name = udt_name OR st.table_name = udt_name)   where table_schema = ?"  (Only schema)
       res2 <- fmap ( (\i@(t,c,j,k,l,m,n,d,z,b)-> (t,) $ (\ty -> (justError "no unique" $  M.lookup (t,c) (M.fromList uniqueMap) )  ( join $ fromShowable2 ty . BS.pack . T.unpack <$>  (join $ listToMaybe. T.splitOn "::" <$> n) ) ty )  (createType  schema (t,c,j,k,l,m,n,d,z,b)) )) <$>  query conn "select ta.table_name,o.column_name,data_type,udt_schema,udt_name,is_nullable,column_default, null ,domain_name , st.table_name is not null from information_schema.tables ta natural join information_schema.columns  o left join metadata.table_translation t on o.column_name = t.column_name     left join metadata.sum_table st on st.schema_name = udt_schema and ('_' || st.table_name = udt_name OR st.table_name = udt_name)   where table_schema = ?"  (Only schema)
       let
          keyList =  fmap (\(t,k)-> ((t,keyValue k),k)) res2
          keyMap = M.fromList keyList
          lookupKey3 :: (Functor f) => f (Text,Maybe (Vector Text)) -> f (Text,Vector Key)
          lookupKey3 = fmap  (\(t,c)-> (t,maybe V.empty (fmap (\ci -> justError ("no key " <> T.unpack ci) $ M.lookup (t,ci) keyMap)) c) )
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

       res <- lookupKey3 <$> query conn "SELECT t.table_name,pks FROM metadata.tables t left join metadata.pks  p on p.schema_name = t.schema_name and p.table_name = t.table_name where t.schema_name = ?" (Only schema) :: IO [(Text,Vector Key )]
       resTT <- fmap readTT . M.fromList <$> query conn "SELECT table_name,table_type FROM information_schema.tables where table_schema = ? " (Only schema) :: IO (Map Text TableType)
       let lookFk t k =V.toList $ lookupKey2 (fmap (t,) k)
       fks <- M.fromListWith S.union . fmap (\i@(tp,tc,kp,kc,rel) -> (tp,S.singleton $ Path (S.fromList $ lookFk tp kp) (addRec tp tc $ FKJoinTable tp (zipWith3 (\a b c -> Rel a b c) (lookFk tp kp ) (V.toList rel) (lookFk tc kc)) tc) (S.fromList $ F.toList $ justError "no pk found" $ M.lookup tc (M.fromList res) ))) <$> query conn foreignKeys (Only schema) :: IO (Map Text (Set (Path (Set Key) (SqlOperation ) )))
       let all =  M.fromList $ fmap (\(c,l)-> (c,S.fromList $ fmap (\(t,n)-> (\(Just i) -> i) $ M.lookup (t,keyValue n) keyMap ) l )) $ groupSplit (\(t,_)-> t)  $ (fmap (\((t,_),k) -> (t,k))) $  M.toList keyMap :: Map Text (Set Key)
           pks =  (\(c,pksl)-> let
                                  pks = S.fromList $ F.toList pksl
                                  inlineFK =  fmap (\k -> (\t -> Path (S.singleton k ) (addRec c (inlineName t) $  FKInlineTable $ inlineName t) S.empty ) $ keyType k ) .  filter (isInline .keyType ) .  S.toList <$> M.lookup c all
                                  eitherFK =  fmap (\k -> (\t -> Path (S.singleton k ) (addRec c (inlineName t) $  FKInlineTable $ inlineName t) S.empty ) $ keyType k ) .  filter (isKEither .keyType ) .  S.toList <$> M.lookup c all
                                  -- eitherFK =   M.lookup c eitherMap
                                  attr = S.difference ({-S.filter (not. isKEither.keyType)  $ -}(\(Just i) -> i) $ M.lookup c all) ((S.fromList $ (maybe [] id $ M.lookup c descMap) )<> pks)
                                in (pks ,Raw schema  ((\(Just i) -> i) $ M.lookup c resTT) (M.lookup c transMap) (S.filter (isKDelayed.keyType)  attr) c (fromMaybe [] (fmap (S.fromList . fmap (lookupKey .(c,) )  . V.toList) <$> M.lookup c uniqueConstrMap)) (maybe [] id $ M.lookup c authorization)  pks (maybe [] id $ M.lookup  c descMap) (fromMaybe S.empty $ M.lookup c fks    <> fmap S.fromList inlineFK <> fmap S.fromList eitherFK   ) attr )) <$> res :: [(Set Key,Table)]
       let (i1,i2,i3) = (keyMap, M.fromList $ filter (not.S.null .fst)  pks,M.fromList $ fmap (\(_,t)-> (tableName t ,t)) pks)
       sizeMapt <- M.fromList . catMaybes . fmap  (\(t,cs)-> (,cs) <$>  M.lookup t i3 ) <$> query conn tableSizes (Only schema)
       mvar <- newMVar M.empty
       metaschema <- if (schema /= "metadata")
          then Just <$> keyTables  conn userconn ("metadata",user)
          else return Nothing
       return  $ InformationSchema schema user i1 i2 i3 sizeMapt M.empty mvar  userconn conn metaschema

addRec i j
  | i == j = RecJoin
  | otherwise = id


liftTable' :: InformationSchema -> Text -> TBData Text a -> TBData Key a
liftTable' inf tname (_,v)   = (tableMeta ta,) $ mapComp (\(KV i) -> KV $ mapComp (liftField inf tname) <$> (M.mapKeys (S.map (fmap (lookKey inf tname))) i)) v
            where
                  ta = lookTable inf tname


fixPatch inf t (i , k ,p) = (i,k,fmap (fixPatchAttr inf t) p)

unRecRel (RecJoin l) = l
unRecRel l = l

fixPatchAttr inf t p@(PAttr _ _ ) =  p
fixPatchAttr inf tname p@(PInline rel e ) =  PInline rel (fmap (\(_,o,v)-> (tableMeta $ lookTable inf tname2,o,fmap (fixPatchAttr  inf tname2 )v)) e)
    where Just (FKInlineTable tname2) = fmap (unRecRel.pathRel) $ L.find (\r@(Path i _ _)->  S.map (fmap keyValue ) (pathRelRel r) == S.singleton (Inline (keyValue rel)) )  (F.toList$ rawFKS  ta)
          ta = lookTable inf tname
fixPatchAttr inf tname p@(PFK rel2 pa t b ) =  PFK rel2 (fmap (fixPatchAttr inf tname) pa) (tableMeta $ lookTable inf tname2) b
    where (Path _ (FKJoinTable _ rel tname2 ) _) = justError (show (rel2 ,rawFKS ta)) $ L.find (\(Path i _ _)->  i == S.fromList (_relOrigin <$> rel2))  (F.toList$ rawFKS  ta)
          ta = lookTable inf tname

liftKeys
  :: InformationSchema
     -> Text
     -> FTB1 Identity Text a
     -> FTB1 Identity Key a
liftKeys inf tname = fmap (liftTable' inf tname)


liftField :: InformationSchema -> Text -> TB Identity Text a -> TB Identity Key a
liftField inf tname (Attr t v) = Attr (lookKey inf tname t) v
liftField inf tname (FKT ref  rel2 tb) = FKT (mapComp (liftField inf tname) <$> ref)   ( rel) (liftKeys inf tname2 tb)
    where (FKJoinTable _ rel tname2 ) = unRecRel $ pathRel $ justError (show (rel2 ,rawFKS ta)) $ L.find (\(Path i _ _)->  S.map keyValue i == S.fromList (_relOrigin <$> rel2))  (F.toList$ rawFKS  ta)
          ta = lookTable inf tname
liftField inf tname (IT rel tb) = IT (mapComp (liftField inf tname ) rel) (liftKeys inf tname2 tb)
    where Just (Path _ (FKInlineTable tname2 ) _) = L.find (\r@(Path i _ _)->  S.map (fmap keyValue ) (pathRelRel r) == S.fromList (keyattr rel))  (F.toList$ rawFKS  ta)
          ta = lookTable inf tname



lookTable :: InformationSchema -> Text -> Table
lookTable inf t = justError ("no table: " <> T.unpack t) $ M.lookup t (tableMap inf)

lookKey :: InformationSchema -> Text -> Text -> Key
lookKey inf t k = justError ("table " <> T.unpack t <> " has no key " <> T.unpack k ) $ M.lookup (t,k) (keyMap inf)

lookFresh inf n tname i = justError "no freshKey" $ M.lookup (n,tname,i) (pluginsMap inf)

newKey name ty p = do
  un <- newUnique
  return $ Key name Nothing    p Nothing un ty


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
  -- [Only id] <- liftIO $ query (rootconn inf) "INSERT INTO metadata.modification_table (username,modification_time,table_name,data_index2,modification_data  ,schema_name) VALUES (?,?,?,?,? :: bytea[],?) returning modification_id "  (username inf ,ltime,rawName table, V.fromList (  (fmap (TBRecord2 "metadata.key_value"  . second (Binary . B.encode) ) pidx )) , Binary  .B.encode <$> V.fromList pdata , schemaName inf)
  return (TableModification (Just 0) table i )


withInf d s f = withConn d (f <=< (\conn -> keyTables conn conn (s,"postgres")))

withConnInf d s f = withConn d (\conn ->  f =<< liftIO ( keyTables  conn conn (s,"postgres")) )


testParse db sch q = withConnInf db sch (\inf -> do
                                       let rp = tableView (tableMap inf) (fromJust $ M.lookup q (tableMap inf))
                                           rpd = rp -- forceDesc True (markDelayed True rp)
                                           rpq = selectQuery rpd
                                       print rpd
                                       print rpq
                                       q <- queryWith_ (fromRecord (unTB1 $ unTlabel rpd) ) (conn  inf) (fromString $ T.unpack $ rpq)
                                       return $ q
                                           )

testMetaQuery q = testParse "test" "metadata"  q
testFireMetaQuery q = testParse "incendio" "metadata"  q
testFireQuery q = testParse "incendio" "incendio"  q
testNutrition q = testParse "incendio" "nutrition"  q
testAcademia q = testParse "academia" "academia"  q

selectAll inf table   = liftIO $ do
      let
          tb =  tableView (tableMap inf) table
          tbf = tb -- forceDesc True (markDelayed True tb)
      print (tableName table,selectQuery tbf )
      (t,v) <- duration  $ queryWith_  (fromAttr (unTlabel tbf)) (conn inf)(fromString $ T.unpack $ selectQuery $ tbf)
      print (tableName table,t)
      return v

dbTable mvar table = do
    mmap <- takeMVar mvar
    (mtable,td) <- case (M.lookup table mmap ) of
         Just (i,td) -> do
           putMVar mvar mmap
           return (i,td)
         Nothing -> errorWithStackTrace ("no table " <> show table)
    return (mtable,td)


eventTable inf table = do
    let mvar = mvarMap inf
    mmap <- takeMVar mvar
    (mtable,td) <- case (M.lookup (tableMeta table) mmap ) of
         Just (i,td) -> do
           putMVar mvar mmap
           return (i,td)
         Nothing -> do
           res <- selectAll  inf table
           mnew <- newMVar (fmap unTB1 res)
           (e,h) <- R.newEvent
           ini <- readMVar mnew
           forkIO $ forever $ do
              h =<< takeMVar mnew
           bh <- R.stepper ini e
           let td = (R.tidings bh e)
           putMVar mvar (M.insert (tableMeta table) (mnew,td) mmap)
           return (mnew,td)
    return (mtable,fmap TB1 <$> td)



testLoadDelayed inf t = do
   let table = lookTable inf t
       tb = tableView (tableMap inf) table
   print tb
   res  <- queryWith_ (fromAttr (unTlabel tb)) (conn inf) (fromString $ T.unpack $ selectQuery tb )
   mapM (loadDelayed inf (unTB1 $ unTlabel tb ). unTB1 ) res

testFireQueryLoad t  = withConnInf "incendio" "incendio" (flip testLoadDelayed t)

mergeTB1 (TB1  (m,Compose k) ) (TB1  (m2,Compose k2) )
  | m == m2 = TB1  (m,Compose $ liftA2 (<>) k k2)
  | otherwise = TB1  (m,Compose $ liftA2 (<>) k k2) -- errorWithStackTrace (show (m,m2))

ifOptional i = if isKOptional (keyType i) then unKOptional i else i
ifDelayed i = if isKDelayed (keyType i) then unKDelayed i else i


-- Load optional not  loaded delayed values
-- and merge to older values
loadDelayed :: InformationSchema -> TBData Key () -> TBData Key Showable -> IO (Maybe (TBIdx Key Showable))
loadDelayed inf t@(k,v) values@(ks,vs)
  | S.null $ _kvdelayed k = return Nothing
  | L.null delayedattrs  = return Nothing
  | otherwise = do
       let
           whr = T.intercalate " AND " ((\i-> (keyValue i) <>  " = ?") <$> S.toList (_kvpk k) )
           table = justError "no table" $ M.lookup (_kvpk k) (pkMap inf)
           delayedTB1 =  (ks,) . _tb $ KV ( filteredAttrs)
           delayed =  mapKey' (kOptional . ifDelayed . ifOptional) (mapValue' (const ()) delayedTB1)
           str = "SELECT " <> explodeRecord (relabelT' runIdentity Unlabeled delayed) <> " FROM " <> showTable table <> " WHERE " <> whr
       print str
       is <- queryWith (fromRecord delayed) (conn inf) (fromString $ T.unpack str) (fmap unTB $ F.toList $ _kvvalues $  runIdentity $ getCompose $ tbPK' (tableNonRef' values))
       case is of
            [] -> errorWithStackTrace "empty query"
            [i] ->return $ fmap (\(i,j,a) -> (i,getPKM (ks,vs),a)) $ difftable delayedTB1(mapKey' (kOptional.kDelayed.unKOptional) . mapFValue' (LeftTB1 . Just . DelayedTB1 .  unSOptional ) $ i  )
            _ -> errorWithStackTrace "multiple result query"
  where
    delayedattrs = concat $ fmap (keyValue . (\(Inline i ) -> i)) .  F.toList <$> M.keys filteredAttrs
    filteredAttrs = M.filterWithKey (\key v -> S.isSubsetOf (S.map _relOrigin key) (_kvdelayed k) && (all (maybe False id) $ fmap (fmap (isNothing .unSDelayed)) $ fmap unSOptional $ kattr $ v)  ) (_kvvalues $ unTB vs)

applyAttr' :: (Show a,Ord a ,a~ Index a)  =>  TB Identity Key a  -> PathAttr Key a -> DBM Key a (TB Identity Key a)
applyAttr' (Attr k i) (PAttr _ p)  = return $ Attr k (applyShowable i p)
applyAttr' sfkt@(FKT iref rel i) (PFK _ p m b )  =  do
                            let ref =  F.toList $ M.mapWithKey (\key vi -> foldl  (\i j ->  edit key j i ) vi p ) (mapFromTBList iref)
                                edit  key  k@(PAttr  s _) v = if (_relOrigin $ head $ F.toList $ key) == s then  mapComp (  flip applyAttr k . traceShow (k,v)) v else v
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
  where edit  key  k@(PAttr  s _) v = if (_relOrigin $ head $ F.toList $ key) == s then  traComp (flip applyAttr' k ) v else return v
        edit  key  k@(PInline s _ ) v = if (_relOrigin $ head $ F.toList $ key) == s then  traComp (flip applyAttr' k ) v else return v
        edit  key  k@(PFK rel s _ _ ) v = if  key == S.fromList rel then  traComp (flip applyAttr' k ) v else return v
applyTB1'
  :: (Index a~ a ,Show a , Ord a ) =>
    TB2 Key a
     -> PathFTB (TBIdx Key a)
     -> DBM Key a (TB2 Key a)
applyTB1' = applyFTBM (fmap pure $ createTB1) applyRecord'

createAttr' :: (Ord a ,Show a ,Index a ~ a) => PathAttr Key a -> DBM Key a (TB Identity Key a)
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
createTB1'  i = errorWithStackTrace (show i)



type Database k v = MVar (Map (KVMetadata k) (MVar [TBData k v],R.Tidings [TBData k v]))
type DBM k v = ReaderT (Database k v) IO

atTable ::  KVMetadata Key -> DBM Key v [TBData Key v]
atTable k = do
  i <- ask
  (m,c)<- liftIO$ dbTable i k
  liftIO $ R.currentValue (R.facts c)

test inf i j = runDBM inf (applyTB1' i j)
runDBM inf m = do
    runReaderT m (mvarMap inf)
