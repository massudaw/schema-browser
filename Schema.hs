{-# LANGUAGE TupleSections,BangPatterns,OverloadedStrings #-}

module Schema where

import Types
import Data.Unique
import qualified Data.Foldable as F
import Step
import Data.Maybe
import Data.String
import Control.Monad.IO.Class
import GHC.Stack
import Data.Monoid
import Utils
import Control.Exception
import System.Time.Extra

import Data.Functor.Identity
import Database.PostgreSQL.Simple
import Data.Time

import Data.Vector (Vector)
import qualified Data.Vector as V

import Control.Monad
import Control.Applicative
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Map (Map)
import Data.Set (Set)
import Debug.Trace
import Control.Concurrent

import Data.Text.Lazy(Text)
import qualified Data.Text.Lazy as T

import qualified Reactive.Threepenny as R


import Query
import Postgresql


createType :: Text ->  Unique -> (Text,Text,Maybe Text,Text,Text,Text,Text,Maybe Text,Maybe Text,Maybe Text) -> Key
createType _ un (t,c,trans,"tsrange",_,_,n,def,_,_) = (Key   c trans un (nullable n $ KInterval $ Primitive "timestamp without time zone"))
createType _ un (t,c,trans,"tstzrange",_,_,n,def,_,_) = (Key   c trans un (nullable n $ KInterval $ Primitive "timestamp with time zone"))
createType _ un (t,c,trans,"daterange",_,_,n,def,_,_) = (Key   c trans un (nullable n $ KInterval $ Primitive "date"))
createType _ un (t,c,trans,"int4range",_,_,n,def,_,_) = (Key   c trans un (nullable n $ KInterval $ Primitive "int4"))
createType _ un (t,c,trans,"numrange",_,_,n,def,_,_) = (Key   c trans un (nullable n $ KInterval $ Primitive "numeric"))
createType _ un (t,c,trans,"USER-DEFINED",_,"floatrange",n,def,_,_) = (Key   c trans un (nullable n $ KInterval $ Primitive "double precision"))
createType _ un (t,c,trans,"USER-DEFINED",_,"trange",n,def,_,_) = (Key   c trans un (nullable n $ KInterval $ Primitive "time"))
-- Table columns Primitive
createType s un (t,c,trans,"USER-DEFINED",udtschema ,udtname,n,def,_,_) |  udtschema == s = (Key c trans un (nullable n $ InlineTable  udtschema udtname ))
createType s un (t,c,trans,"ARRAY",udtschema ,udtname,n,def,_,_) | udtschema == s = (Key c trans un (nullable n $ KArray $ InlineTable  udtschema $T.drop 1 udtname ))
createType _ un (t,c,trans,"ARRAY",_,i,n,def,p,_) = (Key   c trans un (nullable n $ KArray $ (Primitive (T.tail i))))
createType _ un (t,c,trans,_,_,"geometry",n,def,p,_) = (Key   c trans un (nullable n $ Primitive $ (\(Just i) -> i) p))
createType _ un (t,c,trans,_,_,"box3d",n,def,p,_) = (Key   c trans un (nullable n $ Primitive $  "box3d"))
createType _ un (t,c,trans,ty,_,_,n,def,_,Just "pdf" ) =(Key c   trans un (serial def . nullable n $ KDelayed $ Primitive "pdf" ))
createType _ un (t,c,trans,ty,_,_,n,def,_,Just "jpg" ) =(Key c   trans un (serial def . nullable n $ KDelayed $ Primitive "jpg" ))
createType _ un (t,c,trans,ty,_,_,n,def,_,Just "ofx" ) =(Key c   trans un (serial def . nullable n $ KDelayed $ Primitive "ofx" ))
createType _ un (t,c,trans,ty,_,_,n,def,_,Just dom ) =(Key c   trans un (serial def . nullable n $ Primitive dom))
createType _ un (t,c,trans,ty,_,_,n,def,_,_) =(Key c   trans un (serial def . nullable n $ Primitive ty))
--createType un v = error $ show v

serial (Just xs ) t = if T.isPrefixOf  "nextval" xs then KSerial t else t
serial Nothing t = t

nullable "YES" t = KOptional t
nullable "NO" t = t

data InformationSchema
  = InformationSchema
  { schemaName :: Text
  , keyMap :: Map (Text,Text) Key
  , pkMap :: Map (Set Key) Table
  , tableMap :: Map Text Table
  , pluginsMap :: Map (Text,Text,Text) Key
  , mvarMap :: MVar (Map Table ({-R.Event [TB1 Showable], R.Handler [TB1 Showable], -}MVar [(TB1 Showable)]))
  , conn :: Connection
  , rootconn :: Connection
  }

type TableSchema = (Map (Text,Text) Key,Map (Set Key) Table,Map Text Table)

foreignKeys :: Query
foreignKeys = "select origin_table_name,target_table_name,origin_fks,target_fks,rel_fks from metadata.fks where origin_schema_name = target_schema_name  and  target_schema_name = ?"


queryAuthorization :: Connection -> Text -> Text -> IO (Map Text [Text])
queryAuthorization conn schema user = do
    sq <- query conn aq (schema,user)
    let convert (tname,authorizations) = (tname ,V.toList authorizations)
    return $ M.fromList $ convert <$> sq
  where aq = "select table_name,authorizations from metadata.authorization where table_schema = ? and grantee = ? "

keyTables :: Connection -> Connection -> (Text ,Text)-> IO InformationSchema
keyTables conn userconn (schema ,user) = do
       uniqueMap <- join $ mapM (\i-> (i,) <$> newUnique) <$>  query conn "select o.table_name,o.column_name from information_schema.tables natural join information_schema.columns o where table_schema = ? "(Only schema)
       res2 <- fmap ( (\i@(t,c,o,j,k,l,m,n,d,z)-> (t,) $ createType  schema ((\(t,c,i,j,k,l,m,n,d,z)-> (\(Just i) -> i) $ M.lookup (t,c) (M.fromList uniqueMap)) i) i )) <$>  query conn "select table_name,o.column_name,translation,data_type,udt_schema,udt_name,is_nullable,column_default, type,domain_name from information_schema.tables natural join information_schema.columns  o left join metadata.table_translation t on o.column_name = t.column_name    left join   public.geometry_columns on o.table_schema = f_table_schema  and o.column_name = f_geometry_column where table_schema = ?"  (Only schema)
       --res2 <- fmap ( (\i@(t,c,o,j,k,l,m,n,d,z)-> (t,) $ createType  schema ((\(t,c,i,j,k,l,m,n,d,z)-> (\(Just i) -> i) $ M.lookup (t,c) (M.fromList uniqueMap)) i) i )) <$>  query conn "select table_name,o.column_name,translation,data_type,udt_schema,udt_name,is_nullable,column_default,'' :: text ,domain_name from information_schema.tables natural join information_schema.columns  o left join metadata.table_translation t on o.column_name = t.column_name where table_schema = ? " {- left join   public.geometry_columns on o.table_schema = f_table_schema  and o.column_name = f_geometry_column " -} (Only schema)
       let
          keyList =  fmap (\(t,k)-> ((t,keyValue k),k)) res2
       -- keyMap <- preprocessSumTypes (M.fromList keyList)
          keyMap = M.fromList keyList
       let
          lookupKey3 :: (Functor  g, Functor f) => f (Text,g Text) -> f (Text,g Key)
          lookupKey3 = fmap  (\(t,c)-> (t,fmap (\ci -> justError ("no key " <> T.unpack ci) $ M.lookup (t,ci) keyMap) c) )
          lookupKey2 :: Functor f => f (Text,Text) -> f Key
          lookupKey2 = fmap  (\(t,c)-> justError ("nokey" <> show (t,c)) $ M.lookup ( (t,c)) keyMap )
          lookupKey ::  (Text,Text) ->  Key
          lookupKey = (\(t,c)-> justError ("nokey" <> show (t,c)) $ M.lookup ( (t,c)) keyMap )
          readTT :: Text ->  TableType
          readTT "BASE TABLE" = ReadWrite
          readTT "VIEW" = ReadOnly
          readTT i =  error $ T.unpack i
       authorization <- queryAuthorization conn schema user
       descMap <- M.fromList . fmap  (\(t,c)-> (t,(\(Just i) -> i) $ M.lookup (t,c) keyMap) ) <$> query conn "SELECT table_name,description FROM metadata.table_description WHERE table_schema = ? " (Only schema)
       transMap <- M.fromList   <$> query conn "SELECT table_name,translation FROM metadata.table_name_translation WHERE schema_name = ? " (Only schema)
       eitherMap <- fmap (M.fromListWith mappend)  . join $  mapM (\(t,l,n)-> do
         un <- newUnique
         let
           lcol = lookupKey . (t,) <$> V.toList l
           tnew = Key n Nothing un (KEither (keyType <$> lcol) )
         return (t,[Path (S.fromList lcol) (FKEitherField tnew lcol) (S.singleton tnew) ]) ) <$> query conn "SELECT table_name,sum_columns,column_name FROM metadata.table_either WHERE table_schema = ? " (Only schema)


       res <- lookupKey3 <$> query conn "SELECT table_name,pks FROM metadata.pks  where schema_name = ?" (Only schema) :: IO [(Text,Vector Key )]
       resTT <- fmap readTT . M.fromList <$> query conn "SELECT table_name,table_type FROM information_schema.tables where table_schema = ? " (Only schema) :: IO (Map Text TableType)
       let lookFk t k =V.toList $ lookupKey2 (fmap (t,) k)
       fks <- M.fromListWith S.union . fmap (\i@(tp,tc,kp,kc,rel) -> (tp,S.singleton $ Path (S.fromList $ lookFk tp kp) (FKJoinTable tp (zipWith3 (\a b c -> Rel a b c) (lookFk tp kp ) (V.toList rel) (lookFk tc kc)) tc) (S.fromList $ lookFk tc kc))) <$> query conn foreignKeys (Only schema) :: IO (Map Text (Set (Path (Set Key) (SqlOperation ) )))
       let all =  M.fromList $ fmap (\(c,l)-> (c,S.fromList $ fmap (\(t,n)-> (\(Just i) -> i) $ M.lookup (t,keyValue n) keyMap ) l )) $ groupSplit (\(t,_)-> t)  $ (fmap (\((t,_),k) -> (t,k))) $  M.toList keyMap :: Map Text (Set Key)
           pks =  (\(c,pksl)-> let
                                  pks = S.fromList $ F.toList pksl
                                  inlineFK =  (fmap (\k -> (\t -> Path (S.singleton k ) (FKInlineTable $ inlineName t) S.empty ) $ keyType k ) .  filter (isInline .keyType ) .  S.toList ) <$> (M.lookup c all)
                                  eitherFK =   M.lookup c eitherMap
                                  attr = S.difference ((\(Just i) -> i) $ M.lookup c all) ((S.fromList $maybeToList $ M.lookup c descMap) <> pks)
                                in (pks ,Raw schema  ((\(Just i) -> i) $ M.lookup c resTT) (M.lookup c transMap) (S.filter (isKDelayed.keyType)  attr) c (maybe [] id $ M.lookup c authorization)  pks (M.lookup  c descMap) (fromMaybe S.empty $ M.lookup c fks    <> fmap S.fromList inlineFK <> fmap S.fromList eitherFK   ) attr )) <$> res :: [(Set Key,Table)]
       let (i1,i2,i3) = (keyMap, M.fromList $ filter (not.S.null .fst)  pks,M.fromList $ fmap (\(_,t)-> (tableName t ,t)) pks)
       mvar <- newMVar M.empty
       return  $ InformationSchema schema i1 i2 i3 M.empty mvar  userconn conn

liftKeys
  :: InformationSchema
     -> Text
     -> FTB1 Identity Text a
     -> FTB1 Identity Key a
liftKeys inf tname tb
  = liftTable tname tb
  where
        liftTable tname (TB1 _ v )  = TB1  (tableMeta ta) $ mapComp (\(KV i) -> KV $ mapComp (liftField tname) <$> (M.mapKeys (S.map (lookKey inf tname)) i)) v
            where
                  ta = lookTable inf tname
        liftTable tname (LeftTB1 j ) = LeftTB1 $ liftTable tname <$> j
        liftTable tname (ArrayTB1 j ) = ArrayTB1 $ liftTable tname <$> j
        liftField :: Text -> TB Identity Text a -> TB Identity Key a
        liftField tname (TBEither n k j ) = TBEither (lookKey inf tname n) (mapComp (liftField tname) <$> k ) (mapComp (liftField tname ) <$> j)
        liftField tname (Attr t v) = Attr (lookKey inf tname t) v
        liftField tname (FKT ref i rel2 tb) = FKT (mapComp (liftField tname) <$> ref)  i ( rel) (liftTable tname tb)
            where Just (Path _ (FKJoinTable _ rel _ ) _) = L.find (\(Path i _ _)->  S.map keyValue i == S.fromList (concat $ fmap keyattr ref))  (F.toList$ rawFKS  ta)
                  ta = lookTable inf tname
        liftField tname (IT rel tb) = IT (mapComp (liftField tname ) rel) (liftTable tname2 tb)
            where Just (Path _ (FKInlineTable tname2 ) _) = L.find (\(Path i _ _)->  S.map keyValue i == S.fromList (keyattr rel))  (F.toList$ rawFKS  ta)
                  ta = lookTable inf tname


withConn s action =  do
  conn <- liftIO $connectPostgreSQL $ "user=postgres password=queijo dbname=" <> fromString (T.unpack s)
  action conn

lookTable :: InformationSchema -> Text -> Table
lookTable inf t = justError ("no table: " <> T.unpack t) $ M.lookup t (tableMap inf)

lookKey :: InformationSchema -> Text -> Text -> Key
lookKey inf t k = justError ("table " <> T.unpack t <> " has no key " <> T.unpack k ) $ M.lookup (t,k) (keyMap inf)

lookFresh inf n tname i = justError "no freshKey" $ M.lookup (n,tname,i) (pluginsMap inf)

newKey name ty = do
  un <- newUnique
  return $ Key name Nothing    un ty


catchPluginException :: InformationSchema -> Text -> Text -> IO (Maybe a) -> IO (Maybe a)
catchPluginException inf pname tname i = do
  i `catch` (\e  -> do
                execute (rootconn inf) "INSERT INTO metadata.plugin_exception (schema_name,table_name,plugin_name,exception) values(?,?,?,?)" (schemaName inf,pname,tname,show (e :: SomeException) )
                return Nothing )


logTableModification
  :: Show b =>
     InformationSchema
     -> TableModification b -> IO (TableModification b)
logTableModification inf (TableModification Nothing table i) = do
  time <- getCurrentTime
  let ltime =  utcToLocalTime utc $ time
  [Only id] <- liftIO $ query (rootconn inf) "INSERT INTO metadata.modification_table (modification_time,table_name,modification_data,schema_name) VALUES (?,?,?,?) returning modification_id "  (ltime,rawName table,show i , schemaName inf)
  return (TableModification (id) table i )


withInf d s f = withConn d (f <=< (\conn -> keyTables conn conn (s,"postgres")))
withConnInf d s f = withConn d (\conn ->  f =<< liftIO ( keyTables  conn conn (s,"postgres")) )


testParse db sch q = withConnInf db sch (\inf -> do
                                       let (rp,rpq) = rootPaths' (tableMap inf) (fromJust $ M.lookup q (tableMap inf))
                                       --putStrLn (  show rpq)
                                       q <- queryWith_ (fromAttr (rp) ) (conn  inf) (fromString $ T.unpack $ rpq)
                                       --print q
                                       return $ q
                                           )

testFireMetaQuery q = testParse "incendio" "metadata"  q
testFireQuery q = testParse "incendio" "incendio"  q
testAcademia q = testParse "academia" "academia"  q

selectAll inf table   = liftIO $ do
      let -- rp = rootPaths'  (tableMap inf) table
          tb =  tableView (tableMap inf) table
      (t,v) <- duration  $ queryWith_  (fromAttr (unTlabel tb)) (conn inf)(fromString $ T.unpack $ selectQuery tb)
      print (tableName table,selectQuery tb,t)
      return v

addTable inf table = do
    let mvar = mvarMap inf
    mmap <- takeMVar mvar
    (isEmpty,mtable) <- case (M.lookup table mmap ) of
         Just i -> do
           emp <- isEmptyMVar i
           putMVar mvar mmap
           return (emp,i)
         Nothing -> do
           res <- selectAll  inf table
           mnew <- newMVar res
           putMVar mvar (M.insert table mnew mmap)
           return (True,mnew )
    t <- readMVar mtable
    return t


testLoadDelayed inf t = do
   let table = lookTable inf t
       tb = {-filterKey (\i _-> not . any  (isKDelayed . keyType ) $  S.toList i ) $-} tableView (tableMap inf) table
       tbdel = {-filterKey (\i _-> any  (isKDelayed . keyType ) $  S.toList i ) $-} tableView (tableMap inf) table
   print tb
   print tbdel
   res  <- queryWith_ (fromAttr (unTlabel tb)) (conn inf) (fromString $ T.unpack $ selectQuery tb )
   mapM (loadDelayed inf (unTlabel tbdel )) res

testFireQueryLoad t  = withConnInf "incendio" "incendio" (flip testLoadDelayed t)

mergeTB1 (TB1 m (Compose k) ) (TB1 m2 (Compose k2) )
  | m == m2 = TB1 m (Compose $ liftA2 (<>) k k2)
  | otherwise = TB1 m (Compose $ liftA2 (<>) k k2) -- errorWithStackTrace (show (m,m2))

ifOptional i = if isKOptional (keyType i) then unKOptional i else i
ifDelayed i = if isKDelayed (keyType i) then unKDelayed i else i

-- Load optional not  loaded delayed values
-- and merge to older values
loadDelayed inf t@(TB1 k v) values@(TB1 ks vs)
  | S.null $ _kvdelayed k = return Nothing
  | L.null delayedattrs  = return Nothing
  | otherwise = do
       let
           str = "SELECT ROW(" <> attr <> ") FROM " <> showTable table <> " WHERE " <> whr
           whr = T.intercalate " AND " ((\i-> (keyValue i) <>  " = ?") <$> S.toList (_kvpk k) )
           attr = T.intercalate "," delayedattrs
           table = justError "no table" $ M.lookup (_kvpk k) (pkMap inf)
           delayed = fmap (const ()) $ mapKey (ifDelayed . ifOptional) $ TB1 k $ Compose $ Identity $ KV $  (M.filterWithKey (\key v -> S.isSubsetOf key (_kvdelayed k) && (all (maybe False id) $ fmap (fmap (isNothing .unSDelayed)) $ fmap unSOptional $ kattr $ v)  ) (_kvvalues $ unTB vs) )
       print str
       is <- queryWith (fromAttr delayed)  (conn inf) (fromString $ T.unpack str) (fmap unTB $ F.toList $ _kvvalues $  runIdentity $ getCompose $ tbPK (tableNonRef values))
       case is of
            [] -> errorWithStackTrace "empty query"
            [i] ->return $ Just $ EditTB (mapKey (kOptional.kDelayed)  . fmap (SOptional. Just . SDelayed .Just) $ i  ) values
            _ -> errorWithStackTrace "multiple result query"
  where delayedattrs =  (concat $ fmap keyValue . F.toList <$> M.keys (M.filterWithKey (\key v -> S.isSubsetOf key (_kvdelayed k) && maybe False id  (fmap (isNothing .unSDelayed) $ unSOptional $ _tbattr $ unTB v )) (_kvvalues $ unTB vs) ))



