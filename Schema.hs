{-# LANGUAGE TupleSections,BangPatterns,OverloadedStrings #-}

module Schema where

import Types
import Data.Unique
import qualified Data.Foldable as F
import Data.Maybe
import Data.String
import Control.Monad.IO.Class
import Data.Monoid
import Utils

import Database.PostgreSQL.Simple

import Data.Vector (Vector)
import qualified Data.Vector as V

import Control.Monad
import Control.Applicative
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Map (Map)
import Data.Set (Set)
import Debug.Trace

import Data.Text.Lazy(Text)
import qualified Data.Text.Lazy as T





createType :: Text ->  Unique -> (Text,Text,Maybe Text,Text,Text,Text,Text,Maybe Text,Maybe Text,Maybe Text) -> Key
createType _ un (t,c,trans,"tsrange",_,_,n,def,_,_) = (Key   c Nothing trans un (nullable n $ KInterval $ Primitive "timestamp without time zone"))
createType _ un (t,c,trans,"tstzrange",_,_,n,def,_,_) = (Key   c Nothing trans un (nullable n $ KInterval $ Primitive "timestamp with time zone"))
createType _ un (t,c,trans,"daterange",_,_,n,def,_,_) = (Key   c Nothing trans un (nullable n $ KInterval $ Primitive "date"))
createType _ un (t,c,trans,"int4range",_,_,n,def,_,_) = (Key   c Nothing trans un (nullable n $ KInterval $ Primitive "int4"))
createType _ un (t,c,trans,"numrange",_,_,n,def,_,_) = (Key   c Nothing trans un (nullable n $ KInterval $ Primitive "numeric"))
createType _ un (t,c,trans,"USER-DEFINED",_,"floatrange",n,def,_,_) = (Key   c Nothing trans un (nullable n $ KInterval $ Primitive "double precision"))
-- Table columns Primitive
createType s un (t,c,trans,"USER-DEFINED",udtschema ,udtname,n,def,_,_) |  udtschema == s = (Key c Nothing trans un (nullable n $ traceShowId $  InlineTable  udtschema udtname ))
createType s un (t,c,trans,"ARRAY",udtschema ,udtname,n,def,_,_) | udtschema == s = (Key c Nothing trans un (nullable n $ KArray $ InlineTable  udtschema $T.drop 1 udtname ))
createType _ un (t,c,trans,"ARRAY",_,i,n,def,p,_) = (Key   c Nothing trans un (nullable n $ KArray $ (Primitive (T.tail i))))
createType _ un (t,c,trans,_,_,"geometry",n,def,p,_) = (Key   c Nothing trans un (nullable n $ Primitive $ (\(Just i) -> i) p))
createType _ un (t,c,trans,_,_,"box3d",n,def,p,_) = (Key   c Nothing trans un (nullable n $ Primitive $  "box3d"))
createType _ un (t,c,trans,ty,_,_,n,def,_,Just dom ) =(Key c   Nothing trans un (serial def . nullable n $ Primitive dom))
createType _ un (t,c,trans,ty,_,_,n,def,_,_) =(Key c   Nothing trans un (serial def . nullable n $ Primitive ty))
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
  -- , hashedGraph :: HashQuery
  -- , hashedGraphInv :: HashQuery
  -- , graphP :: Graph (Set Key) (SqlOperation Table)
  , pluginsMap :: Map (Text,Text,Text) Key
  , conn :: Connection
  , rootconn :: Connection
  }

type TableSchema = (Map (Text,Text) Key,Map (Set Key) Table,Map Text Table)

foreignKeys :: Query
foreignKeys = "select origin_table_name,target_table_name,origin_fks,target_fks from metadata.fks where origin_schema_name = target_schema_name  and  target_schema_name = ?"

queryAuthorization :: Connection -> Text -> Text -> IO (Map Text [Text])
queryAuthorization conn schema user = do
    sq <- query conn aq (schema,user)
    let convert (tname,authorizations) = (tname ,V.toList authorizations)
    return $ M.fromList $ convert <$> sq
  where aq = "select table_name,authorizations from metadata.authorization where table_schema = ? and grantee = ? "

keyTables :: Connection -> Connection -> (Text ,Text)-> IO InformationSchema
keyTables conn userconn (schema ,user) = do
       uniqueMap <- join $ mapM (\i-> (i,) <$> newUnique) <$>  query conn "select o.table_name,o.column_name from information_schema.tables natural join information_schema.columns o where table_schema = ? "(Only schema)
       res2 <- fmap ( (\i@(t,c,o,j,k,l,m,n,d,z)-> (t,) $ createType  schema ((\(t,c,i,j,k,l,m,n,d,z)-> (\(Just i) -> i) $ M.lookup (t,c) (M.fromList uniqueMap)) i) i )) <$>  query conn "select table_name,o.column_name,translation,data_type,udt_schema,udt_name,is_nullable,column_default, type,domain_name from information_schema.tables natural join information_schema.columns  o left join metadata.table_translation t on o.column_name = t.column_name  left join   public.geometry_columns on o.table_schema = f_table_schema  and o.column_name = f_geometry_column where table_schema = ? " (Only schema)
       let
          keyMap = M.fromList keyList
          keyList =  fmap (\(t,k)-> ((t,keyValue k),k)) res2
       let
          lookupKey3 :: (Functor  g, Functor f) => f (Text,g Text) -> f (Text,g Key)
          lookupKey3 = fmap  (\(t,c)-> (t,fmap (\ci -> justError ("no key " <> T.unpack ci) $ M.lookup (t,ci) keyMap) c) )
          lookupKey2 :: Functor f => f (Text,Text) -> f Key
          lookupKey2 = fmap  (\(t,c)-> justError ("nokey" <> show (t,c)) $ M.lookup ( (t,c)) keyMap )
          readTT :: Text ->  TableType
          readTT "BASE TABLE" = ReadWrite
          readTT "VIEW" = ReadOnly
          readTT i =  error $ T.unpack i
       authorization <- queryAuthorization conn schema user
       descMap <- M.fromList . fmap  (\(t,c)-> (t,(\(Just i) -> i) $ M.lookup (t,c) keyMap) ) <$> query conn "SELECT table_name,description FROM metadata.table_description WHERE table_schema = ? " (Only schema)
       transMap <- M.fromList   <$> query conn "SELECT table_name,translation FROM metadata.table_name_translation WHERE schema_name = ? " (Only schema)
       res <- lookupKey3 <$> query conn "SELECT table_name,pks FROM metadata.pks  where schema_name = ?" (Only schema) :: IO [(Text,Vector Key )]
       resTT <- fmap readTT . M.fromList <$> query conn "SELECT table_name,table_type FROM information_schema.tables where table_schema = ? " (Only schema) :: IO (Map Text TableType)
       let lookFk t k =V.toList $ lookupKey2 (fmap (t,) k)
       fks <- M.fromListWith S.union . fmap (\i@(tp,tc,kp,kc) -> (tp,S.singleton $ Path (S.fromList $ lookFk tp kp) (FKJoinTable tp (zip (lookFk tp kp ) (lookFk tc kc)) tc) (S.fromList $ lookFk tc kc))) <$> query conn foreignKeys (Only schema) :: IO (Map Text (Set (Path (Set Key) (SqlOperation Text ) )))
       let all =  M.fromList $ fmap (\(c,l)-> (c,S.fromList $ fmap (\(t,n)-> (\(Just i) -> i) $ M.lookup (t,keyValue n) keyMap ) l )) $ groupSplit (\(t,_)-> t)  res2 :: Map Text (Set Key)
           pks =  (\(c,pksl)-> let
                                  pks = S.fromList $ F.toList pksl
                                  inlineFK =  (fmap (\k -> (\t -> Path (S.singleton k ) (FKInlineTable $ inlineName t) S.empty ) $ keyType k ) .  filter (isInline .keyType ) .  S.toList  )<$> (M.lookup c all)
                                  attr = S.difference ((\(Just i) -> i) $ M.lookup c all) ((S.fromList $maybeToList $ M.lookup c descMap) <> pks)
                                in (pks ,Raw schema  ((\(Just i) -> i) $ M.lookup c resTT) (M.lookup c transMap)  c (maybe [] id $ M.lookup c authorization)  pks (M.lookup  c descMap) (fromMaybe S.empty $ M.lookup c fks    <> fmap S.fromList inlineFK  ) attr )) <$> res :: [(Set Key,Table)]
       let ret@(i1,i2,i3) = (keyMap, M.fromList $ filter (not.S.null .fst)  pks,M.fromList $ fmap (\(_,t)-> (tableName t ,t)) pks)
       paths <- schemaKeys' conn schema ret
       -- let graphI =  graphFromPath (filter (\i -> fst (pbound i) /= snd (pbound i) ) $ paths <> (fmap (fmap ((\(Just i) -> i) . flip M.lookup i3)) <$> concat (fmap (F.toList.snd) (M.toList fks))))
           -- graphP = warshall2 $ graphI
           -- graph = hashGraph $ graphP
           -- invgraph = hashGraphInv' $ graphP
       return  $ InformationSchema schema i1 i2 i3 M.empty userconn conn

inlineName (KOptional i) = inlineName i
inlineName (KArray a ) = inlineName a
inlineName (InlineTable _ i) = i

inlineFullName (KOptional i) = inlineFullName i
inlineFullName (KArray a ) = inlineFullName a
inlineFullName (InlineTable s i) = s <> "." <> i

isInline (KOptional i ) = isInline i
isInline (KArray i ) = isInline i
isInline (InlineTable _ i) = True
isInline _ = False

{-graphFromPath p = Graph {hvertices = fmap fst bs,
                         tvertices = fmap snd bs,
                         edges = fmap pure $ pathMap p
                         }
  where bs = fmap pbound p-}

-- TODO : Implement ordinal information
schemaKeys' :: Connection -> Text -> TableSchema -> IO [PathQuery]
schemaKeys' conn schema (keyTable,map,_) = do
       resView <- query conn "select table_name,pks,origin_fks from metadata.fks join metadata.pks on origin_table_name = table_name and origin_schema_name = schema_name where schema_name = ?" (Only schema)
       let
           viewRels = (\(pk,fk) -> Path pk (FetchTable $ (\(Just i) -> i) $ M.lookup pk map) fk). (\(t,pk,fks) -> (S.fromList $ (\i->(\(Just i) -> i) $ M.lookup (t,i) keyTable ) <$> (V.toList pk) ,S.fromList $ (\i->(\(Just i) -> i) $ M.lookup (t,i) keyTable ) <$>  (V.toList fks) ) ) <$> resView
       return viewRels



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
  return $ Key name Nothing Nothing    un ty
