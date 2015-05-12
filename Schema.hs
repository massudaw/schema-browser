{-# LANGUAGE TupleSections,BangPatterns,OverloadedStrings #-}

module Schema where

import Types
import Query
import Data.Unique
import Warshal
import qualified Data.Foldable as F
import Data.Foldable (Foldable)
import Data.Traversable (Traversable)
import Data.Char ( isAlpha )
import Data.Maybe
import Data.String
import Control.Monad.IO.Class
import Data.Functor.Identity
import Data.Monoid


import Database.PostgreSQL.Simple
import Database.PostgreSQL.Simple.ToField

import Data.Vector (Vector)
import qualified Data.Vector as V

import Control.Monad
import GHC.Exts
import Data.Tuple
import Control.Applicative
import Data.List ( nubBy,nub, sort,intercalate,sortBy,isInfixOf )
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Map (Map)
import Data.Set (Set)
import Debug.Trace

import Data.Text.Lazy(Text)
import qualified Data.Text.Lazy as T
import qualified Data.ByteString.Char8 as BS





createType :: Unique -> (Text,Text,Maybe Text,Text,Text,Text,Text,Maybe Text,Maybe Text,Maybe Text) -> Key
createType un (t,c,trans,"tsrange",_,_,n,def,_,_) = (Key   c Nothing trans un (nullable n $ KInterval $ Primitive "timestamp without time zone"))
createType un (t,c,trans,"int4range",_,_,n,def,_,_) = (Key   c Nothing trans un (nullable n $ KInterval $ Primitive "int4"))
createType un (t,c,trans,"numrange",_,_,n,def,_,_) = (Key   c Nothing trans un (nullable n $ KInterval $ Primitive "numeric"))
createType un (t,c,trans,"USER-DEFINED",_,"floatrange",n,def,_,_) = (Key   c Nothing trans un (nullable n $ KInterval $ Primitive "double precision"))
-- Table columns Primitive
createType un (t,c,trans,"USER-DEFINED",udtschema ,udtname,n,def,_,_) |  udtschema == "incendio" = (Key c Nothing trans un (nullable n $ traceShowId $  InlineTable  udtschema udtname ))
createType un (t,c,trans,"ARRAY",udtschema ,udtname,n,def,_,_) | udtschema == "incendio" = (Key c Nothing trans un (nullable n $ KArray $ InlineTable  udtschema $T.drop 1 udtname ))
createType un (t,c,trans,"ARRAY",_,i,n,def,p,_) = (Key   c Nothing trans un (nullable n $ KArray $ (Primitive (T.tail i))))
createType un (t,c,trans,_,_,"geometry",n,def,p,_) = (Key   c Nothing trans un (nullable n $ Primitive $ (\(Just i) -> i) p))
createType un (t,c,trans,_,_,"box3d",n,def,p,_) = (Key   c Nothing trans un (nullable n $ Primitive $  "box3d"))
createType un (t,c,trans,ty,_,_,n,def,_,Just dom ) =(Key c   Nothing trans un (serial def . nullable n $ Primitive dom))
createType un (t,c,trans,ty,_,_,n,def,_,_) =(Key c   Nothing trans un (serial def . nullable n $ Primitive ty))
--createType un v = error $ show v

serial (Just xs ) t = if T.isPrefixOf  "nextval" xs then KSerial t else t
serial Nothing t = t

nullable "YES" t = KOptional t
nullable "NO" t = t

data InformationSchema
  = InformationSchema
  { keyMap :: Map (Text,Text) Key
  , pkMap :: Map (Set Key) Table
  , tableMap :: Map Text Table
  , hashedGraph :: HashQuery
  , hashedGraphInv :: HashQuery
  , graphP :: Graph (Set Key) (SqlOperation Table)
  , pluginsMap :: Map (Text,Text,Text) Key
  , conn :: Connection
  }

type TableSchema = (Map (Text,Text) Key,Map (Set Key) Table,Map Text Table)

foreignKeys :: Query
foreignKeys = "select origin_table_name,target_table_name,origin_fks,target_fks from metadata.fks where origin_schema_name = target_schema_name  and  target_schema_name = ?"


keyTables :: Connection -> Text -> IO InformationSchema
keyTables conn schema = do
       uniqueMap <- join $ mapM (\i-> (i,) <$> newUnique) <$>  query conn "select o.table_name,o.column_name from information_schema.tables natural join information_schema.columns o where table_schema = ? "(Only schema)
       res2 <- fmap ( (\i@(t,c,o,j,k,l,m,n,d,z)-> (t,) $ createType  ((\(t,c,i,j,k,l,m,n,d,z)-> (\(Just i) -> i) $ M.lookup (t,c) (M.fromList uniqueMap)) i) i )) <$>  query conn "select table_name,o.column_name,translation,data_type,udt_schema,udt_name,is_nullable,column_default, type,domain_name from information_schema.tables natural join information_schema.columns  o left join metadata.table_translation t on o.column_name = t.column_name  left join   public.geometry_columns on o.table_schema = f_table_schema  and o.column_name = f_geometry_column where table_schema = ? " (Only schema)
       let keyMap = M.fromList keyList
           keyListSet = groupSplit (\(c,k)-> c) keyList
           keyList =  fmap (\(t,k)-> ((t,keyValue k),k)) res2
       let
        lookupKey' :: Functor f => f (Text,Text) -> f (Text,Key)
        lookupKey' = fmap  (\(t,c)-> (t,(\(Just i) -> i) $ M.lookup (t,c) keyMap) )
        lookupKey2 :: Functor f => f (Text,Text) -> f Key
        lookupKey2 = fmap  (\(t,c)-> justError ("nokey" <> show (t,c)) $ M.lookup ( (t,c)) keyMap )
        readTT :: Text ->  TableType
        readTT "BASE TABLE" = ReadWrite
        readTT "VIEW" = ReadOnly
        readTT i =  error $ T.unpack i
       descMap <- M.fromList . fmap  (\(t,c)-> (t,(\(Just i) -> i) $ M.lookup (t,c) keyMap) ) <$> query conn "SELECT table_name,description FROM metadata.table_description WHERE table_schema = ? " (Only schema)
       res <- lookupKey' <$> query conn "SELECT table_name,column_name FROM information_schema.key_column_usage natural join information_schema.table_constraints WHERE table_schema = ?  AND constraint_type='PRIMARY KEY' union select table_name,unnest(pk_column) as column_name from metadata.view_pk where table_schema = ?" (schema,schema) :: IO [(Text,Key)]
       resTT <- fmap readTT . M.fromList <$> query conn "SELECT table_name,table_type FROM information_schema.tables where table_schema = ? " (Only schema) :: IO (Map Text TableType)
       let lookFk t k =V.toList $ lookupKey2 (fmap (t,) k)
       fks <- M.fromListWith S.union . fmap (\i@(tp,tc,kp,kc) -> (tp,S.singleton $ Path (S.fromList $ lookFk tp kp) (FKJoinTable tp (zip (lookFk tp kp ) (lookFk tc kc)) tc) (S.fromList $ lookFk tc kc))) <$> query conn foreignKeys (Only schema) :: IO (Map Text (Set (Path (Set Key) (SqlOperation Text ) )))
       let all =  M.fromList $ fmap (\(c,l)-> (c,S.fromList $ fmap (\(t,n)-> (\(Just i) -> i) $ M.lookup (t,keyValue n) keyMap ) l )) $ groupSplit (\(t,_)-> t)  res2 :: Map Text (Set Key)
           pks =  fmap (\(c,l)-> let
                                  pks = S.fromList $ fmap snd l
                                  inlineFK =  (fmap (\k -> (\t -> Path (S.singleton k ) (FKInlineTable $ inlineName t) S.empty ) $ keyType k ) .  filter (isInline .keyType ) .  S.toList  )<$> (M.lookup c all)
                                  attr = S.difference ((\(Just i) -> i) $ M.lookup c all) ((S.fromList $maybeToList $ M.lookup c descMap) <> pks)
                                in (pks ,Raw (schema , (\(Just i) -> i) $ M.lookup c resTT) c pks (M.lookup  c descMap) (fromMaybe S.empty $ M.lookup c fks    <> fmap S.fromList inlineFK  ) attr )) $ groupSplit (\(t,_)-> t)  res :: [(Set Key,Table)]
       let ret@(i1,i2,i3) = (keyMap, M.fromList  pks,M.fromList $ fmap (\(_,t)-> (tableName t ,t)) pks)
       paths <- schemaKeys' conn schema ret
       let graphI =  graphFromPath (filter (\i -> fst (pbound i) /= snd (pbound i) ) $ paths <> (fmap (fmap ((\(Just i) -> i) . flip M.lookup i3)) <$> concat (fmap (F.toList.snd) (M.toList fks))))
           graphP = warshall2 $ graphI
           graph = hashGraph $ graphP
           invgraph = hashGraphInv' $ graphP
       return  $ InformationSchema i1 i2 i3 graph invgraph graphP M.empty conn

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

graphFromPath p = Graph {hvertices = fmap fst bs,
                         tvertices = fmap snd bs,
                         edges = fmap pure $ pathMap p
                         }
  where bs = fmap pbound p

-- TODO : Implement ordinal information
schemaKeys' :: Connection -> Text -> TableSchema -> IO [PathQuery]
schemaKeys' conn schema (keyTable,map,_) = do
       resView <- query conn "select table_name,pks,origin_fks from metadata.fks join metadata.pks on origin_table_name = table_name and origin_schema_name = schema_name where schema_name = ?" (Only schema)
       let
           viewRels = (\(pk,fk) -> Path pk (FetchTable $ (\(Just i) -> i) $ M.lookup pk map) fk). (\(t,pk,fks) -> (S.fromList $ (\i->(\(Just i) -> i) $ M.lookup (t,i) keyTable ) <$> (V.toList pk) ,S.fromList $ (\i->(\(Just i) -> i) $ M.lookup (t,i) keyTable ) <$>  (V.toList fks) ) ) <$> resView
       return viewRels



projectAllTable
  :: Traversable t => Map (Set Key) Table
     -> HashQuery
       -> QueryT Identity (t KAttribute)
     -> Table
     -> (t KAttribute, (HashQuery , Table))
projectAllTable baseTables hashGraph m  table@(Raw _ _ bkey _ _ _)  = runQuery  m (hashGraph,Base bkey $ From table  bkey)


projectAllKeys
  :: Traversable t => Map (Set Key) Table
     -> HashQuery
     -> QueryT Identity (t KAttribute)
     -> Set Key
     -> (t KAttribute, (HashQuery , Table))
projectAllKeys baseTables hashGraph m bkey
  = case M.lookup bkey baseTables  of
      Just t ->   runQuery  m (hashGraph,Base bkey $ From t bkey)
      Nothing -> error $  "No baseTable for key " <> show ( fmap showKey (F.toList bkey)) -- <> " in baseMap " <> show (M.mapKeys (S.mapMonotonic showKey) baseTables)

buildQuery q =   "SELECT * FROM " <> fromString (T.unpack $ showTable q)


withInf s f = withConn s (f <=< flip keyTables s)
withConnInf s f = withConn s (\conn ->  f =<< liftIO ( flip keyTables s conn) )

withConn s action =  do
  conn <- liftIO $connectPostgreSQL $ "user=postgres password=queijo dbname=" <> fromString (T.unpack s)
  action conn

lookTable :: InformationSchema -> Text -> Table
lookTable inf t = justError ("no table: " <> T.unpack t) $ M.lookup t (tableMap inf)

lookKey :: InformationSchema -> Text -> Text -> Key
lookKey inf t k = justError ("table " <> T.unpack t <> " has no key " <> T.unpack k ) $ M.lookup (t,k) (keyMap inf)



newKey name ty = do
  un <- newUnique
  return $ Key name Nothing Nothing    un ty
