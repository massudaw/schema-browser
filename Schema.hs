{-# LANGUAGE TupleSections,BangPatterns,OverloadedStrings #-}

module Schema where

import Query
import Data.Unique
import Warshal
import qualified Data.Foldable as F
import Data.Foldable (Foldable)
import Data.Traversable (Traversable)
import Data.Char ( isAlpha )
import Data.Maybe
import Data.Functor.Identity
import Data.Monoid


import Data.GraphViz (preview)
import Data.Graph.Inductive.PatriciaTree
import qualified Data.Graph.Inductive.Graph as PG
import qualified Data.GraphViz.Attributes as GA
import qualified Data.GraphViz.Attributes.Complete as GAC

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



createType :: Unique -> (Text,Text,Maybe Text ,Text,Text,Text,Maybe Text,Maybe Text) -> Key
createType un (t,c,trans,"tsrange",_,n,def,_) = (Key   c Nothing trans un (nullable n $ KInterval $ Primitive "timestamp without time zone"))
createType un (t,c,trans,"int4range",_,n,def,_) = (Key   c Nothing trans un (nullable n $ KInterval $ Primitive "int4"))
createType un (t,c,trans,"ARRAY",i,n,def,p) = (Key   c Nothing trans un (nullable n $ KArray $ (Primitive (T.tail i))))
createType un (t,c,trans,_,"geometry",n,def,p) = (Key   c Nothing trans un (nullable n $ Primitive $ (\(Just i) -> i) p))
createType un (t,c,trans,ty,_,n,def,_) =(Key c   Nothing trans un (serial def . nullable n $ Primitive ty))
--createType un v = error $ show v

serial (Just xs ) t = if T.isPrefixOf  "nextval" xs then KSerial t else t
serial Nothing t = t

nullable "YES" t = KOptional t
nullable "NO" t = t

keyMap (i,_,_,_,_,_) = i
pkMap (_,i,_,_,_,_) = i
tableMap (_,_,i,_,_,_) = i
hashedGraph (_,_,_,i,_,_) = i
hashedGraphInv (_,_,_,_,i,_) = i
graphP (_,_,_,_,_,i) = i

-- type InformationSchema = (Map (Text,Text) Key,Map (Set Key) Table,Map Text Table, HashSchema Key Table, Map (Set Key) (Map (Set Key) (Path Key Table)),Graph Key Table )
type InformationSchema = (Map (Text,Text) Key,Map (Set Key) Table,Map Text Table, HashSchema Key (SqlOperation Table), Map (Set Key) (Map (Set Key) (Path Key (SqlOperation Table))),Graph Key (SqlOperation Table) )
type TableSchema = (Map (Text,Text) Key,Map (Set Key) Table,Map Text Table)

foreignKeys :: Query
foreignKeys = "select clc.relname,cl.relname,array_agg(att2.attname),   array_agg(att.attname) from    (select  con1.conname,unnest(con1.conkey) as parent, unnest(con1.confkey) as child, con1.confrelid,con1.conrelid  from   pg_class cl     join pg_namespace ns on cl.relnamespace = ns.oid   join pg_constraint con1 on con1.conrelid = cl.oid where   ns.nspname = ? and con1.contype = 'f' ) con  join pg_attribute att on  att.attrelid = con.confrelid and att.attnum = con.child  join pg_class cl on  cl.oid = con.confrelid   join pg_class clc on  clc.oid = con.conrelid   join pg_attribute att2 on  att2.attrelid = con.conrelid and att2.attnum = con.parent   group by clc.relname, cl.relname,con.conname union select origin_table_name,target_table_name,origin_fks,target_fks from metadata.view_fks where origin_schema_name = ? and target_schema_name = origin_schema_name "

keyTables :: Connection -> Text -> IO InformationSchema
keyTables conn schema = do
       uniqueMap <- join $ mapM (\i-> (i,) <$> newUnique) <$>  query conn "select o.table_name,o.column_name from information_schema.tables natural join information_schema.columns o where table_schema = ? "(Only schema)
       res2 <- fmap ((\i@(t,c,o,j,k,l,m,n)-> (t,) $ createType  ((\(t,c,i,j,k,l,m,n)-> (\(Just i) -> i) $ M.lookup (t,c) (M.fromList uniqueMap)) i) i )) <$>  query conn "select table_name,o.column_name,translation,data_type,udt_name,is_nullable,column_default, type from information_schema.tables natural join information_schema.columns  o left join metadata.table_translation t on o.column_name = t.column_name  left join   public.geometry_columns on o.table_schema = f_table_schema  and o.column_name = f_geometry_column where table_schema = ? " (Only schema)
       let keyMap = M.fromList keyList
           keyListSet = groupSplit (\(c,k)-> c) keyList
           keyList =  fmap (\(t,k)-> ((t,keyValue k),k)) res2
           ambigous = filter (\(_,l)->length (nubBy (\i j -> keyType i == keyType j) $ fmap snd l) > 1) keyListSet
       -- Log Ambiguous Keys (With same name and different types)
       when (length ambigous > 0) $ do
         print "Ambigous Key Types"
         mapM_ (\(c,l)-> print $ nubBy (\i j -> keyType i == keyType j) $ fmap snd l) ambigous
       let
        lookupKey' :: Functor f => f (Text,Text) -> f (Text,Key)
        lookupKey' = fmap  (\(t,c)-> (t,(\(Just i) -> i) $ M.lookup (t,c) keyMap) )
        lookupKey2 :: Functor f => f (Text,Text) -> f Key
        lookupKey2 = fmap  (\(t,c)->(\(Just i) -> i) $ M.lookup (t,c) keyMap )
        readTT :: Text ->  TableType
        readTT "BASE TABLE" = ReadWrite
        readTT "VIEW" = ReadOnly
       descMap <- M.fromList . fmap  (\(t,c)-> (t,(\(Just i) -> i) $ M.lookup (t,c) keyMap) ) <$> query conn "SELECT table_name,description FROM metadata.table_description WHERE table_schema = ? " (Only schema)
       res <- lookupKey' <$> query conn "SELECT table_name,column_name FROM information_schema.key_column_usage natural join information_schema.table_constraints WHERE table_schema = ?  AND constraint_type='PRIMARY KEY' union select table_name,unnest(pk_column) as column_name from metadata.view_pk where table_schema = ?" (schema,schema) :: IO [(Text,Key)]
       resTT <- fmap readTT . M.fromList <$> query conn "SELECT table_name,table_type FROM information_schema.tables where table_schema = ? " (Only schema) :: IO (Map Text TableType)
       print res
       print res
       let lookFk t k =V.toList $ lookupKey2 (fmap (t,) k)
       fks <- M.fromListWith S.union . fmap (\(tp,tc,kp,kc) -> (tp,S.singleton $ Path (S.fromList $ lookFk tp kp) (FKJoinTable tp (zip (lookFk tp kp ) (lookFk tc kc)) tc) (S.fromList $ lookFk tc kc))) <$> query conn foreignKeys (schema,schema) :: IO (Map Text (Set (Path Key (SqlOperation Text))))
       let all =  M.fromList $ fmap (\(c,l)-> (c,S.fromList $ fmap (\(t,n)-> (\(Just i) -> i) $ M.lookup (t,keyValue n) keyMap ) l )) $ groupSplit (\(t,_)-> t)  res2 :: Map Text (Set Key)
           pks =  fmap (\(c,l)-> let
                                  pks = S.fromList $ fmap snd l
                                  attr = S.difference ((\(Just i) -> i) $ M.lookup c all) pks
                                in (pks ,Raw (schema , (\(Just i) -> i) $ M.lookup c resTT) c pks (M.lookup  c descMap) (fromMaybe S.empty $ M.lookup c fks ) attr )) $ groupSplit (\(t,_)-> t)  res :: [(Set Key,Table)]
       let ret@(i1,i2,i3) = (keyMap, M.fromList  pks,M.fromList $ fmap (\(_,t)-> (tableName t ,t)) pks)
       paths <- schemaKeys' conn schema ret
       let graphI =  graphFromPath (paths <> (fmap (fmap ((\(Just i) -> i) . flip M.lookup i3)) <$> concat (fmap (F.toList.snd) (M.toList fks))))
           graphP = warshall2 $ graphI
           graph = hashGraph $ graphP
           invgraph = hashGraphInv' $ graphP
       print graphI
       print graphP
       return (i1,i2,i3,graph,invgraph,graphP)


schemaAttributes :: Connection -> Text -> InformationSchema -> IO [Path Key Table]
schemaAttributes conn schema (keyTable,map,_,_,_,_) = do
       res <- fmap (fmap (\(t,c,ckn)-> (t,ckn,(\(Just i) -> i) $ M.lookup (t,c) keyTable))) $  query conn "SELECT table_name,column_name,constraint_name FROM information_schema.key_column_usage natural join information_schema.table_constraints WHERE table_schema = ? AND constraint_type='PRIMARY KEY'" (Only schema) :: IO [(Text,Text,Key)]
       let pks =  fmap (\(c,l)-> (c,S.fromList $ fmap (\(_,_,j)-> j ) l )) $ groupSplit (\(t,ck,_)-> (t,ck))  res :: [((Text,Text),Set Key)]
       res2 <- fmap (fmap (\(t,c)-> (t,(\(Just i) -> i) $ M.lookup (t,c) keyTable))) $  query conn "SELECT table_name,column_name FROM information_schema.tables natural join information_schema.columns WHERE table_schema = ? AND table_type='BASE TABLE'" (Only schema):: IO [(Text,Key)]
       let fks =  fmap (\(c,l)-> (c,fmap (\(_,j)-> j) l )) $ groupSplit (\(t,_)-> t)  res2 :: [(Text,[Key])]
           rels = [ Path pkl ((\(Just i) -> i) $ M.lookup pkl map) (S.singleton fkli) |
                    (tfk,fkl)<- fks,
                    fkli <- fkl,
                    ((tpk,pk),pkl)<- pks,
                    not $ fkli `S.member` pkl,
                    tfk == tpk]
       return rels

groupSplit f = fmap (\i-> (f $ head i , i)) . groupWith f

graphFromPath p = Graph {hvertices = fmap fst bs,
                         tvertices = fmap snd bs,
                         edges = pathMap p
                         }
  where bs = fmap pbound p

-- TODO : Implement ordinal information
schemaKeys' :: Connection -> Text -> TableSchema -> IO [Path Key (SqlOperation Table)]
schemaKeys' conn schema (keyTable,map,_) = do
       res <- fmap (fmap (\(t,c,ckn)-> (t,ckn,(\(Just i) -> i) $ M.lookup (t,c) keyTable ))) $  query conn "SELECT table_name,column_name,constraint_name FROM information_schema.key_column_usage natural join information_schema.table_constraints WHERE table_schema = ? AND  constraint_type='PRIMARY KEY'" (Only schema) :: IO [(Text,Text,Key)]
       let pks =  fmap (\(c,l)-> (c,S.fromList $ fmap (\(_,_,j)-> j ) l )) $ groupSplit (\(t,ck,_)-> (t,ck))  res :: [((Text,Text),Set Key)]
       res2 <- fmap (fmap (\(t,c,ckn)-> (t,ckn,(\(Just i) -> i) $ M.lookup (t,c) keyTable ))) $  query conn "SELECT kc.table_name,kc.column_name,constraint_name FROM information_schema.key_column_usage kc natural join information_schema.table_constraints  WHERE kc.table_schema = ?  AND constraint_type='FOREIGN KEY'" (Only schema):: IO [(Text,Text,Key)]
       resView <- query conn "select table_name,pk_column,origin_fks from metadata.view_fks join metadata.view_pk on origin_table_name = table_name and origin_schema_name = table_schema where table_schema = ? " (Only schema)
       let fks =  fmap (\(c,l)-> (c,S.fromList $ fmap (\(_,_,j)-> j) l )) $ groupSplit (\(t,ck,_)-> (t,ck))  res2 :: [((Text,Text),Set Key)]
           rels = [ Path pkl (FetchTable $ (\(Just i) -> i) $ M.lookup pkl map) fkl |
                    ((tfk,fk),fkl)<- fks,
                    ((tpk,pk),pkl)<- pks,
                    tfk == tpk]
           viewRels = (\(pk,fk) -> Path pk (FetchTable $ (\(Just i) -> i) $ M.lookup pk map) fk). (\(t,pk,fks) -> (S.fromList $ (\i->(\(Just i) -> i) $ M.lookup (t,i) keyTable ) <$> (V.toList pk) ,S.fromList $ (\i->(\(Just i) -> i) $ M.lookup (t,i) keyTable ) <$>  (V.toList fks) ) ) <$> resView
       return $ rels <> viewRels



projectAllTable
  :: Traversable t => Map (Set Key) Table
     -> HashSchema Key (SqlOperation Table)
     -> QueryT Identity (t KAttribute)
     -> Table
     -> (t KAttribute, (HashSchema Key (SqlOperation Table), Table))
projectAllTable baseTables hashGraph m  table@(Raw _ _ bkey _ _ _)  = runQuery  m (hashGraph,Base bkey $ From table  bkey)


projectAllKeys
  :: Traversable t => Map (Set Key) Table
     -> HashSchema Key (SqlOperation Table)
     -> QueryT Identity (t KAttribute)
     -> Set Key
     -> (t KAttribute, (HashSchema Key (SqlOperation Table), Table))
projectAllKeys baseTables hashGraph m bkey
  = case M.lookup bkey baseTables  of
      Just t ->   runQuery  m (hashGraph,Base bkey $ From t bkey)
      Nothing -> error $  "No baseTable for key " <> show ( fmap showKey (F.toList bkey)) -- <> " in baseMap " <> show (M.mapKeys (S.mapMonotonic showKey) baseTables)

buildQuery q =   "SELECT * FROM " <> fromString (T.unpack $ showTable q)

