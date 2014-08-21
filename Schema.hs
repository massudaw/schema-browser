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



createType :: Map Text Unique -> (Text,Text,Maybe Text ,Text,Text,Text,Maybe Text) -> (Text,Key)
createType un (t,c,trans,"tsrange",_,n,_) = (t,Key   c trans (fromJust $ M.lookup c un) (nullable n $ KInterval $ Primitive "timestamp without time zone"))
createType un (t,c,trans,_,"geometry",n,p) = (t,Key   c trans (fromJust $ M.lookup c un) (nullable n $ Primitive $ fromJust p))
createType un (t,c,trans,ty,_,n,_) =(t,Key c   trans (fromJust $M.lookup c un) (nullable n $ Primitive ty))
--createType un v = error $ show v

nullable "YES" t = KOptional t
nullable "NO" t = t

keyMap (i,_,_) = i
pkMap (_,i,_) = i
tableMap (_,_,i) = i

type InformationSchema = (Map (Text,Text) Key,Map (Set Key) Table,Map Text Table)

foreignKeys :: Query
foreignKeys = "select clc.relname,cl.relname,array_agg(att2.attname),   array_agg(att.attname) from    (select  unnest(con1.conkey) as parent, unnest(con1.confkey) as child, con1.confrelid,con1.conrelid  from   pg_class cl     join pg_namespace ns on cl.relnamespace = ns.oid   join pg_constraint con1 on con1.conrelid = cl.oid where   ns.nspname = ? and con1.contype = 'f' ) con  join pg_attribute att on  att.attrelid = con.confrelid and att.attnum = con.child  join pg_class cl on  cl.oid = con.confrelid   join pg_class clc on  clc.oid = con.conrelid   join pg_attribute att2 on  att2.attrelid = con.conrelid and att2.attnum = con.parent   group by clc.relname, cl.relname"

-- TODO: Properly treat Maybe Key
-- TODO: Load Foreigh Key Information
keyTables :: Connection -> Text -> IO InformationSchema
keyTables conn schema = do
       uniqueMap <- join $ mapM (\(Only i)-> (i,) <$> newUnique) <$>  query conn "select o.column_name from information_schema.tables natural join information_schema.columns o where table_schema = ? and table_type='BASE TABLE'" (Only schema) -- :: IO (Map Text Unique)
       res2 <- fmap (createType (M.fromList uniqueMap)) <$>  query conn "select table_name,o.column_name,translation,data_type,udt_name,is_nullable, type from information_schema.tables natural join information_schema.columns  o left join metadata.table_translation t on o.column_name = t.column_name  left join   public.geometry_columns on o.table_schema = f_table_schema  and o.column_name = f_geometry_column where table_schema = ? and table_type='BASE TABLE'" (Only schema)
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
        lookupKey' = fmap  (\(t,c)-> (t,fromJust $ M.lookup (t,c) keyMap) )
        lookupKey2 :: Functor f => f (Text,Text) -> f Key
        lookupKey2 = fmap  (\(t,c)->fromJust $ M.lookup (t,c) keyMap )
       descMap <- M.fromList . fmap  (\(t,c)-> (t,fromJust $ M.lookup (t,c) keyMap) ) <$> query conn "SELECT table_name,description FROM metadata.table_description WHERE table_schema = ? " (Only schema)
       res <- lookupKey' <$> query conn "SELECT table_name,column_name FROM information_schema.key_column_usage natural join information_schema.table_constraints WHERE table_schema = ?  AND constraint_type='PRIMARY KEY'" (Only schema) :: IO [(Text,Key)]
       print res
       let lookFk t k =S.fromList $ V.toList $ lookupKey2 (fmap (t,) k)
       fks <- M.fromListWith S.union . fmap (\(tp,tc,kp,kc) -> (tp,S.singleton $ Path (lookFk tp kp) tc (lookFk tc kc))) <$> query conn foreignKeys (Only schema) :: IO (Map Text (Set (Path Key Text)))
       let all =  M.fromList $ fmap (\(c,l)-> (c,S.fromList $ fmap (\(t,n)-> fromJust $ M.lookup (t,keyValue n) keyMap ) l )) $ groupSplit (\(t,_)-> t)  res2 :: Map Text (Set Key)
           pks =  fmap (\(c,l)-> let
                                  pks = S.fromList $ fmap (\(_,j)-> j ) l
                                  attr = S.difference (fromJust $ M.lookup c all) pks
                                in (pks ,Raw schema c pks (M.lookup  c descMap) (fromMaybe S.empty $ M.lookup c fks ) attr )) $ groupSplit (\(t,_)-> t)  res :: [(Set Key,Table)]
       let ret = (keyMap, M.fromList $ fmap (\(c,t)-> (c,t)) pks,M.fromList $ fmap (\(_,t)-> (tableName t ,t)) pks)
       return ret


schemaAttributes :: Connection -> Text -> InformationSchema -> IO [Path Key Table]
schemaAttributes conn schema (keyTable,map,_) = do
       res <- fmap (fmap (\(t,c,ckn)-> (t,ckn,fromJust $ M.lookup (t,c) keyTable))) $  query conn "SELECT table_name,column_name,constraint_name FROM information_schema.key_column_usage natural join information_schema.table_constraints WHERE table_schema = ? AND constraint_type='PRIMARY KEY'" (Only schema) :: IO [(Text,Text,Key)]
       let pks =  fmap (\(c,l)-> (c,S.fromList $ fmap (\(_,_,j)-> j ) l )) $ groupSplit (\(t,ck,_)-> (t,ck))  res :: [((Text,Text),Set Key)]
       res2 <- fmap (fmap (\(t,c)-> (t,fromJust $ M.lookup (t,c) keyTable))) $  query conn "SELECT table_name,column_name FROM information_schema.tables natural join information_schema.columns WHERE table_schema = ? AND table_type='BASE TABLE'" (Only schema):: IO [(Text,Key)]
       let fks =  fmap (\(c,l)-> (c,fmap (\(_,j)-> j) l )) $ groupSplit (\(t,_)-> t)  res2 :: [(Text,[Key])]
           rels = [ Path pkl (fromJust $ M.lookup pkl map) (S.singleton fkli) |
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
schemaKeys :: Connection -> Text -> InformationSchema -> IO [Path Key Table]
schemaKeys conn schema (keyTable,map,_) = do
       res <- fmap (fmap (\(t,c,ckn)-> (t,ckn,fromJust $ M.lookup (t,c) keyTable ))) $  query conn "SELECT table_name,column_name,constraint_name FROM information_schema.key_column_usage natural join information_schema.table_constraints WHERE table_schema = ? AND  constraint_type='PRIMARY KEY'" (Only schema) :: IO [(Text,Text,Key)]
       let pks =  fmap (\(c,l)-> (c,S.fromList $ fmap (\(_,_,j)-> j ) l )) $ groupSplit (\(t,ck,_)-> (t,ck))  res :: [((Text,Text),Set Key)]
       res2 <- fmap (fmap (\(t,c,ckn)-> (t,ckn,fromJust $ M.lookup (t,c) keyTable ))) $  query conn "SELECT kc.table_name,kc.column_name,constraint_name FROM information_schema.key_column_usage kc natural join information_schema.table_constraints  WHERE kc.table_schema = ?  AND constraint_type='FOREIGN KEY'" (Only schema):: IO [(Text,Text,Key)]
       let fks =  fmap (\(c,l)-> (c,S.fromList $ fmap (\(_,_,j)-> j) l )) $ groupSplit (\(t,ck,_)-> (t,ck))  res2 :: [((Text,Text),Set Key)]
           rels = [ Path pkl (fromJust $ M.lookup pkl map) fkl |
                    ((tfk,fk),fkl)<- fks,
                    ((tpk,pk),pkl)<- pks,
                    tfk == tpk]
       return rels

projectAllKeys
  :: Traversable t => Map (Set Key) Table
     -> HashSchema Key Table
     -> QueryT (t Key)
     -> Set Key
     -> (t Key , (HashSchema Key Table, Table))
projectAllKeys baseTables hashGraph m bkey
  = case M.lookup bkey baseTables  of
      Just t ->   runQuery  m (hashGraph,Base bkey $ From t bkey)
      Nothing -> error $  "No baseTable for key " <> showVertex bkey

buildQuery q =   "SELECT * FROM " <> fromString (T.unpack $ showTable q)

