{-# LANGUAGE BangPatterns,OverloadedStrings #-}

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



createType :: (Text,Text,Text,Text) -> IO (Text,Key)
createType (t,c,ty,"YES") =do
  uq <- newUnique
  return (t,Key c uq (KOptional $ Primitive ty))
createType (t,c,ty,"NO") = do
  uq <- newUnique
  return (t,Key c  uq (Primitive ty))
createType v = error $ show v

type InformationSchema = (Map Text Key,Map (Set Key) Table)

foreignKeys :: Query
foreignKeys = "select clc.relname,cl.relname,array_agg(att2.attname),   array_agg(att.attname) from    (select  unnest(con1.conkey) as parent, unnest(con1.confkey) as child, con1.confrelid,con1.conrelid  from   pg_class cl     join pg_namespace ns on cl.relnamespace = ns.oid   join pg_constraint con1 on con1.conrelid = cl.oid where   ns.nspname = ? and con1.contype = 'f' ) con  join pg_attribute att on  att.attrelid = con.confrelid and att.attnum = con.child  join pg_class cl on  cl.oid = con.confrelid   join pg_class clc on  clc.oid = con.conrelid   join pg_attribute att2 on  att2.attrelid = con.conrelid and att2.attnum = con.parent   group by clc.relname, cl.relname"

-- TODO: Properly treat Maybe Key
-- TODO: Load Foreigh Key Information
keyTables :: Connection -> Text -> IO InformationSchema
keyTables conn schema = do
       res2 <- join $ sequence . fmap createType <$>  query conn "SELECT table_name,column_name,data_type,is_nullable FROM information_schema.tables natural join information_schema.columns  WHERE table_schema = ? AND table_type='BASE TABLE'" (Only schema)
       let keyMap = M.fromList keyList
           keyListSet = groupSplit (\(c,k)-> c) keyList
           keyList =  fmap (\(t,k@(Key c _ _))-> (c,k)) res2
           ambigous = filter (\(_,l)->length (nubBy (\i j -> keyType i == keyType j) $ fmap snd l) > 1) keyListSet
       -- Log Ambiguous Keys (With same name and different types)
       when (length ambigous > 0) $ do
         print "Ambigous Key Types"
         mapM_ (\(c,l)-> print $ nubBy (\i j -> keyType i == keyType j) $ fmap snd l) ambigous
       let
        lookupKey :: Functor f => f Text -> f Key
        lookupKey = fmap (fromJust . flip M.lookup keyMap)
       descMap <- M.fromList . fmap lookupKey <$> query conn "SELECT table_name,description FROM public.table_description WHERE table_schema = ? " (Only schema)
       res <- fmap lookupKey <$> query conn "SELECT table_name,column_name FROM information_schema.tables natural join information_schema.columns natural join information_schema.key_column_usage natural join information_schema.table_constraints WHERE table_schema = ? AND table_type='BASE TABLE' AND constraint_type='PRIMARY KEY'" (Only schema) :: IO [(Text,Key)]
       fks <- M.fromListWith S.union . fmap (\(tp,tc,kp,kc) -> (tp,S.singleton $ Path (S.fromList $ V.toList $ lookupKey kp) tc (S.fromList $ V.toList $ lookupKey kc))) <$> query conn foreignKeys (Only schema) :: IO (Map Text (Set (Path Key Text)))
       let all =  M.fromList $ fmap (\(c,l)-> (c,S.fromList $ fmap (\(_,Key n _ _)-> fromJust $ M.lookup n keyMap ) l )) $ groupSplit (\(t,_)-> t)  res2 :: Map Text (Set Key)
           pks =  fmap (\(c,l)-> let pks = S.fromList $ fmap (\(_,j)-> j ) l
                                in (pks ,Raw schema c pks (M.lookup  c descMap) (fromMaybe S.empty $ M.lookup c fks ) (fromJust $ M.lookup c all) )) $ groupSplit (\(t,_)-> t)  res :: [(Set Key,Table)]
       return (keyMap, M.fromList $ fmap (\(c,t)-> (c,t)) pks)


schemaAttributes :: Connection -> Text -> InformationSchema -> IO [Path Key Table]
schemaAttributes conn schema (keyTable,map) = do
       res <- fmap (fmap (\(t,c,ckn)-> (t,ckn,fromJust $ M.lookup c keyTable))) $  query conn "SELECT table_name,column_name,constraint_name FROM information_schema.tables natural join information_schema.columns natural join information_schema.key_column_usage natural join information_schema.table_constraints WHERE table_schema = ? AND table_type='BASE TABLE' AND constraint_type='PRIMARY KEY'" (Only schema) :: IO [(Text,Text,Key)]
       let pks =  fmap (\(c,l)-> (c,S.fromList $ fmap (\(_,_,j)-> j ) l )) $ groupSplit (\(t,ck,_)-> (t,ck))  res :: [((Text,Text),Set Key)]
       res2 <- fmap (fmap (\(t,c)-> (t,fromJust $ M.lookup c keyTable))) $  query conn "SELECT table_name,column_name FROM information_schema.tables natural join information_schema.columns WHERE table_schema = ? AND table_type='BASE TABLE'" (Only schema):: IO [(Text,Key)]
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
schemaKeys conn schema (keyTable,map) = do
       res <- fmap (fmap (\(t,c,ckn)-> (t,ckn,fromJust $ M.lookup c keyTable ))) $  query conn "SELECT table_name,column_name,constraint_name FROM information_schema.tables natural join information_schema.columns natural join information_schema.key_column_usage natural join information_schema.table_constraints WHERE table_schema = ? AND table_type='BASE TABLE' AND constraint_type='PRIMARY KEY'" (Only schema) :: IO [(Text,Text,Key)]
       let pks =  fmap (\(c,l)-> (c,S.fromList $ fmap (\(_,_,j)-> j ) l )) $ groupSplit (\(t,ck,_)-> (t,ck))  res :: [((Text,Text),Set Key)]
       res2 <- fmap (fmap (\(t,c,ckn)-> (t,ckn,fromJust $ M.lookup c keyTable ))) $  query conn "SELECT kc.table_name,kc.column_name,constraint_name FROM information_schema.tables natural join information_schema.key_column_usage kc natural join information_schema.table_constraints inner join information_schema.columns cl on cl.table_name = kc.table_name and cl.column_name = kc.column_name  WHERE kc.table_schema = ? AND table_type='BASE TABLE' AND constraint_type='FOREIGN KEY'" (Only schema):: IO [(Text,Text,Key)]
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

