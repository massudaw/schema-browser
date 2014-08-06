{-# LANGUAGE OverloadedStrings #-}

module Schema where

import Query
import Warshal
import qualified Data.Foldable as F
import Data.Foldable (Foldable)
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



createType :: (Text,Text,Text,Text) -> (Text,Key)
createType (t,c,ty,"YES" ) = (t,Key c (KOptional $ Primitive ty))
createType (t,c,ty,"NO") = (t,Key c (Primitive ty))
createType v = error $ show v

type InformationSchema = (Map (Text,Text) Key,Map (Set Key) Table)

keyTables :: Connection -> Text -> IO InformationSchema
keyTables conn schema = do
       res2 <- fmap (fmap createType) $  query conn "SELECT table_name,column_name,data_type,is_nullable FROM information_schema.tables natural join information_schema.columns  WHERE table_schema = ? AND table_type='BASE TABLE'" (Only schema) :: IO [(Text,Key)]
       let keyMap = M.fromList $ fmap (\(t,k@(Key c _))-> ((t,c),k)) res2
       res <- fmap (fmap (\(t,c)-> (t,fromJust $ M.lookup (t,c) keyMap))) $  query conn "SELECT table_name,column_name FROM information_schema.tables natural join information_schema.columns natural join information_schema.key_column_usage natural join information_schema.table_constraints WHERE table_schema = ? AND table_type='BASE TABLE' AND constraint_type='PRIMARY KEY'" (Only schema) :: IO [(Text,Key)]
       let all =  M.fromList $ fmap (\(c,l)-> (c,S.fromList $ fmap (\(_,j)-> j ) l )) $ groupSplit (\(t,_)-> t)  res2 :: Map Text (Set Key)
           pks =  fmap (\(c,l)-> (S.fromList $ fmap (\(_,j)-> j ) l ,Raw schema c (fromJust $ M.lookup c all) )) $ groupSplit (\(t,_)-> t)  res :: [(Set Key,Table)]
       return (keyMap, M.fromList $ fmap (\(c,t)-> (c,t)) pks)


schemaAttributes :: Connection -> Text -> InformationSchema -> IO [Path Key Table]
schemaAttributes conn schema (keyTable,map) = do
       res <- fmap (fmap (\(t,c,ckn)-> (t,ckn,fromJust $ M.lookup (t,c) keyTable))) $  query conn "SELECT table_name,column_name,constraint_name FROM information_schema.tables natural join information_schema.columns natural join information_schema.key_column_usage natural join information_schema.table_constraints WHERE table_schema = ? AND table_type='BASE TABLE' AND constraint_type='PRIMARY KEY'" (Only schema) :: IO [(Text,Text,Key)]
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
schemaKeys conn schema (keyTable,map) = do
       res <- fmap (fmap (\(t,c,ckn)-> (t,ckn,fromJust $ M.lookup (t,c) keyTable ))) $  query conn "SELECT table_name,column_name,constraint_name FROM information_schema.tables natural join information_schema.columns natural join information_schema.key_column_usage natural join information_schema.table_constraints WHERE table_schema = ? AND table_type='BASE TABLE' AND constraint_type='PRIMARY KEY'" (Only schema) :: IO [(Text,Text,Key)]
       let pks =  fmap (\(c,l)-> (c,S.fromList $ fmap (\(_,_,j)-> j ) l )) $ groupSplit (\(t,ck,_)-> (t,ck))  res :: [((Text,Text),Set Key)]
       res2 <- fmap (fmap (\(t,c,ckn)-> (t,ckn,fromJust $ M.lookup (t,c) keyTable ))) $  query conn "SELECT kc.table_name,kc.column_name,constraint_name FROM information_schema.tables natural join information_schema.key_column_usage kc natural join information_schema.table_constraints inner join information_schema.columns cl on cl.table_name = kc.table_name and cl.column_name = kc.column_name  WHERE kc.table_schema = ? AND table_type='BASE TABLE' AND constraint_type='FOREIGN KEY'" (Only schema):: IO [(Text,Text,Key)]
       let fks =  fmap (\(c,l)-> (c,S.fromList $ fmap (\(_,_,j)-> j) l )) $ groupSplit (\(t,ck,_)-> (t,ck))  res2 :: [((Text,Text),Set Key)]
           rels = [ Path pkl (fromJust $ M.lookup pkl map) fkl |
                    ((tfk,fk),fkl)<- fks,
                    ((tpk,pk),pkl)<- pks,
                    tfk == tpk]
       return rels

projectAllKeys baseTables hashGraph m bkey
  = case M.lookup bkey baseTables  of
      Just t ->   runQuery  m (hashGraph,Base bkey $ From t bkey)
      Nothing -> error $  "No baseTable for key " <> showVertex bkey

buildQuery q =  "SELECT * FROM " <> fromString (T.unpack $ showTable q)

