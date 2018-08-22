{-# LANGUAGE Arrows,TypeFamilies ,NoMonomorphismRestriction,OverloadedStrings ,TupleSections #-}
module Postgresql.Extensions (overloadedRules) where

import Control.Applicative
import Control.Arrow
import Control.Monad.RWS hiding (pass)
import qualified Data.Map as M
import Data.Maybe
import Data.Text (Text)
import Database.PostgreSQL.Simple
import Environment
import Postgresql.Parser
import Prelude hiding (head, takeWhile)
import RuntimeTypes
import Step.Client
import Text
import Types
import qualified Types.Index as G
import Types.Patch

overloadedRules :: M.Map
                        (Text, Text) [(TBData Text Showable -> Bool, OverloadedRule)]
overloadedRules = M.fromListWith (++) (translate <$> postgresqlRules)

postgresqlRules :: [PluginM  (Namespace Text Text RowModifier Text) (Atom (TBData Text Showable)) TransactionM i ()]
postgresqlRules  = [dropSchema,createSchema,alterSchema,createTableCatalog, dropTableCatalog,createColumnCatalog,dropColumnCatalog]

schema_name
  :: Monad m => Text -> PluginM (G.AttributePath Text  MutationTy) (Atom (TBData Text Showable))   m i (Showable)
schema_name  s
  = iforeign [(Rel (Inline s) Equals "name")] (ivalue . irecord $ ifield "name" (ivalue (readV PText)))

column_type
  :: (Monad m ) =>
    PluginM (G.PathIndex PathTID (Union (G.AttributePath Text  MutationTy))) (Atom (FTB (TBData Text Showable)))   m i (Showable,Showable)
column_type
  = ivalue $ isum [iinline "primitive" . iopt . ivalue . irecord $
             iforeign [(Rel "schema_name" Equals "nspname"),(Rel "data_name" Equals "typname")]
               (ivalue $ irecord ((,) <$> ifield "nspname" (ivalue (readV PText)) <*> ifield "typname" (ivalue (readV PText))))
         ,iinline "composite" . iopt . ivalue . irecord $
             iforeign [(Rel "schema_name" Equals "schema_name"),(Rel "data_name" Equals "table_name")]
               (ivalue $ irecord ((,) <$> ifield "schema_name" (ivalue (readV PText)) <*> ifield "table_name" (ivalue (readV PText))))]

createColumnCatalog
  :: PluginM  (Namespace Text Text RowModifier Text) (Atom (TBData Text Showable)) TransactionM i ()
createColumnCatalog  =
  aschema "metadata" $
    atable "catalog_columns" $
      arow RowCreate  $
        proc _ -> do
          c <- ifield "column_name" (ivalue (readV PText)) -< ()
          (s,t) <- iforeign [(Rel "table_name" Equals "table_name"),(Rel "table_schema" Equals "schema_name")]
                      (ivalue $ irecord ((,) <$> schema_name "schema_name"  <*>  ifield "table_name" (ivalue (readV PText)))) -< ()
          (sty,ty) <-  iinline "col_type"  . iftb PIdOpt $ column_type -< ()
          act (\(s,t,c,sty,ty) -> do
            inf <- lift askInf
            let sqr = "ALTER TABLE ?.? ADD COLUMN ? ?.? "
                args = (DoubleQuoted s ,DoubleQuoted t,DoubleQuoted c ,DoubleQuoted  sty ,DoubleQuoted ty )
            executeLogged (rootconn inf)  sqr args
            return ()) -< (s,t,c,sty,ty)

dropColumnCatalog
  :: PluginM  (Namespace Text Text RowModifier Text) (Atom (TBData Text Showable)) TransactionM i ()
dropColumnCatalog  = do
  aschema "metadata" $
    atable "catalog_columns" $
      arow RowDrop $
        proc _ -> do
          c <- ifield "column_name"
              (ivalue (readV PText)) -< ()
          s <- iforeign [(Rel "table_schema" Equals "name")]
              (ivalue $ irecord (ifield "name" (ivalue (readV PText) ))) -< ()
          t <- iforeign [(Rel "table_name" Equals "table_name"),(Rel "table_schema" Equals "schema_name")]
              (ivalue $ irecord (ifield "table_name" (ivalue (readV PText)))) -< ()
          act (\(t,s,c) -> do
            inf <- lift askInf
            executeLogged (rootconn inf) "ALTER TABLE ?.? DROP COLUMN ? "(DoubleQuoted  s ,DoubleQuoted  t, DoubleQuoted c)) -< (t,s,c)
          returnA -< ()


createTableCatalog :: PluginM (Namespace Text Text RowModifier Text)  (Atom (TBData  Text Showable)) TransactionM  i ()
createTableCatalog = do
  aschema "metadata" $
    atable "catalog_tables" $
      arow RowCreate $
        proc _ -> do
          t <- ifield "table_name"
             (ivalue (readV PText)) -< ()
          s <- schema_name "schema_name"  -< ()
          oid <- act (\(sc ,n) -> do
              inf <- lift askInf
              _ <-  liftIO $ executeLogged (rootconn inf) "CREATE TABLE ?.? ()"(DoubleQuoted sc ,DoubleQuoted  n)
              [Only i] <- liftIO $ query (rootconn inf) "select oid from metadata.catalog_tables where table_name =? and schema_name = ? " ((renderShowable n),(renderShowable sc))
              return i) -< (TB1 s,TB1 t)
          ifield "oid" (iftb PIdOpt (ivalue (writeV (PInt 8)))) -< SNumeric oid
          returnA -< ()

dropTableCatalog :: PluginM (Namespace Text Text RowModifier Text)  (Atom (TBData  Text Showable)) TransactionM  i ()
dropTableCatalog = do
  aschema "metadata" $
    atable "catalog_tables" $
      arow RowDrop $
        proc _ -> do
          t <- ifield "table_name"
              (ivalue (readV PText)) -< ()
          (SText ty) <- ifield "table_type"
              (ivalue (readV  PText))-< ()
          s <- schema_name "schema_name"  -< ()
          act (\(ty,sc ,n) ->  do
              inf <- lift askInf
              let tys = case ty of
                  -- TODO: Design enumerations
                    "BASE TABLE" -> "TABLE"
                    "VIEW" -> "VIEW"
                    _ -> error "invalid pattern"
              liftIO$ executeLogged (rootconn inf) ("DROP " <> tys <> " ?.?") (DoubleQuoted sc ,DoubleQuoted n)
              ) -< (ty,TB1 s,TB1 t)
          returnA -< ()


createSchema
  :: PluginM  (Namespace Text Text RowModifier Text) (Atom (TBData Text Showable)) TransactionM i ()
createSchema  = do
  aschema "metadata" $
    atable "catalog_schema" $
      arow RowCreate $
        proc _ -> do
          s <- ifield "name"
              (ivalue (readV  PText))-< ()
          o <- fmap join $ iforeign [(Rel "owner" Equals "oid")]
              (iopt $ ivalue $ irecord (ifield "usename" (iopt $ ivalue (readV PText)) )) -< ()
          oid <- act (\(n,onewm) ->  do
            inf <- lift askInf
            _ <- maybe
              (executeLogged (rootconn inf) "CREATE SCHEMA ? "(Only $ DoubleQuoted n))
              (\o -> executeLogged (rootconn inf) "CREATE SCHEMA ? AUTHORIZATION ? "(DoubleQuoted n, DoubleQuoted o)) onewm
            liftIO $ print =<< formatQuery  (rootconn inf) "select oid from metadata.catalog_schema where name =? " (Only $ (renderShowable n))
            [Only i] <- liftIO$ query (rootconn inf) "select oid from metadata.catalog_schema where name =? " (Only $ (renderShowable n))
            return i) -< (TB1 s,fmap TB1 o)
          ifield "oid" (ivalue (writeV (PInt 8))) -< SNumeric oid
          returnA -< ()

alterSchema
  :: PluginM  (Namespace Text Text RowModifier Text) (Atom (TBData Text Showable)) TransactionM i ()
alterSchema = do
  aschema "metadata" $
    atable "catalog_schema" $
      arow RowUpdate $
        proc _ -> do
          (n,nnewm) <- ifield "name"
              (ivalue (changeV PText)) -< ()
          Just (o,onewm) <- fmap join $ iforeign [(Rel "owner" Equals "oid")]
              (iopt $ ivalue $ irecord (ifield "usename" (iopt (ivalue (changeV PText))) )) -< ()
          act (\(n,o,onewm,nnewm) -> do
            inf <- lift askInf
            when (onewm /= o) . void $
              executeLogged (rootconn inf) "ALTER SCHEMA ? OWNER TO ?" (DoubleQuoted n, DoubleQuoted onewm)
            when (nnewm /= n) . void $
              executeLogged (rootconn inf) "ALTER SCHEMA ? RENAME TO ?" (DoubleQuoted n, DoubleQuoted nnewm) ) -< (n,o,onewm,nnewm)
          returnA -< ()

dropSchema
  :: PluginM  (Namespace Text Text RowModifier Text) (Atom (TBData Text Showable)) TransactionM i ()
dropSchema = do
  aschema "metadata" $
    atable "catalog_schema" $
      arow RowDrop $
        proc _ -> do
          s <- ifield "name" (ivalue (readV  PText))-< ()
          act (\n->  do
            inf <- lift askInf
            _ <- liftIO$ executeLogged (rootconn inf) "DROP SCHEMA ?"(Only $ DoubleQuoted n)
            return ()) -< TB1 s
          returnA -< ()

