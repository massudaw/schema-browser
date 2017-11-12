{-# LANGUAGE Arrows,FlexibleContexts,TypeFamilies ,NoMonomorphismRestriction,OverloadedStrings ,TupleSections #-}
module Postgresql.Backend (connRoot,postgresOps) where

import Types
import Step.Client
import Data.Time
import qualified Types.Index as G
import Control.Arrow
import SchemaQuery
import Environment
import Postgresql.Types
import Default
import Step.Common
import qualified Data.Poset as P
import Control.Exception (uninterruptibleMask,mask_,throw,catch,throw,SomeException)
import Step.Host
import Data.Interval (Extended(..),upperBound)
import Data.Either
import Data.Functor.Apply
import System.Environment
import Control.Concurrent.STM
import Safe
import Control.Monad
import Postgresql.Printer
import Postgresql.Parser
import Utils
import Text
import Control.Monad.Reader
import Control.Lens as Le
import GHC.Stack
import Schema
import RuntimeTypes
import Data.Bifunctor
import Query
import Control.Monad.Writer hiding (pass)
import System.Time.Extra
import Types.Patch
import Debug.Trace
import Data.Ord
import Data.Functor.Identity
import qualified  Data.Map as M
import qualified  Data.HashMap.Strict as HM

import Data.Tuple
import Data.String

import Control.Applicative
import Data.Maybe
import qualified Data.List as L

import Prelude hiding (takeWhile,head)

import qualified Data.Foldable as F
import qualified Data.Text as T
import Data.Text (Text)
import qualified Data.Set as S
import qualified Database.PostgreSQL.Simple.FromRow as FR
import Database.PostgreSQL.Simple

filterFun  = filter (\k -> not $ isFun k )
  where isFun (PFun _ _ _ ) = True
        isFun i = False

overloadedRules = overloaedSchema <> overloaedTables <> overloaedColumns
overloaedSchema = M.intersectionWith mappend (M.fromList [(("metadata","catalog_schema"),[UpdateRule alterSchema ])]) (M.fromList (translate <$> [dropSchema,createSchema]))
overloaedTables =  M.fromListWith (++) $ translate <$> [createTableCatalog, dropTableCatalog]
overloaedColumns = M.fromListWith (++)  ( translate <$> [createColumnCatalog,dropColumnCatalog])

schema_name  s
  = iforeign [(Rel s Equals "name")] (ivalue $ ifield "name" (ivalue (readV ())))

column_type
  = isum [iinline "primitive" . iopt . ivalue $
             iforeign [(Rel "schema_name" Equals "nspname"),(Rel "data_name" Equals "typname")]
               (ivalue ((,) <$> ifield "nspname" (ivalue (readV ())) <*> ifield "typname" (ivalue (readV ()))))
         ,iinline "composite" . iopt . ivalue $
             iforeign [(Rel "schema_name" Equals "schema_name"),(Rel "data_name" Equals "table_name")]
               (ivalue ((,) <$> ifield "schema_name" (ivalue (readV ())) <*> ifield "table_name" (ivalue (readV ()))))]

createColumnCatalog  =
  aschema "metadata" $
    atable "catalog_columns" $
      arow RowCreate $
        proc _ -> do
          c <- ifield "column_name" (ivalue (readV ())) -< ()
          (s,t) <- iforeign [(Rel "table_name" Equals "table_name"),(Rel "table_schema" Equals "schema_name")]
                      (ivalue ((,) <$> schema_name "schema_name"  <*>  ifield "table_name" (ivalue (readV ())))) -< ()
          (sty,ty) <-  iinline "col_type"  . iftb PIdOpt .ivalue $ column_type -< ()
          act (\(s,t,c,sty,ty) -> do
            inf <- lift ask
            liftIO  (execute (rootconn inf) "ALTER TABLE ?.? ADD COLUMN ? ?.? "(DoubleQuoted s ,DoubleQuoted t,DoubleQuoted c ,DoubleQuoted  sty ,DoubleQuoted ty ))
            return ()) -< (s,t,c,sty,ty)

dropColumnCatalog  = do
  aschema "metadata" $
    atable "catalog_columns" $
      arow RowDrop $
        proc _ -> do
          c <- ifield "column_name"
              (ivalue (readV ())) -< ()
          s <- iforeign [(Rel "table_schema" Equals "name")]
              (ivalue (ifield "name" (ivalue (readV ()) ))) -< ()
          t <- iforeign [(Rel "table_name" Equals "table_name"),(Rel "table_schema" Equals "schema_name")]
              (ivalue (ifield "table_name" (ivalue (readV ())))) -< ()
          act (\(t,s,c) -> do
            inf <- lift ask
            liftIO$ execute (rootconn inf) "ALTER TABLE ?.? DROP COLUMN ? "(DoubleQuoted  s ,DoubleQuoted  t, DoubleQuoted c)) -< (t,s,c)
          returnA -< ()


createTableCatalog :: PluginM (Namespace Text Text RowModifier Text)  (Atom (TBData  Text Showable)) TransactionM  i ()
createTableCatalog = do
  aschema "metadata" $
    atable "catalog_tables" $
      arow RowCreate $
        proc _ -> do
          t <- ifield "table_name"
             (ivalue (readV ())) -< ()
          s <- ifield "schema_name"
             (ivalue (readV  ()))-< ()
          oid <- act (\(sc ,n) ->  do
              inf <- lift ask
              liftIO$ execute (rootconn inf) "CREATE TABLE ?.? ()"(DoubleQuoted sc ,DoubleQuoted  n)
              [Only i] <- liftIO$ query (rootconn inf) "select oid from metadata.catalog_tables where table_name =? and schema_name = ? " ((renderShowable n),(renderShowable sc))
              return i) -< (TB1 s,TB1 t)
          ifield "oid" (iftb PIdOpt (ivalue (writeV ()))) -< SNumeric oid
          returnA -< ()

dropTableCatalog :: PluginM (Namespace Text Text RowModifier Text)  (Atom (TBData  Text Showable)) TransactionM  i ()
dropTableCatalog = do
  aschema "metadata" $
    atable "catalog_tables" $
      arow RowDrop $
        proc _ -> do
          t <- ifield "table_name"
              (ivalue (readV ())) -< ()
          s <- ifield "schema_name"
              (ivalue (readV  ()))-< ()
          act (\(sc ,n) ->  do
              inf <- lift ask
              liftIO$ execute (rootconn inf) "DROP TABLE ?.?" (DoubleQuoted sc ,DoubleQuoted n)
              ) -< (TB1 s,TB1 t)
          returnA -< ()


createSchema  = do
  aschema "metadata" $
    atable "catalog_schema" $
      arow RowCreate $
        proc _ -> do
          s <- ifield "name"
              (ivalue (readV  ()))-< ()
          o <- iforeign [(Rel "owner" Equals "oid")]
              (iopt $ ivalue (ifield "usename" ((ivalue (readV ()))) )) -< ()
          oid <- act (\(n,onewm) ->  do
            inf <- lift ask
            maybe
              (liftIO$ execute (rootconn inf) "CREATE SCHEMA ? "(Only $ DoubleQuoted n))
              (\o -> liftIO$ execute (rootconn inf) "CREATE SCHEMA ? AUTHORIZATION ? "(DoubleQuoted n, DoubleQuoted o)) onewm
            [Only i] <- liftIO$ query (rootconn inf) "select oid from metadata.catalog_schema where name =? " (Only $ (renderShowable n))
            return i) -< (TB1 s,fmap TB1 o)
          ifield "oid" (iftb PIdOpt (ivalue (writeV ()))) -< SNumeric oid
          returnA -< ()

alterSchema v p= do
      inf <- ask
      let new = apply  v p
          n = fromJust $ indexFieldRec (keyRef name) v
          nnewm = indexFieldRec (keyRef name) new
          o = fromJust $ indexFieldRec (Nested [keyRef owner] (pure $ keyRef user_name)) v
          onewm = indexFieldRec (Nested [keyRef owner] (pure $ keyRef user_name)) new
          name = lookKey inf "catalog_schema" "name"
          owner= lookKey inf "catalog_schema" "owner"
          user_name = lookKey inf "user" "usename"

      traverse (\new -> when (new /= o )$ void $ liftIO$ execute (rootconn inf) "ALTER SCHEMA ? OWNER TO ?  "(DoubleQuoted o, DoubleQuoted new)) onewm
      traverse (\new -> when (new /= n )$ void $ liftIO$ execute (rootconn inf) "ALTER SCHEMA ? RENAME TO ?  "(DoubleQuoted n, DoubleQuoted new)) nnewm
      l <- liftIO getCurrentTime
      return $ TableModification Nothing (utcToLocalTime utc l) (snd $ username inf) (lookTable inf "catalog_schema") . PatchRow  . traceShowId <$> (diff v new)

dropSchema = do
  aschema "metadata" $
    atable "catalog_schema" $
      arow RowDrop $
        proc _ -> do
          s <- ifield "name" (ivalue (readV  ()))-< ()
          act (\n->  do
            inf <- lift ask
            liftIO$ execute (rootconn inf) "DROP SCHEMA ?"(Only $ DoubleQuoted n)
            return ()) -< TB1 s
          returnA -< ()




insertPatch
  :: (MonadIO m ,Functor m )
     => (TBData Key () -> FR.RowParser (TBData Key Showable ))
     -> Connection
     -> TBIdx Key Showable
     -> TableK Key
     -> m (TBIdx Key Showable )
insertPatch f conn path@(m ,s,i )  t = either errorWithStackTrace (\(m,s,i) -> liftIO$ if not $ L.null serialAttr
      then do
        let
          iquery :: String
          iquery = T.unpack $ prequery <> " RETURNING ROW(" <>  T.intercalate "," (projKey serialAttr) <> ")"
        print iquery
        [out] <- liftIO $ queryWith (f serialTB ) conn (fromString  iquery) directAttr
        let (_,_ ,gen) =  patch out
        return (m, G.getIndex out  , i <> gen)
      else do
        let
          iquery = T.unpack prequery
        print iquery
        execute  conn (fromString  iquery ) directAttr
        return path) checkAllFilled
    where
      checkAllFilled = patchCheck path
      prequery =  "INSERT INTO " <> rawFullName t <>" ( " <> T.intercalate "," (escapeReserved <$> projKey directAttr ) <> ") VALUES (" <> T.intercalate "," (fmap (const "?") $ projKey directAttr)  <> ")"
      attrs =  concat $L.nub $ nonRefTB .  create . traceShowId <$> filterFun i
      testSerial (k,v ) = (isSerial .keyType $ k) && (isNothing. unSSerial $ v)
      direct f = filter (not.all1 testSerial .f)
      serialAttr = flip Attr (LeftTB1 Nothing)<$> filter (isSerial .keyType) ( rawPK t <> F.toList (rawAttrs t))
      directAttr :: [TB Identity Key Showable]
      directAttr = direct aattri attrs
      projKey :: [TB Identity Key a ] -> [Text]
      projKey = fmap (keyValue ._relOrigin) . concat . fmap keyattri
      serialTB = tblist' t (fmap _tb  serialAttr)
      all1 f [] = False
      all1 f i = all f i



deletePatch
  ::
     Connection ->  TBIdx PGKey Showable -> Table -> IO (TBIdx PGKey Showable)
deletePatch conn patch@(m ,G.Idex kold ,_) t = do
    print del
    execute conn (fromString $ T.unpack del) koldPk
    return patch
  where
    equality k = escapeReserved (attrValueName k) <> "="  <> "?"
    koldPk = uncurry Attr <$> zip (_kvpk m) (F.toList kold)
    pred   =" WHERE " <> T.intercalate " AND " (fmap  equality koldPk)
    del = "DELETE FROM " <> rawFullName t <>   pred

applyPatch
  ::
     Connection -> TBIdx PGKey Showable -> IO (TBIdx PGKey Showable)
applyPatch conn patch@(m,G.Idex kold,skv)  = do
    print up
    execute conn (fromString $ T.unpack up)  (fmap attrPatchValue skv <> koldPk ) >> return patch
  where
    equality k = k <> "="  <> "?"
    koldPk = uncurry Attr <$> zip (_kvpk m) (F.toList kold)
    attrPatchName (PAttr k p ) = escapeReserved (keyValue k) <> "=" <> nestP(keyValue k) p
      where nestP k (PInter True (b,j)) = "lowerI(" <> k <> "," <> "?" <>" ," <> (T.pack $show j)<> ")"
            nestP k (PInter False (b,j)) = "upperI(" <> k <> "," <> "?" <> "," <> (T.pack (show j )) <> ")"
            nestP k (PatchSet l) = F.foldl' nestP k  l
            nestP k i = "?"
    attrPatchValue (PAttr  k v) = Attr k (create v) :: TB Identity PGKey Showable
    pred   =" WHERE " <> T.intercalate " AND " (equality . escapeReserved . keyValue . fst <$> zip (_kvpk m) (F.toList kold))
    setter = " SET " <> T.intercalate "," (   attrPatchName <$> skv   )
    up = "UPDATE " <> kvMetaFullName m <> setter <>  pred


updatePatch
  ::
     Connection -> TBData PGKey Showable -> TBData PGKey Showable -> Table -> IO (TBIdx PGKey Showable)
updatePatch conn kv old  t = do
    print up
    execute conn (fromString $ T.unpack up)  (skv <> koldPk ) >> return patch
  where
    patch  = justError ("cant diff states" <> (concat $ zipWith differ (show kv) (show old))) $ diff old kv
    kold = M.toList $ getPKM old
    equality k = k <> "="  <> "?"
    koldPk = uncurry Attr <$> kold
    pred   =" WHERE " <> T.intercalate " AND " (equality . escapeReserved . keyValue . fst <$> kold)
    setter = " SET " <> T.intercalate "," (equality .   escapeReserved . attrValueName <$> skv   )
    up = "UPDATE " <> rawFullName t <> setter <>  pred
    skv = unTB <$> F.toList  (_kvvalues $ unTB tbskv)
    tbskv = snd isM
    isM :: TBData PGKey  Showable
    isM =  justError ("cant diff befor update" <> show (kv,old)) $ diffUpdateAttr kv old

diffUpdateAttr :: (Ord k , Ord a) => TBData k a -> TBData k a -> Maybe (TBData k a )
diffUpdateAttr  kv kold@(t,_ )  =  fmap ((t,) . _tb . KV ) .  allMaybesMap  $ liftF2 (\i j -> if i == j then Nothing else Just i) (unKV . snd . tableNonRef'  $ kv ) (unKV . snd . tableNonRef' $ kold )

differ = (\i j  -> if i == j then [i]  else "(" <> [i] <> "|" <> [j] <> ")" )

paginate inf t order off size koldpre wherepred = do
    let (que,attr) = selectQuery t koldpre order wherepred
    i <- lookupEnv "POSTGRESQL_DECODER"
    let
      jsonDecode =  do
        let quec = fromString $ T.unpack $ "SELECT row_to_json(q),count(*) over () FROM (" <> que <> ") as q " <> offsetQ <> limitQ
        uncurry (queryWith (withCount (fromRecordJSON t) ) (conn inf ) ) (quec, maybe [] (fmap (either(Left .firstTB (recoverFields inf)) Right)) attr)
      textDecode = do
        let quec = fromString $ T.unpack $ "SELECT *,count(*) over () FROM (" <> que <> ") as q " <> offsetQ <> limitQ
        uncurry (queryWith (withCount (fromRecord (unTlabel' t)) ) (conn inf ) ) (quec, maybe [] (fmap (either (Left .firstTB (recoverFields inf)) Right ) ) attr)

    v <- case i of
           Just "JSON" ->  jsonDecode
           Just "TEXT" ->    textDecode
           Nothing -> jsonDecode
    let estimateSize = maybe 0 (\c-> c - off ) $ safeHead ( fmap snd v :: [Int])
    print estimateSize
    return (estimateSize, fmap fst v)
  where

        offsetQ = " OFFSET " <> T.pack (show off)
        limitQ = " LIMIT " <> T.pack (show size)



-- High level db operations


insertMod :: TBData Key Showable -> TransactionM (Maybe (TableModification (RowPatch Key Showable)))
insertMod j  = do
  inf <- ask
  let overloaded  = M.lookup (_kvschema (fst j) ,_kvname (fst j)) overloadedRules
      isCreate (CreateRule _ ) = True
      isCreate _ = False
  case L.find isCreate  =<< overloaded of
    Just (CreateRule l) -> l j
    Nothing ->liftIO $ do
      let
        table = lookTable inf (_kvname (fst  j))
      (t,pk,attrs) <- insertPatch (fromRecord  ) (conn  inf) (patch j) ( table)
      l <- liftIO getCurrentTime
      return $ TableModification Nothing (utcToLocalTime utc l) (snd $ username inf)table . CreateRow <$> either (const Nothing ) Just (typecheck (typeCheckTable (_rawSchemaL table, _rawNameL table)) (create  (t,pk,compact $ deftable inf table <> attrs )))


deleteMod :: TBData Key Showable -> TransactionM (Maybe (TableModification (RowPatch Key Showable)))
deleteMod p@(m,_) = do
  inf <- ask
  let overloaded  = M.lookup (_kvschema m,_kvname m) overloadedRules
      isRule (DropRule _ ) = True
      isRule _ = False
  log <- case L.find isRule =<< overloaded of
    Just (DropRule i) ->  i p
    Nothing ->  liftIO $  do
      let table = lookTable inf (_kvname m)
      deletePatch (conn inf)  (firstPatch (recoverFields inf) (patch p)) table
      l <- liftIO getCurrentTime
      return $ Just $ (TableModification Nothing (utcToLocalTime utc l) (snd $ username inf)table  $ DropRow p)
  return $ log

updateMod :: TBData Key Showable -> TBIdx Key Showable -> TransactionM (Maybe (TableModification (RowPatch Key Showable)))
updateMod old p = do
  inf <- ask
  let
      kv = apply  old p
      overloaded  = M.lookup (_kvschema (fst old) ,_kvname (fst old)) overloadedRules
      isCreate (UpdateRule _ ) = True
      isCreate _ = False
  case L.find isCreate  =<< overloaded of
    Just (UpdateRule i) ->  i old p
    Nothing -> liftIO$ do
      let table = lookTable inf (_kvname (fst  old ))
      patch <- updatePatch (conn  inf) (mapKey' (recoverFields inf) kv )(mapKey' (recoverFields inf) old ) table
      l <- liftIO getCurrentTime
      let mod =  TableModification Nothing (utcToLocalTime utc l) (snd $ username inf) table ( PatchRow $ firstPatch (typeTrans inf) patch)
      return $ Just mod

patchMod :: TBIdx Key Showable -> TransactionM (Maybe (TableModification (RowPatch Key Showable)))
patchMod patch@(m,_,_) = do
  inf <- ask
  liftIO $ do
    let table = lookTable inf (_kvname m )
    patch <- applyPatch (conn  inf) (firstPatch (recoverFields inf ) patch )
    l <- liftIO getCurrentTime
    let mod =  TableModification Nothing (utcToLocalTime utc l) (snd $ username inf) table (PatchRow $ firstPatch (typeTrans inf) patch)
    return (Just mod)



selectAll
  ::
     TBF (Labeled Text) Key ()
     -> Int
     -> Maybe PageToken
     -> Int
     -> [(Key, Order)]
     -> WherePredicate
     -> TransactionM  (Int,
           [(KVMetadata Key,
             Compose
               Identity (KV (Compose Identity (TB Identity))) Key Showable)])
selectAll m offset i  j k st = do
      inf <- ask
      let
          unref (TableRef i) = Just $  upperBound <$>  i
          unref (HeadToken ) = Nothing
      v <- liftIO$ paginate inf m k offset j ( join $ fmap unref i) st
      return v


connRoot dname = (fromString $ "host=" <> host dname <> " port=" <> port dname  <> " user=" <> user dname <> " dbname=" <> dbn  dname <> " password=" <> pass dname   )


tSize = 400

postgresOps = SchemaEditor updateMod patchMod insertMod deleteMod (\ j off p g s o-> (\(l,i) -> (i,(TableRef <$> G.getBounds i) ,l)) <$> selectAll  j (fromMaybe 0 off) p (fromMaybe tSize g) s o )  (\table j -> do
    inf <- ask
    liftIO . loadDelayed inf (tableView (tableMap inf) table ) $ j ) mapKeyType undefined undefined (\ a -> liftIO . logTableModification a) tSize (\inf -> withTransaction (conn inf))  overloadedRules Nothing
