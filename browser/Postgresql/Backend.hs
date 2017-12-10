{-# LANGUAGE Arrows,FlexibleContexts,TypeFamilies ,NoMonomorphismRestriction,OverloadedStrings ,TupleSections #-}
module Postgresql.Backend (connRoot,postgresOps) where

import Types
import Step.Client
import Data.Time
import qualified Types.Index as G
import Control.Arrow
import SchemaQuery
import Control.Monad.RWS hiding(pass)
import Environment
import Postgresql.Types
import Default
import Step.Common
import qualified Data.Poset as P
import Control.Exception (uninterruptibleMask,mask_,throw,catch,throw,SomeException)
import Postgresql.Printer
import Step.Host
import Postgresql.Codegen
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

filterFun  = M.filter (\ v-> not $ isFun v )
  where isFun (Fun _ _ _ ) = True
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
          tb = lookTable inf "catalog_schema"

      traverse (\new -> when (new /= o )$ void $ liftIO$ execute (rootconn inf) "ALTER SCHEMA ? OWNER TO ?  "(DoubleQuoted o, DoubleQuoted new)) onewm
      traverse (\new -> when (new /= n )$ void $ liftIO$ execute (rootconn inf) "ALTER SCHEMA ? RENAME TO ?  "(DoubleQuoted n, DoubleQuoted new)) nnewm
      l <- liftIO getCurrentTime
      return $ TableModification Nothing l (snd $ username inf)  tb . PatchRow   . (G.getIndex (tableMeta tb) new,) <$> diff v new

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
     => InformationSchema
     -> Connection
     -> TBData Key Showable
     -> TableK Key
     -> m (TBData Key Showable)
insertPatch  inf conn i  t = either errorWithStackTrace (\i ->  liftIO $ if not $ L.null serialAttr
      then do
        let
          iquery :: String
          (iquery ,namemap)= codegen $ do
            j <- explodeRecord inf (tableMeta t) (tblist serialAttr)
            return $ T.unpack $ prequery <> " RETURNING (SELECT row_to_json(q) FROM (" <> selectRow "p0" j <> ") as q)"
        print iquery
        [out] <- queryWith (fromRecordJSON inf (tableMeta t) serialTB namemap ) conn (fromString  iquery) directAttr
        let gen =  patch out
        return $apply i gen
      else do
        let
          iquery = T.unpack prequery
        print iquery
        execute  conn (fromString  iquery ) directAttr
        return i) checkAllFilled
    where
      checkAllFilled = tableCheck  (tableMeta t) i
      prequery =  "INSERT INTO " <> rawFullName t <>" ( " <> T.intercalate "," (escapeReserved .keyValue<$> projKey directAttr ) <> ") VALUES (" <> T.intercalate "," (value <$> projKey directAttr)  <> ")"
      attrs =  concat $L.nub $ nonRefTB  <$> F.toList (filterFun $ unKV i)
      testSerial (k,v ) = (isSerial .keyType $ k) && (isNothing. unSSerial $ v)
      direct f = filter (not.all1 testSerial .f)
      serialAttr = flip Attr (LeftTB1 Nothing)<$> filter (isSerial .keyType) ( rawPK t <> F.toList (rawAttrs t))
      directAttr :: [TB Key Showable]
      directAttr = direct aattri attrs
      projKey :: [TB Key a ] -> [Key]
      projKey = fmap _relOrigin . concat . fmap keyattri
      value i = "?"  <> fromMaybe ""  (inlineType (keyType i))
        where
          inlineType (Primitive k (RecordPrim (s,t) )) = Just (" :: " <>s <> "." <> t <> foldMap ktype k )
          inlineType _ = Nothing
          ktype KArray  =  "[]"
          ktype KOptional =  ""

      serialTB = tblist'  (serialAttr)
      all1 f [] = False
      all1 f i = all f i



deletePatch
  ::
     Connection ->  KVMetadata PGKey -> TBIndex Showable -> Table -> IO ()
deletePatch conn m ix@(G.Idex kold) t = do
    print del
    execute conn (fromString $ T.unpack del) koldPk
    return ()
  where
    equality k = escapeReserved (attrValueName k) <> "="  <> "?"
    koldPk = uncurry Attr <$> zip (_kvpk m) (F.toList kold)
    pred   =" WHERE " <> T.intercalate " AND " (fmap  equality koldPk)
    del = "DELETE FROM " <> rawFullName t <>   pred

applyPatch
  ::
     Connection -> KVMetadata PGKey ->(TBIndex Showable ,TBIdx PGKey Showable) -> IO (TBIndex Showable ,TBIdx PGKey Showable)
applyPatch conn m patch@(G.Idex kold,skv)  = do
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
    attrPatchValue (PAttr  k v) = Attr k (create v) :: TB PGKey Showable
    pred   =" WHERE " <> T.intercalate " AND " (equality . escapeReserved . keyValue . fst <$> zip (_kvpk m) (F.toList kold))
    setter = " SET " <> T.intercalate "," (   attrPatchName <$> skv   )
    up = "UPDATE " <> kvMetaFullName m <> setter <>  pred


updatePatch
  ::
     Connection -> KVMetadata PGKey -> TBData PGKey Showable -> TBData PGKey Showable -> Table -> IO (TBIdx PGKey Showable)
updatePatch conn m kv old  t = do
    print up
    execute conn (fromString $ T.unpack up)  (skv <> koldPk ) >> return patch
  where
    patch  = justError ("cant diff states" <> (concat $ zipWith differ (show kv) (show old))) $ diff old kv
    kold = M.toList $ getPKM m old
    equality k = k <> "="  <> "?"
    koldPk = uncurry Attr <$> kold
    pred   =" WHERE " <> T.intercalate " AND " (equality . escapeReserved . keyValue . fst <$> kold)
    setter = " SET " <> T.intercalate "," (equality .   escapeReserved . attrValueName <$> skv   )
    up = "UPDATE " <> rawFullName t <> setter <>  pred
    skv = F.toList  (_kvvalues $ tbskv)
    tbskv = isM
    isM :: TBData PGKey  Showable
    isM =  justError ("cant diff befor update" <> show (kv,old)) $ diffUpdateAttr kv old

diffUpdateAttr :: (Ord k , Ord a) => TBData k a -> TBData k a -> Maybe (TBData k a )
diffUpdateAttr  kv kold  =  fmap KV  .  allMaybesMap  $ liftF2 (\i j -> if i == j then Nothing else Just i) (unKV . tableNonRef'  $ kv ) (unKV . tableNonRef' $ kold )

differ = (\i j  -> if i == j then [i]  else "(" <> [i] <> "|" <> [j] <> ")" )

paginate inf meta t order off size koldpre wherepred = do
  let ((que,name),attr) = selectQuery inf meta t koldpre order wherepred
  v <- do
      let quec = fromString $ T.unpack $ "SELECT row_to_json(q),count(*) over () FROM (" <> que <> ") as q " <> offsetQ <> limitQ
      print quec
      uncurry (queryWith (withCount (fromRecordJSON inf meta t name )) (conn inf ) ) (quec, maybe [] (fmap (either(Left .firstTB (recoverFields inf)) Right)) attr)
  let estimateSize = maybe 0 (\c-> c - off ) $ safeHead ( fmap snd v :: [Int])
  print estimateSize
  return (estimateSize, fmap fst v)
  where
        offsetQ = " OFFSET " <> T.pack (show off)
        limitQ = " LIMIT " <> T.pack (show size)



-- High level db operations


insertMod :: KVMetadata Key -> TBData Key Showable -> TransactionM (Maybe (TableModification (RowPatch Key Showable)))
insertMod m j  = do
  inf <- ask
  let overloaded  = M.lookup (_kvschema m ,_kvname m) overloadedRules
      isCreate (CreateRule _ ) = True
      isCreate _ = False
  case L.find isCreate  =<< overloaded of
    Just (CreateRule l) -> l j
    Nothing ->liftIO $ do
      let
        table = lookTable inf (_kvname m)
      d <- insertPatch  inf (conn  inf) j  table
      l <- liftIO getCurrentTime
      return $ TableModification Nothing (l) (snd $ username inf)table . CreateRow <$> either (const Nothing ) Just (typecheck (typeCheckTable (_rawSchemaL table, _rawNameL table)) d)


deleteMod :: KVMetadata Key -> TBData Key Showable -> TransactionM (Maybe (TableModification (RowPatch Key Showable)))
deleteMod m t = do
  inf <- ask
  let overloaded  = M.lookup (_kvschema m,_kvname m) overloadedRules
      isRule (DropRule _ ) = True
      isRule _ = False
  log <- case L.find isRule =<< overloaded of
    Just (DropRule i) ->  i t
    Nothing ->  liftIO $  do
      let table = lookTable inf (_kvname m)
      deletePatch (conn inf) (recoverFields inf <$> m) (G.getIndex m t) table
      l <- liftIO getCurrentTime
      return $ Just $ (TableModification Nothing (l) (snd $ username inf)table  $ DropRow t)
  return $ log

updateMod :: KVMetadata Key -> TBData Key Showable -> TBIndex Showable -> TBIdx Key Showable -> TransactionM (Maybe (TableModification (RowPatch Key Showable)))
updateMod m old pk p = do
  inf <- ask
  let
      kv = apply  old p
      overloaded  = M.lookup (_kvschema m ,_kvname m) overloadedRules
      isCreate (UpdateRule _ ) = True
      isCreate _ = False
  case L.find isCreate  =<< overloaded of
    Just (UpdateRule i) ->  i old p
    Nothing -> liftIO$ do
      let table = lookTable inf (_kvname m)
      patch <- updatePatch (conn  inf) (recoverFields inf <$>  m) (mapKey' (recoverFields inf) kv )(mapKey' (recoverFields inf) old ) table
      l <- liftIO getCurrentTime
      let mod =  TableModification Nothing l (snd $ username inf) table ( PatchRow $ (G.getIndex m kv,) $firstPatch (typeTrans inf) patch)
      return $ Just mod

patchMod :: KVMetadata Key -> TBIndex Showable -> TBIdx Key Showable-> TransactionM (Maybe (TableModification (RowPatch Key Showable)))
patchMod m pk patch = do
  inf <- ask
  liftIO $ do
    let table = lookTable inf (_kvname m)
    patchout <- applyPatch (conn inf) (recoverFields inf <$>m )(pk,firstPatch (recoverFields inf ) patch)
    l <- liftIO getCurrentTime
    let mod =  TableModification Nothing l (snd $ username inf) table (PatchRow  (firstPatch (typeTrans inf) <$>patchout))
    return (Just mod)



loadDelayed :: InformationSchema -> KVMetadata Key -> TBData Key () -> TBData Key Showable -> IO (Maybe (TBIdx Key Showable))
loadDelayed inf m t@(v) values@(vs)
  | L.null $ _kvdelayed m = return Nothing
  | L.null delayedattrs  = return Nothing
  | otherwise = do
       let
           (labelMap,_) = evalRWS (traverse (lkTB) $  _kvvalues $  tableNonRef2 v :: CodegenT Identity (M.Map (S.Set (Rel Key)) Text)) [Root m] namemap
           delayedTB1 :: TBData Key () -> TBData Key ()
           delayedTB1 (KV i ) = KV $ M.filterWithKey  (\i _ -> isJust $ M.lookup i filteredAttrs ) i
           delayed =  mapKey' unKDelayed (mapValue' (const ()) (delayedTB1 t))
           (str,namemap) = codegen $ do
              tq <- expandBaseTable m t
              rq <- explodeRecord inf m delayed
              let whr = T.intercalate " AND " ((\i-> justError ("no key " <> show i <> show labelMap)  (M.lookup (S.singleton $ Inline i) labelMap) <>  " = ?") <$> _kvpk m)
              return $ "select row_to_json(q) FROM (SELECT " <>  selectRow "p0" rq <> " FROM " <> renderRow tq <> " WHERE " <> whr <> ") as q "
           pk = fmap (firstTB (recoverFields inf) . snd) . L.sortBy (comparing (\(i,_) -> L.findIndex (\ix -> (S.singleton . Inline) ix == i ) $ _kvpk m)) . M.toList . _kvvalues $ tbPK m(tableNonRef' values)
       is <- queryWith (fromRecordJSON inf m delayed namemap) (conn inf) (fromString $ T.unpack str) pk
       res <- case is of
            [] -> errorWithStackTrace "empty query"
            [i] ->return $ diff (KV filteredAttrs) (mapKey' (alterKeyType (Le.over keyFunc makeDelayed)) . mapFValue' makeDelayedV $ i  )
            _ -> errorWithStackTrace "multiple result query"
       return res
  where
    makeDelayed (KOptional :k ) = KOptional :(makeDelayed k)
    makeDelayed (KArray :k ) = KArray :(makeDelayed k)
    makeDelayed [] = [KDelayed ]

    makeDelayedV (TB1 i) = LeftTB1 $ Just (TB1 i)
    makeDelayedV (LeftTB1 i) = LeftTB1 $ makeDelayedV <$> i
    makeDelayedV (ArrayTB1 i) = ArrayTB1 $ makeDelayedV <$> i

    delayedattrs = concat $ fmap (keyValue . _relOrigin ) .  F.toList <$> M.keys filteredAttrs
    filteredAttrs = M.filterWithKey (\key v -> S.isSubsetOf (S.map _relOrigin key) (S.fromList $ _kvdelayed m) && (all (maybe False id) $ fmap (fmap (isNothing .unSDelayed)) $ fmap unSOptional $ kattr $ v)  ) (_kvvalues $ vs)



selectAll
  ::
     KVMetadata Key
     -> TBData Key ()
     -> Int
     -> Maybe PageToken
     -> Int
     -> [(Key, Order)]
     -> WherePredicate
     -> TransactionM (Int,[KV Key Showable])
selectAll meta m offset i  j k st = do
      inf <- ask
      let
          unref (TableRef i) = allMaybes $ unFin . upperBound <$>  i
          unref (HeadToken ) = Nothing
      v <- liftIO$ paginate inf meta m k offset j ( join $ fmap unref i) st
      return v


connRoot dname = (fromString $ "host=" <> host dname <> " port=" <> port dname  <> " user=" <> user dname <> " dbname=" <> dbn  dname <> " password=" <> pass dname   )


tSize = 400

postgresOps = SchemaEditor updateMod patchMod insertMod deleteMod (\ m j off p g s o-> (\(l,i) -> (i,(TableRef <$> G.getBounds m i) ,l)) <$> selectAll  m j (fromMaybe 0 off) p (fromMaybe tSize g) s o )  (\table j -> do
    inf <- ask
    liftIO . loadDelayed inf (tableMeta table) (allRec' (tableMap inf) table ) $ j ) mapKeyType undefined undefined (\ a -> liftIO . logTableModification a) tSize (\inf -> withTransaction (conn inf))  overloadedRules Nothing
