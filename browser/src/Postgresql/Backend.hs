{-# LANGUAGE RecordWildCards,Arrows,GADTs,FlexibleContexts,TypeFamilies ,NoMonomorphismRestriction,OverloadedStrings ,TupleSections #-}
module Postgresql.Backend (connRoot,postgresOps) where

import Control.Exception
import Control.Monad.RWS hiding (pass)
import Control.Monad.Writer hiding (pass)
import Data.Bifunctor
import Data.Either
import qualified Data.Foldable as F
import Data.Functor.Apply
import Data.Interval (Extended(..), upperBound)
import qualified Data.List as L
import qualified Data.ByteString.Char8 as BS
import Data.Maybe
import Data.String
import qualified Data.Text as T
import Data.Text (Text)
import Data.Time
import Data.Tuple
import Database.PostgreSQL.Simple
import Debug.Trace
import Default
import GHC.Int
import Postgresql.Extensions
import Postgresql.Parser
import Postgresql.Printer
import Postgresql.Types
import Prelude hiding (head, takeWhile)
import RuntimeTypes
import Schema
import SchemaQuery
import Types
import qualified Types.Index as G
import Types.Patch
import Utils

insertPatch
  :: (MonadIO m ,Functor m )
     => InformationSchema
     -> Connection
     -> KVMetadata Key
     -> TBData Key Showable
     -> m (TBIdx Key Showable)
insertPatch  inf conn table row  = liftIO $ if not (kvNull serialTB)
      then do
        let
          iquery :: String
          (iquery, namemap)= codegen $ do
            j <- projectTree inf table serialTB 
            return $ T.unpack $ prequery <> " RETURNING (SELECT row_to_json(q) FROM (" <> selectRow "p0" j <> ") as q)"
        liftIO $ logTable inf table . BS.unpack =<< formatQuery conn (fromString iquery) directAttr
        [out] <- queryWith (fromRecordJSON inf table serialTB namemap) conn (fromString iquery) directAttr
        let gen =  patch out
        return (patch out)
      else do
        let
          iquery = T.unpack prequery
        executeLogged  inf table (fromString iquery) directAttr
        return []
    where
      prequery = "INSERT INTO " <> kvMetaFullName table <> " (" <> T.intercalate "," (key <$> directAttrProj) <> ") VALUES (" <> T.intercalate "," (value <$> directAttrProj) <> ")"
      attrs = unkvlist row
      testSerial (Attr k v) = (isSerial (keyType k)) && (isNothing.unSSerial $ v)
      testSerial _ = False
      serialTB = kvlist $ ((\k -> Attr k (keyType k )) <$> filter (isSerial.keyType) (_kvattrs table))
      directAttr :: [TB Key Showable]
      directAttr = filter (not.testSerial) attrs
      directAttrProj = projKey directAttr 

projKey :: [TB Key a ] -> [Key]
projKey = concat . fmap (fromMaybe [] . _relOutputs .index)

value i = "?"  <> fromMaybe ""  (inlineType (keyType i))
key = escapeReserved . keyValue 

attrValueName ::  TB (FKey k) a -> Text
attrValueName (Attr i _ )= keyValue i
attrValueName (IT i  _) = keyValue i

deleteIdx
  ::
     InformationSchema ->  KVMetadata Key -> TBIndex Showable -> Table -> IO ()
deleteIdx inf mk ix@(Idex kold) t = do
    executeLogged inf mk qstr qargs
    return ()
  where
    m = recoverFields inf <$> mk
    qstr = fromString $ T.unpack del
    qargs = koldPk
    equality k = escapeReserved (attrValueName k) <> "="  <> "?"
    koldPk = uncurry Attr <$> zip (_relOrigin <$> _kvpk m) (F.toList kold)
    pred   =" WHERE " <> T.intercalate " AND " (fmap  equality koldPk)
    del = "DELETE FROM " <> rawFullName t <>   pred

applyPatch
  ::
     InformationSchema -> KVMetadata Key ->([TBIndex Showable] ,TBIdx PGKey Showable) -> IO ()
applyPatch inf m patch  = do
    executeLogged inf m qstr qargs
    return ()
  where
    (qstr,qargs,_) = updateQuery (recoverFields inf <$> m)  patch

updateQuery
  :: IsString a1 =>
     KVMetadata (FKey (KType (Prim PGType (Text, Text))))
     -> ([TBIndex Showable], TBIdx PGKey Showable)
     -> (a1, [(KType (Prim KPrim (Text, Text)), FTB Showable)],
         Maybe a2)
updateQuery m (pks,skv) = (qstr,qargs,Nothing)
  where
    qstr = fromString $ T.unpack up
    qargs = (first (fmap textToPrim) <$> (catMaybes $ fst <$> inputs)) <> concat (koldPk <$> pks)
    equality k = k <> "="  <> "?"
    koldPk (Idex kold) = zip (fmap textToPrim . keyType . L.head . F.toList . relOutputSet <$> _kvpk m) (F.toList kold)
    pred   (Idex kold) =  T.intercalate " AND " (equality . escapeReserved . keyValue . fst <$> zip (L.head  . F.toList . relOutputSet <$> _kvpk m) (F.toList kold))
    inputs = execWriter $ mapM (attrPatchName Nothing) (patchNoRef skv)
    setter = " SET " <> T.intercalate "," (snd <$> inputs)
    paren i = "(" <> i <> ")"
    up = "UPDATE " <> kvMetaFullName m <> setter <> " WHERE " <> T.intercalate " OR " ( paren . pred  <$> pks)


attrPatchName :: Maybe Text -> PathAttr PGKey Showable -> Writer [(Maybe (KType (Prim PGType (Text, Text)) , FTB Showable), Text)] ()
attrPatchName pre (PAttr k p ) = sqlPatchFTB atom (maybe "" (\i -> i <> ".") pre <> escapeReserved ( keyValue k)) id (keyType k) p
  where
    atom k c ty (PAtom (SDelta (DSInt i))) = inpVariable  (ty,TB1 $ SNumeric i) ( k <> "=" <> c  (k <> " + ?"))
    atom k c ty i  = inpVariable  (ty,create i) ( k <> "=" <> c "?")
attrPatchName pre (PInline k p ) = sqlPatchFTB atom (maybe "" (\i -> i <> ".") pre <> escapeReserved ( keyValue k)) id (keyType k) p
  where
    atom k c ty (PAtom i)  = mapM_ (attrPatchName (Just k)) i
attrPatchName pre i = error $ show (pre,i)

inpVariable :: (KType (Prim PGType (Text, Text)), FTB Showable) -> Text -> UpdateOperations
inpVariable i j = tell [(Just i,j)]

inpStatic :: Text -> UpdateOperations
inpStatic j = tell [(Nothing,j)]

type UpdateOperations =  Writer [(Maybe (KType (Prim PGType (Text, Text)), FTB Showable), Text)] ()
type SetterGen c = (Text
                -> (Text -> Text)
                -> KType (Prim PGType (Text, Text))
                -> PathFTB c
                -> UpdateOperations)

escapeInline :: Text -> Text
escapeInline str = case T.splitOn "."  str of
           [] -> ""
           [i] -> i
           x:xs ->  "(" <> x <> ")." <> T.intercalate "." xs

sqlPatchFTB :: Show c => SetterGen c ->SetterGen c
sqlPatchFTB f k call (Primitive l c ) s = go k call l s
  where
    go  prefix call (KSerial:xs)  (POpt o) = do
      case o of
        Just j ->go  prefix call xs  j
        Nothing -> inpStatic $  (k <> "=" <>   "null" )
    go  prefix call (KOptional:xs)  (POpt o) = do
      case o of
        Just j ->go  prefix call xs  j
        Nothing -> inpStatic $  (k <> "=" <>   "null" )
    go  prefix ca (KArray:xs)  (PIdx ix o) = do
      case o of
        Just j -> go  (k <> six ix ) ca xs  j
        Nothing -> inpStatic $ (k <> " = " <>  escapeInline prefix <> sixDown ix  <> " || " <> escapeInline prefix <> sixUp ix  )
      where
        six ix = "[" <> T.pack (show (ix + 1 )) <> "]"
        sixUp ix = "[" <> T.pack (show (ix + 2)) <> ":]"
        sixDown ix = "[:" <> T.pack (show (ix )) <> "]"
    go  prefix ca (KInterval:xs) b@(PatchSet _ ) =
      f prefix ca (Primitive (KInterval:xs) c ) b
    go  prefix ca (KInterval:xs)  (PInter s (v,j)) =
      case (s,v) of
        (True,NegInf) ->   inpStatic (k <> " = " <> "lowerI(" <> escapeInline prefix <> ",null," <> (T.pack (show j )) <> ")")
        (True,Finite b) -> go  prefix ((\i ->"lowerI(" <> escapeInline prefix <> "," <> i <> "," <> (T.pack (show j )) <> ")") . ca) xs  b
        (False,PosInf) -> inpStatic (k <> " = " <> "upperI(" <>  escapeInline prefix <> ",null," <> (T.pack (show j )) <> ")")
        (False ,Finite b) -> go  prefix ((\i -> "upperI(" <>  escapeInline prefix <> "," <> i <> "," <> (T.pack (show j )) <> ")") . ca ) xs  b
    go  prefix c ty (PatchSet b) = mapM_ (go  prefix c ty) b
    go  prefix ca ty i@(PAtom _) = f prefix ca (Primitive ty c) i
    go  prefix  _ ty i = error $ show (k,ty,i)


paginate
  :: InformationSchema
  -> KVMetadata Key
  -> KVMeta Key
  -> [(Rel Key, Order)]
  -> Int
  -> Int
  -> Maybe [FTB Showable]
  -> WherePredicate
  -> IO (Int, [TBData Key Showable])
paginate inf meta t order off size koldpre wherepred = do
  let ((que,attr),name) = selectQuery inf meta t koldpre order wherepred
  let quec = fromString $ T.unpack $ 
        "SELECT row_to_json(q),(case WHEN ROW_NUMBER() over () = 1 then count(*) over () else null end) as count FROM (" <> que <> ") as q " <> offsetQ <> limitQ
  liftIO $ logTable inf meta . BS.unpack =<< formatQuery (conn inf ) quec (fromMaybe [] attr)
  v <- queryWith (withCount (fromRecordJSON inf meta t name )) (conn inf) quec (fromMaybe [] attr) `catch` (\e -> print (t,wherepred ) >> throw (e :: SomeException))
  let estimateSize = maybe 0 (\c-> c - off ) $ join $ safeHead ( fmap snd v :: [Maybe Int])
  -- print estimateSize
  return (estimateSize, fmap fst v)
  where
    offsetQ = " OFFSET " <> T.pack (show off)
    limitQ = " LIMIT " <> T.pack (show size)


batchEd :: KVMetadata Key -> [RowPatch Key Showable] -> TransactionM [RowPatch Key Showable]
batchEd m i =  do
  inf <- askInf
  let
    codeGen (RowPatch (i,PatchRow dff)) = addRet $ updateQuery mpg ([i] ,filterWritablePatch dff)
    codeGen (BatchPatch i (PatchRow dff)) = addRet $ updateQuery mpg (i ,filterWritablePatch dff)
    addRet (q,i,j) = (q <> " RETURNING null",i,j)
    mpg = (recoverFields inf <$> filterMetadataReadable m)
    with = "WITH "
    as i j = i <> " AS (" <> j <> ")"
    many l = T.intercalate "," l
    select l  = "SELECT * FROM " <> l <> ""
    union = T.intercalate " UNION ALL "
    query = with <> many (uncurry as <$> tables) <> select ("("<>union (select  .fst <$> tables)<> ")")  <> " as t"
      where names ix = "r" <> T.pack (show ix)
            tables = zip (names <$> [0..]) ((\(i,_,_) -> i ) <$> l)
    l = codeGen  . firstPatchRow (recoverFields inf) <$> catMaybes  (rowPatchNoRef . filterWritableRowPatch <$> F.toList i)
  l <- queryLogged inf m (fromString $ T.unpack query) (concat $ (\(_,i,_) -> i) <$> l)
  liftIO $ print (l :: [Only(Maybe Int)])
  return i

insertMod :: KVMetadata Key -> TBData Key Showable -> TransactionM (RowPatch Key Showable)
insertMod m j  = do
  inf <- askInf
  liftIO $ do
      let
        table = lookTable inf (_kvname m)
        defs = defaultTableData inf table j
        ini = compact (defs ++  patch j)
      d <- either error (maybe (return []) (insertPatch  inf (conn  inf) m) . kvNonEmpty . tableNonRef. filterWriteable ) (tableCheck m (create ini))
      l <- liftIO getCurrentTime
      return $ either (error . unlines ) (createRow' m) (typecheck (typeCheckTable (rawSchema table,rawName table)) (create $ ini ++ d))


deleteMod :: KVMetadata Key -> TBData Key Showable -> TransactionM (((RowPatch Key Showable)))
deleteMod m t = do
  inf <- askInf
  liftIO $  do
      let table = lookTable inf (_kvname m)
          idx = G.getIndex m t
      deleteIdx inf m idx  table
      l <- liftIO getCurrentTime
      return $  RowPatch (idx,DropRow )


patchMod :: KVMetadata Key -> [TBIndex Showable] -> TBIdx Key Showable-> TransactionM (RowPatch Key Showable)
patchMod m pk patch = do
  inf <- askInf
  liftIO $ do
    traverse (\i -> 
      applyPatch inf m (pk, firstPatch (recoverFields inf) i)) (nonEmpty (patchNoRef $ filterWritablePatch patch))
    return $ rebuild  pk (PatchRow patch)

getRow  :: Table -> KVMeta Key -> TBIndex Showable -> TransactionM (TBIdx Key Showable)
getRow table  delayed (Idex idx) = do
  inf <- askInf
  liftIO $ check inf (filterReadable delayed)
  where
    m = tableMeta table
    check inf delayed = do
         let
             (str,namemap) = codegen (getFromQuery inf m delayed)
             pk = fmap (firstTB (recoverFields inf) ) $ zipWith Attr (_relOrigin .simplifyRel <$> _kvpk m) idx
             qstr = (fromString $ T.unpack str)
         liftIO $ logTable inf m . BS.unpack =<< formatQuery (conn inf) qstr pk
         is <- queryWith (fromRecordJSON inf m delayed namemap) (conn inf) qstr pk
         case is of
           [i] -> return $ patch i
           [] -> error $ "empty query: " ++ show (tableName table) ++ show idx
           v -> error $ "multiple result query: " ++ show (tableName table) ++ " - " ++  show idx  ++ "\n"++ show v

filterMetadataReadable :: KVMetadata Key -> KVMetadata Key
filterMetadataReadable i@KVMetadata{..} =i {_kvattrs = filter (\k -> L.elem FRead (keyModifier k)) _kvattrs  , _kvjoins = filter (not . isPlugin) _kvjoins }
  where isPlugin (PluginField _  ) = True
        isPlugin _ = False


filterReadable = kvFilter (\k -> attr (relOutputSet k))
  where attr = F.all (\k -> L.elem FRead (keyModifier k)) 

filterWriteable = kvFilter (\k -> attr (relOutputSet k))
  where attr = F.all (\k -> L.elem FWrite (keyModifier k)) 

filterWritablePatch = filter (\k -> F.all (L.elem FWrite . keyModifier) (relOutputSet $ index k)) 

filterWritableRowPatch (BatchPatch i j) = BatchPatch i (filterWritableRow j )
filterWritableRowPatch (RowPatch (i,j ))= RowPatch (i,filterWritableRow j ) 

filterWritableRow (PatchRow j )= PatchRow $ filterWritablePatch j
filterWritableRow (CreateRow j )= CreateRow $ filterWriteable j
filterWritableRow (DropRow) = DropRow


selectAll
  ::
     KVMetadata Key
     -> KVMeta Key 
     -> Maybe Int
     -> Maybe PageToken
     -> Maybe Int
     -> [(Rel Key, Order)]
     -> WherePredicate
     -> TransactionM ([KV Key Showable],PageToken,Int)
selectAll meta m offset i  j k st = do
  inf <- askInf
  let
      unIndex (Idex i) = i
      unref (TableRef i) = fmap unIndex $ unFin $ upperBound i
  (l,i) <- liftIO $ paginate inf meta (filterReadable m) k (fromMaybe 0 offset) (fromMaybe tSize j) ( join $ fmap unref i) st
  return (i,(TableRef $ G.getBounds meta i) ,l)

connRoot dname = (fromString $ "host=" <> host dname <> " port=" <> port dname  <> " user=" <> user dname <> " dbname=" <> dbn  dname <> " password=" <> pass dname   )

tSize = 100


postgresOps = SchemaEditor patchMod insertMod deleteMod  batchEd  selectAll getRow mapKeyType (\ a -> liftIO . logTableModification a) (\a -> liftIO . logUndoModification a) tSize  (\inf -> withTransaction (conn inf))  overloadedRules
