{-# LANGUAGE RankNTypes, TupleSections,BangPatterns,OverloadedStrings #-}


module Schema where

import Types
import qualified Data.Traversable as Tra
import Data.Unique
import qualified Data.Foldable as F
-- import Step
import Data.Maybe
import Data.String
import Control.Monad.IO.Class
import qualified Data.Binary as B
import GHC.Stack
import Data.Monoid
import Utils
import Control.Exception
import System.Time.Extra

import Data.Functor.Identity
import Database.PostgreSQL.Simple
import Data.Time

import Data.Vector (Vector)
import qualified Data.Vector as V

import Control.Monad
import Control.Applicative
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Map (Map)
import Data.Set (Set)
import Debug.Trace
import Control.Concurrent

import Data.Text.Lazy(Text)
import qualified Data.Text.Lazy as T

import qualified Reactive.Threepenny as R


import Query
import Postgresql


createType :: Text ->  Unique -> (Text,Text,Maybe Text,Text,Text,Text,Text,Maybe Text,Maybe Text,Maybe Text) -> Key
createType _ un (t,c,trans,"tsrange",_,_,n,def,_,_) = (Key   c trans un (nullable n $ KInterval $ Primitive "timestamp without time zone"))
createType _ un (t,c,trans,"tstzrange",_,_,n,def,_,_) = (Key   c trans un (nullable n $ KInterval $ Primitive "timestamp with time zone"))
createType _ un (t,c,trans,"daterange",_,_,n,def,_,_) = (Key   c trans un (nullable n $ KInterval $ Primitive "date"))
createType _ un (t,c,trans,"int4range",_,_,n,def,_,_) = (Key   c trans un (nullable n $ KInterval $ Primitive "int4"))
createType _ un (t,c,trans,"numrange",_,_,n,def,_,_) = (Key   c trans un (nullable n $ KInterval $ Primitive "numeric"))
createType _ un (t,c,trans,"USER-DEFINED",_,"floatrange",n,def,_,_) = (Key   c trans un (nullable n $ KInterval $ Primitive "double precision"))
createType _ un (t,c,trans,"USER-DEFINED",_,"trange",n,def,_,_) = (Key   c trans un (nullable n $ KInterval $ Primitive "time"))
-- Table columns Primitive
createType s un (t,c,trans,"USER-DEFINED",udtschema ,udtname,n,def,_,_) |  udtschema == s = (Key c trans un (nullable n $ InlineTable  udtschema udtname ))
createType s un (t,c,trans,"ARRAY",udtschema ,udtname,n,def,_,_) | udtschema == s = (Key c trans un (nullable n $ KArray $ InlineTable  udtschema $T.drop 1 udtname ))
createType _ un (t,c,trans,"ARRAY",_,i,n,def,p,_) = (Key   c trans un (nullable n $ KArray $ (Primitive (T.tail i))))
createType _ un (t,c,trans,_,_,"geometry",n,def,p,_) = (Key   c trans un (nullable n $ Primitive $ (\(Just i) -> i) p))
createType _ un (t,c,trans,_,_,"box3d",n,def,p,_) = (Key   c trans un (nullable n $ Primitive $  "box3d"))
createType _ un (t,c,trans,ty,_,_,n,def,_,Just "pdf" ) =(Key c   trans un (serial def . nullable n $ KDelayed $ Primitive "pdf" ))
createType _ un (t,c,trans,ty,_,_,n,def,_,Just "jpg" ) =(Key c   trans un (serial def . nullable n $ KDelayed $ Primitive "jpg" ))
createType _ un (t,c,trans,ty,_,_,n,def,_,Just "ofx" ) =(Key c   trans un (serial def . nullable n $ KDelayed $ Primitive "ofx" ))
createType _ un (t,c,trans,ty,_,_,n,def,_,Just dom ) =(Key c   trans un (serial def . nullable n $ Primitive dom))
createType _ un (t,c,trans,ty,_,_,n,def,_,_) =(Key c   trans un (serial def . nullable n $ Primitive ty))
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
  , pluginsMap :: Map (Text,Text,Text) Key
  , mvarMap :: MVar (Map Table ({-R.Event [TB1 Showable], R.Handler [TB1 Showable], -} MVar  [TB1 Showable], R.Tidings [TB1 Showable]))
  , conn :: Connection
  , rootconn :: Connection
  }

type TableSchema = (Map (Text,Text) Key,Map (Set Key) Table,Map Text Table)

foreignKeys :: Query
foreignKeys = "select origin_table_name,target_table_name,origin_fks,target_fks,rel_fks from metadata.fks where origin_schema_name = target_schema_name  and  target_schema_name = ?"


queryAuthorization :: Connection -> Text -> Text -> IO (Map Text [Text])
queryAuthorization conn schema user = do
    sq <- query conn aq (schema,user)
    let convert (tname,authorizations) = (tname ,V.toList authorizations)
    return $ M.fromList $ convert <$> sq
  where aq = "select table_name,authorizations from metadata.authorization where table_schema = ? and grantee = ? "

keyTables :: Connection -> Connection -> (Text ,Text)-> IO InformationSchema
keyTables conn userconn (schema ,user) = do
       uniqueMap <- join $ mapM (\i-> (i,) <$> newUnique) <$>  query conn "select o.table_name,o.column_name from information_schema.tables natural join information_schema.columns o where table_schema = ? "(Only schema)
       res2 <- fmap ( (\i@(t,c,o,j,k,l,m,n,d,z)-> (t,) $ createType  schema ((\(t,c,i,j,k,l,m,n,d,z)-> (\(Just i) -> i) $ M.lookup (t,c) (M.fromList uniqueMap)) i) i )) <$>  query conn "select table_name,o.column_name,translation,data_type,udt_schema,udt_name,is_nullable,column_default, type,domain_name from information_schema.tables natural join information_schema.columns  o left join metadata.table_translation t on o.column_name = t.column_name    left join   public.geometry_columns on o.table_schema = f_table_schema  and o.column_name = f_geometry_column where table_schema = ?"  (Only schema)
       --res2 <- fmap ( (\i@(t,c,o,j,k,l,m,n,d,z)-> (t,) $ createType  schema ((\(t,c,i,j,k,l,m,n,d,z)-> (\(Just i) -> i) $ M.lookup (t,c) (M.fromList uniqueMap)) i) i )) <$>  query conn "select table_name,o.column_name,translation,data_type,udt_schema,udt_name,is_nullable,column_default,'' :: text ,domain_name from information_schema.tables natural join information_schema.columns  o left join metadata.table_translation t on o.column_name = t.column_name where table_schema = ? " {- left join   public.geometry_columns on o.table_schema = f_table_schema  and o.column_name = f_geometry_column " -} (Only schema)
       let
          keyList =  fmap (\(t,k)-> ((t,keyValue k),k)) res2
       -- keyMap <- preprocessSumTypes (M.fromList keyList)
          keyMapPre = M.fromList keyList
          lookupKey' ::  Map (Text,Text) Key -> (Text,Text) ->  Key
          lookupKey' keyMap = (\(t,c)-> justError ("nokey" <> show (t,c)) $ M.lookup ( (t,c)) keyMap )
       eitherItems <-  join $  mapM (\(t,l,n)-> do
         un <- newUnique
         let
           lcol = lookupKey' keyMapPre . (t,) <$> V.toList l
           tnew = Key n Nothing un (KEither (keyType <$> lcol) )
         return (t,[(tnew,Path (S.fromList lcol) (FKEitherField tnew lcol) (S.singleton tnew) )]) ) <$> query conn "SELECT table_name,sum_columns,column_name FROM metadata.table_either WHERE table_schema = ? " (Only schema)
       let eitherMap = M.fromListWith mappend  $ fmap (\(t,j) -> (t,fmap snd j )) $ eitherItems
           keyMap =  foldr (uncurry M.insert) keyMapPre $ concat $ fmap (\(t,j) -> fmap (\ki -> ((t,keyValue ki),ki)) $ fmap fst j ) $ eitherItems
       let
          lookupKey3 :: (Functor f) => f (Text,Maybe (Vector Text)) -> f (Text,Vector Key)
          lookupKey3 = fmap  (\(t,c)-> (t,maybe V.empty (fmap (\ci -> justError ("no key " <> T.unpack ci) $ M.lookup (t,ci) keyMap)) c) )
          lookupKey2 :: Functor f => f (Text,Text) -> f Key
          lookupKey2 = fmap  (\(t,c)-> justError ("nokey" <> show (t,c)) $ M.lookup ( (t,c)) keyMap )
          lookupKey ::  (Text,Text) ->  Key
          lookupKey = (\(t,c)-> justError ("nokey" <> show (t,c)) $ M.lookup ( (t,c)) keyMap )
          readTT :: Text ->  TableType
          readTT "BASE TABLE" = ReadWrite
          readTT "VIEW" = ReadOnly
          readTT i =  error $ T.unpack i
       authorization <- queryAuthorization conn schema user
       descMap <- M.fromList . fmap  (\(t,cs)-> (t,fmap (\c -> (\(Just i) -> i) $ M.lookup (t,c) keyMap) (V.toList cs)) ) <$> query conn "SELECT table_name,description FROM metadata.table_description WHERE table_schema = ? " (Only schema)
       transMap <- M.fromList   <$> query conn "SELECT table_name,translation FROM metadata.table_name_translation WHERE schema_name = ? " (Only schema)

       res <- lookupKey3 <$> query conn "SELECT t.table_name,pks FROM metadata.tables t left join metadata.pks  p on p.schema_name = t.schema_name and p.table_name = t.table_name where t.schema_name = ?" (Only schema) :: IO [(Text,Vector Key )]
       resTT <- fmap readTT . M.fromList <$> query conn "SELECT table_name,table_type FROM information_schema.tables where table_schema = ? " (Only schema) :: IO (Map Text TableType)
       let lookFk t k =V.toList $ lookupKey2 (fmap (t,) k)
       fks <- M.fromListWith S.union . fmap (\i@(tp,tc,kp,kc,rel) -> (tp,S.singleton $ Path (S.fromList $ lookFk tp kp) (FKJoinTable tp (zipWith3 (\a b c -> Rel a b c) (lookFk tp kp ) (V.toList rel) (lookFk tc kc)) tc) (S.fromList $ lookFk tc kc))) <$> query conn foreignKeys (Only schema) :: IO (Map Text (Set (Path (Set Key) (SqlOperation ) )))
       let all =  M.fromList $ fmap (\(c,l)-> (c,S.fromList $ fmap (\(t,n)-> (\(Just i) -> i) $ M.lookup (t,keyValue n) keyMap ) l )) $ groupSplit (\(t,_)-> t)  $ (fmap (\((t,_),k) -> (t,k))) $  M.toList keyMap :: Map Text (Set Key)
           pks =  (\(c,pksl)-> let
                                  pks = S.fromList $ F.toList pksl
                                  inlineFK =  fmap (\k -> (\t -> Path (S.singleton k ) (FKInlineTable $ inlineName t) S.empty ) $ keyType k ) .  filter (isInline .keyType ) .  S.toList <$> M.lookup c all
                                  eitherFK =   M.lookup c eitherMap
                                  attr = S.difference (S.filter (not. isKEither.keyType)  $ (\(Just i) -> i) $ M.lookup c all) ((S.fromList $ (maybe [] id $ M.lookup c descMap) )<> pks)
                                in (pks ,Raw schema  ((\(Just i) -> i) $ M.lookup c resTT) (M.lookup c transMap) (S.filter (isKDelayed.keyType)  attr) c (maybe [] id $ M.lookup c authorization)  pks (maybe [] id $ M.lookup  c descMap) (fromMaybe S.empty $ M.lookup c fks    <> fmap S.fromList inlineFK <> fmap S.fromList eitherFK   ) attr )) <$> res :: [(Set Key,Table)]
       let (i1,i2,i3) = (keyMap, M.fromList $ filter (not.S.null .fst)  pks,M.fromList $ fmap (\(_,t)-> (tableName t ,t)) pks)
       mvar <- newMVar M.empty
       return  $ InformationSchema schema i1 i2 i3 M.empty mvar  userconn conn

liftMod inf k (EditTB a b ) = EditTB (liftKeys inf k a) (liftKeys inf k b)
liftMod inf k (InsertTB a  ) = InsertTB(liftKeys inf k a)
liftMod inf k (DeleteTB a  ) = DeleteTB (liftKeys inf k a)
liftKeys
  :: InformationSchema
     -> Text
     -> FTB1 Identity Text a
     -> FTB1 Identity Key a
liftKeys inf tname tb
  = liftTable tname tb
  where
        liftTable tname (TB1 _ v )  = TB1  (tableMeta ta) $ mapComp (\(KV i) -> KV $ mapComp (liftField tname) <$> (M.mapKeys (S.map (lookKey inf tname)) i)) v
            where
                  ta = lookTable inf tname
        liftTable tname (LeftTB1 j ) = LeftTB1 $ liftTable tname <$> j
        liftTable tname (ArrayTB1 j ) = ArrayTB1 $ liftTable tname <$> j
        liftField :: Text -> TB Identity Text a -> TB Identity Key a
        liftField tname (TBEither n k j ) = TBEither (lookKey inf tname n) (mapComp (liftField tname) <$> k ) (mapComp (liftField tname ) <$> j)
        liftField tname (Attr t v) = Attr (lookKey inf tname t) v
        liftField tname (FKT ref i rel2 tb) = FKT (mapComp (liftField tname) <$> ref)  i ( rel) (liftTable tname2 tb)
            where (Path _ (FKJoinTable _ rel tname2 ) _) = justError (show (rel2 ,rawFKS ta)) $ L.find (\(Path i _ _)->  S.map keyValue i == S.fromList (_relOrigin <$> rel2))  (F.toList$ rawFKS  ta)
                  ta = lookTable inf tname
        liftField tname (IT rel tb) = IT (mapComp (liftField tname ) rel) (liftTable tname2 tb)
            where Just (Path _ (FKInlineTable tname2 ) _) = L.find (\(Path i _ _)->  S.map keyValue i == S.fromList (keyattr rel))  (F.toList$ rawFKS  ta)
                  ta = lookTable inf tname


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
  return $ Key name Nothing    un ty


catchPluginException :: InformationSchema -> Text -> Text -> IO (Maybe a) -> IO (Maybe a)
catchPluginException inf pname tname i = do
  i `catch` (\e  -> do
                execute (rootconn inf) "INSERT INTO metadata.plugin_exception (schema_name,table_name,plugin_name,exception) values(?,?,?,?)" (schemaName inf,pname,tname,show (e :: SomeException) )
                return Nothing )


logTableModification
  :: B.Binary b =>
     InformationSchema
     -> TableModification b -> IO (TableModification b)
logTableModification inf (TableModification Nothing table i) = do
  time <- getCurrentTime
  let ltime =  utcToLocalTime utc $ time
  [Only id] <- liftIO $ query (rootconn inf) "INSERT INTO metadata.modification_table (modification_time,table_name,modification_data,schema_name) VALUES (?,?,?,?) returning modification_id "  (ltime,rawName table, Binary (B.encode $ mapMod keyValue  i) , schemaName inf)
  return (TableModification (id) table i )


withInf d s f = withConn d (f <=< (\conn -> keyTables conn conn (s,"postgres")))
withConnInf d s f = withConn d (\conn ->  f =<< liftIO ( keyTables  conn conn (s,"postgres")) )


testParse db sch q = withConnInf db sch (\inf -> do
                                       let (rp,rpq) = rootPaths' (tableMap inf) (fromJust $ M.lookup q (tableMap inf))
                                       q <- queryWith_ (fromAttr (rp) ) (conn  inf) (fromString $ T.unpack $ rpq)
                                       return $ q
                                           )

testFireMetaQuery q = testParse "incendio" "metadata"  q
testFireQuery q = testParse "incendio" "incendio"  q
testAcademia q = testParse "academia" "academia"  q

selectAll inf table   = liftIO $ do
      let
          tb =  tableView (tableMap inf) table
      print (tableName table,selectQuery tb)
      (t,v) <- duration  $ queryWith_  (fromAttr (unTlabel tb)) (conn inf)(fromString $ T.unpack $ selectQuery tb)
      print (tableName table,t)
      return v

eventTable inf table = do
    let mvar = mvarMap inf
    mmap <- takeMVar mvar
    (mtable,td) <- case (M.lookup table mmap ) of
         Just (i,td) -> do
           putMVar mvar mmap
           return (i,td)
         Nothing -> do
           res <- selectAll  inf table
           mnew <- newMVar res
           (e,h) <- R.newEvent
           ini <- readMVar mnew
           forkIO $ forever $ do
              h =<< takeMVar mnew
           bh <- R.stepper ini e
           let td = (R.tidings bh e)
           putMVar mvar (M.insert table (mnew,td) mmap)
           return (mnew,td)
    return (mtable,td)


addTable inf table = do
    let mvar = mvarMap inf
    mmap <- takeMVar mvar
    (isEmpty,mtable) <- case (M.lookup table mmap ) of
         Just (i,_) -> do
           emp <- isEmptyMVar i
           putMVar mvar mmap
           return (emp,i)
         Nothing -> do
           res <- selectAll  inf table
           mnew <- newMVar res
           putMVar mvar (M.insert table (mnew, pure []) mmap)
           return (True,mnew )
    t <- readMVar mtable

    return t


testLoadDelayed inf t = do
   let table = lookTable inf t
       tb = tableView (tableMap inf) table
   print tb
   res  <- queryWith_ (fromAttr (unTlabel tb)) (conn inf) (fromString $ T.unpack $ selectQuery tb )
   mapM (loadDelayed inf (unTlabel tb )) res

testFireQueryLoad t  = withConnInf "incendio" "incendio" (flip testLoadDelayed t)

mergeTB1 (TB1 m (Compose k) ) (TB1 m2 (Compose k2) )
  | m == m2 = TB1 m (Compose $ liftA2 (<>) k k2)
  | otherwise = TB1 m (Compose $ liftA2 (<>) k k2) -- errorWithStackTrace (show (m,m2))

ifOptional i = if isKOptional (keyType i) then unKOptional i else i
ifDelayed i = if isKDelayed (keyType i) then unKDelayed i else i


-- Load optional not  loaded delayed values
-- and merge to older values
loadDelayed inf t@(TB1 k v) values@(TB1 ks vs)
  | S.null $ _kvdelayed k = return Nothing
  | L.null delayedattrs  = return Nothing
  | otherwise = do
       let
           whr = T.intercalate " AND " ((\i-> (keyValue i) <>  " = ?") <$> S.toList (_kvpk k) )
           attr = T.intercalate "," delayedattrs
           table = justError "no table" $ M.lookup (_kvpk k) (pkMap inf)
           delayed = fmap (const ()) $ mapKey (kOptional . ifDelayed . ifOptional) $ TB1 k $ Compose $ Identity $ KV filteredAttrs
           str = "SELECT " <> explodeRow (relabelT runIdentity Unlabeled delayed) <> " FROM " <> showTable table <> " WHERE " <> whr
       print str
       is <- queryWith (fromAttr delayed) (conn inf) (fromString $ T.unpack str) (fmap unTB $ F.toList $ _kvvalues $  runIdentity $ getCompose $ tbPK (tableNonRef values))
       case is of
            [] -> errorWithStackTrace "empty query"
            [i] ->return $ Just $ EditTB (mapKey (kOptional.kDelayed.unKOptional) . fmap (SOptional . Just . SDelayed .  unSOptional ) $ i  ) values
            _ -> errorWithStackTrace "multiple result query"
  where
    delayedattrs = concat $ fmap keyValue . F.toList <$> M.keys filteredAttrs
    filteredAttrs = M.filterWithKey (\key v -> S.isSubsetOf key (_kvdelayed k) && (all (maybe False id) $ fmap (fmap (isNothing .unSDelayed)) $ fmap unSOptional $ kattr $ v)  ) (_kvvalues $ unTB vs)

zipInter f = M.intersectionWith f
zipDelete f = fmap f . M.difference
zipCreate f =  fmap f . flip M.difference

fullInsert :: InformationSchema -> TB1 Showable -> IO (TB3 Identity Key Showable)
fullInsert inf (TB1 k1 v1 )  = do
   let proj = _kvvalues . unTB
   ret <- TB1 k1 . Compose . Identity . KV <$>  Tra.traverse (\j -> Compose <$>  tbInsertEdit inf   (unTB j) )  (proj v1)
   (m,t) <- eventTable inf (lookTable inf (_kvname k1))
   l <- R.currentValue (R.facts t)
   if  L.elem ret l
      then do
        return ret
      else do
        i <- insertAttr fromAttr  (conn inf) ret (lookTable inf (_kvname k1))
        putMVar m (i:l)
        return i

fullInsert inf (LeftTB1 i ) = LeftTB1 <$> Tra.traverse (fullInsert inf) i
fullInsert inf (ArrayTB1 i ) = ArrayTB1  <$> Tra.traverse (fullInsert inf) i

noInsert :: InformationSchema -> TB1 Showable -> IO (TB3 Identity Key Showable)
noInsert inf (TB1 k1 v1 )  = do
   let proj = _kvvalues . unTB
   TB1 k1 . Compose . Identity . KV <$>  Tra.sequence (fmap (\j -> Compose <$>  tbInsertEdit inf   (unTB j) )  (proj v1))



fullDiffEdit :: InformationSchema -> TB1 Showable -> TB1 Showable -> IO (TB3 Identity Key Showable)
fullDiffEdit inf old@(TB1 k1 v1 ) ed@(TB1 k2 v2) = do
   let proj = _kvvalues . unTB
   ed <-TB1 k2 . Compose . Identity . KV <$>  Tra.sequence (zipInter (\i j -> Compose <$>  tbDiffEdit inf  (unTB i) (unTB j) ) (proj v1 ) (proj v2))
   updateAttr (conn inf) ed old (lookTable inf (_kvname k2))
   return ed

tbDiffEdit :: InformationSchema -> TB Identity Key Showable -> TB Identity Key Showable -> IO (Identity (TB Identity Key  Showable))
tbDiffEdit inf i j
  | i == j =  return (Identity j)
  | otherwise = tbInsertEdit inf  j

tbInsertEdit inf  j@(Attr k1 k2) = return $ Identity  (Attr k1 k2)
tbInsertEdit inf  (IT k2 t2) = Identity . IT k2 <$> (noInsert inf t2 )
tbInsertEdit inf  (FKT k2 f2 rel2 t2) = do
   Identity . (\tb -> FKT  k2 f2 rel2 tb ) <$> fullInsert inf t2
tbInsertEdit inf j = return $ Identity j


