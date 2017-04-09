{-# LANGUAGE TypeOperators,DeriveFunctor,FlexibleInstances ,ScopedTypeVariables,FlexibleContexts,ConstraintKinds,TypeFamilies,RankNTypes, TupleSections,BangPatterns,OverloadedStrings #-}


module Schema where

import Data.String
import System.Environment
import Data.Either
import Postgresql.Sql
import Postgresql.Types
import qualified Data.Poset as P
import Control.Monad.Trans.Maybe
import Codec.Compression.Zlib
import Data.Word
import Data.Int
import Control.DeepSeq
import Control.Monad.State
import Query
import Step.Host
import Data.Ord
import qualified Data.Interval as Interval
import Types
import Text
import Expression
import Step.Common
import Data.Tuple
import Control.Concurrent.STM.TChan
import Control.Concurrent.STM.TVar
import Control.Concurrent.STM
import Types.Patch
import Control.Monad.RWS
import System.Directory
import qualified Types.Index as G

import SchemaQuery
import qualified NonEmpty as Non
import Control.Monad.Writer
import Debug.Trace
import Prelude hiding (head)
import Data.Unique
import qualified Data.Foldable as F
import Data.Maybe
import qualified Data.Binary as B
import GHC.Stack
import Data.Bifunctor(second,first)
import Utils
import Control.Exception
import Control.Monad.Reader
import qualified Control.Lens as Le

import Data.Functor.Identity
import Database.PostgreSQL.Simple
import Data.Time
import RuntimeTypes

import Data.Traversable(sequenceA,traverse)
import Data.Vector (Vector)
import qualified Data.Vector as V

import Control.Applicative
import qualified Data.List as L
import qualified Data.HashMap.Strict as HM
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Map (Map)
import Data.Set (Set)
import Control.Concurrent

import Data.Text (Text)
import qualified Data.Text as T

import qualified Reactive.Threepenny as R

import Postgresql.Parser
import qualified Data.ByteString.Char8 as BS
import qualified Data.ByteString.Lazy as BSL


createType :: (Bool,Bool,Bool,Bool,Bool,Bool,Text,Text,Maybe Int32) -> KType (Prim (Text,Text,Maybe Word32) (Text,Text))
createType  (isNull,isArray,isDelayed,isRange,isDef,isComp,tysch,tyname,typmod)
  = comp (Primitive base)
  where
    add i v = if i then v else id
    comp = add isNull KOptional . add isArray KArray . add isRange KInterval . add isDef KSerial . add isDelayed KDelayed
    base
      | isComp =  RecordPrim (tysch ,tyname)
      | otherwise = AtomicPrim (tysch ,tyname,fromIntegral <$> typmod)


recoverFields :: InformationSchema -> FKey (KType (Prim KPrim  (Text,Text))) -> FKey (KType (Prim PGType PGRecord))
recoverFields inf v = map
  where map = justError ("notype" <> T.unpack (showKey v)) $ M.lookup (keyFastUnique v)  (backendsKey inf )

meta inf = maybe inf id (metaschema inf)




queryAuthorization :: Connection -> Int -> Int -> IO (Map Int [Text])
queryAuthorization conn schema user = do
    sq <- query conn aq (schema,user)
    let convert (tname,authorizations) = (tname ,V.toList authorizations)
    return $ M.fromList $ convert <$> sq
  where aq = "select \"table\",authorizations from metadata.authorization where schema= ? and grantee = ? "

tableSizes = "SELECT c.relname,c.reltuples::bigint AS estimate FROM   pg_class c JOIN   pg_namespace n ON c.relkind = 'r' and n.oid = c.relnamespace WHERE n.nspname = ? "

-- fromShowable2 i j | traceShow (i,j) False = errorWithStackTrace ""
fromShowable2 i@(Primitive (AtomicPrim PText )) v = fromShowable i $  BS.drop 1 (BS.init v)
fromShowable2 i v = fromShowable i v

testSerial  =((=="nextval"). fst . T.break(=='('))

readFModifier :: Text -> FieldModifier
readFModifier "read" = FRead
readFModifier "edit" = FPatch
readFModifier "write" = FWrite


keyTables ,keyTablesInit :: TMVar DatabaseSchema ->  (Text ,Text) -> (Text -> IO (Auth , SchemaEditor)) -> [Plugins] ->  R.Dynamic InformationSchema
keyTables schemaVar (schema ,user) authMap pluglist =  maybe (keyTablesInit schemaVar (schema,user) authMap pluglist ) return.  HM.lookup schema  =<< liftIO (atomically $ readTMVar .globalRef =<< readTMVar schemaVar )

extendedRel :: HM.HashMap (Text,Text) Key -> Text -> Text -> Text -> Key -> Rel Key
extendedRel inf t a b c =  snd access $ (lrel (fst access))

    where path :: [Text]
          path = T.splitOn "->" a
          lrel :: Text -> Rel Key
          lrel t =  Rel (justError "no key" $ HM.lookup (t ,  last path) inf ) (readBinaryOp b) c
          access :: (Text, Rel Key -> Rel Key)
          access = F.foldl' cons  (t,id) (init path)
            where
              cons (t,j) i = (snd $ inlineName $ keyType  k ,j . RelAccess k )
                where
                  k :: Key
                  k = justError "no key" $HM.lookup (t,i) inf

keyTablesInit schemaRef  (schema,user) authMap pluglist = do
       schemaVar <- liftIO$ atomically $ readTMVar schemaRef
       let conn = schemaConn schemaVar
           schemaId = justLookH schema (schemaNameMap schemaVar)
       (oauth,ops ) <- liftIO$ authMap schema
       [Only uid] <- liftIO$ query conn "select oid from metadata.\"user\" where usename = ?" (Only user)
       uniqueMap <- liftIO$join $ mapM (\(t,c,op,mod,tr) -> ((t,c),) .(\ un -> (\def ->  Key c tr (V.toList $ fmap readFModifier mod) op def un )) <$> newUnique) <$>  query conn "select o.table_name,o.column_name,ordinal_position,field_modifiers,translation from  metadata.columns o left join metadata.table_translation t on o.column_name = t.column_name   where table_schema = ? "(Only schema)
       res2 <- liftIO$ fmap ( (\i@(t,c,j,k,del,l,m,d,z,b,typ)-> (t,) $ (\ty -> (justError ("no unique" <> show (t,c,fmap fst uniqueMap)) $  M.lookup (t,c) (M.fromList uniqueMap) )  (join $ fromShowable2 (mapKType ty) .  BS.pack . T.unpack <$> join (fmap (\v -> if testSerial v then Nothing else Just v) (join $ listToMaybe. T.splitOn "::" <$> m) )) ty )  (createType  (j,k,del,l,maybe False testSerial m,d,z,b,typ)) )) <$>  query conn "select table_name,column_name,is_nullable,is_array,is_delayed,is_range,col_def,is_composite,type_schema,type_name ,atttypmod from metadata.column_types where table_schema = ?"  (Only schema)
       let
          keyList =  fmap (\(t,k)-> ((t,keyValue k),k)) res2
          backendkeyMap = M.fromList keyList
          keyMap = fmap (typeTransform ops ) $ HM.fromList keyList
          lookupKey3 :: (Functor f) => f (Int,Text,Maybe (Vector Text),Maybe (Vector Text),Bool) -> f (Text,(Int,Vector Key,Vector Key,Bool))
          lookupKey3 = fmap  (\(o,t,c,s,b)-> (t,(o,maybe V.empty (fmap (\ci -> justError ("no key " <> T.unpack ci <> " " <> T.unpack t ) $ HM.lookup (t,ci) keyMap)) c,maybe V.empty (fmap (\ci -> justError ("no key " <> T.unpack ci) $ HM.lookup (t,ci) keyMap)) s,b)) )
          lookupKey2 :: Functor f => f (Text,Text) -> f Key
          lookupKey2 = fmap  (\(t,c)-> justError ("nokey" <> show (t,c)) $ HM.lookup ( (t,c)) keyMap )
          lookupKey ::  (Text,Text) ->  Key
          lookupKey = (\(t,c)-> justError ("nokey" <> show (t,c)) $ HM.lookup ( (t,c)) keyMap )
          readTT :: Text ->  TableType
          readTT "BASE TABLE" = ReadWrite
          readTT "VIEW" = ReadOnly
          readTT i =  errorWithStackTrace  $ T.unpack i

       authorization <- liftIO$ queryAuthorization conn schemaId uid
       descMap <- liftIO$ M.fromList . fmap  (\(t,cs)-> (t,fmap (\c -> justError (show (t,c)) $ HM.lookup (t,c) keyMap) (V.toList cs)) ) <$> query conn "SELECT table_name,description FROM metadata.table_description WHERE table_schema = ? " (Only schema)
       transMap <- liftIO$ M.fromList   <$> query conn "SELECT \"table\",translation FROM metadata.table_name_translation WHERE schema = ? " (Only schemaId )
       uniqueConstrMap <- liftIO$ M.fromListWith (++) . fmap (fmap pure)   <$> query conn "SELECT table_name,pks FROM metadata.unique_sets WHERE schema_name = ? " (Only schema)
       indexMap <- liftIO$ M.fromListWith (++) . fmap (fmap pure)   <$> query conn "SELECT table_name,columns FROM metadata.catalog_indexes WHERE schema_name = ? " (Only schema)

       res <- liftIO$ lookupKey3 <$> query conn "SELECT oid,t.table_name,pks,scopes,s.table_name is not null FROM metadata.tables t left join metadata.pks  p on p.schema_name = t.schema_name and p.table_name = t.table_name left join metadata.sum_table s on s.schema_name = t.schema_name and t.table_name = s.table_name where t.schema_name = ?" (Only schema)

       resTT <- liftIO$ fmap readTT . M.fromList <$> query conn "SELECT table_name,table_type FROM metadata.tables where schema_name = ? " (Only schema)

       let
        schemaForeign :: Query
        schemaForeign = "select target_schema_name from metadata.fks where origin_schema_name = ? and target_schema_name <> origin_schema_name"
       rslist <- liftIO$query conn  schemaForeign (Only schema)
       rsch <- HM.fromList <$> mapM (\(Only s) -> (s,) <$> keyTables  schemaRef (s,user) authMap pluglist) rslist
       let lookFk t k = V.toList $ lookupKey2 (fmap (t,) k)
           lookRFk s t k = V.toList $ lookupKey2 (fmap (t,) k)
            where
              lookupKey2 :: Functor f => f (Text,Text) -> f Key
              lookupKey2 = fmap  (\(t,c)-> justError ("nokey" <> show  (s,t,c)) $ HM.lookup ( (t,c)) map)
                where map
                        | s == schema = keyMap
                        | otherwise = _keyMapL (justError "no schema" $ HM.lookup s rsch)

           lookupKey' :: Text -> (Text,Text) -> Key
           lookupKey' s (t,c) = justError ("nokey" <> show (t,c)) $ HM.lookup ( (t,c)) map
                where map
                        | s == schema = keyMap
                        | otherwise = _keyMapL (justError "no schema" $ HM.lookup s rsch)

       let
          foreignKeys :: Query
          foreignKeys = "select origin_table_name,target_schema_name,target_table_name,origin_fks,target_fks,rel_fks from metadata.fks where origin_schema_name = ?"
          functionKeys :: Query
          functionKeys = "select table_name,schema_name,column_name,cols,fun from metadata.function_keys where schema_name = ?"
          exforeignKeys :: Query
          exforeignKeys = "select origin_table_name,target_schema_name,target_table_name,origin_fks,target_fks,rel_fks from metadata.extended_view_fks where origin_schema_name = ?"

       fks <- liftIO$ M.fromListWith S.union . fmap (\i@(tp,sc,tc,kp,kc,rel) -> (tp,S.singleton $ Path (S.fromList $ lookFk tp kp) ( FKJoinTable (zipWith3 (\a b c -> Rel a (readBinaryOp b) c) (lookFk tp kp ) (V.toList rel) (lookRFk sc tc kc)) (sc,tc)) )) <$> query conn foreignKeys (Only schema)
       efks <- liftIO$ M.fromListWith S.union . fmap (\i@(tp,sc,tc,kp,kc,rel) -> (tp,S.singleton $ Path (S.fromList $ lookFk tp (head . T.splitOn "->" <$> kp)) ( FKJoinTable (zipWith3 (\a b c -> extendedRel keyMap tp a b c)  (V.toList kp ) (V.toList rel) (lookRFk sc tc kc)) (sc,tc)) )) <$> query conn exforeignKeys (Only schema) :: R.Dynamic (Map Text (Set (Path (Set Key) (SqlOperation ) )))


       functionsRefs <- liftIO$ M.fromListWith S.union . fmap (\i@(tp,sc::Text,tc,cols,fun) -> (tp,S.singleton $ Path (S.singleton $ tc) ( FunctionField tc (readFun fun) (indexer <$> V.toList cols ) ) )) <$> query conn functionKeys (Only schema):: R.Dynamic (Map Text (Set (Path (Set Text) (SqlOperationK Text) ) ))
       let all =  M.fromList $ fmap (\(c,l)-> (c,S.fromList $ fmap (\(t,n)-> (\(Just i) -> i) $ HM.lookup (t,keyValue n) keyMap ) l )) $ groupSplit (\(t,_)-> t)  $ (fmap (\((t,_),k) -> (t,k))) $  HM.toList keyMap :: Map Text (Set Key)
       let i3lnoFun = fmap (\(c,(un,pksl,scp,is_sum))->
                               let
                                  pks = F.toList pksl
                                  inlineFK =  fmap (\k -> (\t -> Path (S.singleton k ) (  FKInlineTable $ inlineName t) ) $ keyType k ) .  filter (isInline .keyType ) .  S.toList <$> M.lookup c all
                                  attrMap =  M.fromList $ fmap (\i -> (keyPosition i,i)) $ S.toList $ justError "no attr" $ M.lookup c (all)
                                  attr = S.difference ((\(Just i) -> i) $ M.lookup c all) ((S.fromList $ (maybe [] id $ M.lookup c descMap) )<> S.fromList pks)
                               in (c ,Raw un schema  (justLook c resTT) (M.lookup un transMap) (S.filter (isKDelayed.keyType)  attr) is_sum c (fromMaybe [] (fmap ( fmap (lookupKey .(c,) )  . V.toList) <$> M.lookup c uniqueConstrMap)) (fromMaybe [] (fmap ( fmap (justError "no key" . flip M.lookup  attrMap)  . V.toList) <$> M.lookup c indexMap)) (maybe [] id $ M.lookup un authorization)  (F.toList scp) pks (maybe [] id $ M.lookup  c descMap) (fromMaybe S.empty $ (M.lookup c efks )<>(M.lookup c fks )<> fmap S.fromList inlineFK  ) S.empty attr )) res :: [(Text,Table)]
       let
           unionQ = "select schema_name,table_name,inputs from metadata.table_union where schema_name = ?"

           tableMapPre = HM.singleton schema (HM.fromList i3lnoFun)
           addRefs table = maybe table (\r -> Le.over rawFKSL (S.union (S.map liftFun r)) table) ref
             where ref =  M.lookup (tableName table) functionsRefs
                   liftFun (Path i (FunctionField k s a) ) =  Path (S.map (lookupKey' ts . (tn,) ) i) (FunctionField (lookupKey' ts (tn ,k)) s (liftASch tableMapPre ts tn <$> a))
                   tn = tableName table
                   ts = rawSchema table

           i3l =fmap addRefs <$> i3lnoFun
       ures <- fmap rights $ liftIO $ decodeViews conn schema
       let
           i3 =  addRecInit (HM.singleton schema (HM.fromList i3l ) <> foldr mappend mempty (tableMap <$> F.toList  rsch)) $  HM.fromList i3l
           pks = M.fromList $ fmap (\(_,t)-> (S.fromList$ rawPK t ,t)) $ HM.toList i3
           i2 =    M.filterWithKey (\k _ -> not.S.null $ k )  pks
           -- unionT (s,n,l) = (n ,(\t -> Project t $ Union  ((\t -> justError "no key" $ HM.lookup t i3 )<$>  F.toList l ) ))

           unionT (s,n ,_ ,Select _ _ _) = (n,id)
           unionT (s,n,_,SqlUnion (Select _ (FromRaw _ i) _ )  (Select _ (FromRaw _ j) _) )
             = (n ,(\t -> Project t ( Union ((\t -> justError "no key" $ HM.lookup (T.pack . BS.unpack $ t) i3 )<$>  [i,j] )) ))
       let
           i3u = foldr (uncurry HM.adjust. swap ) i3 (unionT <$> ures)
           i2u = foldr (uncurry M.adjust. swap) i2 (first (\tn -> justError ("no union table" ++ show tn ). fmap (\(_,i,_,_) ->S.fromList $ F.toList i)  $ M.lookup tn (M.fromList res)) . unionT <$> ures)
       sizeMapt <- liftIO$ M.fromList . catMaybes . fmap  (\(t,cs)-> (,cs) <$>  HM.lookup t i3u ) <$> query conn tableSizes (Only schema)

       metaschema <- if (schema /= "metadata")
          then Just <$> keyTables  schemaRef ("metadata",user) authMap pluglist
          else return Nothing

       mvar <- liftIO$ atomically $ newTMVar  M.empty
       let inf = InformationSchema schemaId schema (uid,user) oauth keyMap (M.fromList $ (\k -> (keyFastUnique k ,k))  <$>  F.toList backendkeyMap  )  (M.fromList $ fmap (\i -> (keyFastUnique i,i)) $ F.toList keyMap) (M.filterWithKey (\k v -> not $ L.elem (tableName v )  convert) $ i2u )  i3u sizeMapt mvar  conn metaschema  rsch ops pluglist
           convert = (concat $ fmap (\(_,_,_,n) -> deps  n) ures)
           -- convert = (concat $ fmap (\(_,_,n) -> F.toList n) ures)
           deps (SqlUnion (Select _ (FromRaw _ i) _)  (Select _ (FromRaw _ j) _)) = fmap (T.pack.BS.unpack) [i,j]
           deps (Select _ _ _ ) = []


       liftIO $ print ures
       mapM (createTableRefs inf) (filter (not . isUnion) $ F.toList i2u)
       var <- liftIO$ atomically $ modifyTMVar (globalRef schemaVar  ) (HM.insert schema inf )
       -- addStats inf
         {-
       traverse (\ req -> do
         r <- liftIO$ forkIO $ forever $
           R.runDynamic $ do
             liftIO$ threadDelay $60*10^6
             transaction inf  req
         R.registerDynamic (killThread r)) $ historySync ops
-}

       return inf

isUnion (Project _ (Union _ )) = True
isUnion _ = False

modifyTMVar v  x = takeTMVar  v >>= putTMVar v. x

createTableRefs :: InformationSchema -> Table -> R.Dynamic (Collection Key Showable,DBRef KeyUnique Showable)
createTableRefs inf i = do
  let table = mapTableK keyFastUnique i
  map <- liftIO$ atomically $ readTMVar (mvarMap inf)
  if isJust (M.lookup i map)
     then
     liftIO $ atomically $ do
       let
           ref :: DBRef KeyUnique Showable
           ref =  justError "" $ M.lookup i map
       idx <- readTVar (idxVar ref )
       (_,st) <- readTVar (collectionState ref)
       return (((M.mapKeys (mapPredicate (recoverKey inf)) idx, fmap (mapKey' (recoverKey inf)) st) :: Collection Key Showable),ref)
     else  do
    t <- liftIO$ getCurrentTime
    let
        diffIni :: [TBIdx KeyUnique Showable]
        diffIni = []
    mdiff <-  liftIO$ atomically $ newBroadcastTChan
    chanidx <-  liftIO$ atomically $ newBroadcastTChan
    nchanidx <- liftIO$ atomically $dupTChan chanidx
    nmdiff <- liftIO$ atomically $dupTChan mdiff
    (ivp,vp) <- readTable inf "dump" (schemaName inf) (i)
    let iv = (M.mapKeys (mapPredicate keyFastUnique) ivp)
        v = (mapKey' (keyFastUnique) <$> vp)

    midx <-  liftIO$ atomically$ newTVar iv
    depmap <- liftIO $ atomically $readTMVar (mvarMap inf )
    let
      move (FKJoinTable i j)  =  do
            let rtable = M.lookup (lookSTable inf j) depmap
                rinf = fromMaybe inf $ HM.lookup (fst j) (depschema inf)
            Just . (FKJoinTable i j,)<$> maybe (fmap snd $ createTableRefs rinf (lookSTable inf j)) return rtable
      move (FKInlineTable _) = return Nothing
      move i = return Nothing
      sidx :: [SecondaryIndex KeyUnique Showable]
      sidx = fmap (\un-> (fmap keyFastUnique un ,G.fromList' ( fmap (\(i,n,j) -> ((G.getUnique (fmap keyFastUnique un ) i,[]),n,j)) $ G.getEntries v))   ) (L.delete (rawPK i) $ _rawIndexes i )

    nestedFKS <-  fmap catMaybes $ traverse move $   pathRel <$> F.toList (rawFKS i)
    newNestedFKS <- liftIO . atomically$ traverse (traverse (cloneTChan.patchVar)) nestedFKS
    collectionState <-  liftIO$ atomically $ newTVar  (sidx,v)
    liftIO$ print (tableName table,rawFKS i ,fmap fst (nestedFKS))
    tdeps <- liftIO$ mapM (\(j,var)-> forkIO $ forever $ catchJust notException(do
        atomically (do
            let isPatch (PatchRow _ ) = True
                isPatch _ = False
            ls <- concat . fmap (filter isPatch) <$> takeMany var
            when (not $ L.null $ ls ) $ do
              state <- readTVar collectionState
              let patches = childrenRefsUnique inf table state (j,ls)
              when (not $ L.null $ patches) $
                writeTChan  nmdiff patches
            )
        )  (\e -> atomically (readTChan var) >>= (\d ->  putStrLn $ show (e :: SomeException,d)<>"\n"))
        ) newNestedFKS
    mapM (\i -> R.registerDynamic (killThread i)) tdeps
    t0 <- liftIO$ forkIO $ forever $ catchJust notException(do
        atomically (do
            ls <- takeMany nchanidx
            let conv (v,s,i,t) = M.alter (\j -> fmap ((\(_,l) -> (s,M.insert i t l ))) j  <|> Just (s,M.singleton i t)) v
            modifyTVar' midx (\s -> F.foldl' (flip conv)   s ls)
            )
        )  (\e -> atomically (readTChan nchanidx ) >>= (\d ->  putStrLn $ show (e :: SomeException,d)<>"\n"))
    R.registerDynamic (killThread t0)
    t1 <- liftIO $forkIO $ forever $ catchJust notException (
        atomically $ do
          patches <- takeMany nmdiff
          when (not $ L.null $ concat patches) $
            modifyTVar' collectionState (\e -> L.foldl' (\i j  -> fromJust $ applyTableRep table i j) e (concat patches))
        )  (\e -> atomically ( takeMany nmdiff ) >>= (\d ->  putStrLn $ show (e :: SomeException,d)<>"\n"))
    R.registerDynamic (killThread t1)
    let dbref = (DBRef nmdiff midx nchanidx collectionState )
    liftIO$ atomically $ modifyTMVar (mvarMap inf) (M.insert i  dbref)
    return ((ivp,vp),dbref)

loadFKSDisk inf table = do
  let
    targetTable = lookTable inf (_kvname (fst table))
    items = unKV . snd  $ table
  fks <- fmap catMaybes $ snd $ F.foldl' (\(s,l) i@(Path si _ ) -> (s <> si ,liftA2 (:) (loadFKDisk inf ( table ) s i) l) )  (S.empty , return []) (P.sortBy (P.comparing (RelSort . S.toList . pathRelRel)) $F.toList (rawFKS targetTable))
  let
    fkSet:: S.Set Key
    fkSet =   S.unions . fmap (S.fromList . fmap _relOrigin . (\i -> if all isInlineRel i then i else filterReflexive i ) . S.toList . pathRelRel ) $ filter isReflexive  $ (P.sortBy (P.comparing (RelSort . F.toList . pathRelRel)) $F.toList (rawFKS targetTable))
    fkSet2:: S.Set Key
    fkSet2 =   (S.fromList $ concat $ fmap (fmap _relOrigin .keyattri) $ fks)
    nonFKAttrs :: [(S.Set (Rel Key) ,Column Key Showable)]
    nonFKAttrs =  fmap (fmap unTB) $M.toList $  M.filterWithKey (\i a -> not $ S.isSubsetOf (S.map _relOrigin i) (S.intersection fkSet fkSet2)) items
  return  $ tblist' targetTable (fmap _tb $fmap snd nonFKAttrs <> fks )

loadFKDisk :: InformationSchema -> TBData Key Showable -> S.Set Key -> Path (S.Set Key ) SqlOperation -> R.Dynamic (Maybe (Column Key Showable))
loadFKDisk inf table old (Path ori (FKJoinTable rel (st,tt) ) ) = do
  let
    targetSchema = if schemaName inf == st then   inf else justError "no schema" $ HM.lookup st (depschema inf)
    targetTable = lookTable targetSchema tt

  ((_,mtable ),_) <- createTableRefs targetSchema targetTable
  let
      relSet = S.fromList $ _relOrigin <$> rel
      tb  = unTB <$> F.toList (M.filterWithKey (\k l ->  not . S.null $ S.map _relOrigin  k `S.intersection` relSet)  (unKV . snd . tableNonRef' $ table))
      fkref = joinRel2  (tableMeta targetTable) (fmap (replaceRel rel )tb ) mtable
  case  FKT (kvlist $ _tb <$> filter (not . (`S.member` old) . _tbattrkey ) tb) rel   <$>fkref of
    Nothing ->  return $ if F.any (isKOptional.keyType . _relOrigin) rel
                   then Just $ FKT (kvlist $ _tb <$> filter (not . (`S.member` old) . _tbattrkey ) tb) rel (LeftTB1 Nothing)
                   else Nothing
    i -> return i
loadFKDisk inf table old (Path ori (FKInlineTable to ) ) = do
    v <- runMaybeT $ do
      IT rel vt  <- MaybeT . return $ unTB <$> M.lookup (S.map Inline   ori) (unKV .snd $ table)
      loadVt <- lift $ traverse (loadFKSDisk inf) vt
      return $ IT rel loadVt
    case v of
      Nothing -> return $ if  F.any (isKOptional .keyType) ori
                    then  Just (IT (head $ S.toList ori ) (LeftTB1 Nothing))
                    else  Nothing
      v -> return v

loadFKDisk  _ _ _ _ = return Nothing

-- Search for recursive cycles and tag the tables
addRecInit :: HM.HashMap Text (HM.HashMap Text Table) -> HM.HashMap Text Table -> HM.HashMap Text Table
addRecInit inf m = fmap recOverFKS m
  where
        recOverFKS t  = t Le.& rawFKSL Le.%~ S.map path
          where
                path pini@(Path k rel ) =
                    Path k (case rel of
                      FKInlineTable nt  -> case  L.filter (not .L.null) $ openPath S.empty [] pini of
                              [] -> if snd nt == tableName t then  RecJoin (MutRec []) (FKInlineTable nt) else FKInlineTable nt
                              e -> RecJoin (MutRec e) (FKInlineTable nt)
                      FKJoinTable b nt -> case L.filter (not .L.null) $  openPath S.empty [] pini of
                              [] -> if snd nt == tableName t then  RecJoin (MutRec []) (FKJoinTable  b nt) else FKJoinTable  b nt
                              e -> RecJoin (MutRec e) (FKJoinTable  b nt)
                      i -> i
                      )
                    where
                      openPath ts p pa@(Path _(FKInlineTable nt) )
                        | snd nt == tableName t = [p]
                        | S.member pa ts =  []
                        | otherwise = openTable (S.insert pa ts) p nt
                      openPath ts p pa@(Path _(FKJoinTable  _ nt) )
                        | snd nt == tableName t  = [p]
                        | S.member pa ts =  []
                        | otherwise = openTable (S.insert pa ts)  p nt
                      openPath ts p (Path _ (FunctionField _ _ _)) = []
                      openPath ts p pa = errorWithStackTrace (show (ts,p,pa))
                      openTable t p (st,nt)  =  do
                              let cons pa
                                    | pa == pini = p
                                    | otherwise = p <> [F.toList (pathRelRel (fmap unRecRel pa))]
                              ix <- fmap (\pa-> openPath t ( cons pa ) (fmap unRecRel pa)) fsk
                              return (concat (L.filter (not.L.null) ix))
                        where tb = justError ("no table" <> show (nt,m)) $ join $ HM.lookup nt <$> (HM.lookup st inf)
                              fsk = F.toList $ rawFKS tb




newKey name ty p = do
  un <- newUnique
  return $ Key name Nothing    [FRead,FWrite] p Nothing un ty


catchPluginException :: InformationSchema -> Int -> Int -> [(Key, FTB Showable)] -> IO a -> IO (Either Int (a))
catchPluginException inf pname tname  idx i = do
  (Right <$> i) `catch` (\e  -> do
                t <- getCurrentTime
                print (t,e :: SomeException)
                id  <- query (rootconn inf) "INSERT INTO metadata.plugin_exception (\"user\",\"schema\",\"table\",\"plugin\",exception,data_index2,instant) values(?,?,?,?,?,? :: metadata.key_value[] ,?) returning id" (fst $ username inf , schemaId inf,pname,tname,Binary (B.encode $ show (e :: SomeException)) ,V.fromList (  (fmap (TBRecord2 "metadata.key_value" . second (Binary . B.encode) . first keyValue) idx) ) , t )
                return (Left (unOnly $ head $id)))

logLoadTimeTable
  ::
     InformationSchema
     -> Table -> TBPredicate Key Showable -> String -> IO a -> IO a
logLoadTimeTable inf table pred mode action = do
  -- ini <- getCurrentTime
  a <- action
  -- end <- getCurrentTime
  -- let ltime time =  STimestamp $ utcToLocalTime utc $ time
  -- liftIO $ execute (rootconn inf) "INSERT INTO metadata.stat_load_table(\"user\",\"table\",\"schema\",load,mode) VALUES (?,?,?,?,?)"  (fst $ username inf ,_tableUnique table,  schemaId inf,Interval.interval (Interval.Finite (ltime ini),True) (Interval.Finite (ltime end),True),mode)
  return a



patchNoRef (m,pk,l) =  (m,pk,concat $ attrNoRef <$> l)
  where
    attrNoRef (PFK _ l _ ) = l
    attrNoRef (PInline i l ) = [PInline i $ patchNoRef <$> l]
    attrNoRef i = [i]

logTableModification
  :: (B.Binary a ,Ord a,Patch a,Show a, Ord (Index a),a ~Index a) =>
     InformationSchema
     -> TableModification (RowPatch Key a)  -> IO (TableModification (RowPatch Key a))
logTableModification inf (TableModification Nothing table ip) = do
  let i = patchNoRef $ case ip of
            PatchRow i -> i
            DropRow i -> patch i
            CreateRow i -> patch i
  time <- getCurrentTime
  env <- lookupEnv "ROOT"
  let
    mod = if isJust env then "master_modification_table" else "modification_table"
  let ltime =  utcToLocalTime utc $ time
      (met,G.Idex pidx,pdata) = firstPatch keyValue  i

  [Only id] <- liftIO $ query (rootconn inf) (fromString $ T.unpack $ "INSERT INTO metadata." <> mod <> " (\"user_name\",modification_time,\"table_name\",data_index,modification_data  ,\"schema_name\") VALUES (?,?,?,?::bytea[],? ,?) returning modification_id " ) (snd $ username inf ,ltime,tableName table, V.fromList $ (  fmap  (Binary . B.encode)   pidx ) , Binary  . B.encode $firstPatchRow keyValue ip, schemaName inf)
  let modt = lookTable (meta inf)  mod
  dbref <- prerefTable (meta inf) modt

  putPatch (patchVar dbref) [encodeTableModification inf  ltime (TableModification (Just id) table ip )]
  return (TableModification (Just id) table ip )

decodeTableModification d
  = (schema,table ,\inf ->  TableModification   (Just mod_id)  (lookTable inf table) (liftPatchRow inf table $ datamod mod_data ))
  where
    table = unOnly . att . ix "table_name" $ d
    schema = unOnly . att . ix "schema_name" $ d
    mod_id = unOnly . att .ix "modification_id" $ d
    mod_data :: Only  (Binary (RowPatch Text Showable))
    mod_data = att .ix "modification_data" $ d
    mod_key :: Non.NonEmpty (Binary (FTB Showable))
    mod_key = fmap unOnly . unCompF . att .ix "data_index" $ d
    datamod =  unBinary  . unOnly

unBinary (Binary i) = i

encodeTableModification inf ltime  (TableModification id table ip)
  =CreateRow (liftTable' (meta inf) "modification_table" $ tblist $ _tb <$>  [
                               Attr "user_name"  (txt$ snd $ username inf)
                              ,Attr "modification_time" (timestamp ltime)
                              ,Attr "table_name" (txt$ tableName table)
                              ,Attr "data_index" (ArrayTB1 $ TB1 . encodeS   <$> mod_key)
                              ,Attr "modification_data" (TB1. SBinary . BSL.toStrict . B.encode  $ firstPatchRow keyValue ip)
                              ,Attr "schema_name" (txt $ schemaName inf)
                              ,Attr "modification_id" (maybe (errorWithStackTrace "no id")int id)
                              ])
  where (met,G.Idex pidx,pdata)
          = firstPatch keyValue $ patchNoRef $ case ip of
              PatchRow i -> i
              CreateRow i -> patch i
              DropRow i -> patch i
        --mod_key :: Non.NonEmpty (Binary (FTB Showable))
        mod_key = Non.fromList $ Binary <$> pidx


att :: (Functor f ,DecodeTB1 f , DecodeShowable a ) => TB g k Showable -> f a
att (Attr i j ) = fmap decodeS $ decFTB  j
ix i d = justError ("no field " ++ show i ) $ indexField (IProd Nothing [i]) d

class DecodeTB1 f where
  decFTB :: FTB a -> f a
  encFTB :: f a-> FTB a

instance  DecodeTB1 Only where
  decFTB (TB1 i ) = Only  i
  encFTB (Only i) = TB1  i

infixr 1 :*:
newtype (:*:) f g a = CompFunctor {unCompF :: (f (g a))}deriving(Functor)


instance  DecodeTB1 g => DecodeTB1 (Interval.Interval :*: g)  where
  decFTB (IntervalTB1 i) = CompFunctor $ fmap decFTB i
  encFTB (CompFunctor i) = IntervalTB1 $ fmap encFTB  i

instance  DecodeTB1 g => DecodeTB1 (Non.NonEmpty :*: g)  where
  decFTB (ArrayTB1 i) = CompFunctor $ fmap decFTB i
  encFTB (CompFunctor i) = ArrayTB1 $ fmap encFTB  i

instance  DecodeTB1 g => DecodeTB1 (Maybe :*: g)  where
  decFTB (LeftTB1 i) = CompFunctor $ fmap decFTB i
  encFTB (CompFunctor i) = LeftTB1 $ fmap encFTB  i

class DecodeTable a where
  decodeT :: TBData Text Showable  -> a
  encodeT :: a -> TBData Text Showable


class DecodeShowable a where
  decodeS :: Showable  -> a
  encodeS:: a-> Showable

instance  B.Binary a => DecodeShowable (Binary a) where
  decodeS (SBinary i) = Binary $ B.decode (BSL.fromStrict i)
  encodeS (Binary i) = SBinary ( BSL.toStrict $ B.encode i)


instance  DecodeShowable Int where
  decodeS (SNumeric i) = i
  encodeS i = SNumeric i

instance  DecodeShowable Double where
  decodeS (SDouble i) = i
  encodeS i = SDouble i

instance  DecodeShowable Text where
  decodeS (SText i) = i
  encodeS i = SText i



lookDesc
  :: InformationSchemaKV Key Showable
     -> TableK k
     -> G.GiST (TBIndex Showable) (TBData Key Showable)
     -> T.Text
lookDesc inf j i = maybe (rawName j)  (\(Attr _ (TB1 (SText v)))-> v) row
  where
    pk = [("schema" ,int $ schemaId inf),("table",int (tableUnique j))]
    row = lookupAccess  (meta inf) pk "translation"  ("table_name_translation", i)

tableOrder
  :: Num b =>
     InformationSchemaKV Key Showable
     -> TableK k
     -> G.GiST (TBIndex Showable) (TBData Key Showable)
     -> FTB Showable
tableOrder inf table orderMap =  maybe (int 0) _tbattr row
  where
    pk = [("table",int . tableUnique $ table ), ("schema",int (schemaId inf))]
    row = lookupAccess (meta inf) pk  "usage" ("ordering",orderMap)

lookupAccess inf l f c = join $ fmap (indexField (IProd  notNull [(lookKey inf (fst c) f)] )) . G.lookup (idex inf (fst c) l) $ snd c

idex inf t v = G.Idex $  fmap snd $ L.sortBy (comparing ((`L.elemIndex` (rawPK $ lookTable inf t)).fst)) $ first (lookKey inf t  ) <$> v

dbTable mvar table = do
    mmap <- atomically $readTMVar mvar
    return . justError ("no mvar " <> show table) . M.lookup table $ mmap


mergeCreate (Just i) (Just j) = Just $ mergeTB1 i j
mergeCreate Nothing (Just i) = Just i
mergeCreate (Just i)  Nothing = Just i
mergeCreate Nothing Nothing = Nothing

mergeTB1 ((m,Compose k) ) ((m2,Compose k2) )
  | otherwise = (m,Compose $ liftA2 (\(KV i ) (KV j) -> KV $ M.unionWith const i j ) k k2) -- errorWithStackTrace (show (m,m2))




type Database k v = InformationSchemaKV k v
type DBM k v = ReaderT (Database k v) IO


atTable k = do
  i <- ask
  k <- liftIO$ dbTable (mvarMap i) k
  liftIO $ atomically $ readTVar (collectionState k)

joinRelT ::  [(Rel Key, FTB Showable)] -> Table ->  G.GiST (G.TBIndex Showable) (TBData Key Showable) -> TransactionM ( FTB (TBData Key Showable))
joinRelT ref tb table  = do
  let out = joinRel (tableMeta tb) ref table
  traverse (\i -> tell [TableModification Nothing tb . CreateRow $ i]) out
  return out

addStats schema = do
  let metaschema = meta schema
  varmap <- liftIO$ atomically $ readTMVar ( mvarMap schema)
  let stats = "table_stats"
  (dbpol,(_,polling))<- transactionNoLog metaschema $ selectFrom stats  Nothing Nothing [] mempty
  let
    row t s ls = tblist . fmap _tb $ [Attr "schema" (int (schemaId schema ) ), Attr "table" (int t) , Attr "size" (TB1 (SNumeric s)), Attr "loadedsize" (TB1 (SNumeric ls)) ]
    lrow t dyn st = liftTable' metaschema "table_stats" . row t (maybe (G.size dyn) (maximum .fmap fst ) $  nonEmpty $  F.toList st) $ (G.size dyn)
    lookdiff tb row =  maybe (Just $ patch row ) (\old ->  diff old row ) (G.lookup (G.getIndex row) tb)
  mapM_ (\(m,_)-> do
    var <- refTable schema (m)
    let event = R.filterJust $ lookdiff <$> R.facts (collectionTid dbpol ) R.<@> (flip (lrow (tableUnique $ (m))) <$>  R.facts (idxTid var ) R.<@> R.rumors (collectionTid  var ) )
    R.onEventIO event (\i -> do
      putPatch (patchVar $ iniRef dbpol) . pure  .PatchRow $ i
      )) (M.toList  varmap)
  return  schema




lookPK :: InformationSchema -> (Set Key) -> Table
lookPK inf pk =
      case  M.lookup pk  (pkMap inf) of
           Just table -> table
           i -> errorWithStackTrace (show pk)


writeSchema (schema,schemaVar) = do
  varmap <- atomically $ M.toList <$>  readTMVar (mvarMap schemaVar)
  when (schema == "gmail")  $ do
           print "start dump"
           let sdir = "dump/"<> (fromString $ T.unpack schema)
           hasDir <- doesDirectoryExist sdir
           when (not hasDir ) $  do
             print $"create dir" <> sdir
             createDirectory sdir
           mapM_ (uncurry (writeTable schemaVar sdir ) ) varmap

writeTable :: InformationSchema -> String -> Table -> DBRef KeyUnique Showable -> IO ()
writeTable inf s t v = do
  print ("dumping table " <> s <> " " <> T.unpack ( tableName t))
  let tname = s <> "/" <> (fromString $ T.unpack (tableName t))
  (sidx,iv,_,_) <- atomically $ readState mempty (mapTableK keyFastUnique t) (v)
  (iidx ,_)<- atomically $ readIndex (v)
  let sidx = first (mapPredicate (keyValue.recoverKey inf))  <$> M.toList iidx
      sdata = fmap (mapKey' (keyValue.recoverKey inf).tableNonRef') $ G.toList $ iv
  when (not (L.null sdata) )$
    B.encodeFile  tname (sidx, sdata)

  return ()



liftPredicate inf tname (WherePredicate i ) = WherePredicate $ first (liftAccess inf tname )<$> i

readTable :: InformationSchema -> Text -> Text -> Table -> R.Dynamic (Collection Key Showable)
readTable inf r s t  = do
  let tname = fromString $ T.unpack $ r <> "/" <> s <> "/" <> tableName t
  has <- liftIO$ doesFileExist tname
  (m,prev) <- if has
    then do
      f <- liftIO$ (Right  <$> B.decodeFile tname ) `catch` (\e -> return $ Left ("error decoding" <> tname  <> show  (e :: SomeException )))
      return $  either (const (M.empty ,[])) (\f -> (\(m,g) -> (M.mapKeys (liftPredicate inf (tableName t) ) m  , fmap (liftTable' inf (tableName t) )$ g )) $ (f :: (Map (TBPredicate Text Showable) (Int, Map Int (PageTokenF Showable)),[TBData Text Showable]))) f
    else
      return (M.empty ,[])
  v <- fmap (createUn (rawPK t)) $ traverse (loadFKSDisk inf) prev
  return (m,v)

selectFromTable :: Text
 -> Maybe Int
 -> Maybe Int
 -> [(Key, Order)]
 -> [(Access Text , AccessOp Showable )]
 -> TransactionM
      (DBVar, Collection Key Showable)
selectFromTable t a b c p = do
  inf  <- ask
  selectFrom  t a b c (WherePredicate $ AndColl $ fmap (lookAccess inf t). PrimColl <$> p)

