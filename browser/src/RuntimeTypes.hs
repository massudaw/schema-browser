{-# LANGUAGE TypeOperators,ScopedTypeVariables,FlexibleInstances,FlexibleContexts,DeriveAnyClass,DeriveGeneric,StandaloneDeriving,TypeFamilies,OverloadedStrings,TemplateHaskell,DeriveTraversable,DeriveFoldable,DeriveFunctor,RankNTypes,ExistentialQuantification #-}
module RuntimeTypes where

import Types
import Types.Index as G
import Data.Ord
import Data.Tuple (swap)
import Data.Time
import Control.Concurrent (ThreadId)
import Types.Patch
import Text
import qualified Data.Functor.Contravariant as C
import Debug.Trace
import qualified Data.IntMap as IM
import Control.Exception
import qualified Data.Map.Lazy.Merge as M
import Postgresql.Types
import Query
import Data.Functor.Constant
import Data.Interval(Interval)
import qualified Data.Interval as Interval
import Control.Applicative.Lift
import GHC.Generics
import Data.Maybe
import Control.DeepSeq
import Data.Binary
import Control.Concurrent.STM.TVar
import Control.Concurrent.STM
import Control.Monad.RWS
import qualified NonEmpty as Non
import qualified Data.Sequence.NonEmpty as NonS
import Utils
import qualified Data.Text as T

import qualified Data.List as L
import Control.Arrow
import Data.Text (Text)
import Control.Applicative

import qualified Reactive.Threepenny as R
import Database.PostgreSQL.Simple hiding (Binary)
import Data.Functor.Identity
import Data.Map (Map)
import qualified Control.Lens as Le
import qualified Data.Map as M
import qualified Data.HashMap.Strict as HM
import qualified Data.Set as S
import Data.Set (Set)
import Control.Monad.Reader
import qualified Data.Foldable as F
import Control.Lens.TH


metaInf :: TVar DatabaseSchema -> IO InformationSchema
metaInf smvar = indexSchema smvar "metadata"

indexSchema :: TVar DatabaseSchema -> Text -> IO InformationSchema
indexSchema smvar text = (\m -> justError ("no schema: "  ++ show text ++ " from: " ++ show (HM.keys m)). HM.lookup text $ m)<$> liftIO ( atomically $ readTVar .globalRef  =<< readTVar  smvar )


type InformationSchema = InformationSchemaKV Key Showable

type UserTable = (Int,Text)

data TidingsAffine  a = TA (R.Behavior a) (R.Event [Index a])

data DatabaseSchema
  = DatabaseSchema
    { schemaIdMap :: M.Map Int Text
    , isRoot :: Bool
    , schemaNameMap  :: HM.HashMap Text Int
    , schemaConn :: Connection
    , globalRef :: TVar (HM.HashMap Text InformationSchema )
    }


data SchemaProperties
  = SchemaProperties
  { schId :: Int
  , schName :: Text
  , schColor:: Maybe Text
  }

data User
 = User
 { userId :: Int
 , userName :: Text
 }deriving(Eq,Show)

schemaId = schId . schemaProperties
schemaName = schName. schemaProperties
schemaColor = schColor . schemaProperties

username = userName .client . loggedUser
usernameId = userId . client . loggedUser

data AuthCookie a
  = AuthCookie
  { client :: a
  , cookie :: Int
  , creation_date :: UTCTime
  } deriving(Eq,Show,Functor,Foldable,Traversable)

data InformationSchemaKV k v
  = InformationSchema
  -- Pure schema properties
  { schemaProperties :: SchemaProperties
  -- User that created the schema and auth state
  , loggedUser :: AuthCookie User
  -- Key by name and table
  , _keyMapL :: HM.HashMap (Text,Text) k
  -- Mapping from keys to backend key
  , _backendKey :: Map KeyUnique PGKey
  -- Full Key from unique id
  , _tableMapL :: HM.HashMap Text Table
  -- Cache storage DB references
  , mvarMap :: TVar (Map (KVMetadata k) (DBRef Key v ))
  -- Backend state
  , rootconn :: Connection
  -- Imported schema information
  , metaschema :: Maybe (InformationSchemaKV k v)
  , depschema :: HM.HashMap Text (InformationSchemaKV k v)
  -- Backend Operations
  , schemaOps :: SchemaEditor
  -- Global database references
  , rootRef :: TVar DatabaseSchema
  }

instance Eq InformationSchema where
  i == j = schemaId i == schemaId j

instance Ord InformationSchema where
  compare i j = compare (schemaId i) (schemaId j)

recurseLookup :: (k -> InformationSchema -> Maybe b) -> InformationSchema -> k -> Maybe b
recurseLookup l inf un = l un  inf <|> F.foldl' (<|>) Nothing (flip (recurseLookup l) un <$> F.toList (depschema inf))
backendsKey = recurseLookup (\un inf -> M.lookup un (_backendKey inf))

conn  = rootconn

data BrowserState
  = BrowserState
  {host :: String
  ,port :: String
  ,dbn :: String
  ,user :: String
  ,pass :: String
  ,schema :: Maybe String
  ,tablename :: Maybe String
  ,rowpk :: Maybe (Non.NonEmpty (Text,Text))
  }

type TBF  k v = (KVMetadata k ,KV k v)

instance Show (InformationSchemaKV k v ) where
  show i = show $ schemaName i

tableMap :: InformationSchema -> HM.HashMap Text (HM.HashMap Text Table)
tableMap s = HM.singleton (schemaName s) (_tableMapL s ) <> F.foldl' mappend mempty (fmap (tableMap . snd) (HM.toList $ depschema s))

keyMap = _keyMapL

data DBRef k v =
  DBRef  { dbRefTable :: TableK k
         , refIndex :: Int
         , refSize :: TVar Int
         --- TODO:  it would be good to support a Channel type that allows filtering on broadcast
         --  For example to restrict propagation on for updates on that chan. Filtering on source instead of destination
         , patchVar :: TChan [TableModificationU k v]
         , idxVar :: TVar (IndexMetadata k v)
         , idxChan :: TChan (IndexMetadataPatch k v)
         , collectionState  :: TVar (TableRep k v)
         , threadIds :: [ThreadId]
         , dblogger  :: TEvent String
         }

type TEvent a = (TVar [a] , TChan a)

meta inf = fromMaybe inf (metaschema inf)

data DBVar2 v =
  DBVar2
  { iniRef :: DBRef Key v
  , idxTid :: R.Tidings (IndexMetadata Key v)
  , collectionTid :: R.Tidings (TableRep Key Showable )
  }

type IndexMetadataPatch k v = (WherePredicateK k, Int, Int, KV k (),PageTokenF v)

type TableIndex k v = GiST (TBIndex v) (TBData k v)
type SecondaryIndex k v = GiST (TBIndex v) (M.Map (TBIndex v) [AttributePath k ()])

instance (Show k ,Show v) => Patch (InformationSchemaKV  k v )  where
  type Index (InformationSchemaKV k v) = [TableModificationU k v]

type RefTables = ( R.Tidings (IndexMetadata CoreKey Showable)
                 , R.Tidings (TableRep CoreKey Showable)
                 , TChan [TableModificationU Key Showable] )

type PKConstraint = C.Predicate [Column CoreKey Showable]

type TBConstraint = C.Predicate (TBData CoreKey Showable)

type SelPKConstraint = [([Rel Key],R.Tidings PKConstraint)]

type SelTBConstraint = [([Rel Key],R.Tidings TBConstraint)]

type PluginRef a = [(Union (Access Key), R.Tidings (Editor (Index a)))]

currentState db = R.currentValue (R.facts $ collectionTid db)
currentIndex db = R.currentValue (R.facts $ idxTid db)

instance (NFData k,  PatchConstr k Showable) => Patch (TableRep k Showable) where
  type Index (TableRep k Showable) = RowPatch k Showable
  applyUndo = applyTableRep

instance (Ord k , Show k , Show v) => Patch (IndexMetadata k v) where
  type Index (IndexMetadata k v) =  [IndexMetadataPatch k v]
  applyUndo i =Right . (,[]). F.foldl' vapply i
    where vapply (IndexMetadata m) (v,s,i,p,t) = IndexMetadata $ M.alter (\j -> fmap ((\(_,l) -> (s,M.insert i (p,t) l ))) j  <|> Just (s,M.singleton i (p,t))) v m

instance (Show v, Show k ,Ord k ,Compact v) => Compact (TableModificationK k  v) where
  compact i = foldCompact assoc i
    where
      assoc (BatchedAsyncTableModification k l)  d@(AsyncTableModification _ _)
        = case assoc (last l) d of
            Just (BatchedAsyncTableModification _ i)-> Just $ BatchedAsyncTableModification k (init l <> i)
            Just i@(AsyncTableModification _ _)-> Just $ BatchedAsyncTableModification k (init l <> [i])
            Nothing -> Just $ BatchedAsyncTableModification k (l <> [d])
      assoc a@(AsyncTableModification o d ) b@(AsyncTableModification o2 d2 )
          = if L.length new  == 1
            then Just (head new)
            else Just (BatchedAsyncTableModification  o [a,b])
        where new = AsyncTableModification o <$> compact [d ,d2]
      assoc (FetchData o d ) (FetchData o2 d2)
          = if L.length new  == 1
            then Just (head new)
            else Nothing
        where new = FetchData o <$> compact [d ,d2]
      assoc (AsyncTableModification o d ) j  = Nothing
      assoc i j = Nothing

instance Compact (IndexMetadataPatch k v) where
  compact i = i

mapRowPatch f (RowPatch i ) = RowPatch $ Le.bimap (fmap f) (fmap f) i

applyGiSTChange ::
     (NFData k, NFData a, G.Predicates (TBIndex a), PatchConstr k a)
  => (KVMetadata k,G.GiST (TBIndex a) (TBData k a))
  -> RowPatch k (Index a)
  -> Either String ((KVMetadata k,G.GiST (TBIndex a) (TBData k a)),RowPatch k (Index a))
applyGiSTChange (m,l) (RowPatch (patom,DropRow))=
  maybe (Right $ ((m,l),RowPatch (patom,DropRow))) Right $
    ((m,G.delete (create <$> patom) G.indexParam l) ,) . mapRowPatch patch . createRow' m <$> G.lookup (create <$> patom) l
applyGiSTChange (m,l) (RowPatch (ipa,PatchRow  patom)) =
  first (m,) <$>case  flip G.lookup l =<< (G.notOptionalM i)  of
    Just v -> do
      (el ,u) <- applyUndo v patom
      return  (case G.notOptionalM (G.getIndex m el) of
          Just pk ->  (if G.notOptionalM i == Just pk
            then G.update (G.notOptional i) (flip apply patom)
            else G.insert (el, G.tbpred m el) G.indexParam .
                 G.delete (G.notOptional i) G.indexParam) l
          Nothing -> G.update (G.notOptional i) (flip apply patom) l, RowPatch (ipa,PatchRow u))
    Nothing -> do
      el <-maybe (Left $ "cant create row" ++ show patom) Right $ createIfChange patom
      return $ (G.insert (el, i ) G.indexParam l,RowPatch (ipa,DropRow ))
  where
    i = fmap create ipa
applyGiSTChange (m,l) p@(RowPatch (idx,CreateRow elp)) =
  maybe (Right ((m,l),p)) Right $
    first (m,) <$> case G.lookup ix  l of
      Just v -> Just (G.update  ix (maybe id (flip apply ) (diff v el)) l,RowPatch (idx,DropRow ))
      Nothing -> Just (G.insert (el, ix) G.indexParam l,RowPatch (idx,DropRow ))
    where
      el = fmap create elp
      ix = create <$> idx

getIndexWithTrace 
  :: (Show k, Show a,Ord k)
  =>  Rel k
  -> TBData k a
  -> [(Union (AttributePath k ()),TBIndex a)]
getIndexWithTrace un row = maybeToList $ do
    list <- nonEmpty (lookupRel un) 
    let (attrs, values) = unzip list
    return (Many attrs, foldr1 merge values)
  where
    merge (Idex i) (Idex j )=  Idex (i <> j)
    isRel (Rel _ _ _ ) = True
    isRel _ = False
    lookupRel l@(RelComposite v ) 
      | L.any isRel v = [(PathForeign v (TipPath (Many $ (\i -> (PathAttr (_relOrigin i) (TipPath ())) ) <$> v )), Idex . fmap _tbattr . unkvlist . justError ("No rel " ++ show (l,row)) $ _tbref  <$> kvLookup l row )]
      | otherwise = concat $ lookupRel <$>  v
    lookupRel r@(Rel (Inline i) j k) = [(PathForeign [r] (TipPath (Many $ pure (PathAttr i (TipPath ())))), Idex . fmap _tbattr . unkvlist .justError ("No rel " ++ show (r,row)) $  _tbref <$> kvLookup r row)]
    lookupRel (RelAccess i j ) = fmap (first (PathInline (_relOrigin i)))   $ ftbToPathIndex $  getIndexWithTrace j <$> justError ("cant find: " ++ show (i,row)) (refLookup  i row)
    lookupRel i@(Inline k ) = [(PathAttr k $ TipPath (),Idex . pure . justError "No attribute path" $ _tbattr <$> kvLookup i row)]
    unIndex (Idex v ) = v

ftbToPathIndex (ArrayTB1 l) = join $ F.toList $ NonS.imap (\ix v -> first (NestedPath (PIdIdx ix)) <$> ftbToPathIndex  v) l 
ftbToPathIndex (LeftTB1 l) = join $ F.toList $ (\v -> first (NestedPath PIdOpt) <$> ftbToPathIndex  v) <$> l 
ftbToPathIndex (TB1 l) = first TipPath <$> l


traverseGetIndex :: [(Union (AttributePath k ()),TBIndex a)] -> [((AttributePath k ()),TBIndex a)]
traverseGetIndex = concat . fmap (fmap swap . traverse unMany .swap)
  where 
    unMany (Many l) = l

applySecondary
  ::  (NFData k,NFData a,G.Predicates (TBIndex a) , a ~ Index a, PatchConstr k a)  =>  RowPatch k (Index a)-> RowPatch k (Index a) -> TableRep k a -> TableRep k a
applySecondary (RowPatch (patom,DropRow )) (RowPatch (_,CreateRow v)) (TableRep (m,sidxs,l))
  = TableRep (m,M.mapWithKey didxs sidxs,l)
  where
    didxs un sidx = G.delete (fmap create $ G.getUnique  un v) G.indexParam sidx
applySecondary (RowPatch (ix,CreateRow elp)) _  (TableRep (m,sidxs,l)) =  TableRep (m, out ,l)
  where
    out = M.mapWithKey didxs sidxs
    didxs un sidx =  alterAttrs el 
      where
        alterAttrs = F.foldl' reducer sidx .traverseGetIndex . getIndexWithTrace (relComp un)
        reducer idx (ref ,u) = G.alterWith (M.insertWith  mappend ix [ref].fromMaybe M.empty) u idx
    el = fmap create elp
applySecondary n@(RowPatch (ix,PatchRow elp)) d@(RowPatch (ixn,PatchRow elpn))  (TableRep (m,sidxs,l)) =  TableRep (m, M.mapWithKey didxs sidxs,l)
  where
    didxs un sidx = F.foldl' reducer sidx . traverseGetIndex . getIndexWithTrace (relComp un) $ el
      where 
        reducer sidx  (ref,u)  = G.alterWith (M.insertWith  mappend ix [ref] . fromMaybe M.empty) u $ G.delete (G.getUnique  un eln) G.indexParam sidx
    el = justError "cant find"$ G.lookup ix l
    eln = apply el elpn
applySecondary _ _ j = j

applyTableRep
  ::  (NFData k,  PatchConstr k Showable)
  => TableRep k Showable
  -> RowPatch k Showable
  -> Either String (TableRep k Showable,RowPatch k Showable)
applyTableRep rep (BatchPatch rows op) = fmap (head . compact.reverse ) <$> F.foldl' (\i j -> (\(v,l) -> fmap (fmap (:l)) $  applyTableRep v j) =<< i ) (Right (rep,[]))  (RowPatch . (,op)  <$>rows)
applyTableRep (TableRep (m,sidxs,l)) p = do
  ((m,g),u)<- applyGiSTChange (m,l) p
  return (applySecondary p u (TableRep (m,sidxs, g)), u)


typecheck f a = case f a of
          Pure i -> Right a
          Other (Constant l) ->  Left l

queryCheckSecond :: (Show k,Ord k) => (WherePredicateK k ,[Rel k]) -> TableRep k Showable-> G.GiST (TBIndex  Showable) (TBData k Showable)
queryCheckSecond pred@(b@(WherePredicate bool) ,pk) (TableRep (m,s,g)) = t1
  where t1 = G.fromList' . maybe id (\pred -> L.filter (flip checkPred pred . leafValue)) notPK  $ fromMaybe (getEntries  g)  (searchPK  b (pk,g)<|>  searchSIdx)
        searchSIdx = (\sset -> L.filter ((`S.member` sset) .leafPred) $ getEntries g)  <$> mergeSIdxs
        notPK = WherePredicate <$> F.foldl' (\l i -> flip G.splitIndexPKB  i =<< l ) (Just bool) (pk : M.keys s )
        mergeSIdxs :: Maybe (S.Set (TBIndex Showable))
        mergeSIdxs = L.foldl1' S.intersection <$> nonEmpty (catMaybes $ fmap (S.unions . fmap (M.keysSet.leafValue)). searchPK b <$> M.toList s)


searchPK ::  (Show k,Ord k) => WherePredicateK k -> ([Rel k],G.GiST (TBIndex  Showable) a ) -> Maybe [LeafEntry (TBIndex  Showable) a]
searchPK (WherePredicate b) (pk, g)= (\p ->  G.projectIndex pk  (WherePredicate p) g) <$>  splitIndexPK b pk


type DBVar = DBVar2 Showable
type Collection k v = (IndexMetadata k v ,GiST (TBIndex v ) (TBData k v))

pluginStatic = pluginStatic' . _plugAction
pluginAction = pluginAction' . _plugAction

pluginActionDiff :: FPlugins -> TBData Text Showable -> IO (Maybe (TBIdx Text Showable))
pluginActionDiff = pluginActionDiff' . _plugAction


pluginRun b@(IOPlugin _) = Right (pluginAction' b)
pluginRun b@(PurePlugin _ ) = Right (pluginAction' b)
pluginRun b@(DiffIOPlugin _ ) = Left (pluginActionDiff' b)
pluginRun b@(DiffPurePlugin _ ) = Left (pluginActionDiff' b)

pluginActionDiff' (DiffIOPlugin a ) = dynIO a
pluginActionDiff' (DiffPurePlugin a ) = return . dynPure a
pluginAction' (IOPlugin   a ) = dynIO a
pluginAction' (PurePlugin  a) = return . dynPure a

checkPredFull inf t predi i
  =  result
  where
    result = if maybe False (G.checkPred i) pred then Just i else Nothing
    pred = predGen (liftAccessU inf t predi)
    predGen inp =  WherePredicate . fmap fixrel <$> conv
      where conv = genPredicateFullU True inp


dynIO url inp =
    runReaderT (dynPK url ()) inp

dynPure url inp = runIdentity $
    dynIO url inp

dynP ~(P s d) = d

dynPK =  runKleisli . dynP

staticP (P i _ ) = i
pluginStatic' (IOPlugin  a) = staticP a
pluginStatic' (DiffIOPlugin a) = staticP a
pluginStatic' (DiffPurePlugin a) = staticP a
pluginStatic' (PurePlugin  a) = staticP a
pluginStatic' (StatefullPlugin [(_,a)]) = pluginStatic' a


pathRelInputs inf table (PluginField (_,FPlugins _ _ a)) 
  = S.fromList  ((concat $ genRel M.empty . liftAccess inf table <$> F.toList (fst $ pluginStatic' a)) <> (concat . fmap (fmap Output .relAccesGen') . fmap ( liftAccess inf table) . L.filter (isJust. filterEmpty)  $ F.toList (snd $ pluginStatic' a)))
pathRelInputs _ _ i = pathRelRel i

genRel :: Ord k => Map Int (Union (Access k)) -> Access k -> [Rel k]
genRel s (Rec ix j) = concat $ genRel (M.insert ix j s) <$> F.toList j
genRel s (Nested i j) = concat $ fmap (RelAccess (relComp i)) . genRel s <$> F.toList j
genRel s (IProd _ i) = [RelAccess (Inline i) (Inline i) ]
genRel s (Point ix) = concat $ genRel (M.delete ix s) <$> maybe [] F.toList (M.lookup ix s)



localInf :: (InformationSchema -> InformationSchema ) -> TransactionM a -> TransactionM a
localInf f = local (first f)

askInf :: TransactionM InformationSchema
askInf = fmap fst ask

type TableModificationU k u= TableModificationK (TableK k) (RowPatch k u )

type (|->) a b = IsoArrow  a b
data IsoArrow a b = IsoArrow { lowerA :: ( a -> b)  , buildA :: (b -> a )}

type TransactionM = RWST (InformationSchema,[TableModification (RowPatch Key Showable)]) () (M.Map (KVMetadata Key) (DBRef Key Showable,[TableModification (RowPatch Key Showable)],[IndexMetadataPatch Key Showable])) R.Dynamic


type PageToken = PageTokenF Showable

deriving instance (Binary v) => Binary (PageTokenF  v)
deriving instance (NFData v) => NFData (PageTokenF  v)

newtype IndexMetadata k v =  IndexMetadata {unIndexMetadata :: (Map (WherePredicateK k) (Int,Map Int (KV k (),PageTokenF v)))} deriving(Show)

newtype TableRep k v = TableRep (KVMetadata k, M.Map [Rel k] (SecondaryIndex k v), TableIndex k v) deriving(Show)

newtype PageTokenF v
  = TableRef (Interval (TBIndex v))
  deriving(Eq,Ord,Show,Generic)

data TBOperation a
  = TBInsert a
  | TBUpdate a a
  | TBNoop a
  deriving(Functor)

data OverloadedRule
  =  CreateRule  (TBData Key Showable -> TransactionM (RowPatch Key Showable))
  |  DropRule  (TBData Key Showable -> TransactionM (RowPatch Key Showable))
  |  UpdateRule  (TBData Key Showable -> TBIdx Key Showable -> TransactionM (RowPatch Key Showable))

data SchemaEditor
  = SchemaEditor
  { patchEd :: KVMetadata Key -> [TBIndex Showable] -> TBIdx Key Showable -> TransactionM (RowPatch Key Showable)
  , insertEd :: KVMetadata Key -> TBData Key Showable ->TransactionM (RowPatch Key Showable)
  , deleteEd :: KVMetadata Key ->TBData Key Showable ->TransactionM (RowPatch Key Showable)
  , batchedEd :: KVMetadata Key -> [RowPatch Key Showable] -> TransactionM [RowPatch Key Showable]
  , listEd :: KVMetadata Key -> TBData Key () -> Maybe Int -> Maybe PageToken -> Maybe Int -> [(Rel Key,Order)] -> WherePredicate -> TransactionM ([TBData Key Showable],PageToken,Int)
  , getEd :: Table -> TBData Key () -> TBIndex Showable -> TransactionM (TBIdx Key Showable)
  , typeTransform :: PGKey -> CoreKey
  , logger :: forall m . MonadIO m => InformationSchema -> TableModification (RowPatch Key Showable)  -> m (TableModification (RowPatch Key Showable))
  , undo :: forall m . MonadIO m => InformationSchema -> RevertModification Table (RowPatch Key Showable)  -> m ()
  , opsPageSize :: Int
  , transactionEd :: InformationSchema -> (forall a  . IO a -> IO a)
  , rules :: M.Map (Text,Text) [(TBData Text Showable -> Bool ,OverloadedRule)]
  }

typeTrans inf = typeTransform (schemaOps inf)

allFields inf = allRec' (tableMap inf)

argsToState  [h,ph,d,u,p,s,m,t,o] = BrowserState h ph d  u p (Just s) (Just t ) (Just ( Non.fromList . fmap (fmap (T.drop 1) . T.break (=='=') )$ T.split (==',') (T.pack o)))
argsToState  [h,ph,d,u,p,s,m,t] = BrowserState h ph d  u p (Just s) (Just t ) Nothing
argsToState  [h,ph,d,u,p,s,m] = BrowserState h ph d  u p  (Just s)  Nothing Nothing
argsToState  [h,ph,d,u,p,s] = BrowserState h ph d  u p  (Just s)  Nothing Nothing
argsToState  [h,ph,d,u,p] = BrowserState h ph d  u p Nothing Nothing Nothing
argsToState i = error (show i)

lookMeta :: InformationSchema -> Text -> KVMetadata Key
lookMeta inf = tableMeta. lookTable inf

lookSMeta :: InformationSchema -> Prim KPrim (Text,Text) -> KVMetadata Key
lookSMeta inf (RecordPrim r ) = tableMeta$ lookSTable inf r

lookTable :: InformationSchema -> Text -> Table
lookTable inf t = justError ("no table: " <> T.unpack t  <> " - " <> show (schName $ schemaProperties inf  )) $ HM.lookup t (_tableMapL inf)

lookTableM :: InformationSchema -> Text -> Maybe Table
lookTableM inf t =  HM.lookup t (_tableMapL inf)

lookSTable :: InformationSchema -> (Text,Text) -> Table
lookSTable inf (s,t) = justError ("no table: " <> T.unpack t) $ join $ HM.lookup t <$> HM.lookup s (tableMap inf)

lookKey :: InformationSchema -> Text -> Text -> Key
lookKey inf t k = justError ("table " <> T.unpack t <> " has no key " <> T.unpack k  <> show (HM.toList (keyMap inf))) $ HM.lookup (t,k) (keyMap inf)

lookKeyM :: InformationSchema -> Text -> Text -> Maybe Key
lookKeyM inf t k =  HM.lookup (t,k) (keyMap inf)

fetchData i = liftIO . atomically .writeTChan (patchVar i) . fmap (FetchData (dbRefTable i) .force )

putPatch m = liftIO. atomically . putPatchSTM m

mapModification :: (Ord b,Ord a,Ord c ,Ord (Index c))=> (a -> b) ->  TableModificationK (TableK a) (RowPatch a c) -> TableModificationK (TableK b )(RowPatch b c)
mapModification f (TableModification a b c d e ) = TableModification a b c (fmap f d) (firstPatchRow f e)
mapModification f (AsyncTableModification d e ) = AsyncTableModification  (fmap f d) (firstPatchRow f e)
mapModification f (BatchedAsyncTableModification  d e ) = BatchedAsyncTableModification (fmap f d) (mapModification f <$> e)
mapModification f (FetchData d e) = FetchData (fmap f d) (firstPatchRow f e)

putPatchSTM m =  writeTChan m -- . force
putIdx m = liftIO .atomically . putIdxSTM m
putIdxSTM m =  writeTChan m  . force

typeCheckValuePrim f (KOptional :i) (LeftTB1 j) = maybe (Pure ()) (typeCheckValuePrim f i) j
typeCheckValuePrim f (KSerial :i) (LeftTB1 j) = maybe (Pure ()) (typeCheckValuePrim f i) j
typeCheckValuePrim f (KArray :i )  (ArrayTB1 l) = F.foldl' (liftA2 const ) (Pure () ) (typeCheckValuePrim f i<$>  l)
typeCheckValuePrim f (KInterval : i) (IntervalTB1 j) = const <$> maybe (Pure ()) (typeCheckValuePrim f i)  (unFin $ Interval.lowerBound j)  <*> maybe (Pure ()) (typeCheckValuePrim f i) (unFin $ Interval.upperBound j)
typeCheckValuePrim f []  (TB1 j) = f j
typeCheckValuePrim f i j = failure ["cant match " ++ show i ++ " with " ++ show j ]

typeCheckValue f (Primitive l i)  j = mapError (fmap (("At " ++ show l ++ " : " ++ show i ++ "\n"++ show j )++)) $ typeCheckValuePrim (f i) l j

typeCheckPrim (PInt j) (SNumeric i) = Pure ()
typeCheckPrim PDouble (SDouble i) = Pure ()
typeCheckPrim PText (SText i) =  Pure ()
typeCheckPrim (PTime _)(STime i) =  Pure ()
typeCheckPrim PColor (SText i) = Pure ()
typeCheckPrim (PDimensional _ _ ) (SDouble i) = Pure ()
typeCheckPrim PCnpj (SText i) = Pure ()
typeCheckPrim PCpf (SText i) = Pure ()
typeCheckPrim (PGeom _ _ ) (SGeo i) = Pure ()
typeCheckPrim PBoolean (SBoolean i) = Pure ()
typeCheckPrim (PMime _ ) (SBinary i ) = Pure ()
typeCheckPrim (PMime "text/json" ) (SJSON i ) = Pure ()
typeCheckPrim PBinary  (SBinary i ) = Pure ()
typeCheckPrim (PDimensional _ _ ) (SDouble i ) = Pure ()
typeCheckPrim PAddress  (SText i) = Pure ()
typeCheckPrim i j  = failure ["cant match " ++ show i ++ " with " ++ show j ]

typeCheckTB (Fun k ref i) = typeCheckValue (\(AtomicPrim l )-> typeCheckPrim l) (keyType k ) i
typeCheckTB (Attr k i ) = typeCheckValue (\(AtomicPrim l )-> typeCheckPrim l) (keyType k ) i
typeCheckTB (IT k i ) = typeCheckValue (\(RecordPrim l) -> typeCheckTable l ) (keyType k)  i
typeCheckTB (FKT k rel2 i ) = const <$> F.foldl' (liftA2 const ) (Pure () ) (typeCheckTB <$>  unkvlist k) <*> mapError (fmap ((show (keyType ._relOrigin <$> rel2)) ++)) (typeCheckValue (\(RecordPrim l) -> typeCheckTable l )  ktype i)
  where
    ktypeRel = mergeFKRef (keyType ._relOrigin <$> rel2)
    ktype :: KType (Prim KPrim (Text,Text))
    ktype = const (RecordPrim  ("","")) <$> ktypeRel


mapError :: (a -> a) -> Errors a b -> Errors a b
mapError f (Other (Constant i)) = Other (Constant (f i))
mapError f (Pure i) = Pure i




typeCheckTable ::  (Text,Text) -> TBData (FKey (KType (Prim KPrim (Text,Text)))) Showable -> Errors [String] ()
typeCheckTable c  l
  =  F.foldl' (liftA2 const ) (Pure () ) (typeCheckTB <$> unkvlist l)

type LookupKey k = (InformationSchema -> Text -> k -> Key, Key -> k)
lookupKeyName = (lookKey ,keyValue)


liftTableF ::  (Show k ,Show a,Ord k) => LookupKey k -> InformationSchema ->  Text -> TBData k a -> TBData Key a
liftTableF f inf  tname i  =  kvlist $ liftFieldF  f inf  tname <$> unkvlist i
  where
    ta = lookTable inf tname


liftTable' :: Show a => InformationSchema -> Text -> TBData Text a -> TBData Key a
liftTable' = liftTableF lookupKeyName


findRefTableKey
  :: (Show t, Ord t) => TableK t -> [Rel t] -> (T.Text, T.Text)
findRefTableKey ta rel =  tname2
  where   (FKJoinTable  _ tname2 )  = unRecRel $ justError ("no fk ref1" <> show (rel ,rawFKS ta)) $ L.find (\r->  pathRelRel r == S.fromList rel)  (F.toList $ rawFKS  ta)


findRefTable inf tname rel =  tname2
  where   (FKJoinTable  _ (_,tname2) )  = unRecRel $ justError ("no fk ref2" <> show (rel ,rawFKS ta)) $ L.find (\r->  S.map (fmap keyValue ) (pathRelRel r) == S.fromList (_relOrigin <$> rel))  (F.toList$ rawFKS  ta)
          ta = lookTable inf tname

liftFieldF :: (Show k ,Show a,Ord k) => LookupKey k -> InformationSchema -> Text -> Column k a -> Column Key a
liftFieldF (f,p) inf tname (Attr t v) = Attr (f inf tname t) v
liftFieldF (f,p) inf tname (FKT ref  rel2 tb) = FKT (mapBothKV (f inf tname ) (liftFieldF (f,p) inf tname) ref)   rel (liftTableF (f,p) rinf tname2 <$> tb)
  where FKJoinTable  rel (schname,tname2)  = unRecRel $ justError ("no fk ref3" <> show (tname,ref,rel2 ,pathRelRel <$> rawFKS ta)) $ L.find (\r-> S.map (fmap p) (pathRelRel r)  == S.fromList  rel2)  (rawFKS  ta)
        rinf = fromMaybe inf (HM.lookup schname (depschema inf))
        ta = lookTable inf tname
liftFieldF (f,p) inf tname (IT rel tb) = IT (f inf tname  rel) (liftTableF (f,p) inf tname2 <$> tb)
  where FKInlineTable _ (_,tname2)  = unRecRel $ justError ("no fk ref4" <>show (rel ,rawFKS ta)) $ L.find (\r->  S.map (fmap p) (pathRelRel r) == S.singleton (Inline rel))  (F.toList$ rawFKS  ta)
        ta = lookTable inf tname
liftFieldF (f,p) inf tname (Fun  k t v) = Fun (f inf tname k ) (fmap(fmap (f inf tname) )<$> t) v



liftField :: Show a=> InformationSchema -> Text -> Column Text a -> Column Key a
liftField = liftFieldF lookupKeyName

liftRowPatch inf t (RowPatch i) = RowPatch$  liftPatchRow inf t i
liftPatchRow inf t (k,PatchRow i) = (k,PatchRow $ liftPatch inf t i)
liftPatchRow inf t (ix,CreateRow i) = (ix,CreateRow $ liftTable' inf t i)
liftPatchRow inf t (ix,DropRow ) = (ix,DropRow   )

liftPatch :: a ~ Index a => InformationSchema -> Text -> TBIdx Text a -> TBIdx Key a
liftPatch inf t  p =  fmap (liftPatchAttr inf t) p


liftPatchAttr :: a ~ Index a => InformationSchema -> Text -> PathAttr Text a -> Index (Column Key a)
liftPatchAttr inf t p@(PAttr k v ) =  PAttr (lookKey inf t k)  v
liftPatchAttr inf tname p@(PInline rel e ) =  PInline ( lookKey inf tname rel) (liftPatch inf tname2 <$>  e)
  where
    FKInlineTable _ (_,tname2) = justError"cannot lift patch" $ unRecRel <$> L.find (\r->  S.map (fmap keyValue ) (pathRelRel r) == S.singleton (Inline rel) )  (F.toList$ rawFKS  ta)
    ta = lookTable inf tname
liftPatchAttr inf tname p@(PFK rel2 pa  b ) =  PFK rel (fmap (liftPatchAttr inf tname) pa)  (liftPatch rinf tname2 Control.Applicative.<$> b)
  where
    FKJoinTable  rel (schname,tname2)  = unRecRel $ justError (show ("liftPatchAttr",rel2 ,rawFKS ta)) $ L.find (\r->  S.map (keyValue ._relOrigin ) (pathRelRel r) == S.fromList (_relOrigin <$> rel2))  (F.toList$ rawFKS  ta)
    ta = lookTable inf tname
    rinf = fromMaybe inf (HM.lookup schname (depschema inf))


liftPredicateF m inf tname (WherePredicate i) = WherePredicate $ first (liftRel  inf tname) . fmap (fmap (first (fmap ((fst m ) inf tname))))<$> i
  
liftASchRel 
  :: (Text -> Text -> Maybe Table) 
  -> Text 
  -> Text 
  -> Text 
  -> Text 
  -> Rel Text  
  -> Rel Key
liftASchRel inf s tname st ttarget (Rel l e t) = Rel (lookKey s tname <$> l) e (lookKey st ttarget <$> t)
  where
    lookKey s tname c = justError ("no attr: " ++ show (c,tname,s)) $ L.find ((==c).keyValue ) =<< (rawAttrs <$> (inf s tname))
liftASchRel  _ i j k l m = error (show (i,j,k,l,m))

liftASch
  :: (T.Text -> T.Text -> Maybe Table)
     -> T.Text -> T.Text -> Rel T.Text -> Rel Key
liftASch inf s tname (Inline l) = Inline $  lookKey  l
  where
    tb = inf s tname
    lookKey c = justError ("no attr: " ++ show (c,tname,s)) $ L.find ((==c).keyValue ) =<< (rawAttrs <$>tb)
liftASch inf s tname (RelComposite l) =
  fromMaybe (relComp $ liftASch inf s tname <$> l) $ do 
      tb <- inf s tname
      rel <- L.find (\i -> relOutputSet (relComp l) ==  relOutputSet (relComp (S.map (fmap keyValue) $ pathRelRel i))) (rawFKS tb)
      return $ case unRecRel rel of
                FKJoinTable l _ -> relComp l
                FKInlineTable l _ -> Inline l
liftASch inf s tname (RelAccess i c) = RelAccess (relComp $ pathRelRel rel) (liftASch inf sch st c)
  where
    ref = liftASch inf s tname i
    tb = inf s tname
    rel  = justError ("no fk" ++ show i) $ L.find (\i -> relOutputSet ref == relOutputSet (relComp (pathRelRel i)) ) =<< ( rawFKS <$> tb)
    (sch,st) = case unRecRel rel of
          FKJoinTable  _ l -> l
          FKInlineTable  _ l -> l
liftASch inf s tname l =  maybe (error $ "no match" ++ show l ) id rel
  where
    tb = inf s tname
    rel = do 
       rel <- L.find (\i -> relOutputSet l ==  (relOutputSet (relComp (S.map (fmap keyValue) $ pathRelRel i))) ) =<< (rawFKS <$> tb)
       return $ case unRecRel rel of
                FKJoinTable  l _ -> relComp l
                FKInlineTable  i _ -> Inline i


liftASch inf s tname i = error ("No match: " ++ show (s,tname,i))

lookKeyNested inf s tname = HM.lookup tname =<<  HM.lookup s inf


recLookupInf inf tname rel = recLookup (liftRel inf tname rel)

liftRel :: InformationSchema -> Text -> Rel Text -> Rel Key
liftRel inf = liftASch (lookKeyNested (tableMap inf)) (schemaName inf)
liftRelM inf t r = Just $ liftRel  inf t r

liftAccessM ::  InformationSchema -> Text -> Access Text  -> Maybe (Access Key)
liftAccessM inf tname (Point i  ) =  Just $ Point i
liftAccessM inf tname (Rec i j ) =  Rec i <$> liftAccessMU inf tname  j
liftAccessM inf tname (IProd b l) = IProd b  <$> lookKeyM inf tname l
liftAccessM inf tname (Nested i c) = Nested <$> ref <*> join (fmap (\ l -> liftAccessMU inf  (snd (proj l)) c ) n)
  where
    ref = traverse (traverse (lookKeyM inf tname)) i
    tb = lookTable inf tname
    n = join $ (\ ref -> L.find (\i -> S.fromList (F.toList (_relOrigin <$> ref)) == S.map _relOrigin (pathRelRel i) ) (rawFKS tb)) <$> ref
    proj n = case n of
          FKJoinTable  _ l   ->  l
          FKInlineTable  _ l   ->  l

liftAccessM _ _ i = error (show i)


liftAccessMU inf tname (ISum i) =  ISum <$> traverse (liftAccessM inf tname)  i
liftAccessMU inf tname (Many i) =  Many <$> traverse (liftAccessM inf tname)  i

liftAccessF :: (Show k ,Ord k) => LookupKey k -> InformationSchema -> Text -> Access k-> Access Key
liftAccessF lk inf tname (Point i  ) =  Point i
liftAccessF lk inf tname (Rec i j ) =  Rec i (liftAccessF lk inf tname  <$> j)
liftAccessF lk inf tname (IProd b l) = IProd b $ fst lk inf tname l
liftAccessF lk inf tname (Nested i c) = Nested (Non.fromList r) (liftAccessF lk rinf (snd l)<$> c)
  where
    rinf = fromMaybe inf (HM.lookup  (fst l) (depschema inf))
    ref = fmap ((fst lk) inf tname )<$> i
    tb = lookTable inf tname
    n = unRecRel $ justError ("no fk " ++ show (i,tname,S.map _relOrigin . pathRelRel <$> rawFKS tb,rawFKS tb) )$ L.find (\i -> S.fromList (_relOrigin <$> F.toList ref) == S.map _relOrigin (pathRelRel i) ) (rawFKS tb)
    (r,l) = case n of
        FKJoinTable  r l   ->  (r,l)
        FKInlineTable  r l   ->  ([Inline r],l)
        i -> error (show i)
liftAccessF _ _ _  i = error (show i)

liftAccess = liftAccessF lookupKeyName

liftAccessU inf t = fmap (liftAccess inf t )

lookAccess :: InformationSchema -> Text -> (Rel Text , [(Rel Text,AccessOp Showable )]) -> (Rel Key, [(Rel Key,AccessOp Showable )])
lookAccess inf tname (l1,l2) = (liftRel inf tname l1 , first (fmap (lookKey inf tname)) <$> l2 )

genPredicateFull'
  :: (Ord a,Show a)
  => t
  -> Map Int (Union (Access a))
  -> Access a
  -> Maybe (BoolCollection (Rel a, Either a1 UnaryOperator))
genPredicateFull' i s (Rec ix l) = AndColl <$> (nonEmpty . catMaybes $ genPredicateFull' i (M.insert ix l s) <$> F.toList l)
genPredicateFull' i s (Point ix) = AndColl <$> (nonEmpty . catMaybes $ genPredicateFull' i (M.delete ix  s) <$> F.toList (maybe [] F.toList $ M.lookup ix s))
genPredicateFull' i s (IProd b l) =  Just . maybe (PrimColl (Inline l ,Right Exists)) (\i -> PrimColl (Inline l,Right i )) $ b
genPredicateFull' i s (Nested p l) = fmap (\(a,b) -> (RelAccess (relComp p) a , b )) <$> genPredicateFullU' i s l
genPredicateFull' _ s i = error (show i)

genPredicateFullU t = genPredicateFullU' t M.empty
genPredicateFull t = genPredicateFull' t M.empty

genPredicateFullU'
  :: (Ord a, Show a)
  => t
  -> Map Int (Union (Access a))
  -> Union (Access a)
  -> Maybe (BoolCollection (Rel a, Either a1 UnaryOperator))
genPredicateFullU' i s (Many l) = AndColl <$> nonEmpty (catMaybes $ genPredicateFull' i s<$> l)
genPredicateFullU' i s (ISum l) = OrColl <$> nonEmpty (catMaybes $ genPredicateFull' i s<$> l)

genPredicateU i (Many l) = AndColl <$> (nonEmpty $ catMaybes $ (\(o) -> genPredicate i o) <$> l)
genPredicateU i (ISum l) = OrColl <$> (nonEmpty $ catMaybes $ (\(o) -> genPredicate i o) <$> l)

genPredicate o (IProd b l) =  (\i -> PrimColl (Inline l,Right (if o then i else Not i ) )) <$> b
genPredicate i n@(Nested p  l ) = fmap AndColl $ nonEmpty $ catMaybes $ (\a -> if i then genPredicate i (IProd Nothing (_relOrigin a)) else  Nothing ) <$> F.toList p
genPredicate _ i = error (show i)



notException e =  if isJust eb || isJust es || isJust as then Nothing else Just e
  where
    eb :: Maybe BlockedIndefinitelyOnMVar
    eb = fromException e
    as :: Maybe AsyncException
    as = fromException e
    es :: Maybe BlockedIndefinitelyOnSTM
    es = fromException e

showFKText inf m v = L.take 50 . L.intercalate "," $  (renderShowable <$> allKVRec' inf m v)

patchNoRef l =  concat $ attrNoRef <$> l
  where
    attrNoRef (PFK _ l _ ) = l
    attrNoRef (PInline i l ) = [PInline i $ patchNoRef <$> l]
    attrNoRef (PFun _ _ _) = []
    attrNoRef i = [i]

mergeCreate (Just i) (Just j) = Just $ mergeKV i j
mergeCreate Nothing (Just i) = Just i
mergeCreate (Just i)  Nothing = Just i
mergeCreate Nothing Nothing = Nothing


recComplement :: forall a . Show a => InformationSchema -> KVMetadata Key ->  TBData Key () -> WherePredicate -> TBData Key  a -> Maybe (TBData Key ())
recComplement inf m  p (WherePredicate i) r =  filterAttrs attrList m r p
  where
    attrList  = fst <$> F.toList i
    filterAttrs :: [Rel Key] -> KVMetadata Key  -> TBData Key  a -> TBData Key () -> Maybe (TBData Key ())
    filterAttrs r m e v
      | _kvIsSum m && L.any (isJust . unLeftItens) (unkvlist e) =  (\i -> kvlist . pure <$>  ((\v -> go r m (index i ) i v) =<< kvLookup (index i) v)) =<< L.find (isJust . unLeftItens) (unkvlist e)
      | otherwise = fmap kvmap . join . fmap notPKOnly . notEmpty . M.merge M.dropMissing M.preserveMissing (M.zipWithMaybeMatched (go r m)) (unKV e) . unKV $ v
      where notPKOnly k =   if relOutputSets (M.keys k) `S.isSubsetOf` relOutputSets (_kvpk m <> r ) then Nothing else Just k
    notEmpty i = if M.null readable then Nothing else Just readable
      where readable = M.filterWithKey (\k _ -> F.any (L.elem FRead . keyModifier ._relOrigin) (relUnComp k)) i
    go r m _ (FKT l rel tb) (FKT l1 rel1 tb1)
      | S.isSubsetOf (S.fromList (_relAccess <$> rel)) (S.fromList $ _kvpk m <> r) =  Just (FKT l1 rel1 tb1)
      | otherwise =  result
      where
        result = FKT l1 rel1 <$> if merged == LeftTB1 Nothing then Nothing else (sequenceA merged)
        merged = filterAttrs  (_relTarget <$> rel) m2 <$> tb <*> tb1
        FKJoinTable _ ref = unRecRel $ justError "cant find fk rec complement" $ L.find (\r-> pathRelRel r  == S.fromList rel)  (_kvjoins m)
        m2 = lookSMeta inf (RecordPrim ref)
    go _ m _ (IT  it tb) ( IT it1 tb1) = IT it1 <$> if merged == LeftTB1 Nothing then Nothing else (sequenceA merged)
      where
        merged = filterAttrs [] ms <$> tb <*> tb1
        ms = lookSMeta inf  k
        k = _keyAtom $ keyType it
    go r m _ _ v@(Attr k a) = if L.elem (Inline k) (_kvpk m <> r) then Just v else Nothing
    go r m _ _ v@(Fun _ _ _) = Nothing

relOutputSets s = S.unions (relOutputSet <$> s )

recPK inf = filterTBData pred inf
  where
    pred = (\m k _ ->
            let
                pkdesc = S.unions $ relOutputSet <$>  _kvpk m
            in not . S.null $ relOutputSet k `S.intersection` pkdesc)

recPKDescIndex inf = filterTBData pred inf
  where
    pred = (\m k _ ->
            let
                pkdesc = S.unions $ relOutputSet <$> (_kvpk m <> _kvdesc m <> concat (_kvuniques m))
            in not . S.null $ relOutputSet k `S.intersection` pkdesc)



recPKDesc inf = filterTBData pred inf
  where
    pred = (\m k _ ->
            let
                pkdesc = S.unions $ relOutputSet <$> (_kvpk m <> _kvdesc m)
            in not . S.null $ relOutputSet k `S.intersection` pkdesc)

filterTBData :: (KVMetadata Key -> Rel Key -> TB Key a -> Bool) ->  InformationSchema -> KVMetadata Key -> TBData Key  a -> TBData Key a
filterTBData  pred inf =  filterAttrs S.empty
  where
    filterAttrs l m = mapKV (go m) . kvFilterWith (\i v -> pred m i v || not (S.null (relOutputSet i `S.intersection` l)))
    go m (FKT l  rel  tb) = FKT l rel $ filterAttrs (S.fromList $ _relOrigin . _relTarget <$> rel) m2  <$> tb
      where
        FKJoinTable _ ref = unRecRel $ justError ("cant find fk rec desc: " <> show (rel ,_kvjoins m))$ L.find (\r-> pathRelRel r  == S.fromList rel)  (_kvjoins m)
        m2 = lookSMeta inf (RecordPrim ref)
    go m (IT  it tb) = IT it $ filterAttrs S.empty ms <$> tb
      where
        ms = lookSMeta inf  k
        k = _keyAtom $ keyType it
    go m (Attr k a) = Attr k a


allKVRecL :: InformationSchema -> KVMetadata Key ->  FTB (KV Key Showable) -> [FTB Showable]
allKVRecL inf m = concat . F.toList . fmap (allKVRec' inf m)

allKVRec' :: InformationSchema -> KVMetadata Key -> TBData Key  Showable -> [FTB Showable]
allKVRec' inf m e =  concat $ fmap snd (L.sortBy (comparing (\i -> maximum $ (`L.elemIndex` _kvdesc m)  <$> (relUnComp $ fst i) ))  . M.toList $ go  <$> unKV (eitherDescPK m e))
  where
    go (FKT l  rel  tb) = allKVRecL  inf m2 tb
      where
        FKJoinTable _ ref = unRecRel $ justError "cant find fk kv" $ L.find (\r-> pathRelRel r  == S.fromList rel)  (_kvjoins m)
        m2 = lookSMeta inf (RecordPrim ref)
    go (IT  it tb) = allKVRecL inf ms tb
      where
        ms = lookSMeta inf  k
        k = _keyAtom $ keyType it
    go (Attr _ a) = [a]

patchRowM' m o v =  RowPatch . (G.getIndex m v,) . PatchRow  <$> diff o v
patchRow' m o v =  RowPatch (G.getIndex m v,PatchRow (diff' o v))
createRow' m v =  RowPatch (G.getIndex m v,CreateRow v)
dropRow' m v = RowPatch (G.getIndex m v,DropRow )

createUn :: (Show k ,Ord k) => KVMetadata k -> [Rel k] -> [TBData k Showable] -> G.GiST (TBIndex Showable) (TBData k Showable)
createUn m un = G.fromList  (justError ("empty: " ++ show un) . transPred) . L.filter (isJust . transPred)
  where transPred = G.notOptionalM . G.getUnique un

tablePredicate inf t p = (WherePredicate . AndColl $ fmap (lookAccess inf t). PrimColl .fixrel <$> p)
tablePredicate' p = (WherePredicate . AndColl $ PrimColl .fixrel <$> p)

lookRef k = _fkttable . lookAttrs' k

tablePK t = (_rawSchemaL t ,_rawNameL t)

lookAttrs' k = err . lookAttrsM k
  where
      err= justError ("no attr " <> show k )

lookAttr' k = _tbattr . err . lookAttrM k
  where
      err= justError ("no attr " <> show k )

lookAttrsM k m = M.lookup (S.fromList k) ta
    where
      ta = M.mapKeys (S.map keyValue . relOutputSet ) (unKV m)

lookAttrM k =  lookAttrsM [k]

fixrel (Inline  i,op) = (Inline i,[(Inline i,op)])
fixrel (RelAccess i j , op) = (RelAccess i (fst sub),snd sub)
  where sub = fixrel . (,op) $ j
fixrel (i,op) = (i,[])

fixfilters (IProd j i,op) = (IProd j i,[(i,op)])
fixfilters (Nested i j , op) = (Nested i (fmap fst sub),concat $  fmap snd sub)
  where sub = fixfilters . (,op) <$> j
fixfilters (i,op) = (i,[])

data SchemaChange k p
  = SchemaChange  (RowPatch k p) (Map (TableK p) [SchemaChange k p])

type TableModification p = TableModificationK Table p

data RevertModification k p
  = RevertModification { source :: TableModificationK k p
                       , undoDiff :: p
                       }
  deriving (Eq, Show, Functor, Generic)

secondary (TableRep (m,s,g)) = s
primary (TableRep (m,s,g)) = g

predNull (WherePredicate i) = L.null i

filterfixedS table fixed (s,v)
  = if predNull fixed
       then v
       else queryCheckSecond (fixed ,rawPK table) (TableRep (tableMeta table,s,v))

data TableModificationK k p
  = TableModification { tableId :: Maybe Int
                      , tableTime :: UTCTime
                      , tableUser :: Text
                      , tableObj :: k
                      , tableDiff :: p
                      }
  | NestedModification  (TableModificationK k p) (M.Map (AttributePath Key (AccessOp Key , FTB Showable)) (TableModificationK k p ))
  | BatchedAsyncTableModification k  [TableModificationK k p]
  | AsyncTableModification {
                       tableObj :: k
                      , tableDiff :: p
                      }
  | FetchData { tableObj :: k
              , tableDiff :: p
              }
  deriving (Eq, Show, Functor, Generic)

instance (NFData i, NFData l) => NFData (TableModificationK i l)
instance (NFData i, NFData l) => NFData (AttributePath i l)
instance (NFData i, NFData l) => NFData (PathIndex i l)
instance  NFData PathTID

makeLenses ''InformationSchemaKV


