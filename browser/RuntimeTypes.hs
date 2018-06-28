{-# LANGUAGE FlexibleInstances,FlexibleContexts,DeriveAnyClass,DeriveGeneric,StandaloneDeriving,TypeFamilies,OverloadedStrings,TemplateHaskell,DeriveTraversable,DeriveFoldable,DeriveFunctor,RankNTypes,ExistentialQuantification #-}
module RuntimeTypes where

import Types
import Types.Index as G
import Data.Ord
import Data.Time
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



data InformationSchemaKV k v
  = InformationSchema
  { schemaId :: Int
  , schemaName :: Text
  , schemaColor :: Maybe Text
  , username :: UserTable
  , authtoken :: Auth
  , _keyMapL :: HM.HashMap (Text,Text) k
  , colMap ::  HM.HashMap Text (IM.IntMap k)
  , _backendKey :: Map KeyUnique PGKey
  , _keyUnique :: Map KeyUnique k
  , _pkMapL :: Map (Set k) Table
  , _tableMapL :: HM.HashMap Text Table
  , mvarMap :: TVar (Map (TableK k) (DBRef Key v ))
  , rootconn :: Connection
  , metaschema :: Maybe (InformationSchemaKV k v)
  , depschema :: HM.HashMap Text (InformationSchemaKV k v)
  , schemaOps :: SchemaEditor
  , plugins :: [Plugins]
  , rootRef :: TVar DatabaseSchema
  }

instance Eq InformationSchema where
  i == j = schemaId i == schemaId j

instance Ord InformationSchema where
  compare i j = compare (schemaId i) (schemaId j)

recoverKey inf un = justError ("no key " <> show un) $ M.lookup un (_keyUnique inf) <|> deps
  where deps = join $ L.find isJust $ (M.lookup  un . _keyUnique) <$> F.toList (depschema inf)

backendsKey s = _backendKey s <> F.foldl' mappend mempty (fmap (backendsKey .snd)$ HM.toList $ depschema s)

data Auth
  = PostAuth Connection
  | NoAuth

conn s = case authtoken s of
      PostAuth i -> i

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
pkMap = _pkMapL

data DBRef k v =
  DBRef  { dbRefTable :: TableK k
         , refIndex :: Int
         , refSize :: TVar Int
         , patchVar :: TChan [TableModificationU k v]
         , idxVar :: TVar (IndexMetadata k v)
         , idxChan :: TChan (IndexMetadataPatch k v)
         , collectionState  :: TVar (TableRep k v)
         }

meta inf = fromMaybe inf (metaschema inf)

data DBVar2 v =
  DBVar2
  { iniRef :: DBRef Key v
  , idxTid :: R.Tidings (IndexMetadata Key v)
  , collectionTid :: R.Tidings (TableIndex Key v)
  , collectionSecondaryTid :: R.Tidings (Map [Key] (SecondaryIndex Key v))
  }



type IndexMetadataPatch k v = (WherePredicateK k, Int, Int, PageTokenF v)

type TableIndex k v = GiST (TBIndex v) (TBData k v)
type SecondaryIndex k v = GiST (TBIndex v) (M.Map (TBIndex v) [AttributePath k (AccessOp v , FTB v)])


instance (Show k ,Show v) => Patch (InformationSchemaKV  k v )  where
  type Index (InformationSchemaKV k v) = [TableModificationU k v]


type RefTables = ( R.Tidings (IndexMetadata CoreKey Showable)
                 , R.Tidings (TableIndex CoreKey Showable)
                 , R.Tidings (M.Map [Key] (SecondaryIndex Key Showable))
                 , TChan [TableModificationU Key Showable] )

type PKConstraint = C.Predicate [Column CoreKey Showable]

type TBConstraint = C.Predicate (TBData CoreKey Showable)

type SelPKConstraint = [([Set (Rel Key)],R.Tidings PKConstraint)]

type SelTBConstraint = [([Set (Rel Key)],R.Tidings TBConstraint)]

type PluginRef a = [(Union (Access Key), R.Tidings (Maybe (Index a)))]

currentState db = R.currentValue (R.facts $ collectionTid db)
currentIndex db = R.currentValue (R.facts $ idxTid db)

instance (NFData k,  PatchConstr k Showable) => Patch (TableRep k Showable) where
  type Index (TableRep k Showable) = [RowPatch k Showable]
  applyUndo i j = fmap reverse <$> F.foldl' (\i j -> (\(v,l) -> fmap (:l) <$> applyTableRep v j) =<< i ) (Right (i,[]))  j

instance (Ord k , Show k , Show v) => Patch (IndexMetadata k v) where
  type Index (IndexMetadata k v) =  [(WherePredicateK k ,Int,Int,PageTokenF v)]
  applyUndo i =Right . (,[]). F.foldl' vapply i
    where vapply (IndexMetadata m) (v,s,i,t) = IndexMetadata $ M.alter (\j -> fmap ((\(_,l) -> (s,M.insert i t l ))) j  <|> Just (s,M.singleton i t)) v m

instance (Show v, Show k ,Ord k ,Compact v) => Compact (TableModificationK k  v) where
  compact i = foldCompact assoc i
    where
      assoc (AsyncTableModification o d ) (AsyncTableModification o2 d2 )
          = if L.length new  == 1
            then Just (head new)
            else Nothing
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
     (NFData k, NFData a, G.Predicates (G.TBIndex a), PatchConstr k a)
  => (KVMetadata k,G.GiST (G.TBIndex a) (TBData k a))
  -> RowPatch k (Index a)
  -> Either String ((KVMetadata k,G.GiST (G.TBIndex a) (TBData k a)),RowPatch k (Index a))
applyGiSTChange (m,l) (RowPatch (patom,DropRow))=
  maybe (Right $ ((m,l),RowPatch (patom,DropRow))) Right $
    ((m,G.delete (create <$> patom) G.indexParam l) ,) . mapRowPatch patch . createRow' m <$> G.lookup (create <$> patom) l
applyGiSTChange (m,l) (RowPatch (ipa,PatchRow  patom)) =
  first (m,) <$>case flip G.lookup l =<< (G.notOptionalM i)  of
    Just v -> do
      (el ,u) <- applyUndo v patom
      let pkel = G.getIndex m el
      return $
        ((if pkel == i
          then G.update (G.notOptional i) (const el)
          else G.insert (el, G.tbpred m el) G.indexParam .
            G.delete (G.notOptional i) G.indexParam) l, RowPatch (ipa,PatchRow u))

    Nothing -> do
      el <-maybe (Left $ "cant create row" ++ show patom) Right $ createIfChange patom
      return $ (G.insert (el, G.tbpred m el) G.indexParam l,RowPatch (ipa,DropRow ))
  where
    i = fmap create ipa
applyGiSTChange (m,l) p@(RowPatch (idx,CreateRow (elp))) =
  maybe (Right ((m,l),p)) Right $
    first (m,) <$> case G.lookup ix  l of
      Just v -> Nothing
      Nothing -> Just (G.insert (el, ix) G.indexParam l,RowPatch (idx,DropRow ))
    where
      el = fmap create elp
      ix = create <$> idx

recAttr
  :: (Show k, Ord k)
    => [k]
    -> TB k a
    -> [(AttributePath k (Either (FTB a, BinaryOperator) b, FTB a),TBIndex a)]
recAttr un (Attr i k) = first (PathAttr i) <$> recPred (\i -> [(TipPath (Left (TB1 i,Equals),TB1 i), G.Idex [TB1 i])]) k
recAttr un f@(FKT l rel k) = first (PathForeign rel) <$> recPred (\i ->
  let nest = concat $ recAttr un <$> F.toList  (_kvvalues  i)
  in [(TipPath . Many $ One .fst <$> nest, G.getUnique  un i )]) ( fst .unTBRef <$> liftFK f)

recPred
  :: (t -> [(PathIndex PathTID b, d)])
    -> FTB t
    -> [(PathIndex PathTID b, d)]
recPred f (TB1 i) = f i
recPred f (LeftTB1 i) = fmap (first (NestedPath PIdOpt )) . join $ recPred f <$> (maybeToList i)
recPred f (ArrayTB1 i) = concat . F.toList $ Non.imap (\ix i -> fmap (first (NestedPath (PIdIdx ix ))) $ recPred f i ) i

applySecondary
  ::  (NFData k,NFData a,G.Predicates (G.TBIndex a) , a ~ Index a, PatchConstr k a)  =>  RowPatch k (Index a)-> RowPatch k (Index a) -> TableRep k a -> TableRep k a
applySecondary (RowPatch (patom,DropRow )) (RowPatch (_,CreateRow v)) (TableRep (m,sidxs,l))
  = TableRep (m,M.mapWithKey didxs sidxs,l)
  where
    didxs un sidx = G.delete (fmap create $ G.getUnique  un v) G.indexParam sidx
applySecondary (RowPatch (ix,CreateRow elp)) _  (TableRep (m,sidxs,l)) =  TableRep (m,M.mapWithKey didxs sidxs,l)
  where
    didxs un sidx = maybe sidx (F.foldl' (\sidx (ref ,u) -> G.alterWith (M.insertWith  mappend ix [ref].fromMaybe M.empty) u sidx) sidx .recAttr un ).safeHead $ F.toList $ M.filterWithKey (\k _-> not . S.null $ (S.map _relOrigin k) `S.intersection` (S.fromList un) )  $ _kvvalues el


    el = fmap create elp
applySecondary n@(RowPatch (ix,PatchRow elp)) d@(RowPatch (ixn,PatchRow elpn))  (TableRep (m,sidxs,l)) =  TableRep (m, M.mapWithKey didxs sidxs,l)
  where
    didxs un sidx = maybe sidx (F.foldl' (\sidx  (ref,u)  -> G.alterWith (M.insertWith  mappend ix [ref] . fromMaybe M.empty) u $ G.delete (G.getUnique  un eln) G.indexParam sidx ) sidx. recAttr un ) $  safeHead $ F.toList $ M.filterWithKey (\k _-> not . S.null $ (S.map _relOrigin k) `S.intersection` (S.fromList un) )  $ _kvvalues el
    el = justError "cant find"$ G.lookup ix l
    eln = apply el elpn
    -- eln = create elpn
applySecondary _ _ i = i

applyTableRep
  ::  (NFData k,  PatchConstr k Showable)
  => TableRep k Showable
  -> RowPatch k Showable
  -> Either String (TableRep k Showable,RowPatch k Showable)
applyTableRep rep (BatchPatch rows op) = fmap (head . compact) <$> F.foldl' (\i j -> (\(v,l) -> fmap (fmap (:l)) $  applyTableRep v j) =<< i ) (Right (rep,[]))  (RowPatch . (,op)  <$>rows)
applyTableRep (TableRep (m,sidxs,l)) p = do
  ((m,g),u)<- applyGiSTChange (m,l) p
  return (applySecondary p u (TableRep (m,sidxs, g)), u)


typecheck f a = case f a of
          Pure i -> Right a
          Other (Constant l) ->  Left l

queryCheckSecond :: (Show k,Ord k) => (WherePredicateK k ,[k]) -> TableRep k Showable-> G.GiST (TBIndex  Showable) (TBData k Showable)
queryCheckSecond pred@(b@(WherePredicate bool) ,pk) (TableRep (m,s,g)) = t1
  where t1 = G.fromList' . maybe id (\pred -> L.filter (flip checkPred pred . leafValue)) notPK  $ fromMaybe (getEntries  g)  (searchPK  b (pk,g)<|>  searchSIdx)
        searchSIdx = (\sset -> L.filter ((`S.member` sset) .leafPred) $ getEntries g) <$> mergeSIdxs
        notPK = WherePredicate <$> F.foldl' (\l i -> flip G.splitIndexPKB  i =<< l ) (Just bool) (pk : M.keys s )
        mergeSIdxs :: Maybe (S.Set (TBIndex Showable))
        mergeSIdxs = L.foldl1' S.intersection <$> nonEmpty (catMaybes $ fmap (S.unions . fmap (M.keysSet.leafValue)). searchPK b <$> (M.toList s))


searchPK ::  (Show k,Ord k) => WherePredicateK k -> ([k],G.GiST (TBIndex  Showable) a ) -> Maybe [LeafEntry (TBIndex  Showable) a]
searchPK (WherePredicate b) (pk, g)= (\p -> G.projectIndex pk  (WherePredicate p) g) <$>  splitIndexPK b pk


type DBVar = DBVar2 Showable
type Collection k v = (IndexMetadata k v ,GiST (TBIndex v ) (TBData k v))

type PrePlugins = FPlugins Text
type Plugins = (Int,PrePlugins)
type VarDef = (Text,KType CorePrim)


data FPlugins k =
    FPlugins
      { _name  :: Text
      , _bounds :: Text
      , _plugAction :: FPlugAction k
      }

data FPlugAction k
  = StatefullPlugin [(([VarDef],[VarDef]),FPlugAction k) ]
  | IOPlugin  (ArrowReaderM IO)
  | PurePlugin (ArrowReaderM Identity)
  | DiffPurePlugin (ArrowReaderDiffM Identity)
  | DiffIOPlugin (ArrowReaderDiffM IO)

type ArrowReaderDiffM m  = Parser (Kleisli (ReaderT (TBData Text Showable) m )) (Union (Access Text),Union (Access Text)) () (Maybe (Index (TBData Text Showable)))


pluginStatic = pluginStatic' . _plugAction
pluginAction = pluginAction' . _plugAction

pluginActionDiff :: FPlugins a-> TBData Text Showable -> IO (Maybe (TBIdx Text Showable))
pluginActionDiff = pluginActionDiff' . _plugAction

pluginStatic' (IOPlugin  a) = staticP a
pluginStatic' (DiffIOPlugin a) = staticP a
pluginStatic' (DiffPurePlugin a) = staticP a
pluginStatic' (PurePlugin  a) = staticP a

pluginRun b@(IOPlugin _) = Right (pluginAction' b)
pluginRun b@(PurePlugin _ ) = Right (pluginAction' b)
pluginRun b@(DiffIOPlugin _ ) = Left (pluginActionDiff' b)
pluginRun b@(DiffPurePlugin _ ) = Left (pluginActionDiff' b)

pluginActionDiff' (DiffIOPlugin a ) = dynIO a
pluginActionDiff' (DiffPurePlugin a ) = return . dynPure a
pluginAction' (IOPlugin   a ) = dynIO a
pluginAction' (PurePlugin  a) = return . dynPure a

staticP ~(P s d) = s

dynIO url inp =
    runReaderT (dynPK url ()) inp

dynPure url inp = runIdentity $
    dynIO url inp

dynP ~(P s d) = d

dynPK =  runKleisli . dynP


localInf :: (InformationSchema -> InformationSchema ) -> TransactionM a -> TransactionM a
localInf f = local (first f)

askInf :: TransactionM InformationSchema
askInf = fmap fst ask

type TableModificationU k u= TableModificationK (TableK k) (RowPatch k u )

type TransactionM = RWST (InformationSchema,[TableModification (RowPatch Key Showable)]) [(WherePredicate,TableModification (RowPatch Key Showable))] (M.Map (Table,WherePredicate) (DBRef Key Showable)) R.Dynamic

type PageToken = PageTokenF Showable

deriving instance (Binary v) => Binary (PageTokenF  v)
deriving instance (NFData v) => NFData (PageTokenF  v)

newtype IndexMetadata k v =  IndexMetadata {unIndexMetadata :: (Map (WherePredicateK k) (Int,Map Int (PageTokenF v)))} deriving(Show)

newtype TableRep k v = TableRep (KVMetadata k, M.Map [k] (SecondaryIndex k v), TableIndex k v) deriving(Show)

newtype PageTokenF v
  = TableRef (Interval (TBIndex v))
  deriving(Eq,Ord,Show,Generic)

data OverloadedRule
  =  CreateRule  (TBData Key Showable -> TransactionM (RowPatch Key Showable))
  |  DropRule  (TBData Key Showable -> TransactionM (RowPatch Key Showable))
  |  UpdateRule  (TBData Key Showable -> TBIdx Key Showable -> TransactionM (RowPatch Key Showable))

data SchemaEditor
  = SchemaEditor
  { editEd  :: KVMetadata Key -> TBData Key Showable -> TBIndex Showable -> TBIdx Key Showable -> TransactionM (RowPatch Key Showable)
  , patchEd :: KVMetadata Key ->[TBIndex Showable] -> TBIdx Key Showable -> TransactionM (RowPatch Key Showable)
  , insertEd :: KVMetadata Key -> TBData Key Showable ->TransactionM (RowPatch Key Showable)
  , deleteEd :: KVMetadata Key ->TBData Key Showable ->TransactionM (RowPatch Key Showable)
  , listEd :: KVMetadata Key ->TBData  Key () -> Maybe Int -> Maybe PageToken -> Maybe Int -> [(Key,Order)] -> WherePredicate -> TransactionM ([TBData Key Showable],PageToken,Int)
  , getEd :: Table -> TBData Key Showable -> TransactionM (Maybe (RowPatch Key Showable))
  , typeTransform :: PGKey -> CoreKey
  , logger :: forall m . MonadIO m => InformationSchema -> TableModification (RowPatch Key Showable)  -> m (TableModification (RowPatch Key Showable))
  , undo :: forall m . MonadIO m => InformationSchema -> RevertModification Table (RowPatch Key Showable)  -> m ()
  , opsPageSize :: Int
  , transactionEd :: InformationSchema -> (forall a  . IO a -> IO a)
  , rules :: M.Map (Text,Text) [(TBData Text Showable -> Bool ,OverloadedRule)]
  }

typeTrans inf = typeTransform (schemaOps inf)


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
lookTable inf t = justError ("no table: " <> T.unpack t) $ HM.lookup t (_tableMapL inf)

lookTableM :: InformationSchema -> Text -> Maybe Table
lookTableM inf t =  HM.lookup t (_tableMapL inf)

lookSTable :: InformationSchema -> (Text,Text) -> Table
lookSTable inf (s,t) = justError ("no table: " <> T.unpack t) $ join $ HM.lookup t <$> HM.lookup s (tableMap inf)

lookKey :: InformationSchema -> Text -> Text -> Key
lookKey inf t k = justError ("table " <> T.unpack t <> " has no key " <> T.unpack k  <> show (HM.toList (keyMap inf))) $ HM.lookup (t,k) (keyMap inf)

lookKeyPosition :: InformationSchema -> Text -> Int -> Key
lookKeyPosition inf t k = justError ("table " <> T.unpack t <> " has no key " <> show k  <> show (HM.lookup t (colMap inf))) $  IM.lookup k =<< HM.lookup t (colMap inf)

lookKeyM :: InformationSchema -> Text -> Text -> Maybe Key
lookKeyM inf t k =  HM.lookup (t,k) (keyMap inf)

fetchData i = liftIO . atomically .writeTChan (patchVar i) . force  . fmap (FetchData (dbRefTable i)  )

putPatch m = liftIO. atomically . putPatchSTM m

mapModification :: (Ord b,Ord a,Ord c ,Ord (Index c))=> (a -> b) ->  TableModificationK (TableK a) (RowPatch a c) -> TableModificationK (TableK b )(RowPatch b c)
mapModification f (TableModification a b c d e ) = TableModification a b c (fmap f d) (firstPatchRow f e)
mapModification f (AsyncTableModification d e ) = AsyncTableModification  (fmap f d) (firstPatchRow f e)
mapModification f (FetchData d e) = FetchData (fmap f d) (firstPatchRow f e)

putPatchSTM m =  writeTChan m . force
putIdx m = liftIO .atomically . putIdxSTM m
putIdxSTM m =  writeTChan m . force

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
typeCheckTB (FKT k rel2 i ) = const <$> F.foldl' (liftA2 const ) (Pure () ) (typeCheckTB <$>  _kvvalues k) <*> mapError (fmap ((show (keyType ._relOrigin <$> rel2)) ++)) (typeCheckValue (\(RecordPrim l) -> typeCheckTable l )  ktype i)
  where
    ktypeRel = mergeFKRef (keyType ._relOrigin <$> rel2)
    ktype :: KType (Prim KPrim (Text,Text))
    ktype = const (RecordPrim  ("","")) <$> ktypeRel


mapError :: (a -> a) -> Errors a b -> Errors a b
mapError f (Other (Constant i)) = Other (Constant (f i))
mapError f (Pure i) = Pure i




typeCheckTable ::  (Text,Text) -> TBData (FKey (KType (Prim KPrim (Text,Text)))) Showable -> Errors [String] ()
typeCheckTable c  l
  =  F.foldl' (liftA2 const ) (Pure () ) (typeCheckTB <$> _kvvalues l)

type LookupKey k = (InformationSchema -> Text -> k -> Key, Key -> k)
lookupKeyName = (lookKey ,keyValue)
lookupKeyPosition= (lookKeyPosition,keyPosition )
-- lookupKey = (lookKeyPosition,keyFastUnique)


liftTableF ::  (Show k ,Ord k) => LookupKey k -> InformationSchema ->  Text -> TBData k a -> TBData Key a
liftTableF f inf  tname (KV i)  =  kvlist $ liftFieldF  f inf  tname <$> F.toList i
  where
    ta = lookTable inf tname



liftTable' :: InformationSchema -> Text -> TBData Text a -> TBData Key a
liftTable' = liftTableF lookupKeyName



findRefTableKey
  :: (Show t, Ord t) => TableK t -> [Rel t] -> (T.Text, T.Text)
findRefTableKey ta rel =  tname2
  where   (FKJoinTable  _ tname2 )  = unRecRel $ justError (show (rel ,rawFKS ta)) $ L.find (\r->  pathRelRel r == S.fromList rel)  (F.toList $ rawFKS  ta)


findRefTable inf tname rel =  tname2
  where   (FKJoinTable  _ (_,tname2) )  = unRecRel $ justError (show (rel ,rawFKS ta)) $ L.find (\r->  S.map (fmap keyValue ) (pathRelRel r) == S.fromList (_relOrigin <$> rel))  (F.toList$ rawFKS  ta)
          ta = lookTable inf tname

liftFieldF :: (Show k ,Ord k) => LookupKey k -> InformationSchema -> Text -> Column k a -> Column Key a
liftFieldF (f,p) inf tname (Attr t v) = Attr (f inf tname t) v
liftFieldF (f,p) inf tname (FKT ref  rel2 tb) = FKT (mapBothKV (f inf tname ) (liftFieldF (f,p) inf tname) ref)   rel (liftTableF (f,p) rinf tname2 <$> tb)
  where FKJoinTable  rel (schname,tname2)  = unRecRel $ justError (show (tname,rel2 ,rawFKS ta)) $ L.find (\r-> S.map (fmap p) (pathRelRel r)  == S.fromList rel2)  (F.toList$ rawFKS  ta)
        rinf = fromMaybe inf (HM.lookup schname (depschema inf))
        ta = lookTable inf tname
liftFieldF (f,p) inf tname (IT rel tb) = IT (f inf tname  rel) (liftTableF (f,p) inf tname2 <$> tb)
  where FKInlineTable _ (_,tname2)  = unRecRel $ justError (show (rel ,rawFKS ta)) $ L.find (\r->  S.map (fmap p) (pathRelRel r) == S.singleton (Inline rel))  (F.toList$ rawFKS  ta)
        ta = lookTable inf tname
liftFieldF (f,p) inf tname (Fun  k t v) = Fun (f inf tname k ) (fmap(fmap (f inf tname) )<$> t) v



liftField :: InformationSchema -> Text -> Column Text a -> Column Key a
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
    where (FKInlineTable _ (_,tname2)) = fromJust $ unRecRel Control.Applicative.<$> L.find (\r->  S.map (fmap keyValue ) (pathRelRel r) == S.singleton (Inline rel) )  (F.toList$ rawFKS  ta)
          ta = lookTable inf tname
liftPatchAttr inf tname p@(PFK rel2 pa  b ) =  PFK rel (fmap (liftPatchAttr inf tname) pa)  (liftPatch rinf tname2 Control.Applicative.<$> b)
    where (FKJoinTable  rel (schname,tname2) )  = unRecRel $ justError (show (rel2 ,rawFKS ta)) $ L.find (\r->  S.map (fmap keyValue ) (pathRelRel r) == S.fromList rel2)  (F.toList$ rawFKS  ta)
          ta = lookTable inf tname
          rinf = fromMaybe inf (HM.lookup schname (depschema inf))


liftPredicateF m inf tname (WherePredicate i) = WherePredicate $ first (liftRel  inf tname) . fmap (fmap (first ((fst m ) inf tname)))<$> i

liftASch :: TableMap  -> Text -> Text -> Rel Text  -> Rel Key
liftASch inf s tname (Inline l) = Inline $  lookKey  l
  where
    tb = lookup tname =<<  lookup s inf
    lookup i m = HM.lookup i m
    lookKey c = justError ("no attr: " ++ show (c,tname,s)) $ L.find ((==c).keyValue ) =<< (tableAttrs <$>tb)

liftASch inf s tname (RelAccess i c) = RelAccess (F.toList $ pathRelRel rel) (liftASch inf sch st c)
  where
    ref = liftASch inf s tname <$> i
    lookup i m = justError ("no look " <> show i) $ HM.lookup i m
    tb = lookup tname $  lookup s inf
    rel  = justError "no fk" $ L.find (\i -> S.fromList (_relOrigin <$> ref) == S.map _relOrigin (pathRelRel i) ) (rawFKS tb)
    (sch,st) = case unRecRel rel of
          FKJoinTable  _ l -> l
          FKInlineTable  _ l -> l



recLookupInf inf tname rel = recLookup (liftRel inf tname rel)

liftRel :: InformationSchema -> Text -> Rel Text -> Rel Key
liftRel inf = liftASch (tableMap inf ) (schemaName inf)
liftRelM inf t r = Just $ liftRel  inf t r

liftAccessM ::  InformationSchema -> Text -> Access Text  -> Maybe (Access Key)
liftAccessM inf tname (Point i  ) =  Just $ Point i
liftAccessM inf tname (Rec i j ) =  Rec i <$> liftAccessMU inf tname  j
liftAccessM inf tname (IProd b l) = IProd b  <$> lookKeyM inf tname l
liftAccessM inf tname (Nested i c) = Nested <$> ref <*> join (fmap (\ l -> liftAccessMU inf  (snd (proj l)) c ) n)
  where
    ref = traverse (lookKeyM inf tname) i
    tb = lookTable inf tname
    n = join $ (\ ref -> L.find (\i -> S.fromList ref == S.map _relOrigin (pathRelRel i) ) (rawFKS tb)) <$> ref
    proj n = case n of
          FKJoinTable  _ l   ->  l
          FKInlineTable  _ l   ->  l

liftAccessM _ _ i = error (show i)


liftAccessMU inf tname (ISum i) =  ISum <$> traverse (liftAccessMU inf tname)  i
liftAccessMU inf tname (Many i) =  Many <$> traverse (liftAccessMU inf tname)  i
liftAccessMU inf tname (One i) =  One <$> liftAccessM inf tname  i

liftAccessF :: (Show k ,Ord k) => LookupKey k -> InformationSchema -> Text -> Access k-> Access Key
liftAccessF lk inf tname (Point i  ) =  Point i
liftAccessF lk inf tname (Rec i j ) =  Rec i (liftAccessF lk inf tname  <$> j)
liftAccessF lk inf tname (IProd b l) = IProd b $ fst lk inf tname l
liftAccessF lk inf tname (Nested i c) = Nested ref (liftAccessF lk rinf (snd l)<$> c)
  where
    rinf = fromMaybe inf (HM.lookup  (fst l) (depschema inf))
    ref = (fst lk) inf tname <$> i
    tb = lookTable inf tname
    n = justError ("no fk " ++ show (i,tname) )$ L.find (\i -> S.fromList (ref)== S.map _relOrigin (pathRelRel i) ) (rawFKS tb)
    l = case n of
          FKJoinTable  _ l   ->  l
          FKInlineTable  _ l   ->  l
liftAccessF _ _ _  i = error (show i)

liftAccess = liftAccessF lookupKeyName

liftAccessU inf t = fmap (liftAccess inf t )

lookAccess :: InformationSchema -> Text -> (Rel Text , [(Text,AccessOp Showable )]) -> (Rel Key, [(Key,AccessOp Showable )])
lookAccess inf tname (l1,l2) = (liftRel inf tname l1 , first (lookKey inf tname) <$> l2 )

genPredicateFull
  :: Show a =>
     t
     -> Access a
     -> Maybe (BoolCollection (Rel a, Either a1 UnaryOperator))
genPredicateFull i (Rec _ _) = Nothing  -- AndColl <$> (nonEmpty $ catMaybes $ genPredicateFull i <$> l)
genPredicateFull i (Point _) = Nothing -- AndColl <$> (nonEmpty $ catMaybes $ genPredicateFull i <$> l)
genPredicateFull i (IProd b l) =  (\i -> PrimColl (Inline l,Right i ))  <$> b
genPredicateFull i (Nested p l) = fmap (\(a,b) -> (RelAccess (fmap (Inline  ) p) a , b )) <$> genPredicateFullU i l
genPredicateFull _ i = error (show i)

genPredicateFullU
  :: Show a =>
     t
     -> Union (Access a)
     -> Maybe (BoolCollection (Rel a, Either a1 UnaryOperator))
genPredicateFullU i (Many l) = AndColl <$> nonEmpty (catMaybes $ genPredicateFullU i <$> l)
genPredicateFullU i (ISum l) = OrColl <$> nonEmpty (catMaybes $ genPredicateFullU i <$> l)
genPredicateFullU i (One l) = genPredicateFull i  l

genPredicateU i (Many l) = AndColl <$> (nonEmpty $ catMaybes $ (\(One o) -> genPredicate i o) <$> l)
genPredicateU i (Many l) = OrColl <$> (nonEmpty $ catMaybes $ (\(One o) -> genPredicate i o) <$> l)

genPredicate o (IProd b l) =  (\i -> PrimColl (Inline l,Right (if o then i else Not i ) )) <$> b
genPredicate i n@(Nested p  l ) = fmap AndColl $ nonEmpty $ catMaybes $ (\a -> if i then genPredicate i (IProd Nothing a) else  Nothing ) <$> p
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
    attrNoRef i = [i]

mergeCreate (Just i) (Just j) = Just $ mergeTB1 i j
mergeCreate Nothing (Just i) = Just i
mergeCreate (Just i)  Nothing = Just i
mergeCreate Nothing Nothing = Nothing

mergeTB1 k  k2
  = (\(KV i ) (KV j) -> KV $ M.unionWith const i j ) k k2

recComplement :: InformationSchema -> KVMetadata Key -> TBData Key  a -> TBData Key () -> Maybe (TBData Key ())
recComplement inf m e total =  filterAttrs m e total
  where
    filterAttrs m e = fmap KV . notEmpty . M.merge M.dropMissing M.preserveMissing (M.zipWithMaybeMatched go) (_kvvalues e)  ._kvvalues
    notEmpty i = if M.null i then Nothing else Just i
    go _ (FKT l  rel  tb) (FKT l1  rel1  tb1) = fmap (FKT l1 rel1) $ if merged == LeftTB1 Nothing then Nothing else (sequenceA merged)
      where
        merged = filterAttrs m2 <$> tb <*> tb1
        FKJoinTable _ ref = unRecRel $ fromJust $ L.find (\r-> pathRelRel r  == S.fromList rel)  (_kvjoins m)
        m2 = lookSMeta inf (RecordPrim ref)
    go _ (IT  it tb) ( IT it1 tb1)= fmap (IT it1)  $ if merged == LeftTB1 Nothing then Nothing else (sequenceA merged)
      where
        merged = filterAttrs ms <$> tb <*> tb1
        ms = lookSMeta inf  k
        k = _keyAtom $ keyType it
    go _ _ (Attr k a) = Nothing -- Attr k a


recPKDesc :: InformationSchema -> KVMetadata Key -> TBData Key  a -> TBData Key a
recPKDesc inf m e =  filterAttrs m e
  where
    filterAttrs m = KV . fmap go . M.filterWithKey (\k _ -> not . S.null $ S.map _relOrigin k `S.intersection` pkdesc)  ._kvvalues
      where pkdesc = S.fromList $ _kvpk m <> _kvdesc m
    go (FKT l  rel  tb) = FKT l rel $ filterAttrs m2  <$> tb
      where
        FKJoinTable _ ref = unRecRel $ fromJust $ L.find (\r-> pathRelRel r  == S.fromList rel)  (_kvjoins m)
        m2 = lookSMeta inf (RecordPrim ref)
    go (IT  it tb) = IT it $ filterAttrs ms <$> tb
      where
        ms = lookSMeta inf  k
        k = _keyAtom $ keyType it
    go (Attr k a) = Attr k a


allKVRecL :: InformationSchema -> KVMetadata Key ->  FTB (KV Key Showable) -> [FTB Showable]
allKVRecL inf m = concat . F.toList . fmap (allKVRec' inf m)

allKVRec' :: InformationSchema -> KVMetadata Key -> TBData Key  Showable -> [FTB Showable]
allKVRec' inf m e =  concat $ fmap snd (L.sortBy (comparing (\i -> maximum $ (`L.elemIndex` _kvdesc m)  <$> fmap _relOrigin (F.toList $ fst i) ))  $ M.toList (go  <$> eitherDescPK m e))
  where
    go (FKT l  rel  tb) = allKVRecL  inf m2 tb
      where
        FKJoinTable _ ref = unRecRel $ fromJust $ L.find (\r-> pathRelRel r  == S.fromList rel)  (_kvjoins m)
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

createUn :: (Show k ,Ord k) => KVMetadata k -> [k] -> [TBData k Showable] -> G.GiST (G.TBIndex Showable) (TBData k Showable)
createUn m un   =  G.fromList  (justError ("empty"  ++ show un) .transPred) .  L.filter (isJust . transPred)
  where transPred =   G.notOptionalM . G.getUnique  un

tablePredicate inf t p = (WherePredicate $ AndColl $ fmap (lookAccess inf t). PrimColl .fixrel <$> p)

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
      ta = M.mapKeys (S.map (keyValue._relOrigin)) (unKV m)

lookAttrM k =  lookAttrsM [k]

fixrel (Inline  i,op) = (Inline i,[(i,op)])
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

data TableModificationK k p
  = TableModification { tableId :: Maybe Int
                      , tableTime :: UTCTime
                      , tableUser :: Text
                      , tableObj :: k
                      , tableDiff :: p
                      }
  -- | NestedModification  (TableModificationK k p) (M.Map (AttributePath Key (AccessOp Key , FTB Showable)) (TableModificationK k p ))
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


