{-# LANGUAGE FlexibleInstances,FlexibleContexts,DeriveAnyClass,DeriveGeneric,StandaloneDeriving,TypeFamilies,OverloadedStrings,TemplateHaskell,DeriveTraversable,DeriveFoldable,DeriveFunctor,RankNTypes,ExistentialQuantification #-}
module RuntimeTypes where

import Control.Concurrent
import Types
import Types.Index as G
import Data.Ord
import Types.Patch
import Text
import qualified Data.IntMap as IM
import Control.Exception
import Postgresql.Types
import Query
import Data.Functor.Constant
import Data.Time
import Step.Common
import Data.Interval(Interval)
import qualified Data.Interval as Interval
import Control.Applicative.Lift
import Debug.Trace
import GHC.Generics
import Data.Unique
import Data.Maybe
import Control.DeepSeq
import Data.Binary
import Control.Concurrent.STM.TQueue
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
import Control.Monad.Writer

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
import Data.Traversable
import Control.Lens.TH
import GHC.Stack


metaInf :: TVar DatabaseSchema -> IO InformationSchema
metaInf smvar = indexSchema smvar "metadata"

indexSchema :: TVar DatabaseSchema -> Text -> IO InformationSchema
indexSchema smvar text = (\m -> justError ("no schema: "  ++ show text ++ " from: " ++ show (HM.keys m)). HM.lookup text $ m)<$> liftIO ( atomically $ readTVar .globalRef  =<< readTVar  smvar )


type InformationSchema = InformationSchemaKV Key Showable
type UserTable = (Int,Text)

data TidingsAffine  a = TA  (R.Behavior a) (R.Event (Index a))

data DatabaseSchema
  = DatabaseSchema
    { schemaIdMap :: M.Map Int Text
    , isRoot :: Bool
    , schemaNameMap  :: HM.HashMap Text Int
    , schemaConn :: Connection
    , globalRef :: TVar (HM.HashMap Text InformationSchema )
    }

type TBRef k s = (Map k (FTB s), TBData k s )

type PTBRef k s = (Map k (FTB s), TBIdx k s )

data InformationSchemaKV k v
  = InformationSchema
  { schemaId :: Int
  , schemaName :: Text
  , schemaColor :: Maybe Text
  , username :: UserTable
  , authtoken :: Auth
  , _keyMapL :: HM.HashMap (Text,Text) k
  , colMap ::  HM.HashMap Text (IM.IntMap k)
  , _backendKey :: Map Unique PGKey
  , _keyUnique :: Map Unique k
  , _pkMapL :: Map (Set k ) Table
  , _tableMapL :: HM.HashMap Text Table
  , tableSize :: Map Table Int
  , mvarMap :: TVar (Map (TableK k) (DBRef KeyUnique v ))
  , rootconn :: Connection
  , metaschema :: Maybe (InformationSchemaKV k v)
  , depschema :: HM.HashMap Text (InformationSchemaKV k v)
  , schemaOps :: SchemaEditor
  , plugins :: [Plugins ]
  , rootRef :: TVar DatabaseSchema
  }

instance Eq InformationSchema where
  i == j = schemaId i == schemaId j

instance Ord InformationSchema where
  compare i j = compare (schemaId i) (schemaId j)

recoverKey inf un = justError ("no key " <> show un) $ M.lookup un (_keyUnique inf) <|> deps
  where deps = join $ L.find isJust $ (M.lookup  un . _keyUnique) <$> F.toList (depschema inf)

backendsKey s = _backendKey s <> Prelude.foldl mappend mempty (fmap (backendsKey .snd)$ HM.toList $ depschema s)

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


tableMap :: InformationSchema -> HM.HashMap Text (HM.HashMap Text Table)
tableMap s = HM.singleton (schemaName s) (_tableMapL s ) <> Prelude.foldl mappend mempty (fmap (tableMap . snd) (HM.toList $ depschema s))

keyMap = _keyMapL
pkMap = _pkMapL

data DBRef k v =
  DBRef  { patchVar :: TChan [RowPatch k v]
         , idxVar :: TVar (Map (WherePredicateK k) (Int,Map Int (PageTokenF  v)))
         , idxChan :: TChan (WherePredicateK k , Int,Int ,PageTokenF  v)
         , collectionState  :: TVar (KVMetadata k, [SecondaryIndex k v],TableIndex k v)
         }

data DBVar2  v=
  DBVar2
  { iniRef :: DBRef Unique v
  , idxTid :: R.Tidings (Map WherePredicate (Int,Map Int (PageTokenF  v)))
  , collectionTid :: R.Tidings (TableIndex Key v)
  , collectionSecondaryTid :: R.Tidings [SecondaryIndex Key v]
  , collectionPatches :: R.Event [RowPatch Key v ]
  }


type IndexMetadata k v = Map (WherePredicateK k) (Int,Map Int (PageTokenF  v))
type TableIndex k v = GiST (TBIndex v) (TBData k v)
type SecondaryIndex k v = ([k],GiST (TBIndex v) (TBIndex v,[AttributePath k ()]))

type TableRep k v  = (KVMetadata k,[SecondaryIndex k v],TableIndex k v)

instance Ord v => Compact (RowPatch k v) where
  compact i =  concat . L.transpose $ compact .  snd <$> groupSplit2  index id i

instance Address (RowPatch k v) where
  type Idx (RowPatch k v ) = TBIndex v
  index (PatchRow (i,_)) =  i
  index (CreateRow (i,_)) =  i
  index (DropRow i) =  i

instance Patch (TBRef Key Showable) where
  type Index (TBRef Key Showable) = (Map Key (FTB Showable),TBIdx Key Showable)
  diff (i,j) (k,l)
    | i == k =  (k ,) <$> diff j l
    | otherwise =  Just (k,patch l)
  patch (i,j) = (i,patch j)
  applyIfChange (i,j) (k,l)
    | i == k = (k,) <$> applyIfChange j l
    | otherwise = (k,) <$> applyIfChange j l
  createIfChange (i,j) = (i,) <$> createIfChange j

type RefTables = (R.Tidings (IndexMetadata CoreKey Showable),Collection CoreKey Showable, R.Tidings (G.GiST (G.TBIndex  Showable) (TBData CoreKey Showable)),R.Tidings [SecondaryIndex CoreKey Showable ], TChan [RowPatch KeyUnique Showable] )

type PKConstraint = [Column CoreKey Showable] -> Bool

type TBConstraint = TBData CoreKey Showable -> Bool

type SelPKConstraint = [([Column CoreKey ()],R.Tidings PKConstraint)]

type SelTBConstraint = [([Column CoreKey ()],R.Tidings TBConstraint)]

type PluginRef a = [(Union (Access Key), R.Tidings (Maybe (Index a)))]

instance (NFData k, NFData a,G.Predicates (G.TBIndex a) , PatchConstr k a) => Patch (KVMetadata k,G.GiST (G.TBIndex  a ) (TBData k a)) where
  type Index (KVMetadata k,G.GiST (G.TBIndex  a ) (TBData k a)  ) = RowPatch k (Index a)
  applyIfChange = applyGiSTChange

instance (NFData k, NFData a,G.Predicates (G.TBIndex a) , PatchConstr k a) => Patch (TableRep k a) where
  type Index (TableRep k a) = RowPatch k (Index a)
  applyIfChange = applyTableRep


applyGiSTChange ::
     (NFData k, NFData a, G.Predicates (G.TBIndex a), PatchConstr k a)
  => (KVMetadata k,G.GiST (G.TBIndex a) (TBData k a))
  -> RowPatch k (Index a)
  -> Maybe (KVMetadata k,G.GiST (G.TBIndex a) (TBData k a))
applyGiSTChange (m,l) (DropRow patom) =
  Just . (m,)$G.delete (create <$> patom) G.indexParam l
applyGiSTChange (m,l) (PatchRow (ipa, patom)) =
  (m,) <$>case G.lookup (G.notOptional i) l of
    Just v -> do
      el <- applyIfChange v patom
      let pkel = G.getIndex m el
      return $
        (if pkel == i
          then G.update (G.notOptional i) (const el)
          else G.insert (el, G.tbpred m el) G.indexParam .
            G.delete (G.notOptional i) G.indexParam) l

    Nothing -> do
      el <- createIfChange patom
      return $ G.insert (el, G.tbpred m el) G.indexParam l
  where
    i = fmap create ipa

applyGiSTChange (m,l) (CreateRow (idx,elp)) =
  (m,) <$> case G.lookup ix  l of
    Just v ->
      Just $
        G.insert (el, ix) G.indexParam . G.delete ix G.indexParam $ l
    Nothing -> Just $ G.insert (el, ix) G.indexParam l
  where
    el = fmap create elp
    ix = create <$> idx


applyTableRep
  ::  (NFData k,NFData a,G.Predicates (G.TBIndex   a) , PatchConstr k a)  => TableRep k a -> RowPatch k (Index a) -> Maybe (TableRep k a)
applyTableRep (m,sidxs,l) (DropRow patom)
  = Just (m,didxs <$> sidxs, G.delete (create <$>  patom ) G.indexParam  l)
  where
    didxs (un ,sidx)= (un,maybe sidx (\v -> G.delete v G.indexParam sidx ) (G.getUnique un <$> v))
    v = G.lookup (create <$>  patom )  l
applyTableRep (m,sidxs,l) (PatchRow patom) =  (m,dixs <$> sidxs ,). snd <$> applyGiSTChange (m,l) (PatchRow patom)
   where
     dixs (un,sidx) = (un,sidx)--(\v -> G.insert (v,G.getIndex i) G.indexParam sidx ) (G.getUnique un  el))
applyTableRep (m,sidxs,l) (CreateRow (ix,elp) ) =  Just  (m,didxs <$> sidxs,case G.lookup i l  of
          Just v ->  if v == el then l else G.insert (el,i) G.indexParam . G.delete i  G.indexParam $ l
          Nothing -> G.insert (el,i) G.indexParam  l)
   where
     didxs (un,sidx) =  (un,G.insert ((G.getIndex m el,[]),G.getUnique un  el) G.indexParam sidx  )
     el = fmap create elp
     i =  create <$> ix

typecheck f a = case f a of
          Pure i -> Right a
          Other (Constant l) ->  Left l

queryCheckSecond :: (Show k,Ord k) => (WherePredicateK k ,[k]) -> TableRep k Showable-> G.GiST (TBIndex  Showable) (TBData k Showable)
queryCheckSecond pred@(b@(WherePredicate bool) ,pk) (m,s,g) = t1
  where t1 = G.fromList' . maybe id (\pred -> L.filter (flip checkPred pred . leafValue)) notPK $ fromMaybe (getEntries  g)  (searchPK  b (pk,g)<|>  searchSIdx)
        searchSIdx = (\sset -> L.filter ((`S.member` sset) .leafPred) $ getEntries g) <$> mergeSIdxs
        notPK = WherePredicate Control.Applicative.<$> F.foldl' (\l i -> flip G.splitIndexPKB  i =<< l ) (Just bool) (pk : fmap fst s )
        mergeSIdxs :: Maybe (S.Set (TBIndex Showable))
        mergeSIdxs = foldl1 S.intersection <$> nonEmpty (catMaybes $ fmap (S.fromList . fmap (fst.leafValue)) . searchPK b <$> s)


searchPK ::  (Show k,Eq k) => WherePredicateK k -> ([k],G.GiST (TBIndex  Showable) a ) -> Maybe [LeafEntry (TBIndex  Showable) a]
searchPK (WherePredicate b) (pk, g)= (\p -> G.queryL (mapPredicate (\i -> justError "no predicate pk " $ L.elemIndex i pk)  $ WherePredicate p) g) <$>  splitIndexPK b pk


type DBVar = DBVar2 Showable
type Collection k v = (Map (WherePredicateK k) (Int,Map Int (PageTokenF  v)),GiST (TBIndex   v ) (TBData k v))

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
  = StatefullPlugin [(([VarDef ],[VarDef]),FPlugAction k) ]
  | IOPlugin  (ArrowReaderM IO)
  | PurePlugin (ArrowReaderM Identity)
  | DiffPurePlugin (ArrowReaderDiffM Identity)
  | DiffIOPlugin (ArrowReaderDiffM IO)

type ArrowReaderDiffM m  = Parser (Kleisli (ReaderT (TBData Text Showable) m )) (Union (Access Text)) () (Maybe (Index (TBData Text Showable)))


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


type TransactionM = RWST InformationSchema [TableModification (RowPatch Key Showable)] (Map (Table,WherePredicate) (DBVar,Collection Key Showable)) R.Dynamic

type PageToken = PageTokenF Showable

deriving instance (Binary v) => Binary (PageTokenF  v)
deriving instance (NFData v) => NFData (PageTokenF  v)

newtype PageTokenF v
  = TableRef (Interval (TBIndex v))
  deriving(Eq,Ord,Show,Generic)


data OverloadedRule
  =  CreateRule  (TBData Key Showable -> TransactionM (Maybe (TableModification (RowPatch Key Showable))))
  |  DropRule  (TBData Key Showable -> TransactionM (Maybe (TableModification (RowPatch Key Showable))))
  |  UpdateRule  (TBData Key Showable -> TBIdx Key Showable -> TransactionM (Maybe (TableModification (RowPatch Key Showable))))

data SchemaEditor
  = SchemaEditor
  { editEd  :: KVMetadata Key -> TBData Key Showable -> TBIndex Showable -> TBIdx Key Showable -> TransactionM (Maybe (TableModification (RowPatch Key Showable)))
  , patchEd :: KVMetadata Key ->TBIndex Showable ->TBIdx Key Showable -> TransactionM (Maybe (TableModification (RowPatch Key Showable)))
  , insertEd :: KVMetadata Key ->TBData Key Showable -> TransactionM (Maybe (TableModification (RowPatch Key Showable)))
  , deleteEd :: KVMetadata Key -> TBData Key Showable -> TransactionM (Maybe (TableModification (RowPatch Key Showable)))
  , listEd :: KVMetadata Key ->TBData  Key () -> Maybe Int -> Maybe PageToken -> Maybe Int -> [(Key,Order)] -> WherePredicate -> TransactionM ([TBData Key Showable],PageToken,Int)
  , getEd :: Table -> TBData Key Showable -> TransactionM (Maybe (TBIdx Key Showable))
  , typeTransform :: PGKey -> CoreKey
  , joinListEd :: [(Table,TBData Key Showable, SqlOperation )]  -> Table -> Maybe Int -> Maybe PageToken -> Maybe Int -> [(Key,Order)] -> WherePredicate -> TransactionM ([TBData Key Showable],Maybe PageToken,Int)
  , joinSyncEd :: [(Table,TBData Key Showable, SqlOperation )] -> [(Text ,Column Key Showable)]  -> Table -> Maybe Int -> Maybe PageToken -> Maybe Int -> [(Key,Order)] -> WherePredicate -> TransactionM ([TBData Key Showable],Maybe PageToken,Int)
  , logger :: forall m . MonadIO m => InformationSchema -> TableModification (RowPatch Key Showable)  -> m (TableModification (RowPatch Key Showable))
  , opsPageSize :: Int
  , transactionEd :: InformationSchema -> (forall a  . IO a -> IO a)
  , rules :: M.Map (Text,Text) [OverloadedRule]
  , historySync :: Maybe (TransactionM ())
  }

typeTrans inf = typeTransform (schemaOps inf)


argsToState  [h,ph,d,u,p,s,m,t,o] = BrowserState h ph d  u p (Just s) (Just t ) (Just ( Non.fromList . fmap (fmap (T.drop 1) . T.break (=='=') )$ T.split (==',') (T.pack o)))
argsToState  [h,ph,d,u,p,s,m,t] = BrowserState h ph d  u p (Just s) (Just t ) Nothing
argsToState  [h,ph,d,u,p,s,m] = BrowserState h ph d  u p  (Just s)  Nothing Nothing
argsToState  [h,ph,d,u,p,s] = BrowserState h ph d  u p  (Just s)  Nothing Nothing
argsToState  [h,ph,d,u,p] = BrowserState h ph d  u p Nothing Nothing Nothing
argsToState i = errorWithStackTrace (show i)

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

putPatch m a= liftIO$ do
  atomically $ putPatchSTM m a

putPatchSTM m =  writeTChan m . force. fmap (firstPatchRow keyFastUnique)
putIdx m = liftIO .atomically . writeTChan m . force

typeCheckValuePrim f (KOptional :i) (LeftTB1 j) = maybe (Pure ()) (typeCheckValuePrim f i) j
typeCheckValuePrim f (KDelayed :i) (LeftTB1 j) = maybe (Pure ()) (typeCheckValuePrim f i) j
typeCheckValuePrim f (KSerial :i) (LeftTB1 j) = maybe (Pure ()) (typeCheckValuePrim f i) j
typeCheckValuePrim f (KArray :i )  (ArrayTB1 l) = F.foldl' (liftA2 const ) (Pure () ) (typeCheckValuePrim f i<$>  l)
typeCheckValuePrim f (KInterval : i) (IntervalTB1 j) = const <$> maybe (Pure ()) (typeCheckValuePrim f i)  (unFin $ Interval.lowerBound j)  <*> maybe (Pure ()) (typeCheckValuePrim f i) (unFin $ Interval.upperBound j)
typeCheckValuePrim f []  (TB1 j) = f j
typeCheckValuePrim f i j = failure ["cant match " ++ show i ++ " with " ++ show j ]

typeCheckValue f (Primitive l i)  j = mapError (fmap (("At " ++ show l ++ " : " ++ show i)++)) $ typeCheckValuePrim (f i) l j

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
typeCheckPrim PDynamic (SDynamic i ) = Pure ()
typeCheckPrim (PTypeable _) (SHDynamic i ) = Pure ()
typeCheckPrim (PMime _ ) (SBinary i ) = Pure ()
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
lookupKeyPosition= (lookKeyPosition , keyPosition)


liftTableF ::  (Show k ,Ord k) => LookupKey k -> InformationSchema ->  Text -> TBData k a -> TBData Key a
liftTableF f inf  tname v   =  (\(KV i) -> KV $ mapFromTBList $ liftFieldF  f inf  tname <$> F.toList i) v
  where
    ta = lookTable inf tname



liftTable' :: InformationSchema -> Text -> TBData Text a -> TBData Key a
liftTable' = liftTableF lookupKeyName


liftKeys
  :: InformationSchema
     -> Text
     -> FTB1 Text a
     -> FTB1 Key a
liftKeys inf tname = fmap (liftTable' inf tname)

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
liftFieldF (f,p) inf tname (Fun  k t v) = Fun (f inf tname k ) (fmap(liftAccessF (f,p) inf tname )<$> t) v



liftField :: InformationSchema -> Text -> Column Text a -> Column Key a
liftField = liftFieldF lookupKeyName

liftPatchRow inf t (PatchRow (k,i)) = PatchRow (k,liftPatch inf t i)
liftPatchRow inf t (CreateRow (ix,i)) = CreateRow (ix,liftTable' inf t i)
liftPatchRow inf t (DropRow i) = DropRow   i

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


fixPatchRow inf t (PatchRow (k,i)) = PatchRow (k,fixPatch inf  t i)
fixPatchRow inf t (CreateRow i) = CreateRow i
fixPatchRow inf t (DropRow i) = DropRow i

fixPatch ::   InformationSchema -> Text -> TBIdx Key a  -> TBIdx Key a
fixPatch _ _ =id


liftAccessM ::  InformationSchema -> Text -> Access Text  -> Maybe (Access Key)
liftAccessM inf tname (Point i  ) =  Just $ Point i
liftAccessM inf tname (Rec i j ) =  Rec i <$> liftAccessMU inf tname  j
liftAccessM inf tname (IProd b l) = IProd b  <$> lookKeyM inf tname l
liftAccessM inf tname (Nested i c) = Nested <$> ref <*> join (fmap (\ l -> liftAccessMU inf  (snd (proj l)) c ) n)
  where
    ref = traverse (liftAccessM inf tname) i
    tb = lookTable inf tname
    n = join $ (\ ref -> L.find (\i -> S.fromList (iprodRef <$> ref) == S.map _relOrigin (pathRelRel i) ) (rawFKS tb)) <$> ref
    proj n = case n of
          FKJoinTable  _ l   ->  l
          FKInlineTable  _ l   ->  l

liftAccessM _ _ i = errorWithStackTrace (show i)


liftAccessMU inf tname (ISum i) =  ISum <$> traverse (liftAccessMU inf tname)  i
liftAccessMU inf tname (Many i) =  Many <$> traverse (liftAccessMU inf tname)  i
liftAccessMU inf tname (One i) =  One <$> liftAccessM inf tname  i

liftAccessF :: (Show k ,Ord k) => LookupKey k ->InformationSchema -> Text -> Access k-> Access Key
liftAccessF lk inf tname (Point i  ) =  Point i
liftAccessF lk inf tname (Rec i j ) =  Rec i (liftAccessF lk inf tname  <$> j)
liftAccessF lk inf tname (IProd b l) = IProd b $ fst lk inf tname l
liftAccessF lk inf tname (Nested i c) = Nested ref (liftAccessF lk rinf (snd l)<$> c)
  where
    rinf = fromMaybe inf (HM.lookup  (fst l) (depschema inf))
    ref = liftAccessF lk inf tname <$> i
    tb = lookTable inf tname
    n = justError ("no fk " ++ show (i,ref,rawFKS tb) )$ L.find (\i -> S.fromList (iprodRef <$> ref)== S.map _relOrigin (pathRelRel i) ) (rawFKS tb)
    l = case n of
          FKJoinTable  _ l   ->  l
          FKInlineTable  _ l   ->  l
liftAccessF _ _ _  i = errorWithStackTrace (show i)

liftAccess = liftAccessF lookupKeyName

liftAccessU inf t = fmap (liftAccess inf t )

lookAccess :: InformationSchema -> Text -> (Access Text , AccessOp Showable ) -> (Access Key, AccessOp Showable )
lookAccess inf tname l = Le.over Le._1 (liftAccess inf tname)  l


genPredicateFull
  :: Show a =>
     t
     -> Access a
     -> Maybe (BoolCollection (Access a, Either a1 UnaryOperator))
genPredicateFull i (Rec _ _) = Nothing  -- AndColl <$> (nonEmpty $ catMaybes $ genPredicateFull i <$> l)
genPredicateFull i (Point _) = Nothing -- AndColl <$> (nonEmpty $ catMaybes $ genPredicateFull i <$> l)
genPredicateFull i (IProd b l) =  (\i -> PrimColl (IProd b l,Right i ))  <$> b
genPredicateFull i (Nested p l) = fmap (\(a,b) -> (Nested p (Many[One a]) , b )) <$> genPredicateFullU i l
genPredicateFull _ i = errorWithStackTrace (show i)

genPredicateFullU
  :: Show a =>
     t
     -> Union (Access a)
     -> Maybe (BoolCollection (Access a, Either a1 UnaryOperator))
genPredicateFullU i (Many l) = AndColl <$> nonEmpty (catMaybes $ genPredicateFullU i <$> l)
genPredicateFullU i (ISum l) = OrColl <$> nonEmpty (catMaybes $ genPredicateFullU i <$> l)
genPredicateFullU i (One l) = genPredicateFull i  l


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

allKVRec :: InformationSchema -> KVMetadata Key ->  TB2 Key Showable -> [FTB Showable]
allKVRec inf m = concat . F.toList . fmap (allKVRec' inf m)

allKVRec' :: InformationSchema -> KVMetadata Key -> TBData Key  Showable -> [FTB Showable]
allKVRec' inf m e=  concatMap snd (L.sortBy (comparing (\i -> maximum $ (`L.elemIndex` _kvdesc m)  <$> fmap _relOrigin (F.toList $ fst i) ))  $ M.toList (go  <$> eitherDescPK m e))
  where
    go (FKT _  rel  tb) =  allKVRec  inf (tableMeta ta) tb
      where
        FKJoinTable  _ ref  = unRecRel $ fromJust $ L.find (\r-> pathRelRel r  == S.fromList rel)  (_kvjoins m)
        ta = lookSTable inf ref

    go (IT  it tb) = allKVRec inf ms tb
      where
        ms = lookSMeta inf  k
        k = _keyAtom $ keyType it
    go (Attr _ a) = [a]

createRow' m v = CreateRow (G.getIndex m v,v)
dropRow' m v = DropRow (G.getIndex m v)

makeLenses ''InformationSchemaKV
