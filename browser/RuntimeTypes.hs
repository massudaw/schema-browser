{-# LANGUAGE FlexibleInstances,FlexibleContexts,DeriveAnyClass,DeriveGeneric,StandaloneDeriving,TypeFamilies,OverloadedStrings,TemplateHaskell,DeriveTraversable,DeriveFoldable,DeriveFunctor,RankNTypes,UndecidableInstances,ExistentialQuantification #-}
module RuntimeTypes where


import Control.Concurrent

import Types
import Control.Exception
import Postgresql.Types
import Data.Time
import Step.Common
import Data.Interval(Interval)
import Debug.Trace
import GHC.Generics
import Data.Unique
import Data.Maybe
import Control.DeepSeq
import Data.Binary
import Types.Index as G
import Control.Concurrent.STM.TQueue
import Control.Concurrent.STM.TMVar
import Control.Concurrent.STM
import Control.Monad.RWS
import Types.Patch
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
import Network.Google.OAuth2
import Control.Lens.TH
import GHC.Stack


metaInf :: TMVar DatabaseSchema -> IO InformationSchema
metaInf smvar = justError "no meta" . HM.lookup "metadata" <$> liftIO ( atomically $ readTMVar .globalRef  =<< readTMVar  smvar )


type InformationSchema = InformationSchemaKV Key Showable
type UserTable = (Int,Text)

data TidingsAffine  a = TA  (R.Behavior a) (R.Event (Index a))


data DatabaseSchema
  = DatabaseSchema
    { schemaIdMap :: M.Map Int Text
    , isRoot :: Bool
    , schemaNameMap  :: HM.HashMap Text Int
    , schemaConn :: Connection
    , globalRef :: TMVar (HM.HashMap Text InformationSchema )
    }



data InformationSchemaKV k v
  = InformationSchema
  { schemaId :: Int
  , schemaName :: Text
  , username :: UserTable
  , authtoken :: Auth
  , _keyMapL :: HM.HashMap (Text,Text) k
  , _backendKey :: Map Unique PGKey
  , _keyUnique :: Map Unique k
  , _pkMapL :: Map (Set k ) Table
  , _tableMapL :: HM.HashMap Text Table
  , tableSize :: Map Table Int
  , mvarMap :: TMVar (Map (TableK k) (DBRef KeyUnique v ))
  , rootconn :: Connection
  , metaschema :: Maybe (InformationSchemaKV k v)
  , depschema :: HM.HashMap Text (InformationSchemaKV k v)
  , schemaOps :: SchemaEditor
  , plugins :: [Plugins ]
  }


recoverKey inf un = justError ("no key " <> show un) $ M.lookup un (_keyUnique inf) <|> deps
  where deps = join $ L.find isJust $ (\i -> M.lookup  un  (_keyUnique i)) <$> F.toList (depschema inf)

backendsKey s = _backendKey s <> Prelude.foldl mappend mempty (fmap (backendsKey .snd)$ HM.toList $ depschema s)

data Auth
  = PostAuth Connection
  | OAuthAuth (Maybe (Text,R.Tidings OAuth2Tokens))

token s = case authtoken s of
      OAuthAuth i -> i
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

type TBF f k v = (KVMetadata k ,Compose  f  (KV (Compose f (TB f))) k v)


tableMap :: InformationSchema -> HM.HashMap Text (HM.HashMap Text Table)
tableMap s = HM.singleton (schemaName s) (_tableMapL s ) <> Prelude.foldl mappend mempty (fmap tableMap  (fmap snd $ HM.toList $ depschema s))

keyMap = _keyMapL
pkMap = _pkMapL

data DBRef k v =
  DBRef  { patchVar :: TChan [RowPatch k v]
         , idxVar :: TVar (Map (WherePredicateK k) (Int,Map Int (PageTokenF  v)))
         , idxChan :: TChan (WherePredicateK k , Int,Int ,PageTokenF  v)
         , collectionState  :: TVar ([SecondaryIndex k v],TableIndex k v)
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
type SecondaryIndex k v = ([k],GiST (TBIndex v) (TBIndex v,[AttributePath k ]))
type TableRep k v  = ([SecondaryIndex k v],TableIndex k v)

applyTableRep
  ::  (NFData k,NFData a,G.Predicates (G.TBIndex   a) , PatchConstr k a)  => TableK k -> TableRep k a -> RowPatch k (Index a) -> Maybe (TableRep k a)
applyTableRep table (sidxs,l) (DropRow patom)
  = Just $ (didxs <$> sidxs, G.delete (create <$> G.notOptional (G.getIndex patom )) G.indexParam  l)
  where
    didxs (un ,sidx)= (un,maybe sidx (\v -> G.delete v G.indexParam sidx ) (G.getUnique un <$> v))
    v = G.lookup (create <$> G.notOptional (G.getIndex patom ))  l
applyTableRep table (sidxs,l) (PatchRow patom@(m,ipa, p)) =  (dixs <$> sidxs ,) <$> applyIfChange l (PatchRow patom)
   where
     dixs (un,sidx) = (un,sidx)--(\v -> G.insert (v,G.getIndex i) G.indexParam sidx ) (G.getUnique un  el))
applyTableRep table (sidxs,l) (CreateRow elp ) =  Just  (didxs <$> sidxs,case G.lookup i l  of
                  Just v ->  if v == el then l else G.insert (el,G.tbpred  el) G.indexParam . G.delete i  G.indexParam $ l
                  Nothing -> G.insert (el,G.tbpred  el) G.indexParam  l)
   where
     didxs (un,sidx) =  (un,G.insert (((G.getIndex el,[]),G.getUnique un  el)) G.indexParam sidx  )
     el = fmap (fmap create) elp
     i = G.notOptional $ G.getIndex el


queryCheckSecond :: (Show k,Ord k) => (WherePredicateK k ,[k])-> TableRep k Showable-> G.GiST (TBIndex  Showable) (TBData k Showable)
queryCheckSecond pred@(b@(WherePredicate bool) ,pk) (s,g) = t1
  where t1 = G.fromList' . maybe id (\pred -> L.filter (flip checkPred (pred) . leafValue)) notPK $ fromMaybe (getEntries  g)  (searchPK  b (pk,g)<|>  searchSIdx)
        searchSIdx = (\sset -> L.filter ((`S.member` sset) .leafPred) $ getEntries g) <$> mergeSIdxs
        notPK = fmap WherePredicate $ F.foldl' (\l i -> flip G.splitIndexPKB  i =<< l ) (Just bool) (pk : fmap fst s )
        mergeSIdxs :: Maybe (S.Set (TBIndex Showable))
        mergeSIdxs = foldl1 S.intersection <$> (nonEmpty $ catMaybes $ fmap (S.fromList . fmap (fst.leafValue)) . searchPK b <$> s)


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
  | BoundedPlugin2  (ArrowReaderM IO)
  | PurePlugin (ArrowReaderM Identity)
  | DiffPurePlugin (ArrowReaderDiffM Identity)
  | DiffIOPlugin (ArrowReaderDiffM IO)

type ArrowReaderDiffM m  = Parser (Kleisli (ReaderT (Maybe (TBData Text Showable)) m )) (Access Text) () (Maybe (Index (TBData Text Showable)))

pluginStatic = pluginStatic' . _plugAction
pluginAction = pluginAction' . _plugAction
pluginActionDiff = pluginActionDiff' . _plugAction

pluginStatic' (BoundedPlugin2  a) = staticP a
pluginStatic' (DiffIOPlugin a) = staticP a
pluginStatic' (DiffPurePlugin a) = staticP a
pluginStatic' (PurePlugin  a) = staticP a

pluginRun b@(BoundedPlugin2 _) = Right (pluginAction' b)
pluginRun b@(PurePlugin _ ) = Right (pluginAction' b)
pluginRun b@(DiffIOPlugin _ ) = Left (pluginActionDiff' b)
pluginRun b@(DiffPurePlugin _ ) = Left (pluginActionDiff' b)

pluginActionDiff' (DiffIOPlugin a ) = fmap join . traverse (dynIO a)
pluginActionDiff' (DiffPurePlugin a ) = fmap join . traverse (fmap return (dynPure a))
pluginAction' (BoundedPlugin2   a ) = fmap join . traverse (dynIO a)
pluginAction' (PurePlugin  a) = fmap join . traverse ((fmap return) (dynPure a ))

staticP ~(P s d) = s

dynIO url inp = do
    runReaderT (dynPK url ()) (Just inp)

dynPure url inp = runIdentity $ do
    dynIO url inp

dynP ~(P s d) = d

dynPK =  runKleisli . dynP


type TransactionM = RWST InformationSchema [TableModification (RowPatch Key Showable)] (Map (Table,WherePredicate) (DBVar,Collection Key Showable)) R.Dynamic

type PageToken = PageTokenF Showable

deriving instance (Binary v) => Binary (PageTokenF  v)
deriving instance (NFData v) => NFData (PageTokenF  v)

data PageTokenF v
  = PageIndex Int
  | NextToken Text
  | TableRef [Interval (FTB v)]
  | HeadToken
  deriving(Eq,Ord,Show,Generic)


data OverloadedRule
  =  CreateRule  (TBData Key Showable -> TransactionM (Maybe (TableModification (RowPatch Key Showable))))
  |  DropRule  (TBData Key Showable -> TransactionM (Maybe (TableModification (RowPatch Key Showable))))
  |  UpdateRule  (TBData Key Showable -> TBData Key Showable -> TransactionM (Maybe (TableModification (RowPatch Key Showable))))

data SchemaEditor
  = SchemaEditor
  { editEd  :: TBData Key Showable -> TBData Key Showable -> TransactionM (Maybe (TableModification (RowPatch Key Showable)))
  , patchEd :: TBIdx Key Showable -> TransactionM (Maybe (TableModification (RowPatch Key Showable)))
  , insertEd :: TBData Key Showable -> TransactionM (Maybe (TableModification (RowPatch Key Showable)))
  , deleteEd :: TBData Key Showable -> TransactionM (Maybe (TableModification (RowPatch Key Showable)))
  , listEd :: TBF (Labeled Text) Key () -> Maybe Int -> Maybe PageToken -> Maybe Int -> [(Key,Order)] -> WherePredicate -> TransactionM ([TBData Key Showable],Maybe PageToken,Int)
  , getEd :: Table -> TBData Key Showable -> TransactionM (Maybe (TBIdx Key Showable))
  , typeTransform :: PGKey -> CoreKey
  , joinListEd :: [(Table,TBData Key Showable, Path (Set Key ) SqlOperation )]  -> Table -> Maybe Int -> Maybe PageToken -> Maybe Int -> [(Key,Order)] -> WherePredicate -> TransactionM ([TBData Key Showable],Maybe PageToken,Int)
  , joinSyncEd :: [(Table,TBData Key Showable, Path (Set Key ) SqlOperation )] -> [(Text ,Column Key Showable)]  -> Table -> Maybe Int -> Maybe PageToken -> Maybe Int -> [(Key,Order)] -> WherePredicate -> TransactionM ([TBData Key Showable],Maybe PageToken,Int)
  ,logger :: MonadIO m => InformationSchema -> TableModification (RowPatch Key Showable)  -> m (TableModification (RowPatch Key Showable))
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

lookTable :: InformationSchema -> Text -> Table
lookTable inf t = justError ("no table: " <> T.unpack t) $ HM.lookup t (_tableMapL inf)

lookTableM :: InformationSchema -> Text -> Maybe Table
lookTableM inf t =  HM.lookup t (_tableMapL inf)

lookSTable :: InformationSchema -> (Text,Text) -> Table
lookSTable inf (s,t) = justError ("no table: " <> T.unpack t) $ join $ HM.lookup t <$> HM.lookup s (tableMap inf)

lookKey :: InformationSchema -> Text -> Text -> Key
lookKey inf t k = justError ("table " <> T.unpack t <> " has no key " <> T.unpack k  <> show (HM.toList (keyMap inf))) $ HM.lookup (t,k) (keyMap inf)

lookKeyM :: InformationSchema -> Text -> Text -> Maybe Key
lookKeyM inf t k =  HM.lookup (t,k) (keyMap inf)

putPatch m a= liftIO$ do
  i <- getCurrentTime
  print ("putPatch",i,length a)
  atomically $ putPatchSTM m a

putPatchSTM m =  writeTChan m . force. fmap (firstPatchRow keyFastUnique)
putIdx m = liftIO .atomically . writeTChan m . force


liftTable' :: InformationSchema -> Text -> TBData Text a -> TBData Key a
liftTable' inf tname (_,v)   = (tableMeta ta,) $ mapComp (\(KV i) -> KV $ mapFromTBList $ mapComp (liftField inf tname) <$> F.toList i) v
  where
                  ta = lookTable inf tname


liftKeys
  :: InformationSchema
     -> Text
     -> FTB1 Identity Text a
     -> FTB1 Identity Key a
liftKeys inf tname = fmap (liftTable' inf tname)

findRefTable inf tname rel2 =  tname2

  where   (FKJoinTable  _ (_,tname2) )  = (unRecRel.pathRel) $ justError (show (rel2 ,rawFKS ta)) $ L.find (\(Path i _ )->  S.map (keyValue) i == S.fromList (_relOrigin <$> rel2))  (F.toList$ rawFKS  ta)
          ta = lookTable inf tname



liftField :: InformationSchema -> Text -> Column Text a -> Column Key a
liftField inf tname (Attr t v) = Attr (lookKey inf tname t) v
liftField inf tname (FKT ref  rel2 tb) = FKT (mapBothKV (lookKey inf tname ) (mapComp (liftField inf tname) ) ref)   ( rel) (liftKeys rinf tname2 tb)
    where FKJoinTable  rel (schname,tname2)  = unRecRel $ pathRel $ justError (show (rel2 ,rawFKS ta)) $ L.find (\(Path i _ )->  S.map keyValue i == S.fromList (_relOrigin <$> rel2))  (F.toList$ rawFKS  ta)
          rinf = fromMaybe inf (HM.lookup schname (depschema inf))
          ta = lookTable inf tname
liftField inf tname (IT rel tb) = IT (lookKey inf tname  rel) (liftKeys inf tname2 tb)
  where FKInlineTable (_,tname2)  = unRecRel. pathRel  $ justError (show (rel ,rawFKS ta)) $ L.find (\r@(Path i _ )->  S.map (fmap keyValue ) (pathRelRel r) == S.singleton (Inline rel))  (F.toList$ rawFKS  ta)
        ta = lookTable inf tname

liftPatchRow inf t (PatchRow i) = PatchRow $ liftPatch inf t i
liftPatchRow inf t (CreateRow i) = CreateRow $ liftTable' inf t i
liftPatchRow inf t (DropRow i) = DropRow $ liftTable' inf t i

liftPatch :: a ~ Index a => InformationSchema -> Text -> TBIdx Text a -> TBIdx Key a
liftPatch inf t (_ , k ,p) = (tableMeta ta ,  k,fmap (liftPatchAttr inf t) p)
  where ta = lookTable inf t


liftPatchAttr :: a ~ Index a => InformationSchema -> Text -> PathAttr Text a -> Index (Column Key a)
liftPatchAttr inf t p@(PAttr k v ) =  PAttr (lookKey inf t k)  v
liftPatchAttr inf tname p@(PInline rel e ) =  PInline ( lookKey inf tname rel) ((liftPatch inf tname2 ) <$>  e)
    where Just (FKInlineTable (_,tname2)) = fmap (unRecRel.pathRel) $ L.find (\r@(Path i _ )->  S.map (fmap keyValue ) (pathRelRel r) == S.singleton (Inline (rel)) )  (F.toList$ rawFKS  ta)
          ta = lookTable inf tname
liftPatchAttr inf tname p@(PFK rel2 pa  b ) =  PFK rel (fmap (liftPatchAttr inf tname) pa)  (fmap (liftPatch rinf tname2 ) $ b)
    where (FKJoinTable  rel (schname,tname2) )  = (unRecRel.pathRel) $ justError (show (rel2 ,rawFKS ta)) $ L.find (\(Path i _ )->  S.map keyValue i == S.fromList (_relOrigin <$> rel2))  (F.toList$ rawFKS  ta)
          ta = lookTable inf tname
          rinf = fromMaybe inf (HM.lookup schname (depschema inf))


fixPatchRow inf t (PatchRow i) = PatchRow $ fixPatch inf  t i
fixPatchRow inf t (CreateRow i) = CreateRow i
fixPatchRow inf t (DropRow i) = DropRow i

fixPatch ::  a ~ Index a => InformationSchema -> Text -> TBIdx Key a  -> TBIdx Key a
fixPatch inf t (i , k ,p) = (i,k,fmap (fixPatchAttr inf t) p)
  where
    fixPatchAttr ::  InformationSchema -> Text -> PathAttr Key a -> PathAttr Key a
    fixPatchAttr inf t p@(PAttr _ _ ) =  p
    fixPatchAttr inf tname p@(PInline rel e ) =  PInline rel (fmap (\(_,o,v)-> (tableMeta $ lookTable inf tname2,o,fmap (fixPatchAttr  inf tname2 )v)) e)
        where Just (FKInlineTable (_,tname2)) = fmap (unRecRel.pathRel) $ L.find (\r@(Path i _ )->  S.map (fmap keyValue ) (pathRelRel r) == S.singleton (Inline (keyValue rel)) )  (F.toList$ rawFKS  ta)
              ta = lookTable inf tname
    fixPatchAttr inf tname p@(PFK rel2 pa  b ) =  PFK rel2 (fmap (fixPatchAttr inf tname) pa)  b
        where (FKJoinTable  _ (schname,tname2) )  = (unRecRel.pathRel) $ justError (show (rel2 ,rawFKS ta)) $ L.find (\(Path i _ )->  i == S.fromList (_relOrigin <$> rel2))  (F.toList$ rawFKS  ta)
              ta = lookTable inf tname
              rinf = fromMaybe inf (HM.lookup schname (depschema inf))
    fixPatchAttr inf tname p@(PFun k _ b ) =  PFun ki (expr,a) b
      where (FunctionField ki expr a )   = (unRecRel.pathRel) $ justError (show (k,rawFKS ta)) $ L.find (\(Path i _ )->  i == S.singleton(k))  (F.toList$ rawFKS  ta)
            ta = lookTable inf tname
liftAccessM :: InformationSchema -> Text -> Access Text  -> Maybe (Access Key)
liftAccessM inf tname (Point i  ) =  Just $ Point i
liftAccessM inf tname (Rec i j ) =  Rec i <$> (liftAccessM inf tname  j)
liftAccessM inf tname (ISum i) =  ISum <$> traverse (liftAccessM inf tname)  i
liftAccessM inf tname (Many i) =  Many <$> traverse (liftAccessM inf tname)  i
liftAccessM inf tname (IProd b l) = IProd b <$> traverse  (lookKeyM inf tname) l
liftAccessM inf tname (Nested i c) = Nested <$> ref <*> join (fmap (\ l -> liftAccessM inf  (snd (proj l)) c ) n)
  where
    ref = liftAccessM inf tname i
    tb = lookTable inf tname
    n = join $ (\(IProd _ refk )-> L.find (\i -> S.fromList refk == (S.map _relOrigin $ pathRelRel i) ) (rawFKS tb)) <$> ref
    proj n = case n of
          (Path _ rel@(FKJoinTable  _ l  ) ) ->  l
          (Path _ rel@(FKInlineTable  l  ) ) ->  l

liftAccessM _ _ i = errorWithStackTrace (show i)



liftAccess :: InformationSchema -> Text -> Access Text  -> Access Key
liftAccess inf tname (Point i  ) =  Point i
liftAccess inf tname (Rec i j ) =  Rec i (liftAccess inf tname  j)
liftAccess inf tname (ISum i) =  ISum $ fmap (liftAccess inf tname)  i
liftAccess inf tname (Many i) =  Many $ fmap (liftAccess inf tname)  i
liftAccess inf tname (IProd b l) = IProd b $ fmap (lookKey inf tname) l
liftAccess inf tname (Nested i c) = Nested ref (liftAccess rinf (snd l) c)
  where
    rinf = fromMaybe inf (HM.lookup  (fst l) (depschema inf))
    ref@(IProd _ refk) = liftAccess inf tname i
    tb = lookTable inf tname
    n = justError ("no fk " ++ show (i,refk,rawFKS tb) )$ L.find (\i -> S.fromList refk == (S.map _relOrigin $ pathRelRel i) ) (rawFKS tb)
    l = case n of
          (Path _ rel@(FKJoinTable  _ l  ) ) ->  l
          (Path _ rel@(FKInlineTable  l  ) ) ->  l

liftAccess _ _ i = errorWithStackTrace (show i)


lookAccess :: InformationSchema -> Text -> (Access Text , AccessOp Showable ) -> (Access Key, AccessOp Showable )
lookAccess inf tname l = Le.over (Le._1) (liftAccess inf tname)  l


genPredicateFull i (Rec _ _) = Nothing  -- AndColl <$> (nonEmpty $ catMaybes $ genPredicateFull i <$> l)
genPredicateFull i (Point _) = Nothing -- AndColl <$> (nonEmpty $ catMaybes $ genPredicateFull i <$> l)
genPredicateFull i (Many l) = AndColl <$> (nonEmpty $ catMaybes $ genPredicateFull i <$> l)
genPredicateFull i (ISum l) = OrColl <$> (nonEmpty $ catMaybes $ genPredicateFull i <$> l)
genPredicateFull i (IProd b l) =  (\i -> PrimColl (IProd b l,Right i ))  <$> b
genPredicateFull i n@(Nested p@(IProd _ _ ) l ) = fmap (\(a,b) -> (Nested p a , b )) <$> genPredicateFull i l
genPredicateFull _ i = errorWithStackTrace (show i)

notException e =  if isJust eb || isJust es || isJust as then Nothing else Just e
  where
    eb :: Maybe BlockedIndefinitelyOnMVar
    eb = fromException e
    as :: Maybe AsyncException
    as = fromException e
    es :: Maybe BlockedIndefinitelyOnSTM
    es = fromException e


makeLenses ''InformationSchemaKV
