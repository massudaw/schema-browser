{-# LANGUAGE DeriveAnyClass,DeriveGeneric,StandaloneDeriving,TypeFamilies,OverloadedStrings,TemplateHaskell,DeriveTraversable,DeriveFoldable,DeriveFunctor,RankNTypes,ExistentialQuantification #-}
module RuntimeTypes where


import Control.Concurrent

import Types
import Step.Common
import GHC.Generics
import Data.Unique
import Data.Maybe
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
import Data.Text
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


metaInf :: DatabaseSchema -> IO InformationSchema
metaInf smvar = justError "no meta" . HM.lookup "metadata" <$> liftIO ( readMVar (globalRef smvar))


type InformationSchema = InformationSchemaKV Key Showable
data DatabaseSchema
  = DatabaseSchema
    { schemaIdMap :: M.Map Int Text
    , schemaNameMap  :: HM.HashMap Text Int
    , schemaConn :: Connection
    , globalRef :: MVar (HM.HashMap Text InformationSchema )
    }
data InformationSchemaKV k v
  = InformationSchema
  { schemaId :: Int
  , schemaName :: Text
  , username :: (Int,Text)
  , authtoken :: Auth
  , _keyMapL :: HM.HashMap (Text,Text) k
  , _backendKey :: Map Unique PGKey
  , _pkMapL :: Map (Set k ) Table
  , _tableMapL :: HM.HashMap Text Table
  , tableSize :: Map Table Int
  , mvarMap :: TMVar (Map (KVMetadata k) (DBVar2 k v ))
  , rootconn :: Connection
  , metaschema :: Maybe (InformationSchemaKV k v)
  , depschema :: HM.HashMap Text (InformationSchemaKV k v)
  , schemaOps :: SchemaEditor
  , plugins :: [Plugins ]
  }

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

data DBVar2 k v=
  DBVar2
  { patchVar :: TQueue [TBIdx k v]
  , idxVar :: TMVar (Map WherePredicate (Int,Map Int (PageTokenF k v)))
  , idxVarLoad :: TMVar (GiST (WherePredicate ,G.Predicate Int) ())
  , patchTid :: R.Tidings [TBIdx k v]
  , idxTid :: R.Tidings (Map WherePredicate (Int,Map Int (PageTokenF k v)))
  , collectionTid :: R.Tidings (TableIndex k v )
  }


idxColTid db =  (,) <$> idxTid db <*> collectionTid db

type DBVar = DBVar2 Key Showable
type Collection k v = (Map WherePredicate (Int,Map Int (PageTokenF k v)),GiST (TBIndex k  v ) (TBData k v))
type TableIndex k v = GiST (TBIndex k  v ) (TBData k v)

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
  | BoundedPlugin2  ( ArrowReaderM IO)
  | PurePlugin (ArrowReaderM Identity)


pluginStatic = pluginStatic' . _plugAction
pluginAction = pluginAction' . _plugAction

pluginStatic' (BoundedPlugin2  a) = staticP a
pluginStatic' (PurePlugin  a) = staticP a
pluginAction' (BoundedPlugin2   a ) = fmap join . traverse (dynIO a)
pluginAction' (PurePlugin  a) = fmap join . traverse ((fmap return) (dynPure a ))

staticP ~(P s d) = s

dynIO url inp = do
    runReaderT (dynPK url ()) (Just inp)

dynPure url inp = runIdentity $ do
    dynIO url inp

dynP ~(P s d) = d

dynPK =  runKleisli . dynP


type TransactionM = RWST InformationSchema [TableModification (TBIdx Key Showable)] (Map (Table,WherePredicate) (TableIndex Key Showable))  IO

type PageToken = PageTokenF Key Showable

deriving instance (Binary v,Binary k) => Binary (PageTokenF k v)

data PageTokenF k v
  = PageIndex Int
  | NextToken Text
  | TableRef [(k, FTB v)]
  | HeadToken
  deriving(Eq,Ord,Show,Generic)


data SchemaEditor
  = SchemaEditor
  { editEd  :: TBData Key Showable -> TBData Key Showable -> TransactionM (Maybe (TableModification (TBIdx Key Showable)))
  , patchEd :: TBIdx Key Showable -> TransactionM (Maybe (TableModification (TBIdx Key Showable)))
  , insertEd :: TBData Key Showable -> TransactionM (Maybe (TableModification (TBIdx Key Showable)))
  , deleteEd :: TBData Key Showable -> TransactionM (Maybe (TableModification (TBIdx Key Showable)))
  , listEd :: TBF (Labeled Text) Key () -> Maybe Int -> Maybe PageToken -> Maybe Int -> [(Key,Order)] -> WherePredicate -> TransactionM ([TBData Key Showable],Maybe PageToken,Int)
  , getEd :: Table -> TBData Key Showable -> TransactionM (Maybe (TBIdx Key Showable))
  , typeTransform :: PGKey -> CoreKey
  , joinListEd :: [(Table,TBData Key Showable, Path (Set Key ) SqlOperation )]  -> Table -> Maybe Int -> Maybe PageToken -> Maybe Int -> [(Key,Order)] -> WherePredicate -> TransactionM ([TBData Key Showable],Maybe PageToken,Int)
  , joinSyncEd :: [(Table,TBData Key Showable, Path (Set Key ) SqlOperation )] -> [(Text ,Column Key Showable)]  -> Table -> Maybe Int -> Maybe PageToken -> Maybe Int -> [(Key,Order)] -> WherePredicate -> TransactionM ([TBData Key Showable],Maybe PageToken,Int)
  ,logger :: InformationSchema -> TableModification (TBIdx Key Showable)  -> IO (TableModification (TBIdx Key Showable))
  , opsPageSize :: Int
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

lookSTable :: InformationSchema -> (Text,Text) -> Table
lookSTable inf (s,t) = justError ("no table: " <> T.unpack t) $ join $ HM.lookup t <$> HM.lookup s (tableMap inf)

lookKey :: InformationSchema -> Text -> Text -> Key
lookKey inf t k = justError ("table " <> T.unpack t <> " has no key " <> T.unpack k  <> show (HM.toList (keyMap inf))) $ HM.lookup (t,k) (keyMap inf)


putPatch m = atomically . writeTQueue m -- . force


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
    where FKInlineTable (_,tname2)  = unRecRel.pathRel  $ justError (show (rel ,rawFKS ta)) $ L.find (\r@(Path i _ )->  S.map (fmap keyValue ) (pathRelRel r) == S.singleton (Inline rel))  (F.toList$ rawFKS  ta)
          ta = lookTable inf tname

liftPatch :: a ~ Index a => InformationSchema -> Text -> TBIdx Text a -> TBIdx Key a
liftPatch inf t (_ , k ,p) = (tableMeta ta ,G.mapKeys (lookKey inf t )  k,fmap (liftPatchAttr inf t) p)
  where ta = lookTable inf t


liftPatchAttr :: a ~ Index a => InformationSchema -> Text -> PathAttr Text a -> Index (Column Key a)
liftPatchAttr inf t p@(PAttr k v ) =  PAttr (lookKey inf t k)  v
liftPatchAttr inf tname p@(PInline rel e ) =  PInline ( lookKey inf tname rel) ((liftPatch inf tname2 ) <$>  e)
    where Just (FKInlineTable (_,tname2)) = fmap (unRecRel.pathRel) $ L.find (\r@(Path i _ )->  S.map (fmap keyValue ) (pathRelRel r) == S.singleton (Inline (rel)) )  (F.toList$ rawFKS  ta)
          ta = lookTable inf tname
liftPatchAttr inf tname p@(PFK rel2 pa t b ) =  PFK rel (fmap (liftPatchAttr inf tname) pa) (tableMeta $ lookTable rinf tname2) (fmap (liftPatch rinf tname2 ) $ b)
    where (FKJoinTable  rel (schname,tname2) )  = (unRecRel.pathRel) $ justError (show (rel2 ,rawFKS ta)) $ L.find (\(Path i _ )->  S.map keyValue i == S.fromList (_relOrigin <$> rel2))  (F.toList$ rawFKS  ta)
          ta = lookTable inf tname
          rinf = fromMaybe inf (HM.lookup schname (depschema inf))


fixPatch ::  a ~ Index a => InformationSchema -> Text -> TBIdx Key a  -> TBIdx Key a
fixPatch inf t (i , k ,p) = (i,k,fmap (fixPatchAttr inf t) p)
  where
    fixPatchAttr ::  InformationSchema -> Text -> PathAttr Key a -> PathAttr Key a
    fixPatchAttr inf t p@(PAttr _ _ ) =  p
    fixPatchAttr inf tname p@(PInline rel e ) =  PInline rel (fmap (\(_,o,v)-> (tableMeta $ lookTable inf tname2,o,fmap (fixPatchAttr  inf tname2 )v)) e)
        where Just (FKInlineTable (_,tname2)) = fmap (unRecRel.pathRel) $ L.find (\r@(Path i _ )->  S.map (fmap keyValue ) (pathRelRel r) == S.singleton (Inline (keyValue rel)) )  (F.toList$ rawFKS  ta)
              ta = lookTable inf tname
    fixPatchAttr inf tname p@(PFK rel2 pa t b ) =  PFK rel2 (fmap (fixPatchAttr inf tname) pa) (tableMeta $ lookTable rinf tname2) b
        where (FKJoinTable  _ (schname,tname2) )  = (unRecRel.pathRel) $ justError (show (rel2 ,rawFKS ta)) $ L.find (\(Path i _ )->  i == S.fromList (_relOrigin <$> rel2))  (F.toList$ rawFKS  ta)
              ta = lookTable inf tname
              rinf = fromMaybe inf (HM.lookup schname (depschema inf))

liftAccess :: InformationSchema -> Text -> Access Text  -> Access Key
liftAccess inf tname (ISum i) =  ISum $ fmap (liftAccess inf tname)  i
liftAccess inf tname (Many i) =  Many $ fmap (liftAccess inf tname)  i
liftAccess inf tname (IProd b l) = IProd b $ fmap (lookKey inf tname) l
liftAccess inf tname (Nested i c) = Nested ref (liftAccess inf (snd l) c)
  where
    ref@(IProd _ refk) = liftAccess inf tname i
    tb = lookTable inf tname
    n = justError "no fk" $ L.find (\i -> S.fromList refk == (S.map _relOrigin $ pathRelRel i) ) (rawFKS tb)
    l = case n of
          (Path _ rel@(FKJoinTable  _ l  ) ) ->  l
          (Path _ rel@(FKInlineTable  l  ) ) ->  l
liftAccess _ _ i = errorWithStackTrace (show i)


lookAccess :: InformationSchema -> Text -> (Access Text , AccessOp Showable ) -> (Access Key, AccessOp Showable )
lookAccess inf tname l = Le.over (Le._1) (liftAccess inf tname)  l


makeLenses ''InformationSchemaKV

