{-# LANGUAGE TemplateHaskell,DeriveTraversable,DeriveFoldable,DeriveFunctor,RankNTypes,ExistentialQuantification #-}
module RuntimeTypes where


import Control.Concurrent

import Types
import Data.Unique
import Types.Index
import Control.Concurrent.STM.TQueue
import Control.Concurrent.STM
import Types.Patch
import qualified NonEmpty as Non
import Utils
import qualified Data.Text as T

import Control.Arrow
import Data.Text
import Control.Applicative
import Control.Monad.Writer

import qualified Reactive.Threepenny as R
import Database.PostgreSQL.Simple
import Data.Functor.Identity
import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import Control.Monad.Reader
import Data.Foldable
import Data.Traversable
import Data.IORef
import Network.Google.OAuth2
import Control.Lens.TH
import GHC.Stack

data Parser m s a b = P (s,s) (m a b) deriving Functor

data InformationSchema
  = InformationSchema
  { schemaName :: Text
  , username :: Text
  , token :: Maybe (Text,R.Tidings OAuth2Tokens)
  , _keyMapL :: Map (Text,Text) Key
  , _backendKey :: Map Unique PGKey
  , _pkMapL :: Map (Set Key) Table
  , _tableMapL :: Map Text Table
  , tableSize :: Map Table Int
  , mvarMap :: MVar (Map (KVMetadata Key) (DBVar ))
  , conn :: Connection
  , rootconn :: Connection
  , metaschema :: Maybe InformationSchema
  , schemaOps :: SchemaEditor
  , plugins :: [Plugins ]
  }

data BrowserState
  = BrowserState
  {host :: String
  ,port :: String
  ,dbn :: String
  ,user :: String
  ,pass :: String
  ,schema :: Maybe String
  ,tablename :: Maybe String
  ,rowpk :: Maybe [(Text,Text)]
  }



tableMap = _tableMapL
keyMap = _keyMapL
pkMap = _pkMapL

data DBVar2 k v=
  DBVar2
  { patchVar :: TQueue [TBIdx k v]
  , idxVar :: MVar (Map [Column k v ] (Int,Map Int PageToken))
  , patchTid :: R.Tidings [TBIdx k v]
  , idxTid :: R.Tidings (Map [Column k v ] (Int,Map Int PageToken))
  , collectionTid :: R.Tidings (TableIndex k v )
  }


idxColTid db =  (,) <$> idxTid db <*> collectionTid db

type DBVar = DBVar2 Key Showable
type Collection k v = (Map [Column k v] (Int,Map Int PageToken),GiST (TBIndex k  v ) (TBData k v))
type TableIndex k v = GiST (TBIndex k  v ) (TBData k v)

type Plugins = FPlugins Text
type VarDef = (Text,KType CorePrim)

data FPlugins k
  =  StatefullPlugin
  { _name ::  Text
  , _bounds :: Text
  , _statefullAction :: [(([VarDef ],[VarDef]),FPlugins k) ]
  }
  | BoundedPlugin2
  { _name :: Text
  , _bounds :: Text
  , _arrowIO :: ArrowReaderM IO
  }
  | PurePlugin
  { _name :: Text
  , _bounds :: Text
  , _arrowPure :: ArrowReaderM Identity
  }


pluginStatic (BoundedPlugin2 _ _ a) = staticP a
pluginStatic (PurePlugin _ _ a) = staticP a
pluginAction (BoundedPlugin2 _ _  a ) = fmap join . traverse (dynIO a)
pluginAction (PurePlugin _ _ a) = fmap join . traverse ((fmap return) (dynPure a ))

staticP ~(P s d) = s

dynIO url inp = do
    runReaderT (dynPK url ()) (Just inp)

dynPure url inp = runIdentity $ do
    dynIO url inp

dynP ~(P s d) = d

dynPK =  runKleisli . dynP


type TransactionM = WriterT [TableModification (TBIdx Key Showable)] IO


data PageToken
  = PageIndex Int
  | NextToken Text
  | TableRef [(Key , FTB Showable)]
  deriving(Eq,Ord,Show)


data SchemaEditor
  = SchemaEditor
  { editEd  :: InformationSchema -> TBData Key Showable -> TBData Key Showable -> TransactionM (Maybe (TableModification (TBIdx Key Showable)))
  , patchEd :: InformationSchema -> TBIdx Key Showable -> TransactionM (Maybe (TableModification (TBIdx Key Showable)))
  , insertEd :: InformationSchema -> TBData Key Showable -> TransactionM (Maybe (TableModification (TBIdx Key Showable)))
  , deleteEd :: InformationSchema -> TBData Key Showable -> TransactionM (Maybe (TableModification (TBIdx Key Showable)))
  , listEd :: InformationSchema -> Table -> Maybe Int -> Maybe PageToken -> Maybe Int -> [(Key,Order)] -> [(Text ,Column Key Showable)]-> TransactionM ([TB2 Key Showable],Maybe PageToken,Int)
  , updateEd :: InformationSchema -> Table -> TBData Key Showable -> Maybe PageToken -> Maybe Int -> TransactionM ([TB2 Key Showable],Maybe PageToken,Int)
  , getEd :: InformationSchema -> Table -> TBData Key Showable -> TransactionM (Maybe (TBIdx Key Showable))
  , typeTransform :: PGKey -> CoreKey
  }

typeTrans inf = typeTransform (schemaOps inf)


argsToState  [h,ph,d,u,p,s,t,o] = BrowserState h ph d  u p (Just s) (Just t ) (Just (fmap (fmap (T.drop 1) . T.break (=='=') )$ T.split (==',') (T.pack o)))
argsToState  [h,ph,d,u,p,s] = BrowserState h ph d  u p  (Just s)  Nothing Nothing
argsToState  [h,ph,d,u,p] = BrowserState h ph d  u p Nothing Nothing Nothing
argsToState i = errorWithStackTrace (show i)

lookTable :: InformationSchema -> Text -> Table
lookTable inf t = justError ("no table: " <> T.unpack t) $ M.lookup t (tableMap inf)

lookKey :: InformationSchema -> Text -> Text -> Key
lookKey inf t k = justError ("table " <> T.unpack t <> " has no key " <> T.unpack k ) $ M.lookup (t,k) (keyMap inf)


putPatch m = atomically . writeTQueue m -- . force


data Access a
  = IProd Bool [a]
  | ISum  [Access a]
  | Nested (Access a) (Access a)
  | Rec Int (Access a)
  | Point Int
  | Many [Access a]
  deriving(Show,Eq,Ord,Functor,Foldable,Traversable)

type ArrowReader  = Parser (Kleisli (ReaderT (Maybe (TBData Text Showable)) IO)) (Access Text) () (Maybe (TBData  Text Showable))
type ArrowReaderM m  = Parser (Kleisli (ReaderT (Maybe (TBData Text Showable)) m )) (Access Text) () (Maybe (TBData  Text Showable))

makeLenses ''InformationSchema

