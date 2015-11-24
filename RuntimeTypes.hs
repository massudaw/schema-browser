{-# LANGUAGE DeriveTraversable,DeriveFoldable,DeriveFunctor,RankNTypes,ExistentialQuantification #-}
module RuntimeTypes where

import Control.Concurrent
import Types
import Control.Arrow
import Data.Text
import Control.Monad.IO.Class
import Patch
import Control.Monad.Writer

import qualified Reactive.Threepenny as R
import Database.PostgreSQL.Simple
import Data.Functor.Identity
import Data.Map (Map)
import Data.Set (Set)
import Control.Monad.Reader
import Data.Foldable
import Data.Traversable
import Data.IORef
import Network.Google.OAuth2

data Parser m s a b = P (s,s) (m a b) deriving Functor

data InformationSchema
  = InformationSchema
  { schemaName :: Text
  , username :: Text
  , token :: Maybe (Text,IORef OAuth2Tokens)
  , keyMap :: Map (Text,Text) Key
  , pkMap :: Map (Set Key) Table
  , tableMap :: Map Text Table
  , tableSize :: Map Table Int
  , pluginsMap :: Map (Text,Text,Text) Key
  , mvarMap :: MVar (Map (KVMetadata Key) (DBVar ))
  , conn :: Connection
  , rootconn :: Connection
  , metaschema :: Maybe InformationSchema
  , schemaOps :: SchemaEditor
  }

type DBVar2 k v = ( MVar  ((Int,Map Int PageToken),[TBData k v ]), R.Tidings ((Int,Map Int PageToken ),[TBData k v ]))
type DBVar = DBVar2 Key Showable

type Plugins = FPlugins Text
data FPlugins k
  =  StatefullPlugin
  { _name ::  Text
  , _bounds :: Text
  , _statevar :: [[(Text,KType (Prim (Text,Text) (Text,Text)))]]
  , _statefullAction :: [FPlugins k ]
  }
  | BoundedPlugin2
  { _name :: Text
  , _bounds :: Text
  , _arrowbounds :: (Access Text,Access Text)
  , _boundedAction2 :: InformationSchema -> (Maybe (TB2 k  Showable)) -> IO (Maybe (TB2 k Showable))
  }
  | PurePlugin
  { _name :: Text
  , _bounds :: Text
  , _arrowbounds :: (Access Text,Access Text)
  , _action :: InformationSchema -> Maybe (TB2 k Showable) -> Maybe (TB2 k Showable)
  }
  | ArrowPlugin
  { _name :: Text
  , _bounds :: Text
  , _arrow :: ArrowReader
  }

type TransactionM = WriterT [TableModification (TBIdx Key Showable)] IO

data PageToken
  = Index Int
  | NextToken Text
  deriving(Eq,Ord,Show)


data SchemaEditor
  = SchemaEditor
  { editEd  :: InformationSchema -> TBData Key Showable -> TBData Key Showable -> TransactionM  (TBData Key Showable)
  , insertEd :: InformationSchema -> TBData Key Showable -> TransactionM  (Maybe (TableModification (TBIdx Key Showable)))
  , deleteEd :: InformationSchema ->  TBData Key Showable -> Table -> IO (Maybe (TableModification (TBIdx Key Showable)))
  , listEd :: InformationSchema -> Table -> Maybe PageToken -> Maybe Int -> TransactionM ([TB2 Key Showable],Maybe PageToken,Int)
  , updateEd :: InformationSchema -> Table -> TBData Key Showable -> Maybe PageToken -> Maybe Int -> TransactionM ([TB2 Key Showable],Maybe PageToken,Int)
  , getEd :: InformationSchema -> Table -> TBData Key Showable -> TransactionM (Maybe (TBIdx Key Showable))
  }



data Access a
  = IProd Bool [a]
  | ISum  [Access a]
  | Nested (Access a) (Access a)
  | Rec Int (Access a)
  | Point Int
  | Many [Access a]
  deriving(Show,Eq,Ord,Functor,Foldable,Traversable)

type ArrowReader  = Parser (Kleisli (ReaderT (Maybe (TB2 Text Showable)) IO)) (Access Text) () (Maybe (TB2  Text Showable))
type ArrowReaderM m  = Parser (Kleisli (ReaderT (Maybe (TB2 Text Showable)) m )) (Access Text) () (Maybe (TB2  Text Showable))

