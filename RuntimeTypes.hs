{-# LANGUAGE DeriveTraversable,DeriveFoldable,DeriveFunctor,RankNTypes,ExistentialQuantification #-}
module RuntimeTypes where

import Control.Concurrent
-- import Schema
import Types
import Control.Arrow
import Data.Text.Lazy
import Control.Monad.IO.Class
-- import Step

import qualified Reactive.Threepenny as R
import Database.PostgreSQL.Simple
import Data.Map (Map)
import Data.Set (Set)
import Control.Monad.Reader
import Data.Foldable
import Data.Traversable

data Parser m s a b = P (s,s) (m a b) deriving Functor

data InformationSchema
  = InformationSchema
  { schemaName :: Text
  , username :: Text
  , keyMap :: Map (Text,Text) Key
  , pkMap :: Map (Set Key) Table
  , tableMap :: Map Text Table
  , tableSize :: Map Table Int
  , pluginsMap :: Map (Text,Text,Text) Key
  , mvarMap :: MVar (Map (KVMetadata Key) ({-R.Event [TB1 Showable], R.Handler [TB1 Showable], -} MVar  [TBData Key Showable], R.Tidings [TBData Key Showable]))
  , conn :: Connection
  , rootconn :: Connection
  , metaschema :: Maybe InformationSchema
  }

data Plugins
  =  StatefullPlugin
  { _name ::  Text
  , _bounds :: Text
  , _statebounds :: [(Access Text,Access Text)]
  , _statevar :: [[(Text,KType Text)]]
  , _statefullAction :: WrappedCall
  }
  | BoundedPlugin2
  { _name :: Text
  , _bounds :: Text
  , _arrowbounds :: (Access Text,Access Text)
  , _boundedAction2 :: InformationSchema -> (Maybe (TB1 Showable)) -> IO (Maybe (TB1 Showable))
  }
  | SequentialPlugin
  { _name :: Text
  , _splugs :: [ Plugins]
  }
  | ArrowPlugin
  { _name :: Text
  , _bounds :: Text
  , _arrow :: ArrowReader
  }

{-
data  PollingPlugins fi fo
  = BoundedPollingPlugins
  { _pollingName :: Text
  , _pollingTime :: Int
  , _pollingBounds :: (Text,(Access Text,Access Text))
  , _pollingBoundedAction :: InformationSchema ->  fi -> fo
  }
-}


data WrappedCall =  forall m . MonadIO m =>  WrappedCall
      { runCall ::  forall a . m a -> IO a
      , stepsCall :: [InformationSchema -> MVar (Maybe (TB1 Showable))  -> (Maybe (TB1 Showable) -> m ()) -> m () ]
      }




data Access a
  = IProd Bool [a]
  | ISum  [Access a]
  | Nested (Access a) (Access a)
  | Many [Access a]
  deriving(Show,Eq,Ord,Functor,Foldable,Traversable)


type ArrowReader  = Parser (Kleisli (ReaderT (Maybe (TB1 Showable)) IO)) (Access Text) () (Maybe (TB2  Text Showable))
