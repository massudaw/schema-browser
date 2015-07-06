{-# LANGUAGE RankNTypes,ExistentialQuantification #-}
module RuntimeTypes where

import Control.Concurrent
import Schema
import Types
import Data.Text.Lazy
import Control.Monad.IO.Class
import Step

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
  , _boundedAction2 :: InformationSchema -> (Maybe (TB1 (Key,Showable))) -> IO (Maybe (TB1 (Key,Showable)))
  }


data  PollingPlugins fi fo
  = BoundedPollingPlugins
  { _pollingName :: String
  , _pollingTime :: Int
  , _pollingBounds :: (Text,(Access Text,Access Text))
  , _pollingBoundedAction :: InformationSchema ->  fi -> fo
  }

data WrappedCall =  forall m . MonadIO m =>  WrappedCall
      { runCall ::  forall a . m a -> IO a
      , stepsCall :: [InformationSchema -> MVar (Maybe (TB1 (Key,Showable)))  -> (Maybe (TB1 (Key,Showable)) -> m ()) -> m () ]
      }





