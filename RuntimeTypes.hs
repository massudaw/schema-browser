{-# LANGUAGE TemplateHaskell,DeriveTraversable,DeriveFoldable,DeriveFunctor,RankNTypes,ExistentialQuantification #-}
module RuntimeTypes where

import Control.Concurrent
import Types
import Control.Arrow
import Data.Text
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
import Control.Lens.TH

data Parser m s a b = P (s,s) (m a b) deriving Functor

data InformationSchema
  = InformationSchema
  { schemaName :: Text
  , username :: Text
  , token :: Maybe (Text,IORef OAuth2Tokens)
  , _keyMapL :: Map (Text,Text) Key
  , _pkMapL :: Map (Set Key) Table
  , _tableMapL :: Map Text Table
  , tableSize :: Map Table Int
  , mvarMap :: MVar (Map (KVMetadata Key) (DBVar ))
  , conn :: Connection
  , rootconn :: Connection
  , metaschema :: Maybe InformationSchema
  , schemaOps :: SchemaEditor
  }


tableMap = _tableMapL
keyMap = _keyMapL
pkMap = _pkMapL

type DBVar2 k v = (MVar  ((Int,Map Int PageToken),[TBData k v ]), R.Tidings ((Int,Map Int PageToken ),[TBData k v ]))
type DBVar = DBVar2 Key Showable

type Plugins = FPlugins Text
type VarDef = (Text,KType (Prim (Text,Text) (Text,Text)))

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
  = Index Int
  | NextToken Text
  deriving(Eq,Ord,Show)


data SchemaEditor
  = SchemaEditor
  { editEd  :: InformationSchema -> TBData Key Showable -> TBData Key Showable -> TransactionM  (TBData Key Showable)
  , insertEd :: InformationSchema -> TBData Key Showable -> TransactionM  (Maybe (TableModification (TBIdx Key Showable)))
  , deleteEd :: InformationSchema -> TBData Key Showable -> Table -> IO (Maybe (TableModification (TBIdx Key Showable)))
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

makeLenses ''InformationSchema
