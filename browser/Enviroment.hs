{-# LANGUAGE Arrows,FlexibleInstances,FlexibleContexts,DeriveAnyClass,DeriveGeneric,StandaloneDeriving,TypeFamilies,OverloadedStrings,DeriveTraversable,DeriveFoldable,DeriveFunctor,RankNTypes,UndecidableInstances,ExistentialQuantification #-}
module Enviroment where


import Control.Concurrent

import RuntimeTypes
import Step.Host
import Step.Client
import Types
import Control.Exception
import Postgresql.Types
import Data.Time
import Step.Common
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
import Control.Monad.Reader hiding (withReaderT)
import qualified Data.Foldable as F
import Data.Traversable
import GHC.Stack




type PluginM ix s m  a = Parser (Kleisli (RWST s (Index s) () m )) ix ()  a


newtype Atom a = Atom {unAtom' :: a } deriving (Eq,Ord,Show,Functor)

instance Patch (Atom a) where
  type Index (Atom a) = [Index a]

instance Patch a => Patch (M.Map u a ) where
  type Index  (M.Map u a) = [(u,Index a)]


data Row pk  k
  = Row pk  [AttributePath k ()]
  deriving(Show)

data Module t pk k
  = Module  t [Row pk k]
  deriving(Show)

data Namespace n t pk k
  = Namespace n [Module t pk k ]
  deriving(Show)

data Universe u n t pk k
  = Universe u [Namespace n t pk k]
  deriving(Show)


indexTID (PIdIdx  ix )  (ArrayTB1 l) = l Non.!! ix
indexTID PIdOpt  (LeftTB1 l) = fromJust l


readV v = P ( [v],[]) (Kleisli (\_ -> ask ))
writeV v o = P ( [],[v]) (Kleisli (\_ -> tell o ))

incrementValue :: PluginM [Universe String String String (TBIndex Showable) String] (M.Map String (M.Map String  (M.Map String  (TableIndex String Showable ))))  IO ()
incrementValue
  = iuniverse "incendio" $
      ischema "incendio" $
        itable "test" $
          irow (G.Idex [TB1 1]) $
            ifield "counter" $
              iftb (PIdIdx 10) $
                ivalue $ proc t ->  do
                  v <- readV () -< ()
                  writeV () [10]  -<t
                  returnA -< ()


withReaderT g f = mapRWST (fmap (\(r,s,w) -> (r,s,g w ))) . withRWST  (\i j -> (f i ,j))
withReaderT2 g f a = do
  env <- ask
  mapRWST (fmap (\(r,s,w) -> (r,s,g env w ))) . withRWST  (\i j -> (f i ,j)) $ a

-- Primitive Value
ivalue ::Show s =>
       PluginM [v]  (Atom s) IO a
       -> PluginM [PathIndex PathTID v]  (Atom (FTB s) ) IO  a
ivalue (P (tidxi ,tidxo) (Kleisli op) )  = P (TipPath <$> tidxi,TipPath  <$> tidxo) (Kleisli $ (withReaderT ( fmap  PAtom) (fmap unTB1 ) . op ))

-- DataStructure (Array,Maybe,Interval)
iftb ::
       PathTID
       -> PluginM [PathIndex PathTID v]  (Atom (FTB b))  IO a
       -> PluginM [PathIndex PathTID v]  (Atom (FTB b))  IO  a
iftb s   (P (tidxi ,tidxo) (Kleisli op) )  = P (NestedPath s <$> tidxi,NestedPath s <$> tidxo) (Kleisli $ (withReaderT id (fmap (indexTID s) ) . op  ))

-- Attribute indexing
ifield ::
       (Show k ,Ord k) => k
       -> PluginM [PathIndex PathTID () ]  (Atom (FTB Showable )) IO  a
       -> PluginM [AttributePath k () ]  (TBData k Showable )  IO a
ifield s (P (tidxi ,tidxo) (Kleisli op) )  = P (PathAttr s <$> tidxi,PathAttr s <$> tidxo) (Kleisli $ (withReaderT2 (\l@(m,_) v -> (m,fmap patch $ G.getIndex l , PAttr s <$> v)) (Atom . _tbattr .fromJust . indexField (IProd Nothing [s])   ) . op ))

iinline ::
       (Patch s ,Show s ,Show k ,Ord k) => k
       -> PluginM [PathIndex PathTID (AttributePath k ())]  (Atom (FTB (TBData k s)))  IO  a
       -> PluginM [AttributePath k () ]  (TBData k s)  IO a
iinline s (P (tidxi ,tidxo) (Kleisli op) )  = P (PathInline s <$> tidxi,PathInline s <$> tidxo) (Kleisli $ (withReaderT2 (\l@(m,_) v -> (m,fmap patch $ G.getIndex l, PInline s   <$> v)) (Atom . _fkttable .fromJust . indexField (IProd Nothing [s])   ) . op ))


iforeign ::
       (Patch s ,Show s ,Show k ,Ord k) => [Rel k]
       -> PluginM [PathIndex PathTID (AttributePath k ())  ]  (Atom (FTB (TBData k s)))  IO  a
       -> PluginM [AttributePath k () ]  (TBData k s)  IO a
iforeign s (P (tidxi ,tidxo) (Kleisli op) )  = P (PathForeign s <$> tidxi,PathForeign s <$> tidxo) (Kleisli $ (withReaderT2 (\l@(m,_) v -> (m,fmap patch $ G.getIndex l,PFK s [] <$> v) ) (Atom . _fkttable .fromJust . indexField (IProd Nothing (_relOrigin <$> s))   ) . op ))


-- Row

irow ::
       TBIndex Showable
       -> PluginM [AttributePath k ()]  (TBData k Showable )  IO  a
       -> PluginM [Row (TBIndex Showable) k ]  (TableIndex k Showable )  IO a
irow s (P (tidxi ,tidxo) (Kleisli op) )  = P ([Row s tidxi],[Row s tidxo]) (Kleisli $ (withReaderT (PatchRow ) (fromJust . G.lookup  s ) . op ))

-- Table

itable :: Ord t
       => t
       -> PluginM [Row pk k]  (TableIndex k Showable )  IO  a
       -> PluginM [Module t pk k ]  (M.Map t (TableIndex k Showable) )  IO a
itable s (P (tidxi ,tidxo) (Kleisli op) )  = P ([Module s tidxi],[Module s tidxo]) (Kleisli $ (withReaderT (li . (s,)) (fromJust . M.lookup  s ) . op ))

-- Schema
ischema :: Ord s
       => s
       -> PluginM [Module t pk k]  (M.Map t (TableIndex k Showable ))  IO  a
       -> PluginM [Namespace s t pk k ]  (M.Map s (M.Map t (TableIndex k Showable)))  IO a
ischema s (P (tidxi ,tidxo) (Kleisli op) )  = P ([Namespace s tidxi],[Namespace s tidxo]) (Kleisli $ (withReaderT (li . (s,)) (fromJust . M.lookup  s ) . op ))

-- Database
iuniverse   :: Ord u
       => u
       -> PluginM [Namespace s t pk  k]  (M.Map s (M.Map t (TableIndex k Showable )))  IO  a
       -> PluginM [Universe u s t pk  k ]  (M.Map u (M.Map s (M.Map t (TableIndex k Showable)))) IO a
iuniverse s (P (tidxi ,tidxo) (Kleisli op) )  = P ([Universe s tidxi],[Universe s tidxo]) (Kleisli $ (withReaderT (li . (s,)) (fromJust . M.lookup  s ) . op ))


li i = [i]
