{-# LANGUAGE Arrows,FlexibleInstances,FlexibleContexts,DeriveAnyClass,DeriveGeneric,StandaloneDeriving,TypeFamilies,OverloadedStrings,DeriveTraversable,DeriveFoldable,DeriveFunctor,RankNTypes,UndecidableInstances,ExistentialQuantification #-}
module Environment where


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




type PluginM ix s m  i a = Parser (Kleisli (RWST s (Index s) ()  m )) (Union ix) i  a

type PluginM' ix s m  i a = Parser (Kleisli (RWST s (Index s) ()  m )) ix i  a


newtype Atom a = Atom { unAtom' :: a } deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

instance Patch (Atom a) where
  type Index (Atom a) = [Index a]

instance Patch a => Patch (M.Map u a ) where
  type Index  (M.Map u a) = [(u,Index a)]

data RowModifier
  = RowCreate
  | RowDrop
  | RowPatch
  deriving(Show)

data Row pk  k
  = Row pk  (Union (AttributePath k ()))
  | RowSum pk  (Union (AttributePath k ()))
  | RowIndex (TBIndex Showable) RowModifier (Union (AttributePath k ()))
  deriving(Show)

data Module t pk k
  = Module  t (Union (Row pk k))
  deriving(Show)

data Namespace n t pk k
  = Namespace n (Union (Module t pk k ))
  deriving(Show)

data Universe u n t pk k
  = Universe u (Union ( Namespace n t pk k))
  deriving(Show)

runEnv  r  e  =  (\(_,_,i) -> i) Control.Applicative.<$> runRWST   ( (runKleisli $ dynP r ) ()) e ()

indexTID (PIdIdx  ix )  (ArrayTB1 l) = l Non.!! ix
indexTID PIdOpt  (LeftTB1 l) = justError "no opt value" l

-- indexTIDM (PIdIdx  ix )  (ArrayTB1 l) = l `Non.atMay` ix
indexTIDM PIdOpt  (LeftTB1 l) = l

liftTID (PIdIdx ix) l = PIdx ix (Just l)
liftTID PIdOpt  l = POpt $ Just l


readM  v =  P ( Many [One v],Many[]) (Kleisli (const get ))
readV v = P ( Many [One v],Many[]) (Kleisli (\_ -> unAtom' <$> ask ))
writeV v = P ( Many[],Many [One v]) (Kleisli (\i ->   tell  [i] ))


withReaderT g f = mapRWST (fmap (\(r,s,w) -> (r,s,g w ))) . withRWST  (\i j -> (f i ,j))

withReaderT2 g f a = do
  env <- ask
  mapRWST (fmap (\(r,s,w) -> (r, s,g env w ))) . withRWST  (\i j -> (f i ,j)) $ a

withReaderT3 f g  a= do
  env <- ask
  maybe (return Nothing) (\_ -> withRWST  (\i j -> (justError "no opt" $ g  i ,j)) .  mapRWST (fmap (\(r,s,w) -> (Just r,s, f w )))  $ a)  (g env)

-- Primitive Value
ivalue :: (Monad m ,Show s) =>
  PluginM v  (Atom s) m i a
  -> PluginM (PathIndex PathTID v)  (Atom (FTB s) ) m i a
ivalue (P (tidxi ,tidxo) (Kleisli op) )  = P (TipPath <$> tidxi,TipPath  <$> tidxo) (Kleisli (withReaderT (fmap  PAtom) (fmap unTB1) . op ))



-- DataStructure (Array,Maybe,Interval)
iftb :: Monad m =>
       PathTID
       -> PluginM (PathIndex PathTID v)  (Atom (FTB b))  m i a
       -> PluginM (PathIndex PathTID v)  (Atom (FTB b))  m i a
iftb s   (P (tidxi ,tidxo) (Kleisli op) )  = P (NestedPath s <$> tidxi,NestedPath s <$> tidxo) (Kleisli (withReaderT (fmap (liftTID s)) (fmap (indexTID s) ) . op  ))

iopt :: Monad m =>
       PluginM (PathIndex PathTID v)  (Atom (FTB b))  m i a
       -> PluginM (PathIndex PathTID v)  (Atom (FTB b))  m i (Maybe a)
iopt (P (tidxi ,tidxo) (Kleisli op) )  = P (NestedPath PIdOpt <$> tidxi, NestedPath PIdOpt <$> tidxo) (Kleisli (withReaderT3 (fmap (liftTID PIdOpt)) (traverse (indexTIDM PIdOpt) ) . op  ))


-- Attribute indexing
ifield ::
       (Monad m ,Show k ,Ord k) => k
       -> PluginM (PathIndex PathTID () )  (Atom (FTB Showable )) m i a
       -> PluginM (AttributePath k () )  (Atom (TBData k Showable ))  m i a
ifield s (P (tidxi ,tidxo) (Kleisli op) )  = P (PathAttr s <$> tidxi,PathAttr s <$> tidxo) (Kleisli (withReaderT2 (\(Atom l@_) v -> [PAttr s <$> v]) (fmap (_tbattr .justError ("no field " ++ show s ). indexField (IProd Nothing s)   )) . op ))

iinline ::
       (Monad m ,Patch s ,Show s ,Show k ,Ord k) => k
       -> PluginM (PathIndex PathTID (AttributePath k ()))  (Atom (FTB (TBData k s)))  m  i a
       -> PluginM (AttributePath k () )  (Atom (TBData k s))  m i a
iinline s (P (tidxi ,tidxo) (Kleisli op) )  = P (PathInline s <$> tidxi,PathInline s <$> tidxo) (Kleisli (withReaderT2 (\(Atom l@_) v -> [PInline s   <$> v]) (fmap (_fkttable .justError ( "no inline " ++ show s). indexField (IProd Nothing s)   )) . op ))


iforeign ::
       (Monad m ,Patch s ,Show s ,Show k ,Ord k) => [Rel k]
       -> PluginM (PathIndex PathTID (AttributePath k ())  )  (Atom (FTB (TBData k s)))  m  i a
       -> PluginM (AttributePath k () )  (Atom (TBData k s))  m i a
iforeign s (P (tidxi ,tidxo) (Kleisli op) )  = P (PathForeign s <$> tidxi,PathForeign s <$> tidxo) (Kleisli (withReaderT2 (\(Atom l@_ )v -> [PFK s [] <$> v] ) (fmap ( _fkttable . justError ("no foreign " ++ show s). indexField (Nested(IProd Nothing ._relOrigin <$> s) (Many []))   ) ). op ))


-- Row

isum :: (Monad m,  Monoid (Index o) )
  => [PluginM (AttributePath k ()) o m i (Maybe a)]
  -> PluginM (AttributePath k ()) o m i a
isum  ls   =  P (Many $ fmap (fst .staticP) ls,Many $ fmap (snd.staticP)  ls ) (Kleisli (\i -> fmap (justError "no value ") $ foldr (liftA2 (<|>)) (return Nothing) $ (\ j -> (unKleisli . dynP $ j) i ) <$> ls))
  where unKleisli (Kleisli op) = op


arow :: Monad m =>
  RowModifier
  -> PluginM (AttributePath k ()) o m i a
  -> PluginM (Row RowModifier k ) o m i a
arow  m (P (tidxi ,tidxo) (Kleisli op) )  = P (manyU[Row m tidxi],manyU[Row m tidxo]) (Kleisli (withReaderT id id . op ))



irow :: (Show k ,Ord k ,Monad m )=>
  (TBIndex Showable ,RowModifier)
       -> PluginM (AttributePath k ())  (Atom (TBData k Showable ))  m  i a
       -> PluginM (Row RowModifier k )  (KVMetadata k,TableIndex k Showable )  m i a
irow (ix,s) (P (tidxi ,tidxo) (Kleisli op) )  = P (manyU [RowIndex ix s tidxi],manyU[RowIndex ix s tidxo]) (Kleisli $ (withReaderT (PatchRow  . (ix,) . last . compact ) (Atom . action ) . op ))
  where
    action = case s of
        RowPatch -> justError ("no pk " ++ show ix). G.lookup ix . snd


-- Table

itable :: Monad m
       => (Show t ,Ord t)
       => t
       -> PluginM (Row pk k)  (TableIndex k Showable )  m  i a
       -> PluginM (Module t pk k )  (M.Map t (TableIndex k Showable) )  m i a
itable s (P (tidxi ,tidxo) (Kleisli op) )  = P (manyU[Module s tidxi],manyU[Module s tidxo]) (Kleisli (withReaderT (pure . (s,)) (justError ("no table "++ show s). M.lookup  s ) . op ))

atable ::( Show t ,Monad m)
       => Ord t
       => t
       -> PluginM (Row pk k)  o  m  i a
       -> PluginM (Module t pk k )  o  m i a
atable s (P (tidxi ,tidxo) (Kleisli op) )  = P (manyU[Module s tidxi],manyU[Module s tidxo]) (Kleisli (withReaderT id id  . op ))


-- Schema
ischema :: (Monad m ,Show s ,Ord s)
       => s
       -> PluginM (Module t pk k)  (M.Map t (TableIndex k Showable ))  m  i a
       -> PluginM (Namespace s t pk k )  (M.Map s (M.Map t (TableIndex k Showable)))  m i a
ischema s (P (tidxi ,tidxo) (Kleisli op) )  = P (manyU[Namespace s tidxi],manyU[Namespace s tidxo]) (Kleisli (withReaderT (pure . (s,)) (justError ("no schema" ++ show s). M.lookup  s ) . op ))

aschema :: (Monad m ,Ord s)
       => s
       -> PluginM (Module t pk k)  o  m  i a
       -> PluginM (Namespace s t pk k )  o  m i a
aschema s (P (tidxi ,tidxo) (Kleisli op) )  = P (manyU[Namespace s tidxi],manyU[Namespace s tidxo]) (Kleisli (withReaderT id id . op ))


-- Database
iuniverse   :: (Monad m ,Show u ,Ord u)
       => u
       -> PluginM (Namespace s t pk  k)  (M.Map s (M.Map t (TableIndex k Showable )))  m  i a
       -> PluginM (Universe u s t pk  k )  (M.Map u (M.Map s (M.Map t (TableIndex k Showable)))) m i a
iuniverse s (P (tidxi ,tidxo) (Kleisli op) )  = P (manyU [Universe s tidxi],manyU [Universe s tidxo]) (Kleisli (withReaderT (pure . (s,)) (justError ("no database " ++ show s). M.lookup  s ) . op ))

translate  r
   = case staticP r  of
       (Many [One (Namespace i (Many [One (Module m (Many [One (Row RowDrop _ )]))]))],_) -> let
          lift j i = do
             inf <- ask
             now <- liftIO getCurrentTime
             ((Just . TableModification Nothing now (snd $ username inf) (lookTable inf m ). DropRow . G.getIndex (lookMeta inf m)  . F.foldl' apply i ) . fmap (liftPatch inf  m)) Control.Applicative.<$> j (Atom $ mapKey' keyValue i)
        in ((i,m),[DropRule (lift (runEnv r))])
       (Many [One (Namespace i (Many [One (Module m (Many [One (Row RowCreate _ )]))]))],_) -> let
           lift j i = do
             inf <- ask
             now <- liftIO getCurrentTime
             ((Just . TableModification Nothing now (snd $username inf)(lookTable inf m ). createRow' (lookMeta inf m) . F.foldl' apply i ) . fmap (liftPatch inf  m)) Control.Applicative.<$> j (Atom $ mapKey' keyValue i)
        in((i,m),[CreateRule (lift (runEnv r))])
       (Many [One (Namespace i (Many [One (Module m (Many [One (Row RowPatch _ )]))]))],_)  -> let
           lift j i p = do
             inf <- ask
             now <- liftIO getCurrentTime
             ((\a-> Just . TableModification Nothing now (snd $username inf) (lookTable inf m ). PatchRow . (G.getIndex (lookMeta inf m) i,) . L.head .  compact $ (p:a) ) . fmap (liftPatch inf  m)) Control.Applicative.<$> j (Atom $ mapKey' keyValue i)
        in((i,m),[UpdateRule (lift (runEnv r))])


