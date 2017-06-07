{-# LANGUAGE TypeFamilies,Arrows,OverloadedStrings,DeriveFoldable,DeriveTraversable,StandaloneDeriving,FlexibleContexts,NoMonomorphismRestriction,Arrows,FlexibleInstances, DeriveGeneric,DeriveFunctor  ,GeneralizedNewtypeDeriving,TupleSections #-}
module Step.Common (PluginTable,Parser(..),Access(..),ArrowReaderM,ArrowReader,KeyString(..),BoolCollection(..),WherePredicateK(..),WherePredicate(..),TBPredicate(..),mapPredicate ) where

import Types.Common
import Control.Arrow.Transformer.Static
import Data.Binary
import Types.Primitive
import Data.Tuple
import Control.Monad.Reader
import Control.Applicative
import Data.Text (Text)
import Data.String
import Data.Functor.Identity
import GHC.Generics
import qualified Data.Text as T
import qualified Data.Map as M

import qualified Data.Foldable as F

import Control.Arrow
import Control.DeepSeq
import Control.Category (Category(..),id)
import Prelude hiding((.),id,head)
import Data.Monoid
import Data.Foldable(Foldable)
import Data.Traversable(Traversable)


mapPredicate f (WherePredicate i ) = WherePredicate (fmap (first (fmap f )) i)
type WherePredicateK k = TBPredicate k Showable
type WherePredicate = WherePredicateK Key

newtype TBPredicate k a
  = WherePredicate (BoolCollection (Access k ,AccessOp a ))
  deriving (Show,Eq,Ord,Generic)
instance (NFData k, NFData a) => NFData (TBPredicate k a)
instance (Binary k, Binary a) => Binary (TBPredicate k a)


instance Monoid (WherePredicateK k) where
  mempty = WherePredicate (AndColl [])
  mappend (WherePredicate i) (WherePredicate  j) = WherePredicate (AndColl [i,j])


data Parser m s a b = P (s,s) (m a b) deriving Functor

type ArrowReader  = ArrowReaderM IO
type PluginTable v = Parser (Kleisli (ReaderT (Maybe (TBData Text Showable)) Identity)) (Union (Access Text)) () v

type ArrowReaderM m  = Parser (Kleisli (ReaderT (Maybe (TBData Text Showable)) m )) (Union (Access Text)) () (Maybe (TBData  Text Showable))

deriving instance Functor m => Functor (Kleisli m i )




newtype StaticEnv  m t k v = StaticEnv (StaticArrow ((,) (t,t))  m  k v ) deriving (Arrow , Functor,Applicative , Category)

instance (Monoid s ,Applicative (a i),Monoid m) => Monoid (StaticEnv a s i m) where
  mempty = StaticEnv $ StaticArrow (mempty ,pure mempty)
  mappend (StaticEnv (StaticArrow (i , l))) (StaticEnv (StaticArrow( j ,m ))) =  StaticEnv $ StaticArrow  (mappend i j,liftA2 mappend l  m )

instance (Monoid s ,Arrow m)  => Arrow (Parser m s) where
  arr f = (P mempty (arr f ))
  first (P s d )  = P s (first d )

instance (Monoid s,Arrow m) => Category (Parser m s) where
   id = P mempty id
   P i j . P l  m = P (i <> l) (j . m  )

instance Applicative m => Applicative (Kleisli m a) where
  pure i = Kleisli (const (pure i ))
  Kleisli f <*> Kleisli j  =  Kleisli  $ (\i -> f i <*> j i )

instance Alternative m => Alternative (Kleisli m a) where
  empty = Kleisli (const empty)
  Kleisli f <|> Kleisli j  =  Kleisli  $ (\i -> f i <|> j i )




class KeyString i where
  keyString :: i -> Text

instance KeyString Key where
  keyString = keyValue

instance KeyString Text where
  keyString = id

instance Eq a => Monoid (Union a ) where
  mempty = Many []
  mappend (ISum j) (ISum i) = ISum (i <> j)
  mappend (Many j) (Many i) = Many (i <> j)

instance Applicative Union where
  pure i = Many [i]
  Many f <*> Many a = Many (zipWith ($) f a)

instance Alternative Union where
  empty = ISum []
  ISum f <|> ISum g = ISum (f <> g)

instance (Monoid s ,Applicative (a i)) => Applicative (Parser a s i) where
  pure i = P mempty (pure i)
  P i  j <*> P l m  = P (i <> l) (j <*> m )

instance  (Monoid s,Alternative (a i)) => Alternative (Parser a s i ) where
  empty = P mempty empty
  P i l <|> P j m  = P (i <>  j)  (l <|> m)

instance (Monoid s ,Applicative (a i) , IsString m) => IsString (Parser a s i m) where
  fromString s = pure (fromString s)


instance (Monoid s ,Applicative (a i),Monoid m) => Monoid (Parser a s i m) where
  mempty = P mempty (pure mempty)
  mappend (P i  l) (P j m ) =  P (mappend i j) (liftA2 mappend l  m )

