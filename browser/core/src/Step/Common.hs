{-# LANGUAGE TypeFamilies,Arrows,OverloadedStrings,DeriveFoldable,DeriveTraversable,StandaloneDeriving,FlexibleContexts,NoMonomorphismRestriction,Arrows,FlexibleInstances, DeriveGeneric,DeriveFunctor  ,GeneralizedNewtypeDeriving,TupleSections #-}
module Step.Common (PluginTable,Parser(..),Access(..),ArrowReaderM,ArrowReader,KeyString(..),BoolCollection(..),WherePredicateK(..),WherePredicate(..),TBPredicate(..),mapPredicate ,static) where

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
type PluginTable v = Parser (Kleisli (ReaderT ((TBData Text Showable)) Identity)) (Union (Access Text)) () v

type ArrowReaderM m  = Parser (Kleisli (ReaderT ((TBData Text Showable)) m )) (Union (Access Text)) () (Maybe (TBData  Text Showable))


deriving instance Functor m => Functor (Kleisli m i )

static (P i _ ) = i



newtype StaticEnv  m t k v = StaticEnv (StaticArrow ((,) (t,t))  m  k v ) deriving (Arrow , Functor,Applicative , Category)

instance (Monoid s ,Applicative (a i),Monoid m) => Monoid (StaticEnv a s i m) where
  mempty = StaticEnv $ StaticArrow (mempty ,pure mempty)
  mappend (StaticEnv (StaticArrow (i , l))) (StaticEnv (StaticArrow (j ,m ))) =  StaticEnv $ StaticArrow  (mappend i j,liftA2 mappend l  m )

instance (Ring s ,Arrow m)  => Arrow (Parser m s) where
  arr f = (P one (arr f ))
  first (P s d )  = P s (first d )

instance (Ring s ,ArrowChoice m)  => ArrowChoice (Parser m s) where
  (|||) (P (si,so) d ) (P (ki,ko)  j ) = P (si `add` ki ,so `add` ko) (d ||| j)

instance (Ring s,Arrow m) => Category (Parser m s) where
  id = P one id
  P i j . P l  m = P (i `mult` l) (j . m  )


instance Applicative m => Applicative (Kleisli m a) where
  pure i = Kleisli (const (pure i ))
  Kleisli f <*> Kleisli j  =  Kleisli  $ (\i -> f i <*> j i )

instance Alternative m => Alternative (Kleisli m a) where
  empty = Kleisli (const empty)
  Kleisli f <|> Kleisli j  =  Kleisli  $ (\i -> f i <|> j i )



instance (Ring a , Ring b) => Ring (a,b) where
  zero = (zero,zero)
  one = (one,one)
  mult (a,b) (c,d) = (mult  a c, mult b d)
  add (a,b) (c,d) = (add a c, add b d)

instance Ring (Union a) where
  zero = ISum []
  one = Many []

  ISum l `add` ISum j = ISum (l <>  j)
  l `add` ISum j = ISum (l :  j)
  ISum l `add`j = ISum (l <> pure j)
  i `add`j = ISum [i,j]

  Many i `mult` Many j = Many $  i <> j
  Many i `mult`j = Many $  i <> pure j
  i `mult` Many j = Many $  pure i <> j
  i `mult` j = Many  [i,j]


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
  mappend (Many j) i = Many (j <> pure i)
  mappend i (Many j)  = Many (pure i <> j)

instance Applicative Union where
  pure i = Many [One i]
  Many f <*> Many a = Many (zipWith (<*>) f a)

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


instance (Monoid s ,Monad e ) => Monoid (Parser (Kleisli e) s a m) where
  mappend (P i  (Kleisli l)) (P j (Kleisli m) ) =  P (mappend i j) (Kleisli (\i -> l i >>   m i ))

