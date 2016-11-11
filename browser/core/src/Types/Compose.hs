{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveGeneric #-}
module Types.Compose where

import GHC.Generics
import Data.Binary
import Data.Bifunctor

newtype Compose f g k a = Compose {getCompose :: f (g k a) } deriving (Functor,Foldable,Traversable,Ord,Eq,Show,Generic)

instance (Binary (f (g k a)) ) => Binary (Compose f g k a )

instance (Functor f ,Bifunctor g)  => Bifunctor (Compose f g ) where
  first f  = Compose . fmap (first f) . getCompose
  second f = Compose . fmap (second f) . getCompose


mapComp :: (Functor t) => (f c a -> g d b) ->  Compose t f c a -> Compose t g d b
mapComp f =  Compose. fmap  f . getCompose

traComp :: (Applicative k ,Traversable t ,Functor t )=> (f c a -> k (g d b)) ->  Compose t f c a -> k (Compose t g d b)
traComp f =  fmap Compose. traverse f . getCompose



