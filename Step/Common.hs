{-# LANGUAGE TypeFamilies,Arrows,OverloadedStrings,DeriveFoldable,DeriveTraversable,StandaloneDeriving,FlexibleContexts,NoMonomorphismRestriction,Arrows,FlexibleInstances, DeriveFunctor  #-}
module Step.Common (PluginTable,Parser(..),Access(..),ArrowReaderM,ArrowReader,KeyString(..),BoolCollection(..),WherePredicate(..)) where

import Types
import Types.Index
import Data.GiST.BTree as G
import Data.Tuple
import Control.Monad.Reader
import Control.Applicative
import Data.Text (Text)
import Data.String
import Data.Functor.Identity
import qualified Data.Text as T
import qualified Data.Map as M

import Data.GiST.GiST as G
import qualified Data.Foldable as F

import Control.Arrow
import Control.Category (Category(..),id)
import Prelude hiding((.),id,head)
import Data.Monoid
import Data.Foldable(Foldable)
import Data.Traversable(Traversable)

data Access a
  = IProd Bool [a]
  | ISum  [Access a]
  | Nested (Access a) (Access a)
  | Rec Int (Access a)
  | Point Int
  | Many [Access a]
  deriving(Show,Eq,Ord,Functor,Foldable,Traversable)

data WherePredicate
  -- = LegacyPredicate [(T.Text,Column Key Showable)]
  = WherePredicate (BoolCollection (Access T.Text ,T.Text,FTB Showable ))
  deriving (Show,Eq,Ord)

instance Monoid WherePredicate where
  mempty = WherePredicate (AndColl [])
  mappend (WherePredicate i) (WherePredicate  j) = WherePredicate (AndColl [i,j])


data Parser m s a b = P (s,s) (m a b) deriving Functor

type ArrowReader  = Parser (Kleisli (ReaderT (Maybe (TBData Text Showable)) IO)) (Access Text) () (Maybe (TBData  Text Showable))
type PluginTable v = Parser (Kleisli (ReaderT (Maybe (TBData Text Showable)) Identity)) (Access Text) () v

type ArrowReaderM m  = Parser (Kleisli (ReaderT (Maybe (TBData Text Showable)) m )) (Access Text) () (Maybe (TBData  Text Showable))

data BoolCollection a
 = AndColl [BoolCollection a]
 | OrColl [BoolCollection a]
 | PrimColl a
 deriving(Show,Eq,Ord,Functor,Foldable)

instance Predicates (WherePredicate,G.Predicate Int) where
  type Penalty (WherePredicate ,G.Predicate Int)= ([DiffShowable],Int)
  type Query (WherePredicate ,G.Predicate Int)= (WherePredicate ,G.Predicate Int)
  consistent (c1,i) (c2,j) = consistent c1 c2 && consistent i j
  penalty (c1,i) (c2,j) = (penalty c1 c2 ,penalty i j)
  match  (c1,i) (c2,j) = match c1 c2 && match i j
  union i  = (union (fst <$> i), union (snd <$> i))
  pickSplit = pickSplitG

instance Predicates WherePredicate where
  type Penalty WherePredicate = [DiffShowable]
  type Query WherePredicate = WherePredicate
  consistent (WherePredicate c1) (WherePredicate c2)  = F.all id $ M.mergeWithKey (\_ i j -> Just $ consistent (snd i) (snd j)) (const False <$>) (const False <$>) (M.fromList $fmap projKey  $ F.toList c1) (M.fromList $ fmap projKey $ F.toList c2)
    where projKey (a,b,c) =  (a,(b,c))

  match (WherePredicate c1) (WherePredicate c2)  = F.all id $ M.mergeWithKey (\_ i j -> Just $ match (swap i) (snd j)) (const False <$>) (const False <$>) (M.fromList $fmap projKey  $ F.toList c1) (M.fromList $ fmap projKey $ F.toList c2)
    where projKey (a,b,c) =  (a,(b,c))

  penalty (WherePredicate c1) (WherePredicate c2) =F.toList $ M.mergeWithKey (\_ i j -> Just $ penalty  (snd i) (snd j) ) (fmap (loga .unFin . fst .minP. (\(a,c) -> c))) (fmap (loga . unFin . fst . minP. (\(a,c) -> c))) (M.fromList $fmap projKey  $ F.toList c1) (M.fromList $ fmap projKey $ F.toList c2)
    where projKey (a,b,c) =  (a,(b,c))
  pickSplit = pickSplitG
  union l = WherePredicate $ AndColl $ fmap (\(k,(a,b))-> PrimColl(k,a,b))$ M.toList $ foldl1 ( M.mergeWithKey (\_ i j -> Just $ pairunion [i,j]) (fmap id) (fmap id) ) ((\(WherePredicate pr ) -> M.fromList .fmap projKey  . F.toList $ pr)<$> l)
    where projKey (a,b,c) =  (a,(b,c))
          pairunion i = (head $ fst <$> i,union $ snd <$> i)



deriving instance Functor m => Functor (Kleisli m i )


instance (Monoid s ,Arrow m)  => Arrow (Parser m s) where
  arr f = (P mempty (arr f ))
  first (P s d )  = P s (first d )

instance (Monoid s,Arrow m) => Category (Parser m s) where
   id = P mempty id
   P (i) (j) . P (l ) (m) = P (i <> l) (j . m  )

instance Applicative m => Applicative (Kleisli m a) where
  pure i = Kleisli (const (pure i ))
  Kleisli f <*> Kleisli j  =  Kleisli  $ (\i -> f i <*> j i )



class KeyString i where
  keyString :: i -> Text

instance KeyString Key where
  keyString = keyValue

instance KeyString Text where
  keyString = id

instance Eq a => Monoid (Access a ) where
  mempty = Many []
  mappend (Many j) (Many i) = Many (i <> j)
  mappend y@(Nested i l ) z@(Nested j m)
    | i == j = Nested i (mappend l m)
    | otherwise = Many [ y,z]
  mappend i j@(Many _) = mappend (Many [i]) j
  mappend j@(Many _) i  = mappend j (Many [i])
  mappend i j = mappend (Many [i]) (Many [j])

instance (Monoid s ,Applicative (a i)) => Applicative (Parser a s i) where
  pure i = P mempty (pure i)
  P i  j <*> P l m  = P (i <> l) (j <*> m )

instance (Monoid s ,Applicative (a i) , IsString m) => IsString (Parser a s i m) where
  fromString s = pure (fromString s)

instance (Monoid s ,Applicative (a i),Monoid m) => Monoid (Parser a s i m) where
  mempty = P mempty (pure mempty)
  mappend (P i  l) (P j m ) =  P (mappend i j) (liftA2 mappend l  m )

