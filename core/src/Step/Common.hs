{-# LANGUAGE TypeFamilies,Arrows,OverloadedStrings,DeriveFoldable,DeriveTraversable,StandaloneDeriving,FlexibleContexts,NoMonomorphismRestriction,Arrows,FlexibleInstances, GeneralizedNewtypeDeriving,DeriveGeneric,DeriveFunctor  ,GeneralizedNewtypeDeriving,TupleSections #-}
module Step.Common (
  Parser(..),
  Access(..),
  Constant(..),
  Ring(..),
  KeyString(..),
  BoolCollection(..),
  UnaryOperator(..),
  TBPredicate(..),
  AccessOp,
  Union(..),
  filterEmpty,
  traPredicate,
  mapPredicate,
  static
  ) where

import Types.Common
import Data.Binary
import NonEmpty
import Data.Tuple
import Control.Monad.Reader
import Control.Applicative
import Data.Text (Text)
import Data.String
import Data.Functor.Identity
import GHC.Generics
import Control.Arrow
import Control.DeepSeq
import Control.Category (Category(..),id)
import Prelude hiding((.),id,head)
import Data.Monoid


data Union a
  = Many [a]
  | ISum [a]
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable, Generic)

instance (Binary k) => Binary (Union k)

instance (NFData k) => NFData (Union k)

data Access a
  = IProd (Maybe UnaryOperator) a
  | Nested (NonEmpty (Rel a)) (Union (Access a))
  | Rec Int  (Union (Access a))
  | Point Int
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable, Generic)

instance (Binary k) => Binary (Access k)

instance (NFData k) => NFData (Access k)


mapPredicate f (WherePredicate i ) = WherePredicate (fmap (first (f ).fmap (fmap (first f))) i)
traPredicate f (WherePredicate i ) = WherePredicate <$> (traverse (fmap  swap . traverse ( traverse f ) . swap) i)

data BoolCollection a
  = AndColl [BoolCollection a]
  | OrColl [BoolCollection a]
  | Negate (BoolCollection a)
  | PrimColl a
  deriving (Show, Eq, Ord, Functor, Foldable, Generic, Traversable)

instance NFData a => NFData (BoolCollection a)

instance Binary a => Binary (BoolCollection a)



newtype TBPredicate k a
  = WherePredicate (BoolCollection (Rel k,[(Rel k,AccessOp a )]))
  deriving (Show,Eq,Ord,Generic)

type AccessOp a = Either (FTB a, BinaryOperator) UnaryOperator

leftMap f (Left i) = (Left $ f i)
leftMap f  (Right i)  = Right i

instance Functor (TBPredicate k) where
  fmap f (WherePredicate i ) = WherePredicate ( fmap (fmap (fmap (leftMap (first (fmap f))) ))<$> i  )

instance (NFData k, NFData a) => NFData (TBPredicate k a)
instance (Binary k, Binary a) => Binary (TBPredicate k a)

instance Semigroup (TBPredicate k a) where
  (WherePredicate i) <> (WherePredicate  j) = WherePredicate (AndColl [i,j])

instance Monoid (TBPredicate k a) where
  mempty = WherePredicate (AndColl [])


data Parser m s a b = P s (m a b) deriving Functor


deriving instance Functor m => Functor (Kleisli m i )

static (P i _ ) = i


instance (Ring s ,Arrow m)  => Arrow (Parser m s) where
  arr f = P one (arr f )
  first (P s d )  = P s (first d)


instance (Ring s,Arrow m) => Category (Parser m s) where
  id = P one id
  P i j . P l  m = P (i `mult` l) (j . m  )


instance Applicative m => Applicative (Kleisli m a) where
  pure i = Kleisli (const (pure i ))
  Kleisli f <*> Kleisli j  =  Kleisli  $ (\i -> f i <*> j i )

instance Alternative m => Alternative (Kleisli m a) where
  empty = Kleisli (const empty)
  Kleisli f <|> Kleisli j  =  Kleisli  $ (\i -> f i <|> j i )


class Ring a where
  zero :: a
  one :: a
  mult :: a -> a -> a
  add :: a -> a -> a


instance (Ring a , Ring b) => Ring (a,b) where
  zero = (zero,zero)
  one = (one,one)
  mult (a,b) (c,d) = (mult  a c, mult b d)
  add (a,b) (c,d) = (add a c, add b d)

instance Ring [a] where
  one = []
  mult i j = i <> j

instance Show a => Ring (Union a) where
  zero = ISum []
  one = Many []

  ISum l `add` ISum j = ISum (l <>  j)

  Many i `mult` Many j = Many $  i <> j
  i `mult` j = error $ "unexisting case " ++ show (i,j)



class KeyString i where
  keyString :: i -> Text


instance KeyString Text where
  keyString = id

instance Eq a => Semigroup (Union a ) where
  (Many j) <> (Many i) = Many (i <> j)

instance Eq a => Monoid (Union a ) where
  mempty = Many []
  mappend (Many j) (Many i) = Many (i <> j)

instance Applicative Union where
  pure i = Many [i]
  Many f <*> Many a = Many (f<*> a)

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

instance (Semigroup s ,Monad e ) => Semigroup (Parser (Kleisli e) s a m) where
  (P i  (Kleisli l)) <> (P j (Kleisli m) ) =  P (i <> j) (Kleisli (\i -> l i >>   m i ))

instance (Monoid s ,Monad e ) => Monoid (Parser (Kleisli e) s a m) where

filterEmpty (Nested _ (Many [])) = Nothing
filterEmpty (Nested _ (ISum [])) = Nothing
filterEmpty i = Just i

data UnaryOperator
  = IsNull
  | Not UnaryOperator
  | Exists
  | Range Bool UnaryOperator
  | BinaryConstant BinaryOperator Constant
  deriving (Eq, Ord, Show, Generic)

instance NFData UnaryOperator

instance Binary UnaryOperator


data Constant
  = CurrentTime
  | CurrentDate
  deriving (Eq, Ord, Show, Generic)

instance NFData Constant

instance Binary Constant


