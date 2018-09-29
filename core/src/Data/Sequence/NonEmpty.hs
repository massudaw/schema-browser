{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFoldable #-}

module Data.Sequence.NonEmpty where

import Data.Binary 
import Data.Foldable (toList)
import qualified Data.List.NonEmpty as N
import qualified Data.Sequence as S
import GHC.Generics
import Control.DeepSeq
import Data.Maybe
import Prelude as P
import Control.Lens as Le

data NonEmptySeq a
  = a :| S.Seq a 
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Generic)

instance Applicative NonEmptySeq  where
   pure i = i :| S.empty
   (i :| is)  <*> (j :| js)  =  i j :| (is <*> js)

instance Binary a => Binary (NonEmptySeq a) where
instance NFData a => NFData (NonEmptySeq a) where

atMay :: NonEmptySeq a -> Int -> Maybe a
atMay (i:| _) 0 = Just i
atMay (_:| l) ix 
  | S.length l < ix  = Nothing
  | otherwise = Just $ S.index l (ix -1)

(!!) l = fromJust . atMay l 

elem pred (i:| l) = pred == i || P.elem pred l

instance Semigroup (NonEmptySeq a ) where
  (i :| is)  <> (j :| js)  =  i:| (is <> (j <| js))
zipWith :: (a -> b -> c) -> NonEmptySeq a -> NonEmptySeq b -> NonEmptySeq c
zipWith f (t :| ts) (j :| js) = f t j  :| S.zipWith f ts js  

nonEmptySeq :: S.Seq a -> Maybe (NonEmptySeq a)
nonEmptySeq = go . S.viewl
  where
    go S.EmptyL = Nothing 
    go (x S.:< xs) = Just (x :| xs)


nonEmpty :: [a] -> Maybe (NonEmptySeq a)
nonEmpty [] = Nothing 
nonEmpty (x:xs) = Just (x :| S.fromList xs)

imap :: (Int -> a -> b) -> NonEmptySeq a -> NonEmptySeq b 
imap f (i :| j ) = (f 0 i :| S.mapWithIndex f j )
length (i :| l)  = S.length  l + 1

head :: NonEmptySeq a -> a 
head (i :| _ ) = i

toNonEmpty (i :| j ) = i N.:| toList j 

take :: Int -> NonEmptySeq a -> S.Seq a
take  0 _  = S.empty 
take  1 (i :| xs )  = S.singleton i  
take  ix (i :| xs )  = i <| S.take (ix - 1) xs


drop :: Int -> NonEmptySeq a -> S.Seq a
drop  0 (i :| xs )  = i S.<| xs
drop  1 (i :| xs )  = xs
drop  ix (i :| xs )  = S.drop (ix - 1) xs

toSequence ::  NonEmptySeq a -> S.Seq a 
toSequence (i :| is) = i <| is

fromSequence :: S.Seq a -> NonEmptySeq a
fromSequence = go . S.viewl 
  where
    go S.EmptyL = error "cant be empty" 
    go (x  S.:< xs) = ( x :| xs)


appendSeq :: NonEmptySeq a -> S.Seq a -> NonEmptySeq a
appendSeq ( i :| s ) s1 = i :| (s <> s1 )

fromList :: [a] -> (NonEmptySeq a)
fromList [] = error "cant be empty" 
fromList (x:xs) = ( x :| S.fromList xs)





