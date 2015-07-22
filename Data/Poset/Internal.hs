{-
 - Copyright (C) 2009-2010 Nick Bowler.
 -
 - License BSD2:  2-clause BSD license.  See LICENSE for full terms.
 - This is free software: you are free to change and redistribute it.
 - There is NO WARRANTY, to the extent permitted by law.
 -}

{-# LANGUAGE FlexibleInstances, OverlappingInstances, UndecidableInstances #-}
module Data.Poset.Internal where

import qualified Data.List as List
import qualified Prelude
import Prelude hiding (Ordering(..), Ord(..))

import Data.Monoid

data Ordering = LT | EQ | GT | NC
    deriving (Eq, Show, Read, Bounded, Enum)

-- Lexicographic ordering.
instance Monoid Ordering where
    mempty = EQ
    mappend EQ x = x
    mappend NC _ = NC
    mappend LT _ = LT
    mappend GT _ = GT

-- | Internal-use function to convert our Ordering to the ordinary one.
totalOrder :: Ordering -> Prelude.Ordering
totalOrder LT = Prelude.LT
totalOrder EQ = Prelude.EQ
totalOrder GT = Prelude.GT
totalOrder NC = error "Uncomparable elements in total order."

-- | Internal-use function to convert the ordinary Ordering to ours.
partialOrder :: Prelude.Ordering -> Ordering
partialOrder Prelude.LT = LT
partialOrder Prelude.EQ = EQ
partialOrder Prelude.GT = GT

-- | Class for partially ordered data types.  Instances should satisfy the
-- following laws for all values a, b and c:
--
-- * @a <= a@.
--
-- * @a <= b@ and @b <= a@ implies @a == b@.
--
-- * @a <= b@ and @b <= c@ implies @a <= c@.
--
-- But note that the floating point instances don't satisfy the first rule.
--
-- Minimal complete definition: 'compare' or '<='.
class Eq a => Poset a where
    compare :: a -> a -> Ordering
    -- | Is comparable to.
    (<==>)  :: a -> a -> Bool
    -- | Is not comparable to.
    (</=>)  :: a -> a -> Bool
    (<)     :: a -> a -> Bool
    (<=)    :: a -> a -> Bool
    (>=)    :: a -> a -> Bool
    (>)     :: a -> a -> Bool

    a `compare` b
        | a == b = EQ
        | a <= b = LT
        | b <= a = GT
        | otherwise = NC

    a <    b = a `compare` b == LT
    a >    b = a `compare` b == GT
    a <==> b = a `compare` b /= NC
    a </=> b = a `compare` b == NC
    a <=   b = a < b || a `compare` b == EQ
    a >=   b = a > b || a `compare` b == EQ

-- | Class for partially ordered data types where sorting makes sense.
-- This includes all totally ordered sets and floating point types.  Instances
-- should satisfy the following laws:
--
-- * The set of elements for which 'isOrdered' returns true is totally ordered.
--
-- * The max (or min) of an insignificant element and a significant element
-- is the significant one.
--
-- * The result of sorting a list should contain only significant elements.
--
-- * @max a b@ = @max b a@
--
-- * @min a b@ = @min b a@
--
-- The idea comes from floating point types, where non-comparable elements
-- (NaNs) are the exception rather than the rule.  For these types, we can
-- define 'max', 'min' and 'sortBy' to ignore insignificant elements.  Thus, a
-- sort of floating point values will discard all NaNs and order the remaining
-- elements.
--
-- Minimal complete definition: 'isOrdered'
class Poset a => Sortable a where
    isOrdered :: a -> Bool
    max :: a -> a -> a
    min :: a -> a -> a

    max a b = case a `compare` b of
        LT -> b
        EQ -> a
        GT -> a
        NC -> if isOrdered a then a else if isOrdered b then b else a
    min a b = case a `compare` b of
        LT -> a
        EQ -> b
        GT -> b
        NC -> if isOrdered a then a else if isOrdered b then b else a

sortBy :: (b -> b -> Ordering) -> [b] -> [b]
sortBy f = List.sortBy ((totalOrder .) . f) -- . filter isOrdered

-- | Class for totally ordered data types.  Instances should satisfy
-- @isOrdered a = True@ for all @a@.
class Sortable a => Ord a

-- This hack allows us to leverage existing data structures defined in terms
-- of 'Prelude.Ord'.
instance Data.Poset.Internal.Ord a => Prelude.Ord a where
    compare = (totalOrder .) . compare
    (<)     = (<)
    (<=)    = (<=)
    (>=)    = (>=)
    (>)     = (>)
    min     = min
    max     = max
