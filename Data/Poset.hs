{-
 - Copyright (C) 2009 Nick Bowler.
 -
 - License BSD2:  2-clause BSD license.  See LICENSE for full terms.
 - This is free software: you are free to change and redistribute it.
 - There is NO WARRANTY, to the extent permitted by law.
 -}

-- | Partially ordered data types.  The standard 'Prelude.Ord' class is for
-- total orders and therefore not suitable for floating point.  However, we can
-- still define meaningful 'max' and 'sort' functions for these types.
--
-- We define our own 'Ord' class which is intended as a replacement for
-- 'Prelude.Ord'.  However, in order to take advantage of existing libraries
-- which use 'Prelude.Ord', we make every instance of 'Ord' an instance of
-- 'Prelude.Ord'.  This is done using the OverlappingInstances and
-- UndecidableInstances extensions -- it remains to be seen if problems occur
-- as a result of this.
module Data.Poset (
    sortBy,Poset(..), Sortable(..), Ordering(..), Ord,
    module Data.Poset
) where

import qualified Prelude
import Prelude hiding (Ord(..), Ordering(..))
import Data.Poset.Instances
import Data.Poset.Internal
import qualified Data.Ord as O

import Data.Function
import Data.Monoid
import Data.Set  (Set)
import qualified Data.Set  as Set

instance Poset a => Poset (Maybe a) where
    Just x  <= Just y = x <= y
    Nothing <= _      = True
    _       <= _      = False

instance Poset a => Poset [a] where
    compare = (mconcat .) . zipWith compare

instance O.Ord a => Sortable (Set a) where
    isOrdered i = True
instance O.Ord a => Poset (Set a) where
    compare i j
      | Set.isSubsetOf i j = LT
      | Set.isSubsetOf j i = GT
      |  otherwise = case O.compare i j of
                          O.LT -> LT
                          O.EQ -> EQ
                          O.GT -> GT

-- | Sort a list using the default comparison function.
sort :: Sortable a => [a] -> [a]
sort = sortBy compare

-- | Apply a function to values before comparing.
comparing :: Poset b => (a -> b) -> a -> a -> Ordering
comparing = on compare
