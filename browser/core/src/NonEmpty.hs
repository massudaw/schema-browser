module NonEmpty
  (module NonEmpty
  ,module Data.List.NonEmpty ) where

import qualified Data.List.NonEmpty as Non
import Data.List.NonEmpty hiding (fromList)

import Safe as S
import Prelude as P
import Control.Lens as Le
import GHC.Stack

atMay (i:| _) 0 = Just i
atMay (_:| l) ix = S.atMay l (ix -1)

elem pred (i:| l) = pred == i || P.elem pred l

imap f = Le.imap f


fromList [] = errorWithStackTrace "empty list"
fromList l = Non.fromList l

