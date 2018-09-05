{-# LANGUAGE  TypeFamilies #-}
module Patch where

import Utils
import Control.Applicative

class Address f where
  type Idx f
  type Content f
  index :: f -> Idx f
  content :: f -> Content f
  rebuild :: Idx f -> Content f -> f


class Compact f where
  compact :: [f] -> [f]

class Patch f where
  type Index f
  diff :: f -> f -> Maybe (Index f)
  diff' :: f -> f -> (Index f)
  diff' i j = justError "cant diff" $ diff i j
  apply :: f -> Index f -> f
  apply i = either (\i -> error $ "no apply: " ++ i) fst . applyUndo i
  applyIfChange :: f -> Index f -> Maybe f
  applyIfChange i = either (const Nothing) (Just . fst) . applyUndo i
  applyUndo :: f -> Index f -> Either String (f, Index f)
  applyUndo i j =
    maybe (Left "cant diff") Right $ liftA2 (,) o (flip diff i =<< o)
    where
      o = applyIfChange i j
  create :: Index f -> f
  create i = justError ("no create: ") . createIfChange $ i
  createIfChange :: Index f -> Maybe f
  patch :: f -> Index f


