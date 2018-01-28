module Postgresql.Function (replaceexpr,indexLabel) where

import Types
import Utils
import Safe
import Step.Host
import Data.Monoid
import Data.Text (Text)
import qualified Data.Text as T

replaceexpr :: Expr -> [Text]  -> Text
replaceexpr k ac = go k
  where
    go :: Expr -> Text
    go (Function i e) = i <> "(" <> T.intercalate ","  (go   <$> e) <> ")"
    go (Value i ) = justError "no value" (ac `atMay` i )

indexLabel  :: Show a =>
    Access Key
    -> TBData Key a
    -> (Column  Key a)
indexLabel p@(IProd b l) v =
    case findAttr l v of
      Just i -> i
      Nothing -> error "no fk"
indexLabel p@(Nested l m) v =
  case findFK (l) v of
    Just (IT k (TB1 a)) -> indexLabelU m a
    Just (IT k (LeftTB1 (Just (TB1 a)))) -> indexLabelU m a
    Nothing -> error "no fk"

indexLabel  i v = error (show (i, v))
indexLabelU  (Many [One nt]) v = indexLabel  nt v


