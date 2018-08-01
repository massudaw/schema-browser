module Postgresql.Sql.Types where

import Data.Text (Text)
import Data.Monoid
import qualified Data.Text as T
import Types
import Data.Attoparsec.Char8 as A
import Data.Either
import Control.Applicative
import Control.Monad
import Data.Text(Text)
import Data.ByteString (ByteString)
import qualified Data.ByteString.Char8 as BS


data Value
  =  Ref SQLAttr
  |  Lit Text
  |  ApplyFun Text [Value]
  |  Cast Value Text
  deriving Show

data Pred
  =  InfixOperator ByteString Value Value
  |  UnaryOperator ByteString Value
  |  Boolean Value
  |  FunctionPred [SQLAttr] Text
  deriving Show


data SQLAttr
  = SQLABuildRow SQLRow Text
  | SQLAApply Text [SQLAttr]
  | SQLAReference (Maybe Text) Text
  | SQLAInline Text
  | SQLAValue Value
  | SQLAType SQLAttr Text
  | SQLAIndexAttr SQLAttr Text
  | SQLARename SQLAttr Text
  deriving(Show)

data JoinDirection
  = JDRight
  | JDLeft
  | JDOuter
  | JDNormal
  deriving(Show)

data JoinType
  = JTNormal
  | JTLateral
  deriving(Show)

data SQLPredicate
 = SQLPredicate Pred
 | SQLPAnd SQLPredicate SQLPredicate
 | SQLPOr SQLPredicate SQLPredicate
 | SQLPNot SQLPredicate
  deriving(Show)


data SQLArray
  = SQLAAggregate SQLAttr
  deriving(Show)

data SQLRow
  = SQLRSelect [SQLAttr] (Maybe SQLRow) (Maybe SQLPredicate)
  -- Subselect
  | SQLRRename SQLRow Text
  -- From Clause
  | SQLRFrom SQLRow
  -- Schema.Table reference
  | SQLRReference (Maybe Text) Text
  -- All join types
  | SQLRJoin SQLRow JoinType JoinDirection SQLRow (Maybe SQLPredicate)
  | SQLRUnion SQLRow SQLRow
  | SQLRIntersect SQLRow SQLRow
  | SQLRExcept SQLRow SQLRow
  -- Put Attrs into scope (a).*
  | SQLROpenAttr SQLAttr
  | SQLRInline  Text
  | SQLRUnnest SQLAttr
  deriving(Show)
