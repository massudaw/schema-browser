module Postgresql.Codegen where

import Data.Text (Text)
import Data.Monoid
import qualified Data.Text as T

data SQLAttr
  = SQLABuildRow SQLRow Text
  | SQLAApply Text [SQLAttr]
  | SQLAReference (Maybe Text) Text
  | SQLAInline Text
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
 = SQLPredicate [SQLAttr] Text
 | SQLPAnd SQLPredicate SQLPredicate
 | SQLPOr SQLPredicate SQLPredicate
 | SQLPNot SQLPredicate
  deriving(Show)


data SQLArray
  = SQLAAggregate SQLAttr
  deriving(Show)

data SQLRow
  = SQLRSelect [SQLAttr] (Maybe SQLRow)
  -- Subselect
  | SQLRRename SQLRow Text
  -- From Clause
  | SQLRFrom SQLRow
  -- Schema.Table reference
  | SQLRReference (Maybe Text) Text
  -- All join types
  | SQLRJoin SQLRow JoinType JoinDirection SQLRow (Maybe SQLPredicate)
  -- Put Attrs into scope (a).*
  | SQLROpenAttr SQLAttr
  | SQLRInline  Text
  | SQLRUnnest SQLAttr
  deriving(Show)

opEq = "% = %"
opLte  = "% <= %"
opLt  = "% < %"
opGt  = "% > %"
opGte  = "% >= %"
opIsNull = "% IS NULL"

pNot =  SQLPNot
pAnd = SQLPAnd
pOr = SQLPOr

example =
  SQLRSelect
    [SQLAReference (Just "ex") "c1", SQLAReference Nothing "id"]
    (Just
       (SQLRJoin
          (SQLRFrom (SQLRReference Nothing "example"))
          JTLateral
          JDRight
          (SQLRReference (Just "ex") "example2")
          (Just $ pAnd
             (SQLPredicate
                [ SQLAReference (Just "example") "c1"
                , SQLAReference (Just "ex") "c1"
                ]
                opEq)
             (SQLPredicate [SQLAReference (Just "ex") "c2"] opIsNull))))

test = renderRow example

renderAttr (SQLAReference t a) = maybe a (\t -> t <> "." <> a) t
renderAttr (SQLAIndexAttr a f ) = "(" <> renderAttr a <> ")." <> f
renderAttr (SQLARename a f ) =  renderAttr a <> " AS " <> f
renderAttr (SQLAInline a ) =  a

renderJoinType JTLateral = "LATERAL"
renderJoinType JTNormal = ""
renderJoinDirection JDRight  = "RIGHT"
renderJoinDirection JDLeft = "LEFT"
renderJoinDirection JDOuter = "OUTER"
renderJoinDirection JDNormal = ""

renderPredicate (SQLPAnd l r) = "(" <> renderPredicate l <> " AND " <> renderPredicate r <> ")"
renderPredicate (SQLPOr l r) = "(" <> renderPredicate l <> " OR " <> renderPredicate r <> ")"
renderPredicate (SQLPNot l ) = "NOT (" <> renderPredicate l <> ")"
renderPredicate (SQLPredicate a s ) = T.intercalate "" $ concat $ zipWith (\i j -> [j,i]) (renderAttr <$> a) (T.split ('%'==) s)

renderRow (SQLRSelect i j  ) = "SELECT "  <> T.intercalate "," (renderAttr <$> i ) <> " " <> maybe "" renderRow j
renderRow (SQLRRename r@(SQLRSelect _ _) l ) = "(" <> renderRow r <> ") AS " <> l
renderRow (SQLRRename r l ) = renderRow r <> " AS " <> l
renderRow (SQLRFrom r) = "FROM " <> renderRow r
renderRow (SQLRJoin r t d j p ) = renderRow r <>  " "  <> joinType <> " " <> renderRow j <> " ON " <> maybe "true" renderPredicate  p
  where joinType = T.intercalate " " $ filter (/="") [renderJoinDirection d , "JOIN", renderJoinType t ]
renderRow (SQLRReference s t ) =   maybe t (\i -> i <> "." <> t) s
renderRow (SQLROpenAttr t ) =  "(" <> renderAttr t <> ").*"
renderRow (SQLRInline t ) = t
renderRow (SQLRUnnest a ) =  "UNNEST(" <> renderAttr a <> ")"
renderRow i = error (show i)

