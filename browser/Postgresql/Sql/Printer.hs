module Postgresql.Sql.Printer where

import Postgresql.Sql.Types
import Data.Text (Text)
import Data.Monoid
import qualified Data.Text as T


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
                (FunctionPred [ SQLAReference (Just "example") "c1"
                , SQLAReference (Just "ex") "c1"
                ]
                opEq))
             (SQLPredicate (FunctionPred [SQLAReference (Just "ex") "c2"] opIsNull))))) Nothing

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
renderPredicate (SQLPredicate (FunctionPred a s)) = T.intercalate "" $ concat $ zipWith (\i j -> [j,i]) (renderAttr <$> a) (T.split ('%'==) s)

renderRow (SQLRSelect i j  _ ) = "SELECT "  <> T.intercalate "," (renderAttr <$> i ) <> " " <> maybe "" renderRow j
renderRow (SQLRRename r@(SQLRSelect _ _ _ ) l ) = "(" <> renderRow r <> ") AS " <> l
renderRow (SQLRRename r l ) = renderRow r <> " AS " <> l
renderRow (SQLRFrom r) = "FROM " <> renderRow r
renderRow (SQLRJoin r t d j p ) = renderRow r <>  " "  <> joinType <> " " <> renderRow j <> " ON " <> maybe "true" renderPredicate  p
  where joinType = T.intercalate " " $ filter (/="") [renderJoinDirection d , "JOIN", renderJoinType t ]
renderRow (SQLRReference s t ) =   maybe t (\i -> i <> "." <> t) s
renderRow (SQLROpenAttr t ) =  "(" <> renderAttr t <> ").*"
renderRow (SQLRInline t ) = t
renderRow (SQLRUnnest a ) =  "UNNEST(" <> renderAttr a <> ")"
renderRow i = error (show i)

