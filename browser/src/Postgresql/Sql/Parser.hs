module Postgresql.Sql.Parser where

import Types
import Postgresql.Sql.Types
import Data.Attoparsec.Char8 as A
import Data.Attoparsec.Char8 as A
import Data.Either
import Control.Applicative
import Control.Monad
import Data.Text(Text)
import qualified Data.Text as T
import Data.ByteString (ByteString)
import qualified Data.ByteString.Char8 as BS

import Database.PostgreSQL.Simple


name = do
   l <- letter_ascii
   T.pack . (l:) . BS.unpack <$> A.takeWhile1 (not . (`elem` ("';() .,"::String)))

parseColumn = full <|> simple
    where
      simple = SQLAReference Nothing <$> name
      full = do
        table <-  name
        char '.'
        column <- name
        return (SQLAReference (Just table) column)

parseColumnRef  = rename  <|> fmap SQLAValue value
  where
      rename = do
        old <- value
        many1 space
        string "AS" <|> string "as"
        many1 space
        new <- name
        return (SQLARename (SQLAValue old) new )

parseValue = parseOnly value
testParseColumn = parseOnly select "SELECT col1, table1.col1 , table1.col1 as col2 , col1 as col2 FROM sch1.table1 WHERE ( true AND (NOT true) ) OR false"
parseColList = sepBy parseColumnRef (many space >> char ','>> many space)

command i = do
  r <-  i
  many space >> try (char ';')
  return r

union operation = do
  i1 <- operation
  many space >> string "UNION" >> many space
  i2 <- operation
  return $ SQLRUnion i1 i2

intersect  operation = do
  i1 <- operation
  many space >> string "INTERSECT" >> many space
  i2 <- operation
  return $ SQLRIntersect i1 i2

except operation = do
  i1 <- operation
  many space >> string "EXCEPT" >> many space
  i2 <- operation
  return $ SQLRExcept i1 i2


operation = setop primop <|> primop <|> setop  (paren operation)
  where
    primop = select
    setop primop = union primop <|> intersect primop <|> except primop

select = do
  many space
  string "SELECT"
  many space
  list <- parseColList
  many space
  t <- table
  f <- maybeFilter
  return $ SQLRSelect list  (Just t) f

table = rawTable

rawTable = do
  string "FROM"
  many space
  s <- name
  char '.'
  t <- name
  return $ SQLRReference (Just s) t

value =  tryFun function (tryFun cast (str <|> boolean <|> paren <|> ref))
  where
    tryFun f i = f i <|> i
    str = Lit  <$> (char '\'' *> name  <* char '\'')
    boolean = Lit . T.pack .BS.unpack <$> (string "true" <|> string "false")
    paren = (char '(' >> many space ) *> value <* (many space >> char ')')
    ref =  Ref <$> parseColumn
    cast i  =  do
       v <- i
       many space
       string "::"
       many space
       ty <- name
       return $ Cast  v ty
    function i = do
       n <- name
       args  <- char '(' *> sepBy (many space  *> i <* many space)   (char ',') <* char ')'
       return $ ApplyFun n args



tryFilter = parseOnly whereClause "WHERE (NOT convidados.confirmado)"

paren v = (char '(' >> many space ) *> v <* (many space >> char ')')

predi = tree
  where
    tree = and <|> or <|> notP <|> prim
    notP = fmap SQLPNot $ string "NOT"  >> many space >> prim
    prim = (SQLPredicate . Boolean <$>  value) <|> paren tree
    and =   do
      vl <- prim
      many space
      string "AND"
      many space
      vr <- prim
      return (SQLPAnd vl vr)
    or =   do
      vl <- prim
      many space
      string "OR"
      many space
      vr <- prim
      return (SQLPOr vl vr)


maybeFilter = fmap Just whereClause <|> return Nothing

whereClause =  do
  many space
  string "WHERE"
  many space
  predi


type View = Either (ByteString,String) (Text,Text,Text,SQLRow)

testViews :: String ->  IO [View]
testViews i = do
  conn <- connectPostgreSQL "dbname=incendio  password=jacapodre"
  decodeViews conn i

decodeViews conn schema = do
  result <- query conn "SELECT * FROM pg_views where schemaname = ? " (Only schema)
  mapM (\(s,t,o,vdef) ->  do
    let inp = BS.map (\i -> if i/= '\n' then i else ' ')  vdef
    return (either (Left.(inp,)) (Right.(s,t,o, )) $ parseOnly  (command operation) inp  :: View)) result




