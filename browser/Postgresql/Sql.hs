module Postgresql.Sql where

import Types
import Data.Attoparsec.Char8 as A
import Data.Either
import Control.Applicative
import Control.Monad
import Data.Text(Text)
import Data.ByteString (ByteString)
import qualified Data.ByteString.Char8 as BS

import Database.PostgreSQL.Simple
data ColumnName
  = Column ByteString
  | FullColumn ByteString ByteString
  deriving(Show)

data ColumnRef
  = RenameColumn Value ByteString
  | KeepColumn Value
  deriving(Show)

name = A.takeWhile1 (not . (`elem` (";() .,"::String)))

parseColumn = full <|> simple
    where
      simple = Column <$> name
      full = do
        table <-  name
        char '.'
        column <- name
        return (FullColumn table column)

parseColumnRef  = rename  <|> fmap KeepColumn  value
  where
      rename = do
        old <- value
        many1 space
        string "AS" <|> string "as"
        many1 space
        new <- name
        return (RenameColumn old new )


data OpenTable
  = FromCommand Command ByteString
  | FromRaw ByteString ByteString
  | Empty
  | Join OpenTable OpenTable String
  deriving(Show)

data Command
  = Select [ColumnRef] OpenTable (Maybe Where)
  | SqlUnion Command Command
  | SqlIntersect Command Command
  | SqlExcept Command Command
  deriving(Show)

data BooleanTree
  = Or  BooleanTree BooleanTree
  | And BooleanTree  BooleanTree
  | NotB BooleanTree
  | Prim Pred
  deriving Show

data Value
  =  Ref ColumnName
  |  Lit ByteString
  |  ApplyFun ByteString [Value]
  |  Cast Value ByteString
  deriving Show

data Pred
  =  InfixOperator ByteString Value Value
  |  UnaryOperator ByteString Value
  |  Boolean Value
  deriving Show

data Where
  = Where  BooleanTree
  deriving Show

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
  return $ SqlUnion i1 i2

intersect  operation = do
  i1 <- operation
  many space >> string "INTERSECT" >> many space
  i2 <- operation
  return $ SqlUnion i1 i2

except operation = do
  i1 <- operation
  many space >> string "EXCEPT" >> many space
  i2 <- operation
  return $ SqlUnion i1 i2




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
  return $ Select  list  t f

table = rawTable

rawTable = do
  string "FROM"
  many space
  s <- name
  char '.'
  t <- name
  return $ FromRaw s t

value =  tryFun function (tryFun cast (boolean <|> paren <|> ref))
  where
    tryFun f i = f i <|> i
    boolean = Lit <$> (string "true" <|> string "false")
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
       args  <- char '(' *> sepBy i  (char ',') <* char ')'
       return $ ApplyFun n args



tryFilter = parseOnly whereClause "WHERE (NOT convidados.confirmado)"

paren v = (char '(' >> many space ) *> v <* (many space >> char ')')

predi = tree
  where
    tree = and <|> or <|> notP <|> prim
    notP = fmap NotB $ string "NOT"  >> many space >> prim
    prim = (Prim . Boolean <$>  value) <|> paren tree
    and =   do
      vl <- prim
      many space
      string "AND"
      many space
      vr <- prim
      return (And vl vr)
    or =   do
      vl <- prim
      many space
      string "OR"
      many space
      vr <- prim
      return (And vl vr)




maybeFilter = fmap Just whereClause <|> return Nothing

whereClause =  do
  many space
  string "WHERE"
  many space
  Where  <$> predi


type View = Either (ByteString,String) (Text,Text,Text,Command)

testViews :: String ->  IO [View]
testViews i = do
  conn <- connectPostgreSQL "dbname=incendio  password=jacapodre"
  decodeViews conn i

decodeViews conn schema = do
  result <- query conn "SELECT * FROM pg_views where schemaname = ? " (Only schema)
  mapM (\(s,t,o,vdef) ->  do
    let inp = BS.map (\i -> if i/= '\n' then i else ' ')  vdef
    return (either (Left.(inp,)) (Right.(s,t,o, )) $ parseOnly  (command operation) inp  :: View)) result




