{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}

module Query where

import Warshal
import qualified Data.Foldable as F
import Data.Foldable (Foldable)
import Data.Char ( isAlpha )
import Data.Maybe
import Data.Monoid hiding (Product)

import qualified Data.Text.Lazy as T

import Data.GraphViz (preview)
import Data.Graph.Inductive.PatriciaTree
import qualified Data.Graph.Inductive.Graph as PG
import qualified Data.GraphViz.Attributes as GA
import qualified Data.GraphViz.Attributes.Complete as GAC

import Data.Traversable(Traversable)
import Database.PostgreSQL.Simple
import Database.PostgreSQL.Simple.ToField

import Control.Monad
import GHC.Exts
import Data.Tuple
import Control.Applicative
import Data.List ( nubBy,nub, sort,intercalate,sortBy,isInfixOf )
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Map (Map)
import Data.Set (Set)
import Control.Monad.State
import Control.Monad.State.Class
import System.Environment ( getArgs )
import Text.Parsec hiding(State)
import Text.Parsec.String
import Text.Printf ( printf )
import Data.Text.Lazy(Text)
import Debug.Trace

import Data.Unique

data KType
   = Primitive Text
   | Array KType
   | KOptional KType
   deriving(Eq,Ord)

instance Show KType where
  show = T.unpack . showTy

showTy (Primitive i) = i
showTy (Array i) = showTy i <> "[]"
showTy (KOptional i) = showTy i <> "*"

data Key
    = Key
    { keyValue :: Text
    , keyFastUnique :: Unique
    , keyType :: KType
    }

instance Eq Key where
   k == l = keyFastUnique k == keyFastUnique l
   k /= l = keyFastUnique k /= keyFastUnique l

instance Ord Key where
   k > l = keyFastUnique k > keyFastUnique l
   k < l = keyFastUnique k < keyFastUnique l
   k <= l = keyFastUnique k <= keyFastUnique l
   k >= l = keyFastUnique k >= keyFastUnique l


instance Show Key where
   show = T.unpack . showKey
  --show (Key v u _) = show v <> show (hashUnique u)
showKey (Key v _ t) = v <> "::" <> showTy t


data JoinPath a b
    = From b (Set a)
    | Join b (Set a) (Set (b ,a)) (JoinPath a b)
    deriving(Eq,Ord,Show)

instance Foldable (JoinPath a) where
  foldMap f (Join a _ _ p) = f a <>  F.foldMap f p
  foldMap f (From p _) = f p

data Aggregate a
   = Aggregate [a] Text
   deriving(Show,Eq,Ord)

renderAggr f (Aggregate l s )  = s  <> "(" <> T.intercalate ","  (fmap f l)  <> ")"


data Attribute
   = Metric Key
   | Prod Attribute Attribute
   | Rate Attribute Attribute
   | Agg (Aggregate Attribute)
   deriving(Eq,Ord,Show)

renderAttribute :: Attribute -> Text
renderAttribute (Metric s ) = keyValue s
renderAttribute (Prod m1 m2 ) =  renderAttribute m1 <> "*" <> renderAttribute m2
renderAttribute (Rate m1 m2 ) = renderAttribute m1 <> "/" <> renderAttribute m2
renderAttribute (Agg m2  ) = renderAggr renderAttribute m2


data Filter
   = Category (Set Text)
   | And [Filter]
   | Or [Filter]
   deriving(Eq,Ord,Show)


-- Pretty Print Filter
renderFilter (table ,name,Category i) = tableName table <> "." <> keyValue name <> " IN( " <>  T.intercalate "," (fmap (\s -> "'" <> s <> "'" ) $ S.toList i) <> ")"
renderFilter (table ,name,And i) =  T.intercalate " AND "  (fmap (renderFilter . (table ,name,)) i)



data Table
    =  Base (Set Key) (JoinPath Key Table)
    |  Raw Text Text (Set Key) (Maybe Key) (Set (Path Key Text)) (Set Key)
    |  Filtered [(Key,Filter)] Table
    |  Project [Attribute] Table
    |  Reduce (Set Key) (Set (Aggregate Attribute) )  Table
    |  Limit Table Int
    deriving(Eq,Ord,Show)

tableName (Base _ (From t  _)) = tableName t
tableName (Raw _ t _ _ _ _ ) = t
tableName (Filtered _ t ) = tableName t
tableName (Limit t _) = tableName t
tableName i = error $ show i


--- Traverse the joinPath returning the keyList
joinKeys (From b k ) = fmap (b,) (S.toList k)
joinKeys (Join b k _ p) = fmap (b,) (S.toList k) <> joinKeys p


renderNamespacedKeySet (t,k) = tableName t <> "." <> keyValue k

-- Generate a sql query from the AST
showTable :: Table -> Text
showTable (Filtered f t) = filterTable (fmap (\(k,f) -> (t,k,f) ) f ) t
  where
      filterTable [] b =  showTable b
      filterTable filters b =  "(SELECT *  FROM " <> showTable b <>  " WHERE " <> T.intercalate " AND " (fmap renderFilter filters)  <> ") as " <> ( tableName b )
showTable (Raw s t _ _  _ _) = s <> "." <> t
showTable b@(Base k p) = " FROM (SELECT " <> (T.intercalate "," $ ( keyValue <$> S.toList attrs) <> fmap renderNamespacedKeySet jattrs ) <> joinQuerySet p <>") as base"
  where
    attrs = S.filter (not . (`S.member` (S.fromList $ fmap snd jattrs) )) $ allKeys b
    jattrs = nubBy (\ i j-> snd i == snd j) $ joinKeys p
    joinQuerySet (From b _) =  " FROM " <>  showTable b
    joinQuerySet (Join b _ r p) = joinQuerySet p <>  " JOIN " <> showTable b <> joinPredicate (S.toList r) b
      where joinPredicate r b = " ON " <> T.intercalate " AND " ( fmap (\(t,f) -> tableName t <> "." <> keyValue f <> " = " <> tableName b <> "." <> keyValue f )  r )


showTable (Project [] t) =  "(SELECT " <>  showTable t  <> ") as ctx0"
showTable (Project s t) = "(SELECT " <> T.intercalate ","  (renderAttribute <$> s)  <>  showTable t  <> ") as ctx0"
showTable (Reduce j t p) =  "SELECT " <> T.intercalate "," (fmap keyValue (S.toList j)  <> fmap (renderAttribute.Agg )  (S.toList t ) )   <> " FROM " <>   showTable p  <> " GROUP BY " <> T.intercalate "," (fmap keyValue (S.toList j))
showTable (Limit t v) = showTable t <> " LIMIT 100"


dropTable (Raw sch tbl _ _ _ _ )= "DROP TABLE "<> sch <>"."<> tbl

createTable (Raw sch tbl pk _ fk attr) = "CREATE TABLE " <> sch <>"."<> tbl <> "\n(\n" <> T.intercalate "," commands <> "\n)"
  where commands = (renderAttr <$> S.toList attr ) <> [renderPK]
        renderAttr (Key name _ ty) = name <> " " <> renderTy ty
        renderKeySet pk = T.intercalate "," (fmap keyValue (S.toList pk ))
        renderTy (KOptional ty) = renderTy ty <> " NOT NULL"
        renderTy (Array ty) = renderTy ty <> "[] "
        renderTy (Primitive ty) = ty
        renderPK = "CONSTRAINT " <> tbl <> "_PK PRIMARY KEY (" <>  renderKeySet pk <> ")"


joinPath ((Path i ll j)) (Just p)  = Just $  addJoin  ll ( i `S.union` j)  p
joinPath ((Path i ll j)) Nothing  =  Just $ From ll   ( i `S.union` j)
joinPath (ComposePath i (l,ij,k) j ) m = foldr joinPath  m  (S.toList l <> S.toList k)
joinPath (PathOption i p j ) m =  joinPath ( head $ S.toList p ) m


addJoin :: (Ord b,Ord a) => a -> Set b -> JoinPath b a -> JoinPath b a
addJoin tnew f p = case mapPath tnew f p of
            Left accnew -> Join tnew  f accnew (p )
            Right i -> i
    where
        mapPath :: (Ord b , Ord a) => a -> Set b -> JoinPath b a -> Either (Set (a,b)) (JoinPath b a)
        mapPath tnew f (From t   s ) =  if t == tnew
                then  (Right $ From t  snew )
                else  (Left $ S.mapMonotonic (t,) $  s `S.intersection` f)
            where snew =  s `S.union` f
        mapPath tnew  f (Join t  s clause p ) = res
            where  res = case mapPath tnew f p  of
                    Right pnew  -> Right $ Join t   s (clause `S.union` (S.mapMonotonic (tnew,) $  s `S.intersection` f)) pnew
                    Left accnew -> if t == tnew
                        then Right $ Join t  (s `S.union` f)  (clause `S.union` accnew ) p
                        else Left $ (S.mapMonotonic (t,) $ s `S.intersection` f)  `S.union` accnew




addFilterTable ff b@(Filtered fi _ ) = Filtered (fi<>ff) b
addFilterTable ff b = Filtered ff b

-- Label each table with filter clauses
specializeJoin
  :: Map Key Filter
    -> JoinPath Key Table
    -> (Map Key Filter,JoinPath Key Table )
specializeJoin f (From t s) =  (M.fromList ff , From (addFilterTable ff t) s)
    where ff = catMaybes  (fmap (\ i -> fmap (i,). (flip M.lookup) f $ i) (S.toList s))
specializeJoin f (Join t s r (p) ) =  (ms1,Join (addFilterTable ff t) s r ss)
    where (ms,ss) = specializeJoin f p
          ff = catMaybes  (fmap (\ i -> fmap (i,). (flip M.lookup) f $ i) (S.toList s))
          ms1 = foldr (\(i,j) s -> M.insert i  j s) ms ff

createFilter
  :: Map Key Filter
  ->  HashSchema Key Table
  -> Table
  -> (Map Key Filter, Table)
createFilter filters schema (Base k j) = (m,Base k spec)
    where
      path = queryHash (M.keys  filters)  schema k
      Just join =  foldr joinPath (Just j) (catMaybes path)
      (m,spec) = specializeJoin filters join
createFilter filters schema (Project a t) = fmap (Project a) (createFilter filters schema t)
createFilter filters schema (Reduce  k a t) = fmap (Reduce k a) (createFilter filters schema t)




createAggregate  schema key attr  old
    = Reduce (S.fromList key) (S.fromList attr) (addAggregate schema  key attr (Project [] old))

addAggregate
  :: HashSchema Key Table
     -> [Key] -> [Aggregate Attribute] -> Table -> Table
addAggregate schema key attr (Base k s) =   case   catMaybes $ queryHash key  schema k  of
                        [] -> Base k  s
                        l -> Base k  (fromJust $ foldr joinPath  (Just s) l)

addAggregate schema key aggr (Project a t) =  Project (foldr (:) a attr )  (addAggregate schema key aggr t)
  where attr =  concat $ fmap (\(Aggregate l _)-> l) aggr
addAggregate schema key attr (Reduce j t  p) =  case concat $  fmap (\ki -> catMaybes $  queryHash key  schema (S.singleton ki))  (S.toList j)  of
                        [] -> Reduce (foldr S.insert j key) (foldr S.insert t attr)  (addAggregate schema key attr p )
                        l -> Reduce  j t  p


reduce ::  [Key]
     -> [Aggregate Attribute]
     -> QueryT ()
reduce group aggr = do
  (schema,table) <- get
  put (schema,createAggregate schema group aggr table)
  return ()



freeVars (Metric c) = [c]
freeVars (Rate c k ) = freeVars c <> freeVars k
freeVars (Prod c k ) = freeVars c <> freeVars k
freeVars (Agg (Aggregate l _ ) ) = concatMap freeVars l

predicate
  :: [(Key,Filter)]
     -> QueryT ()
predicate filters = do
  (schema,table) <- get
  put (schema, snd  $ createFilter (M.fromList filters) schema table)


data PK a
  = PK { pkKey:: [a], pkDescription :: [a]} deriving(Functor,Foldable,Traversable)

projectDesc
     :: QueryT (PK Key)
projectDesc =  do
  (schema,table) <- get
  let k@(keys,desc) = baseDescKeys table
      pk = PK (S.toList keys) (S.toList desc)
  put (schema,Limit (Project (fmap Metric (F.toList pk) ) table) 100)
  return pk


project
  :: [Attribute]
     -> QueryT [Key]
project attributes =  do
  (schema,table) <- get
  let result = filter (`elem` attributes) (fmap Metric $ S.toList $ allKeys table)
  put (schema,Limit (Project result table) 100 )
  return $ fmap (\(Metric i) -> i) result

projectAll
     :: QueryT [Key]
projectAll =  do
  (schema,table) <- get
  let result = S.toList $ allKeys table
  put (schema,Limit (Project (fmap Metric result ) table)100)
  return result

baseDescKeys :: Table -> (Set Key ,Set Key)
baseDescKeys (Raw _ _ pk Nothing _ _ ) = (pk,pk)
baseDescKeys (Raw _ _ pk (Just d) _ _ ) = (pk,S.singleton d)
baseDescKeys (Limit p _ ) = baseDescKeys p
baseDescKeys (Filtered _ p) = baseDescKeys p
baseDescKeys (Project _ p) = baseDescKeys p
baseDescKeys (Reduce _ _ p) = baseDescKeys p
baseDescKeys (Base _ p) = from baseDescKeys p
  where from f (From t _ ) = f t
        from f (Join _ _ _ p) =  from f p


allKeys :: Table -> Set Key
allKeys (Raw _ _ _ _ _ p) = p
allKeys (Limit p _ ) = allKeys p
allKeys (Filtered _ p) = allKeys p
allKeys (Project _ p) = allKeys p
allKeys (Reduce _ _ p) = allKeys p
allKeys (Base _ p) = F.foldMap allKeys p


newtype QueryT a
  = QueryT {runQueryT :: State (HashSchema Key Table, Table)  a} deriving(Functor,Applicative,Monad,MonadState (HashSchema Key Table, Table) )

runQuery t =  runState ( runQueryT t)

{-
--- Read Schema Graph
edgeK :: Parser (Path Key Table)
edgeK = do
  let valid = noneOf ('\n':" -|")
      key (i,j) =  Key i (Primitive j)
  i <- (fmap (key . break (==':')) $ many1 valid) `sepBy1` spaces
  string "->" >> spaces
  v <- (fmap (key . break (==':')) $ many1 valid) `sepBy1` spaces
  string "|" >> spaces
  o <- many1 valid
  spaces
  return $ Path (S.fromList i)   ((\(i,j)->Raw  i (T.tail j) S.empty ) $ T.break (=='.') o)(S.fromList v)


readGraph :: FilePath -> IO (Graph Key Table)
readGraph fp = do
  r <- parseFromFile (many1 edgeK) fp
  case r of
    Left err -> error (show err)
    Right es -> return $ Graph { edges = pathMap es
                              , hvertices = nub .  map (fst .pbound) $ es
                              , tvertices = nub .  map (snd .pbound) $ es  }
-}

pathLabel (ComposePath i (p1,p12,p2) j) = T.intercalate "," $  fmap pathLabel (S.toList p1) <> fmap pathLabel (S.toList p2)
pathLabel (PathOption i p j) = T.intercalate "\n" (fmap pathLabel (S.toList p))
pathLabel (Path i t j) = tableName t

instance GA.Labellable (Path Key Table) where
  toLabelValue l  = GAC.StrLabel (pathLabel l)
instance GA.Labellable (Set Key ) where
  toLabelValue i = GAC.StrLabel (T.intercalate "," (keyValue <$> S.toList i))

cvLabeled :: Graph Key Table -> Gr (Set Key) (Path Key Table)
cvLabeled g = PG.mkGraph lvertices ledges
  where v = M.fromList $ zip set [0..]
        set = nub $ hvertices g <> tvertices g
        lvertices = fmap (\e -> (fromJust (M.lookup e v),e)) set
        ledges = fmap (\e -> case pbound e of
                            (t,h) -> (fromJust (M.lookup t v) ,fromJust (M.lookup h v) ,e)) (fmap snd $ M.toList $ edges g)


