{-# LANGUAGE DeriveFunctor,GeneralizedNewtypeDeriving,FlexibleContexts,DeriveFoldable ,TupleSections #-}
module Main where

import qualified Data.Foldable as F
import Data.Foldable (Foldable)
import Data.Char ( isAlpha )
import Data.Maybe
import Data.Monoid ((<>))
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
import Debug.Trace

data Vertex a  = Product  { unProduct :: [a]}
              deriving(Eq,Ord,Functor,Foldable)

instance (Show a ) => Show (Vertex a) where
  show (Product i) = intercalate ","  $ fmap show i

data Edge a b = Edge (Vertex a) (Vertex a) b
            deriving(Eq,Ord,Functor,Foldable)


instance (Show a, Show b) => Show (Edge a b) where
    show (Edge x y o) = printf "%s-> %s| %s " (show x) (show y) (show o)



filterTable [] b =  show b
filterTable filters b =  "(SELECT *  FROM " <> show b <>  " WHERE " <> intercalate " AND " (fmap renderFilter filters)  <> ") as " <> show b

joinPredicate r b = " ON " <> intercalate " AND " ( fmap (\(t,f) -> show t <> "." <> keyValue f <> " = " <> show b <> "." <> keyValue f )  r )

joinQuerySet (From b f  _) =  " FROM " <>  filterTable (fmap (\(k,f) -> (b,k,f) ) f ) b
joinQuerySet (Join b f  _ r (p) ) = joinQuerySet p <>  " JOIN " <> filterTable (fmap (\(k,f) -> (b,k,f) ) f ) b <> joinPredicate (S.toList r) b

data JoinPath b a
    = From b [(a,Filter)] (Set a)
    | Join b [(a,Filter)] (Set a) (Set (b ,a)) (JoinPath b a)
    deriving(Eq,Ord,Show)


data Table
    =  Base Key (JoinPath Table Key)
    |  Raw String
    |  Project (Set Attribute) Table
    |  Reduce (Set Key) (Set (Aggregate Attribute) )  Table
    deriving(Eq,Ord)

showTable (Raw s) = s
showTable (Base k p) =   joinQuerySet p
showTable (Project s t) = "SELECT " <> intercalate ","  (fmap renderAttribute $ S.toList s)  <>  showTable t
showTable (Reduce j t p) =  "(SELECT " <> intercalate "," (fmap (keyValue) (S.toList j)  <> fmap (renderAttribute.Agg )  (S.toList t ) )   <>  showTable p  <> " GROUP BY " <> intercalate "," (fmap (keyValue) (S.toList j) )  <> ") as ctx0"

instance Show Table where
    show  = showTable


addJoin :: (Ord b,Ord a) => b -> [a] -> JoinPath b a -> JoinPath b a
addJoin tnew f p = case mapPath tnew f p of
            Left accnew -> Join tnew [] (S.fromList f) (S.fromList accnew) (p )
            Right i -> i
    where
        mapPath tnew f (From t fi  s ) =  if t == tnew
                then  (Right $ From t fi snew )
                else  (Left $ fmap (t,) $ filter ((flip S.member) s) f)
            where snew =  foldr S.insert  s f
        mapPath tnew  f (Join t fi s clause (p) ) = res
            where  res = case mapPath tnew f p  of
                    Right pnew  -> Right $ Join t fi  s (foldr S.insert clause ((fmap (tnew,) $ filter ((flip S.member) s) f))) (pnew)
                    Left accnew -> if t == tnew
                        then Right $ Join t  fi  (foldr S.insert  s f)  (foldr S.insert  clause accnew ) (p)
                        else Left $ (fmap (t,) $ filter ((flip S.member) s) f) <> accnew

joinSet :: (Ord b,Ord a) => [Path  a b] -> Maybe (JoinPath  b a )
joinSet p = foldr joinPath Nothing p

joinPath (DirectPath (Edge i j ll)) (Just p)  = Just $  addJoin  ll ( unProduct i <>  unProduct j)  p
joinPath (DirectPath (Edge i j ll)) Nothing  =  Just $ From ll  [] (S.fromList ( unProduct i <> unProduct j))
joinPath (ProductPath l  k) m = foldl (flip joinPath)  m  (l <> k)



data Path a b = DirectPath (Edge a b)
            | ProductPath [Path a b] [Path a b]
            deriving(Show, Eq,Ord,Functor,Foldable)



data Graph a = Graph { vertices :: [Vertex a]
                     , edges :: [(Path a Table, Edge a Table)] }
                     deriving(Eq)

instance (Show a) => Show (Graph a) where
    show g = printf "Vertices: %s\nEdges:\n%s"
                    (unwords . map show $ vertices g)
                    (unlines . map showEdge $ edges g)
        where
          showVertice (Product x ) = show x
          showEdge (p,Edge  x y o ) = printf "%s -> %s|%s \n %s " (showVertice x) (showVertice y) (show o) (show p)

data Key
    = Key
    { keyValue :: String
    , keyType :: String
    }deriving(Eq,Ord)

instance Show Key where
  show (Key v t) = v

edgeK :: Parser (Edge Key Table)
edgeK = do
  let valid = noneOf ('\n':" -|")
  i <- (fmap (uncurry Key . break (==':')) $ many1 valid) `sepBy1` spaces
  string "->" >> spaces
  v <- (fmap (uncurry Key . break (==':')) $ many1 valid) `sepBy1` spaces
  string "|" >> spaces
  o <- many1 valid
  spaces
  return $ Edge (Product $ sort $ i)  (Product $ sort  $ v) (Raw o)





readGraph :: FilePath -> IO (Graph Key)
readGraph fp = do
  r <- parseFromFile (many1 edgeK) fp
  case r of
    Left err -> error (show err)
    Right es -> return $ Graph { edges = fmap (\g ->(DirectPath g, g)) es
                              , vertices = nub . concat . map flatEdge $ es }

flatEdge (Edge x y o) =  [x,y]


listEquals :: (Map String (Set String)) -> [Key] -> [Key] -> Bool
listEquals ms v = all (==True) . zipWith (typeEquals ms) v

typeEquals ms (Key c "") (Key m "") = c == m
typeEquals ms k1 k2
    | keyType k1 /= keyType k2  = False
    | otherwise = e
    where s = M.lookup (keyType k1) ms
          e = case s of
                Just set ->  sequal set (keyValue k1) (keyValue k2)
                Nothing -> keyValue k1 == keyValue k2
          sequal s a b =  S.member a s && S.member b s

addEdge ::  Edge Key Table -> Graph Key -> Graph Key
addEdge e@(Edge  pp pd o) g = Graph { edges = sortNub $ go nvertices (trace ("intersectss" <> show (fmap snd intersects) ) intersects ) $ go nvertices [ne]  (ne :edges g)
                   , vertices = nvertices }
    where
      ne =  (DirectPath e,e)
      intersects = filter (\(_,(Edge (Product h) (Product t)  _ ))-> intersectsOne h (unProduct pd) ||  intersectsOne t (unProduct pp) ) (edges g)
      intersectsOne :: [Key] -> [Key] -> Bool
      intersectsOne u p = or (fmap (\x -> elem x p) u)
      nvertices = sort $ nub $ pd : pp : vertices g
      nubEdges = nubBy (\(x,y)(i,j)-> y == j)
      sortEdges = sortBy (\(x,y)(i,j)-> compare y j)
      sortNub = nubEdges . sortEdges
      go [] nes  es = nes <> es
      go ves []  es = es
      go (v:ves) nes es = go ves nees nonDup
         where
            nonDup = sortNub $ nees <> es
            nees =  traceShowId  $  sortNub
                [(ProductPath (fmap fst items) [p3] ,Edge (Product (head $ fmap (edgeT . snd ) items) ) (Product d) (Raw "")) |
                (p3,Edge  (Product p) (Product d) o) <- nes ,
                items <-  replicateM (length p) es ,
                (sort . concat $ fmap (edgeH . snd) items)  ==  p ,
                allTheSame (==)  (fmap(edgeT . snd) items) ,
                all (not . (==d)) (fmap(edgeT . snd) items) ]
                <> [(ProductPath [p3] (fmap fst items) ,Edge (Product p) (Product (head $ fmap (edgeH . snd ) items) ) (Raw "") ) |
                (p3,Edge  (Product p) (Product d) o) <- nes ,
                items <-  replicateM (length d) es ,
                (sort . concat $ fmap (edgeT . snd) items)  ==  d ,
                allTheSame (==)  (fmap(edgeH . snd) items) ,
                all (not . (==p)) (fmap(edgeH . snd) items) ]
            edgeH (Edge _ (Product k) _ ) = k
            edgeT (Edge (Product i) _ _ ) = i


warshall ::  Graph Key -> Graph Key
warshall g = Graph { edges = sort $ go (vertices g) (edges g)
                   , vertices = sort $ nub $ vertices g }
    where
      go [] es     = es
      go (v:vs) es = go vs (nubBy (\(x,y)(i,j)-> y == j) (es
         <> [(ProductPath (fmap fst items) [p3],Edge (Product (head $ fmap (edgeT . snd ) items) ) (Product d) (Raw "")) |
                (p3,Edge  (Product p) (Product d) o) <- es ,
                items <-  replicateM (length p) es ,
                (sort . concat $ fmap (edgeH . snd) items)  ==  p ,
                allTheSame (==)  (fmap(edgeT . snd) items) ,
                all (not . (==d)) (fmap(edgeT . snd) items) ]
         ))
         where
            edgeH (Edge _ (Product k) _ ) = k
            edgeT (Edge (Product i) _ _ ) = i

allTheSame ::  (a -> a -> Bool) ->  [a] -> Bool
allTheSame  f xs = and $ map (f ( head xs)) (tail xs)


nested ::  (Path a b, Edge a b) -> [(a, [(a, [Path a b])])]
nested (p,Edge (Product x) (Product y)  o) = fmap (,fmap (,[p]) y) x


hashGraph  :: Ord a => Graph a -> Map a (Map a [(Path a Table)])
hashGraph = M.map (M.fromListWith (++)) .  M.fromListWith (++)  . concat . fmap nested . edges

find norm end m = case M.lookup norm m of
                    Just i -> M.lookup end i
                    Nothing -> Nothing

queryHash :: Ord a => [a] -> Map a (Map a b) -> a  -> [Maybe b]
queryHash filters schema  base =  map (\f-> find base f schema)  filters


data Aggregate a
   = Aggregate [a] String
   deriving(Show,Eq,Ord)



data Attribute
   = Metric String
   | Prod Attribute Attribute
   | Rate Attribute Attribute
   | Agg (Aggregate Attribute)
   deriving(Eq,Ord,Show)

renderAttribute (Metric s ) = s
renderAttribute (Prod m1 m2  ) =  renderAttribute m1 <> "*" <> renderAttribute m2
renderAttribute (Rate m1 m2  ) = renderAttribute m1 <> "/" <> renderAttribute m2
renderAttribute (Agg m2  ) = renderAggr renderAttribute m2


data Filter
   = Category (Set Int)
   | And [Filter]
   | Or [Filter]
   deriving(Eq,Ord,Show)


-- Pretty Print Filter
renderFilter (table,name,Category i) = show table  <> "." <> keyValue name <> " IN( " <>  intercalate "," (fmap show $ S.toList i) <> ")"
renderFilter (table,name,And i) =  intercalate " AND "  (fmap (renderFilter . (table,name,)) i)



-- Label each table with filter clauses
specializeJoin
  :: Map Key Filter
    -> JoinPath Table Key
    -> (Map Key Filter,JoinPath Table Key)
specializeJoin f (From t fi s) =  (M.fromList ff , From t (ff <> fi) s)
    where ff = catMaybes  (fmap (\ i -> fmap (i,). (flip M.lookup) f $ i) (S.toList s))
specializeJoin f (Join t fi s r (p) ) =  (ms1,Join t ( ff <> fi ) s r ss)
    where (ms,ss) = specializeJoin f p
          ff = catMaybes  (fmap (\ i -> fmap (i,). (flip M.lookup) f $ i) (S.toList s))
          ms1 = foldr (\(i,j) s -> M.insert i  j s) ms ff



type HashSchema  a b = Map a (Map a [Path a b ])


createAggregate  schema key attr  old
    = Reduce (S.fromList key) (S.fromList attr) (addAggregate schema  key attr old )

addAggregate
  :: HashSchema Key Table
     -> [Key] -> [Aggregate Attribute] -> Table -> Table
addAggregate schema key attr (Base k s) =   case concat $  catMaybes $ queryHash key  schema k  of
                        [] -> Base k  s
                        l -> Base k  (fromJust $ foldr joinPath  (Just s) l)
addAggregate schema key attr (Reduce j t  p) =  case concat $ concat $ fmap (\ki -> catMaybes $  queryHash key  schema ki)  (S.toList j)  of
                        [] -> Reduce (foldr S.insert j key) (foldr S.insert t attr)  (addAggregate schema key attr p )
                        l -> Reduce  j t  p


renderAggr f (Aggregate l s )  = s  <> "(" <> intercalate ","  (fmap f l)  <> ")"

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

createFilter filters schema (Base k j) = (m,Base k spec)
    where
      path = queryHash (M.keys  filters)  schema k
      Just join =  foldr joinPath  (Just j )  (concat $ catMaybes  path)
      (m,spec) = specializeJoin filters join
createFilter filters schema (Project a t) = fmap (Project a) (createFilter filters schema t)
createFilter filters schema (Reduce  k a t) = fmap (Reduce k a) (createFilter filters schema t)

predicate
  :: [(Key,Filter)]
     -> QueryT ()
predicate filters = do
  (schema,table) <- get
  put (schema, snd  $ createFilter (M.fromList filters) schema table)

project
  :: [Attribute]
     -> QueryT ()
project attributes =  do
  (schema,table) <- get
  put (schema,Project (S.fromList attributes) table)


entityTable =
    [(cat "id_machine","otmisnet.machine")
    ,(cat "id_client","otmisnet.cliet")
    ,(cat "id_operator","otmisnet.operator")
    ,(cat "id_contour","otmisnet.contour")
    ,(cat "id_order","otmisnet.order")]

attributesTable =
    [(cat "id_service",["timerange","bounding"])
    ,(cat "id_machine",["machine_name","machine_serial","id_client","machine_model"])
    ,(cat "id_operator",["operator_name","operator_cpf","id_client"])
    ,(cat "id_client",["client_name","client_cpf"])]

attr = [Metric "timerange",Metric "bounding",Metric "machine_name"]

cat s = Key s ""

base key entityTable schema = do
  let Just t = M.lookup key entityTable
  put (schema,Base key $ From t [] (S.singleton key))


newtype QueryT a
  = QueryT {runQueryT :: (State (HashSchema Key Table, Table)  a)} deriving(Functor,Applicative,Monad,MonadState (HashSchema Key Table, Table) )

runQuery t s =  snd $ snd $ runState ( runQueryT t) s

main :: IO ()
main = do
  -- [f] <- getArgs
  let f = "Graph.schema"
  print "Query"
  graph <-  readGraph f
  graph2 <-  readGraph "Graph2.schema"
  let g2 = (addEdge (Edge (Product [cat "id_machine",cat "timerange"] )(Product [cat "order_number"]) (Raw "otmisnet.service_order") ) $ g3)
      g1 = warshall graph
      g3 = warshall graph2
  --print $ vertices g1
  --print $ vertices g2
  print  $ vertices g1 == vertices g2
  print $ g1
  print $ g2
  --print $ g3
  print $ length $ edges g1
  print $ length $ edges g2
  --print $ length $ edges g3
  print $ edges g1 == edges g2
  let schema = hashGraph  g1
      baseTable= Base (cat "id_service")$  From  (Raw "onetgeo.services") [] (S.singleton (cat "id_service" ))
  print $  runQuery
    (do
      predicate  [(cat "id_machine", Category $ S.fromList [1,2,3])]
      project [Metric "timerange",Metric "bounding",Metric "machine_name"]
    ) (schema ,baseTable)
  print $ runQuery
    (do
      predicate  [(cat "id_machine", Category $ S.fromList [1,2,3]),(cat "id_order" , Category $ S.fromList [9,8])]
      reduce [(cat "id_operator")] [Aggregate [Metric "timerange"] "min"]
    ) (schema ,baseTable)
