{-# LANGUAGE DeriveFunctor,FlexibleContexts,DeriveFoldable ,TupleSections #-}
module Main where

import qualified Data.Foldable as F
import Data.Functor.Identity
import Data.Foldable (Foldable)
import Data.Char ( isAlpha )
import Data.Maybe
import Data.Monoid ((<>))
import Control.Monad
import GHC.Exts
import Data.Tuple
import Control.Applicative
import Data.List ( nubBy,nub, sort,intercalate )
import qualified Data.Map as M
import qualified Data.Set as S 
import Data.Map (Map) 
import Data.Set (Set) 
import System.Environment ( getArgs )
import Text.Parsec
import Text.Parsec.String
import Text.Printf ( printf )
import Debug.Trace (trace)

data Vertex a  = Product  { unProduct :: [a]}
              deriving(Eq,Show,Ord,Functor,Foldable)
data Edge a b = Edge (Vertex a) (Vertex a) b 
            deriving(Eq,Ord,Show,Functor,Foldable)




joinQueryFilterSet (FilterF (filters , From b _)) = " FROM " <>  filterTable filters b
joinQueryFilterSet (FilterF (filters , Join b _ r p )) = joinQueryFilterSet p <>  " JOIN " <> filterTable filters b <>  joinPredicate (S.toList r ) b 
    
filterTable filters b =  "(SELECT *  FROM " <> b <>  " WHERE " <> intercalate " AND " (fmap renderFilter filters)  <> ") as " <> b
joinPredicate r b = " ON " <> intercalate " AND " ( fmap (\(t,f) ->  t <> "." <> keyValue f <> " = " <> b <> "." <> keyValue f )  r )

joinQuerySet (From b _) =  " FROM " <> b 
joinQuerySet (Join b _ r (Identity p) ) = joinQuerySet p <>  " JOIN " <> b <> joinPredicate (S.toList r) b 


data JoinPath f b a 
    = From b (Set a)
    | Join b (Set a) (Set (b ,a)) (f (JoinPath f b a))
    -- deriving(Show)

addJoin :: (Ord b,Ord a) => b -> [a] -> JoinPath Identity b a -> JoinPath Identity b a
addJoin tnew f p = case mapPath tnew f p of
            Left accnew -> Join tnew (S.fromList f) (S.fromList accnew) (Identity p )
            Right i -> i
    where 
        mapPath tnew f (From t s ) =  if t == tnew
                then  (Right $ From t snew )
                else  (Left $ fmap (t,) $ filter ((flip S.member) s) f)
            where snew =  foldr S.insert  s f
        mapPath tnew  f (Join t s clause (Identity p) ) = res 
            where  res = case mapPath tnew f p  of
                    Right pnew  -> Right $ Join t s (foldr S.insert clause ((fmap (tnew,) $ filter ((flip S.member) s) f))) (Identity pnew)
                    Left accnew -> if t == tnew 
                        then Right $ Join t  (foldr S.insert  s f)  (foldr S.insert  clause accnew ) (Identity p)
                        else Left $ (fmap (t,) $ filter ((flip S.member) s) f) <> accnew

joinSet :: (Ord b,Ord a) => [Path  a b] -> Maybe (JoinPath  Identity b a )
joinSet p = foldr joinPath Nothing p

joinPath (DirectPath (Edge i j ll)) (Just p)  = Just $  addJoin  ll ( unProduct i <>  unProduct j)  p 
joinPath (DirectPath (Edge i j ll)) Nothing  =  Just $ From ll (S.fromList ( unProduct i <> unProduct j))  
joinPath (ProductPath l  k) m = foldl (flip joinPath)  m  (l ++  [k])




data Path a b = DirectPath (Edge a b)
            | ProductPath [Path a b] (Path a b)
            deriving(Show, Eq,Functor,Foldable)



data Graph a = Graph { vertices :: [Vertex a]
                     , edges :: [(Path a String, Edge a String)] }

instance (Show a) => Show (Graph a) where
    show g = printf "Vertices: %s\nEdges:\n%s"
                    (unwords . map show $ vertices g)
                    (unlines . map showEdge $ edges g)
        where
          showVertice (Product x ) = show x  
          showEdge (p,Edge  x y o ) = printf "%s -> %s \n %s " (showVertice x) (showVertice y) (show p)

data Key
    = Key 
    { keyValue :: String 
    , keyType :: String 
    }deriving(Eq,Ord,Show) 

edgeK :: Parser (Edge Key String)
edgeK = do
  let valid = noneOf ('\n':" -|")
  i <- (fmap (uncurry Key . break (==':')) $ many1 valid) `sepBy1` spaces
  string "->" >> spaces
  v <- (fmap (uncurry Key . break (==':')) $ many1 valid) `sepBy1` spaces
  string "|" >> spaces
  o <- many1 valid 
  spaces
  return $ Edge (Product $ sort $ i)  (Product $ sort  $ v) o 


edgeP :: Parser (Edge String String)
edgeP = do
  let valid = noneOf ('\n':" -|")
  i <- (many1 valid) `sepBy1` spaces
  string "->" >> spaces
  v <- (many1 valid) `sepBy1` spaces
  string "|" >> spaces
  o <- many1 valid 
  spaces
  return $ Edge (Product $ sort i)  (Product $ sort v) o 



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
          
setMap = M.fromList [(":Time",S.fromList ["tstzrange(to_timestamp(service_timestamp_init/1000.0),to_timestamp(service_timestamp_end/1000.0))","tstzrange(to_timestamp(timestamp_init/1000.0),to_timestamp(timestamp_end/1000.0))"])]

warshall ::  Graph Key -> Graph Key 
warshall g = Graph { edges = go (vertices g) (edges g)
                   , vertices = vertices g }
    where
      go [] es     = es
      go (v:vs) es = go vs (nubBy (\(x,y)(i,j)-> y == j) (es
         ++ [(ProductPath (fmap fst items) p3,Edge (Product (head $ fmap (edgeT . snd ) items) ) (Product d) o) | 
                (p3,Edge  (Product p) (Product d) o) <- es ,
                items <-  replicateM (length p) es , 
                listEquals setMap (sort . concat $ fmap (edgeH . snd) items)   p   && allTheSame (listEquals setMap)  (fmap( edgeT . snd) items) && all (not . listEquals setMap d) ( fmap(  edgeT . snd) items) ]
         ))
         where 
            edgeH (Edge (Product i) (Product k) _ )  = k
            edgeT (Edge (Product i) (Product k) _ )  = i

allTheSame ::  (a -> a -> Bool) ->  [a] -> Bool
allTheSame  f xs = and $ map (f ( head xs)) (tail xs)


nested ::  (Path a b, Edge a b) -> [(a, [(a, [Path a b])])]
nested (p,Edge (Product x) (Product y)  o) = fmap (,fmap (,[p]) y) x


hashGraph  :: Ord a => Graph a -> Map a (Map a [(Path a String)])
hashGraph = M.map (M.fromListWith (++)) .  M.fromListWith (++)  . concat . fmap nested . edges 

find norm end m = case M.lookup norm m of
                    Just i -> M.lookup end i
                    Nothing -> Nothing

queryHash :: Ord a => [a] -> Map a (Map a b) -> a  -> [Maybe b]
queryHash filters schema  base =  map (\f-> find base f schema)  filters 


{-
data Table 
    = Raw [Vertex String]  [Attribute]
    | Filtered Table [Filter]
    | Grouped Table (([Vertex String],[Attribute]) -> [Vertex String]) (([Vertex String],[Attribute]) -> [Attribute])
    | Sorted Table [Vertex String -> Vertex String]
    -- | Join  [Table]
-}


data Aggregate a 
   = Aggregate [a] String
   deriving(Show,Eq,Ord)


data Attribute 
   = Metric Double
   | Rate Attribute Attribute

data Filter
   = Category (Set Int)
   | And [Filter]
   | Or [Filter]
   

-- Pretty Print Filter
renderFilter (table,name,Category i) = table  <> "." <> keyValue name <> " IN( " <>  intercalate "," (fmap show $ S.toList i) <> ")"
renderFilter (table,name,And i) =  intercalate " AND "  (fmap (renderFilter . (table,name,)) i)

-- Expand Filter list for outside where clause
generateSpecialized  f (From t s) =  catMaybes $ fmap (\i -> fmap (t,i,) . (flip M.lookup) f $ i ) (S.toList s)
generateSpecialized  f (Join t s r (Identity p) ) = (catMaybes $ fmap (\ i -> fmap (t,i,). (flip M.lookup) f $ i) (S.toList s)) <> generateSpecialized f p  

data FilterF a = FilterF ([(String,Key,Filter )],a)

-- Label each table with filter clauses
specializeJoin
  :: Map Key Filter
    -> JoinPath Identity String Key
    -> FilterF (JoinPath FilterF String Key)
specializeJoin f (From t s) =  FilterF (catMaybes $ fmap (\i -> fmap (t,i,) . (flip M.lookup) f $ i ) (S.toList s), (From t s))
specializeJoin f (Join t s r (Identity p) ) = FilterF (catMaybes $ fmap (\ i -> fmap (t,i,). (flip M.lookup) f $ i) (S.toList s) , Join t s r  (specializeJoin f p))


search attributes =  filter (any (\i -> any (== i) attributes) . snd ) 

data Table f  
    =  Base Key (JoinPath f String Key)
    |  Project Key (Set String) (JoinPath f String Key)
    |  Reduce (Set Key) (Set (Aggregate String) ) (Maybe (JoinPath f String Key)) (Table f ) 


type HashSchema  a b = Map a (Map a [Path a b ])

traceShow a = trace (show a ) a

createAggregate  schema key attr  old
    = Reduce (S.fromList key) (S.fromList attr) Nothing (addAggregate schema  key attr old ) 

addAggregate
  :: HashSchema Key String
     -> [Key] -> [Aggregate String] -> Table Identity -> Table Identity
addAggregate schema key attr (Base k s) =   case concat $  catMaybes $ queryHash key  schema k  of
                        [] -> Base k  s  
                        l -> Base k  (fromJust $ foldr joinPath  (Just s) l) 
addAggregate schema key attr (Reduce j t s p) =  case concat $ concat $ fmap (\ki -> catMaybes $  queryHash key  schema ki)  (S.toList j)  of
                        [] -> Reduce (foldr S.insert j key) (foldr S.insert t attr) s  (addAggregate schema key attr p )
                        l -> Reduce  j t  (foldr joinPath  s l) p

showAggregate (Base k s) = joinQuerySet s 
showAggregate (Reduce j t (Just s)  p) =  "REDUCE(" <> show j <> show t <> joinQuerySet s <>  " JOIN (" <>  showAggregate p <>") as ctx0 "
showAggregate (Reduce j t Nothing  p) =  "(SELECT " <> intercalate "," (fmap (keyValue) (S.toList j)  <> fmap renderAggr (S.toList t ) )   <>  showAggregate p  <> " GROUP BY " <> intercalate "," (fmap (keyValue) (S.toList j) )  <> ") as ctx0"

showJoinPath (From i j) = show i <> show j
showJoinPath (Join j t s p ) = show j <> show t <> show s <>   runIdentity (fmap showJoinPath p)

renderAggr (Aggregate l s )  = s  <> "(" <> intercalate "," l <> ")" 

reduce
  :: [(Key, b)]
     -> [Aggregate [Char]]
     -> [(Key, Filter)]
     -> Key
     -> Map Key (Map Key [Path Key String])
     -> [Char]
reduce group aggr filters base  schema = specialized 
    where 
        attributes = nub $ concat $ fmap (\(Aggregate l _) -> l) aggr
        result = queryHash (fmap fst filters <> fmap fst group <> fmap fst  (search attributes attributesTable ) ) schema base
        Just t = joinSet $ concat $ catMaybes result 
        specialized = " SELECT " <> intercalate "," (fmap (keyValue.fst) group  <> fmap renderAggr aggr ) <> joinQueryFilterSet (specializeJoin (M.fromList filters)  t)  <> " GROUP BY " <> intercalate "," (fmap (keyValue . fst) group) 

project
  :: [[Char]]
     -> [(Key, Filter)]
     -> Key
     -> Map Key (Map Key [Path Key String])
     -> [Char]
project attributes filters base  schema = specialized 
    where 
        result = queryHash (fmap fst filters <> fmap fst  (search attributes attributesTable ) ) schema base
        Just t = joinSet $ concat $ catMaybes result 
        specialized = " SELECT " <> intercalate "," attributes   <> joinQueryFilterSet (specializeJoin (M.fromList filters)  t) 

attributesTable =
    [(cat "id_service",["timerange","bounding"])
    ,(cat "id_machine",["machine_name","machine_serial","id_client","machine_model"])
    ,(cat "id_operator",["operator_name","operator_cpf","id_client"])
    ,(cat "id_client",["client_name","client_cpf"])] 


cat s = Key s "" 

main :: IO ()
main = do
  -- [f] <- getArgs
  let f = "Graph.schema"
  print "Graph"
  putStr . show =<< readGraph f
  print "Query"
  graph <-  readGraph f
  let schema = hashGraph . warshall  $ graph 
  print $ project  ["timerange","bounding","machine_name"] [(cat "id_machine",Category (S.fromList [1,2,3]))] (cat "id_service") schema
  print $ reduce [(cat "id_operator","")] [Aggregate ["timerange"] "min"] [(cat "id_machine",Category (S.fromList [1,2,3]))] (cat "id_service") schema
  putStrLn $ showAggregate $ createAggregate schema [cat "id_operator" ] [Aggregate ["timerange"] "MIN"] (Base (cat  "id_service") (From  "onetgeo.services" (S.singleton (cat "id_service" )) )) 

