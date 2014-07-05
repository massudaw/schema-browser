{-# LANGUAGE DeriveFunctor,DeriveFoldable ,TupleSections #-}
module Warshall where

import qualified Data.Foldable as F
import Data.Foldable (Foldable)
import Data.Char ( isAlpha )
import Data.Maybe
import Data.Monoid ((<>))
import Control.Monad
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

data Vertex a  = Product  { unProduct :: [a]}
              deriving(Eq,Show,Ord,Functor,Foldable)
data Edge a b = Edge (Vertex a) (Vertex a) b 
            deriving(Eq,Ord,Show,Functor,Foldable)



data Operation
        =  SqlJoin String String
        |  FieldProjection
        |  TableField
        deriving(Show)

leftPath :: Path String String -> [String]
leftPath (DirectPath (Edge (Product i) _ _) ) = i
leftPath (ProductPath l i )  = leftPath  $ head l





joinQuerySet (From b _) =  " FROM " <> b 
joinQuerySet (Join b _ r p ) = joinQuerySet p <>  " JOIN " <> b <> " ON " <> rel
    where rel =  intercalate " AND " $ fmap (\(t,f) ->  t <> "." <> keyValue f <> " = " <> b <> "." <> keyValue f ) $ S.toList r 
    


data JoinPath b a 
    = From b (Set a)
    | Join b (Set a) (Set (b ,a)) (JoinPath b a)
    deriving(Show)

addJoin :: (Ord b,Ord a) => b -> [a] -> JoinPath b a -> JoinPath b a
addJoin tnew f p = case mapPath tnew f p of
            Left accnew -> Join tnew (S.fromList f) (S.fromList accnew) p 
            Right i -> i
    where 
        mapPath tnew f (From t s ) =  if t == tnew
                then  (Right $ From t snew )
                else  (Left $ fmap (t,) $ filter ((flip S.member) s) f)
            where snew =  foldr S.insert  s f
        mapPath tnew  f (Join t s clause p ) = res 
            where  res = case mapPath tnew f p  of
                    Right pnew  -> Right $ Join t s (foldr S.insert clause ((fmap (tnew,) $ filter ((flip S.member) s) f))) pnew
                    Left accnew -> if t == tnew 
                        then Right $ Join t  (foldr S.insert  s f)  (foldr S.insert  clause accnew ) p 
                        else Left $ (fmap (t,) $ filter ((flip S.member) s) f) <> accnew

joinSet :: (Ord b,Ord a) => [Path   a b ] -> Maybe (JoinPath  b a )
joinSet p = foldl (flip joinPath) Nothing p
    where 
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

productLine = "ab cd-> cd | Field" 

query norm end f = find (fmap f norm) (fmap f end) 

queryHash :: Ord a => [a] -> Map a (Map a b) -> a  -> [Maybe b]
queryHash filters schema  base =  map (\f-> find base f schema)  filters 
    
lookupTable graph = edges graph

extractPathTag  p = extractTag p []  
extractTag (DirectPath (Edge _ _ t)) =   (t:)
extractTag (ProductPath px p2) =  foldr (.)   (extractTag p2) (fmap extractTag px)

pathSet f =   fmap (fmap f . fromJust)  


data Table 
    = Raw [Vertex String]  [Attribute]
    | Filtered Table [Filter]
    | Grouped Table (([Vertex String],[Attribute]) -> [Vertex String]) (([Vertex String],[Attribute]) -> [Attribute])
    | Sorted Table [Vertex String -> Vertex String]
    -- | Join  [Table]

data Attribute 
   = Metric Double
   | Rate Attribute  Attribute 
   | Norm Double 

data Filter
   = Category (Set Int)
   | And [Filter]
   | Or [Filter]
   

renderFilter (name,Category i) = keyValue name <> " IN( " <>  intercalate "," (fmap show $ S.toList i) <> ")"
renderFilter (name,And i) =  intercalate " AND "  (fmap (renderFilter . (name,)) i)

reduce group attributes filters base  schema = specialized 
    where 
        result = queryHash (fmap fst filters <> fmap fst group <> fmap fst attributes) schema base
        Just t = joinSet $ concat $ catMaybes result 
        filterMap = M.fromList filters
        specialized = " SELECT " <> intercalate "," (fmap (keyValue.fst) $ group )  <>   joinQuerySet t <> " WHERE " <> intercalate " AND " (fmap (\(name,f)-> renderFilter (name,And f )) filters)

table :: Map String Table 
table = M.fromList [ ("services", Raw [Product ["id_services"],Product ["time","machine"]] [] ) ]

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
  let result =  queryHash (fmap cat ["id_operator","id_order","id_client"]) schema (cat "id_service")
  print $ reduce [(cat "id_operator","total")] [] [(cat "id_client",[Category (S.fromList [1,2,3])])] (cat "id_service") schema

