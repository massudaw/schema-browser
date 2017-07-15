module Expression (renderFun,readFun,funmap,evaluateFFI,evaluate) where

import Control.Monad
import Control.Monad.State
import Types.Inference
import Control.Monad.Except
import Control.Arrow (first)
import Data.Map (Map)
import qualified Data.Map  as M
import Postgresql.Parser
import Safe
import Data.Interval(upperBound,lowerBound)
import Data.Monoid
import qualified Data.Foldable as F
import qualified Data.List as L
import qualified Data.Text as T
import Step.Host
import Control.Applicative
import Types
import Data.String
import Utils
import Data.Attoparsec.Char8
import Database.PostgreSQL.Simple
import Data.Text
import qualified Data.ByteString.Char8 as BS

import Debug.Trace

readFun f = case parseOnly parseFunction f of
              Right i -> i
              Left i -> error (show i)

parseArg = do
  many (char ' ')
  char '%'
  i <- number
  many (char ' ')
  return $ Value (round i)

parseFunction =  do
  many (char ' ')
  fun <- takeTill (`elem` ("(," :: String))
  f <- char '(' *> sepBy (parseFunction <|> parseArg) (char ',') <* char ')'
  many (char ' ')
  return (Function (pack $ BS.unpack fun ) f)

callFunction :: Connection -> String -> ( [KType (Prim KPrim (Text,Text))],KType (Prim KPrim (Text,Text))) -> [FTB Showable] -> IO (FTB Showable)
callFunction conn fun ty inp = do
  L.head <$> queryWith (parseField (parseShowable (snd ty))) conn (fromString $ " SELECT " ++ fun ++ "(" ++ L.intercalate "," ( const "?" <$> inp) ++ ")") (L.zip (fst ty) inp)


prim l = Primitive l . AtomicPrim
inter = KInterval
funmap :: Map Text (([KType (Prim KPrim (Text,Text))],KType (Prim KPrim (Text,Text))),[FTB Showable] -> FTB Showable)
funmap = M.fromList [
        ("lower",(([prim [KInterval] PAny ], prim [KOptional] PAny ),(\[IntervalTB1 i] -> LeftTB1 $  unFinite $  lowerBound i)))
       ,("upper",(([prim [KInterval] PAny ],prim [KOptional] PAny),(\[IntervalTB1 i] -> LeftTB1 $  unFinite $  upperBound i)))
       ,("adimensional",(([prim [] PDouble],prim []$ PDimensional 1 (0,0,0,0,0,0,0) ),(\[i]-> i)))
       ,("float8sum",(([prim []PAny ,prim []PAny],prim []PAny),(\[i,j]-> i + j )))
       ,("float8sub",(([prim []PAny,prim []PAny],prim []PAny),(\[i,j]-> i - j )))
       ,("float8div",(([prim []PAny ,prim []PAny],prim [] PAny),(\[i,j]-> i / j )))
       ,("float8mul",(([prim []PAny,prim []PAny],prim []PAny),(\[i,j]-> i * j )))
       ,("dimensionalmult",(([prim [](PDimensional 0 (0,0,0,0,0,0,0)) ,prim [](PDimensional 0 (0,0,0,0,0,0,0))],prim [](PDimensional 0 (0,0,0,0,0,0,0))),(\[i,j]-> i * j )))
       ]

renderFun :: (Expr ,[Access Key]) -> String
renderFun (e,ac) = go e
  where
    go :: Expr -> String
    go (Function i e) = T.unpack i ++ "(" ++  L.intercalate "," ( fmap  go   e) ++ ")"
    go (Value i ) =acc $  ac !! i
    acc (IProd _ l) = show l
    acc (Nested i  l) = (L.intercalate "," $ F.toList $ acc <$> i  )++  "." ++ (L.intercalate "," $ F.toList $ acc <$> l  )


preevaluate :: Key -> Expr -> Map Text (([k],k ),[FTB Showable] -> FTB Showable) -> [Access Key] -> [Maybe (FTB Showable)] -> Maybe (Column Key Showable)
-- preevaluate k e fs ac res | traceShow (ac,res) False = undefined
preevaluate k e fs ac res = Fun k (e, ac) <$> go e
  where
    go :: Expr -> Maybe (FTB Showable)
    go (Function i e) = f <$> (traverse go   e)
      where (_,f) = justError ("no function" <> show i) $ M.lookup i fs
    go (Value i ) = join (res `atMay` i)

joinKType (Primitive l (Primitive  i a) ) = Primitive (l ++ i) a


buildAccess :: Access Key -> KType (Prim KPrim (Text,Text))
buildAccess (Nested i (Many [o])) = joinKType $ const (buildAccess o ) <$> (mergeFKRef  (buildAccess <$> F.toList i ))
buildAccess (IProd i l) = keyType l

applyKType :: KType (Prim KPrim (Text,Text))-> KType (Prim KPrim (Text,Text))-> KType (Prim KPrim (Text,Text))
applyKType (Primitive l (AtomicPrim i)) (Primitive l1 (AtomicPrim j)) = Primitive (applyKTypePrim l l1)  (AtomicPrim $ applyPrim i j )
  where
    applyKTypePrim (KOptional :i) (KOptional :j) = KOptional : applyKTypePrim i j
    applyKTypePrim (KInterval :i) (KInterval :j) = KInterval : applyKTypePrim i j
    applyKTypePrim (KArray    :i) (KArray :j) = KArray :(applyKTypePrim i j)
    applyKTypePrim i (KOptional :j) = KOptional :(applyKTypePrim i j)
    applyKTypePrim (KOptional :i) j = KOptional :(applyKTypePrim i j)
    applyKTypePrim [] [] = []
    applyKTypePrim i j = error ("no applyKTypePrim" ++ show (i,j))

applyPrim PAny PAny = PAny
applyPrim i PAny  = error ("cant apply: " ++ show i)
applyPrim PDouble (PDimensional i j ) = PDimensional i j
applyPrim (PDimensional i j ) PDouble = PDimensional i j
applyPrim PAny  i =  i
applyPrim j i
  | i == j =  i
  | otherwise = error ("wrong types: " ++ show (i,j))


evaluateFFI :: Connection -> KType (Prim KPrim (Text,Text)) -> Expr -> Map Text (([KType (Prim KPrim (Text,Text))],KType (Prim KPrim (Text,Text))),[FTB Showable] -> FTB Showable) -> [Access Key] -> [Maybe (FTB Showable)]  -> IO (Maybe (FTB Showable))
evaluateFFI conn  outty e fs ac res=  snd <$> go outty e
  where
    ac2 = buildAccess <$> ac
    go :: KType (Prim KPrim (Text,Text)) -> Expr -> IO (KType (Prim KPrim (Text,Text)) , Maybe (FTB Showable))
    go oty (Function i e) = do
        o <- traverse (uncurry go ) $ L.zip (tyin)  e
        fmap (applyKType  tyout oty ,) $ traverse (callFunction conn (T.unpack i) (L.zipWith applyKType tyin  (fst <$> o), applyKType  tyout oty )) (allMaybes (snd <$> o))
      where ((tyin,tyout),f) = justError ("no function" <> show i) $ M.lookup i fs
    go oty (Value i ) = return $ (ac2 !! i , res !! i)



evaluate :: Key -> Expr -> Map Text (([k],k ),[FTB Showable] -> FTB Showable) -> [Access Key] -> TBData Key Showable -> Maybe (Column Key Showable)
evaluate k e fs ac tb = Fun k (e,ac) <$> go e
  where
    go :: Expr -> Maybe (FTB Showable)
    go (Function i e) = f <$> (traverse go   e)
      where (_,f) = justError ("no function" <> show i) $ M.lookup i fs
    go (Value i ) = join $ flip indexFieldRec tb <$> (ac `atMay` i)


