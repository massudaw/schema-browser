module Expression (buildAccess,readFun,funmap,evaluateFFI,evaluate) where

import Control.Monad
import Data.Either
import qualified Data.Aeson as A
import qualified Data.Aeson.Types as A
import Control.Monad.State
import Data.Time
import Types.Inference
import Control.Monad.Except
import Control.Arrow (first)
import Data.Map (Map)
import qualified Data.Map  as M
import Postgresql.Parser
import Postgresql.Printer
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

callFunction :: Connection -> String -> ( [KType (Prim KPrim (Text,Text))],KType (Prim KPrim (Text,Text))) -> [FTB Showable] -> IO (Maybe (FTB Showable))
callFunction conn fun ty inp = do
  let func = fromString $ " SELECT to_json(" ++ fun ++ ") "
  Only i <- L.head <$> queryLogged conn func (L.zip (fst ty) inp)
  return $ either (error "cant parse" ) id .   (A.parseEither (fmap fst . codegent . parseShowableJSON parsePrimitiveJSON  (snd ty)))<$>  i

multProof (PDimensional i (a1,a2,a3,a4,a5,a6,a7)) (PDimensional j (b1,b2,b3,b4,b5,b6,b7)) = PDimensional (i+j) (a1+b1,a2+b2,a3+b3,a4+b4,a5+b5,a6+b6,a7+b7)
divProof (PDimensional i (a1,a2,a3,a4,a5,a6,a7)) (PDimensional j (b1,b2,b3,b4,b5,b6,b7)) = PDimensional (i+j) (a1-b1,a2-b2,a3-b3,a4-b4,a5-b5,a6-b6,a7-b7)

prim l = Primitive l . AtomicPrim
inter = KInterval

funmap :: Map Text (([KType (Prim KPrim (Text,Text))],KType (Prim KPrim (Text,Text))),[FTB Showable] -> FTB Showable)
funmap = M.fromList [
        ("lower",(([prim [KInterval] PAny],prim [] PAny),\[IntervalTB1 i] -> justError "" $  unFinite $  lowerBound i))
       ,("upper",(([prim [KInterval] PAny],prim [] PAny),\[IntervalTB1 i] -> justError "" $  unFinite $  upperBound i))
       ,("tstzrange_subdiff",(([prim [] (PTime $ PTimestamp (Just utc)),prim [] (PTime $ PTimestamp (Just utc))],prim [] PDouble ),\[TB1 (STime (STimestamp i)),TB1 (STime (STimestamp j))] -> TB1 $ SDouble $ realToFrac $ diffUTCTime i j))
       ,("dimensional",(([prim [] PDouble],prim []$ PDimensional 0 (0,0,0,0,0,0,0) ),\[i]-> i))
       ,("float8sum",(([prim [] PAny,prim [] PAny],prim [] PAny),\[i,j]-> i + j))
       ,("float8sub",(([prim [] PAny,prim [] PAny],prim [] PAny),\[i,j]-> i - j))
       ,("float8div",(([prim [] PAny,prim [] PAny],prim [] PAny),\[i,j]-> i / j))
       ,("float8mul",(([prim [] PAny,prim [] PAny],prim [] PAny),\[i,j]-> i * j))
       ,("dimensionalmult",(([prim []PAny ,prim []PAny],prim []PAny),\[i,j]-> i * j))
       ,("dimensionaldiv",(([prim []PAny ,prim []PAny],prim []PAny),\[i,j]-> i / j))
       ]

replaceList l =  L.foldl' extend emptyTyenv (fmap (Forall [TV "a"] . replaceAny (TVar (TV "a")) ) <$> L.zip [0..] l  )


replaceAny :: Type -> Type -> Type
replaceAny l (TCon1 f i ) = TCon1  f $ replaceAny l i
replaceAny l (TCon (AtomicPrim PAny)) = l
replaceAny l (TCon i ) =  TCon i


ops = (\((inp,out),_) -> Forall [TV "a"]  $ L.foldr TArr ( replaceAny (TVar (TV "a")) . ktypeToType  $ out ) (replaceAny (TVar (TV "a")). ktypeToType <$> inp) ) <$> funmap

renderPostgres :: Expr -> String
renderPostgres = go
  where
    go :: Expr -> String
    go (Function i e) = T.unpack i ++ "(" ++  L.intercalate "," ( fmap  go   e) ++ ")"
    go (Value i ) = "?"



joinKType (Primitive l (Primitive  i a)) = Primitive (l ++ i) a

buildAccess :: Rel Key -> KType (Prim KPrim (Text,Text))
buildAccess n@(RelAccess i o) =  joinKType $ const (buildAccess o ) <$> (mergeFKRef $ buildAccess <$> relUnComp i )
buildAccess (Inline l) = keyType l
buildAccess (Rel l _ op ) = buildAccess l

testFFI = do
  conn <-  connectPostgreSQL  "dbname=incendio user=postgres password=jacapodre"
  let fun = readFun "dimensionalmult(%0,dimensionalmult(%1,%2))" :: Expr
  print fun
  evaluateFFI conn fun funmap [Primitive [] (AtomicPrim (PDimensional 0 (0,0,0,0,0,0,0))) ,Primitive [] (AtomicPrim (PDimensional 0 (0,0,0,0,0,0,0))),Primitive [] (AtomicPrim (PDimensional 0 (0,0,0,0,0,0,0)))] [TB1 (SDouble 3 ) , TB1 (SDouble 2),TB1 (SDouble 3)]


evaluateFFI :: Connection -> Expr -> Map Text (([KType (Prim KPrim (Text,Text))],KType (Prim KPrim (Text,Text))),[FTB Showable] -> FTB Showable) -> [KType (Prim KPrim (Text,Text)) ] -> [FTB Showable]  -> IO (Maybe (FTB Showable))
evaluateFFI conn expr fs ac2 res = evalTop expr
  where
    evalTop ::  Expr -> IO (Maybe (FTB Showable))
    evalTop fun@(Function i e) = do
        let rl = replaceList  (ktypeToType <$> ac2)
        let out = either (error . show ) schemeToKType $ inferExpr ops  rl  fun
        callFunction conn (renderPostgres fun) (ac2, out ) res
    evalTop (Value i ) = return (Just $ justError "no expr" $ res `atMay` fromIntegral i)


schemeToKType (Forall [] i ) = typeToKType i
typeToKType (TCon1 l i ) = Primitive l (typeToPrim i)
typeToKType (TCon  i )  = Primitive [] i
typeToPrim (TCon i ) = i

ktypeToType (Primitive l i) = TCon1 l (TCon i)

evaluate :: Key -> Expr -> Map Text (([k],k ),[FTB Showable] -> FTB Showable) -> [Rel Key] -> TBData Key Showable -> Maybe (Column Key Showable)
evaluate k e fs ac tb = Fun k (e,ac) <$> go e
  where
    go :: Expr -> Maybe (FTB Showable)
    go (Function i e) = f <$> traverse go   e
      where (_,f) = justError ("no function" <> show i) $ M.lookup i fs
    go (Value i ) =  join $ flip recLookup tb <$> (ac `atMay` i)
