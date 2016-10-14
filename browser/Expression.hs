module Expression where

import Data.Map (Map)
import qualified Data.Map  as M
import Data.Monoid
import Step.Host
import Control.Applicative
import Types
import Utils
import Data.Attoparsec.Char8
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

funmap :: Map Text (([KPrim],KPrim ),[FTB Showable] -> FTB Showable)
funmap = M.fromList [("float8mul",(([PDouble,PDouble],PDouble),(\[i,j]-> i * j )))]


preevaluate :: Key -> Expr -> Map Text (([k],k ),[FTB Showable] -> FTB Showable) -> [Access Key] -> [Maybe (FTB Showable)] -> Maybe (Column Key Showable)
preevaluate k e fs ac res = Fun k (e, ac) <$> go e
  where
    go :: Expr -> Maybe (FTB Showable)
    go (Function i e) = f <$> (traverse go   e)
      where (_,f) = justError ("no function" <> show i) $ M.lookup i fs
    go (Value i ) = (res !! i)


evaluate :: Key -> Expr -> Map Text (([k],k ),[FTB Showable] -> FTB Showable) -> [Access Key] -> TBData Key Showable -> Maybe (Column Key Showable)
evaluate k e fs ac tb = Fun k (e,traceShowId $ ac) <$> go e
  where
    go :: Expr -> Maybe (FTB Showable)
    go (Function i e) = f <$> (traverse go   e)
      where (_,f) = justError ("no function" <> show i) $ M.lookup i fs
    go (Value i ) = indexFieldRec (ac !! i ) tb


