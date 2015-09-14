{-# LANGUAGE OverloadedStrings, Arrows ,RecordWildCards#-}
module OFX where
import System.Environment
import Text.Parsec
import Text.PrettyPrint
import Data.OFX
import System.IO
import System.Exit

import qualified Data.Map as M
import Control.Applicative

{-
import Step
import Control.Monad
import Control.Arrow
import RuntimeTypes
-}
import Data.Time
import Types
import qualified Data.Text.Lazy as T


opt f v = LeftTB1 $  f <$> v
serial f v = DelayedTB1 $ f <$> v
txt = TB1 . SText . T.pack
frac = TB1 . SDouble
tzone  = TB1 . STimestamp . zonedTimeToLocalTime

i =: j = (i,j)

convertTrans acc (Transaction {..})  =
    ["fitid" =: serial txt (Just txFITID)
    ,"memo" =:  opt txt txMEMO
    ,"trntype" =: txt (tail $ show txTRNTYPE )
    ,"dtposted" =: tzone txDTPOSTED
    ,"dtuser" =:  opt tzone txDTUSER
    ,"dtavail" =: opt tzone txDTAVAIL
    ,"trnamt" =: frac (read txTRNAMT )
    ,"correctfitid" =: opt txt txCORRECTFITID
    ,"correctaction" =: opt (txt.show) txCORRECTACTION
    ,"srvrtid" =: opt txt txSRVRTID
    ,"checknum" =: opt txt txCHECKNUM
    ,"refnum" =: opt txt txREFNUM
    ,"sic" =: opt txt txSIC
    ,"payeeid" =: opt txt txPAYEEID
    ,"account" =: acc
    ] :: [(T.Text,FTB Showable)]

testAccount = do
  let tfile = "extrato2.ofx"
      acc = TB1 $ SNumeric 4
  file <- readFile tfile
  either (const Nothing) Just . fmap (fmap (convertTrans acc) ) <$> account tfile file

ofxPlugin  i j acc = either (const Nothing) Just . fmap (fmap (convertTrans acc) ) <$> account i j
account :: String -> String -> IO (Either String [Transaction])
account filename contents = do
   ofx <- case parse ofxFile filename contents of
     Left e -> do
       hPutStrLn stderr . show $ e
       exitFailure
     Right g -> return g
   return $
      transactions
     $ ofx
