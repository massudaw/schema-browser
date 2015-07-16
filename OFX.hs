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


opt f v = SOptional $ f <$> v
txt = SText . T.pack
frac = SDouble
tzone  = STimestamp . zonedTimeToLocalTime

i =: j = (i,j)

convertTrans (Transaction {..})  =
    ["fitid" =: txt txFITID
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
    ]

testAccount = do
  let tfile = "extrato2.ofx"
  file <- readFile tfile
  either (const Nothing) Just . fmap (fmap convertTrans) <$> account tfile file

ofxPlugin  i j = either (const Nothing) Just . fmap (fmap convertTrans) <$> account i j
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

