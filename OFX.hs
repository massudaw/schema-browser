{-# LANGUAGE GADTs,OverloadedStrings, Arrows ,RecordWildCards#-}
module OFX (ofxPlugin) where
import Text.Parsec
import Data.OFX
import System.IO
import System.Exit
import Debug.Trace
import Types.Patch

import Control.Applicative
import Control.Monad (join)
import Utils


import Data.Time
import Types hiding (txt)
import Data.Functor.Identity
import qualified Data.Text as T


opt f v = LeftTB1 $  f <$> v
serial f v = LeftTB1 $ f <$> v
txt = TB1 . SText . T.pack
frac = TB1 . SDouble
tzone  = TB1 . STime . STimestamp . zonedTimeToLocalTime

i =: j = PAttr i (patch j)

convertTrans (Transaction {..})  =
    ["fitid" =: serial txt (if txFITID == "0" then Nothing else Just txFITID)
    ,"memo" =:  opt txt txMEMO
    ,PFK [Rel "trntype" Equals "trttype"] ["trntype" =: txt (tail $ show txTRNTYPE )]  (PAtom (kvempty,Idex [txt (tail $ show txTRNTYPE )],["trttype" =: txt (tail $ show txTRNTYPE )]))
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
    ]  :: [PathAttr T.Text Showable]

testAccount = do
  let tfile = "extrato2.ofx"
  file <- readFile tfile
  either (const Nothing) Just . fmap (fmap (convertTrans ) ) <$> account tfile file

ofxPlugin  i j = join . fmap nonEmpty . either (const Nothing) Just . fmap (fmap (convertTrans ) ) <$> account i j
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
