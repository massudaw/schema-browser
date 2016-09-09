module Text where

import Types
import qualified NonEmpty as Non
import Data.Ord
import Control.Monad
import Utils
import Debug.Trace

import Data.Tuple
import Data.Time.Clock
import qualified Data.Char as Char

import Control.Applicative
import Data.Maybe
import Text.Read hiding (choice)
import Data.Time.Parse
import Data.Time.LocalTime
import qualified Data.ByteString.Char8 as BS

import Data.Monoid
import Prelude hiding (takeWhile,head)
import qualified Data.Foldable as F
import qualified Data.List  as L
import qualified Data.Interval as Interval
import qualified Data.Interval as ER


import qualified Data.Text as T


-- This module contains text backend printer and parser

renderShowable :: FTB Showable -> String
renderShowable (LeftTB1 i ) = maybe "" renderShowable i
renderShowable (DelayedTB1 i ) =  maybe "<NotLoaded>" (\i -> "<Loaded| " <> renderShowable i <> "|>") i
renderShowable (SerialTB1 i ) = maybe "" renderShowable i
renderShowable (ArrayTB1 i)  = L.intercalate "," $ F.toList $ fmap renderShowable i
renderShowable (IntervalTB1 i)  = showInterval renderShowable i
  where
    showInterval f i | i == Interval.empty = show i
    showInterval f (Interval.Interval (ER.Finite i,j) (ER.Finite l,m) ) = ocl j <> f i <> "," <> f l <> ocr m
      where
        ocl j = if j then "[" else "("
        ocr j = if j then "]" else ")"
    showInterval f i = show i -- errorWithStackTrace (show i)


renderShowable (TB1  i) = renderPrim i

renderPrim :: Showable -> String
renderPrim (SText a) = T.unpack a
renderPrim (SNumeric a) = show a
renderPrim (SBoolean a) = show a
renderPrim (SDouble a) = show a
renderPrim (STimestamp a) = show a
renderPrim (SLineString a ) = show a
renderPrim (SBounding a ) = show a
renderPrim (SDate a) = show a
renderPrim (SDayTime a) = show a
renderPrim (SBinary _) = show "<Binary>"
renderPrim (SDynamic s) = renderShowable s
renderPrim (SPosition a) = show a
renderPrim (SPInterval a) = show a


defaultType t =
    case t of
      KOptional i -> Just (LeftTB1 Nothing)
      i -> Nothing

readTypeOpt t Nothing = case t of
    KOptional i -> Just $ LeftTB1 Nothing
    i -> Nothing
readTypeOpt t (Just i) = readType t i

readType t = case t of
    Primitive (AtomicPrim i) -> fmap TB1 <$> readPrim i
    KOptional i -> opt LeftTB1 (readType i)
    KSerial i -> opt SerialTB1 (readType i)
    KArray i  -> parseArray (readType i)
    KInterval i -> inter (readType i)
  where
      opt c f "" =  Just $ c Nothing
      opt c f i = fmap (c .Just) $ f i
      parseArray f i =   fmap ArrayTB1 $  allMaybes $ fmap f $ Non.fromList $ unIntercalate (=='\n') i
      inter f v = (\(i,j)-> fmap IntervalTB1 $  Interval.interval <$> fmap ((,lbnd).Interval.Finite) (f i) <*> fmap ((,ubnd).Interval.Finite) (f $ tail j) )  .  break (==',') . tail . init $ v
        where lbnd = case head v of
                        '(' -> False
                        '[' -> True
              ubnd = case last v of
                        ')' -> False
                        ']' -> True


readPrim t =
  case t of
     PText -> readText
     PCnpj -> readCnpj
     PCpf-> readCpf
     PDouble ->  readDouble
     PInt -> readInt
     PTimestamp zone -> readTimestamp
     PInterval -> readInterval
     PDate-> readDate
     PDayTime -> \t -> readDayTime t <|> readDayTimeMin t <|> readDayTimeHour t
     PPosition -> readPosition
     PBoolean -> readBoolean
     PLineString -> readLineString
     PBinary -> readBin
  where
      readInt = nonEmpty (fmap SNumeric . readMaybe)
      readBoolean = nonEmpty (fmap SBoolean . readMaybe)
      readDouble = nonEmpty (fmap SDouble. readMaybe)
      readText = nonEmpty (\i-> fmap SText . readMaybe $  "\"" <> i <> "\"")
      readBin = nonEmpty (\i-> fmap (SBinary . BS.pack ) . readMaybe $  "\"" <> i <> "\"")
      readCnpj = nonEmpty (\i-> fmap (SText . T.pack . fmap Char.intToDigit ) . join . fmap (join . fmap (eitherToMaybe . cnpjValidate ). (allMaybes . fmap readDigit)) . readMaybe $  "\"" <> i <> "\"")
      readCpf = traceShowId . nonEmpty (\i-> fmap (SText . T.pack . fmap Char.intToDigit ) . join . fmap (join . fmap (eitherToMaybe . cpfValidate ). (allMaybes . fmap readDigit)) . readMaybe $  "\"" <> i <> "\"")
      readDate =  fmap (SDate . localDay . fst) . strptime "%Y-%m-%d"
      readDayTime =  fmap (SDayTime . localTimeOfDay . fst) . strptime "%H:%M:%OS"
      readDayTimeMin =  fmap (SDayTime . localTimeOfDay . fst) . strptime "%H:%M"
      readDayTimeHour =  fmap (SDayTime . localTimeOfDay . fst) . strptime "%H"
      readPosition = nonEmpty (fmap SPosition . readMaybe)
      readLineString = nonEmpty (fmap SLineString . readMaybe)
      readTimestamp =  fmap (STimestamp  .  fst) . strptime "%Y-%m-%d %H:%M:%OS"
      readInterval =  fmap SPInterval . (\(h,r) -> (\(m,r)->  (\s m h -> secondsToDiffTime $ h*3600 + m*60 + s ) <$> readMaybe (safeTail r) <*> readMaybe m <*> readMaybe h )  $ break (==',') (safeTail r))  . break (==',')
      nonEmpty f ""  = Nothing
      nonEmpty f i  = f i


readDigit i
  | Char.isDigit i = Just $ Char.digitToInt i
  | otherwise = Nothing

cpfValidate i
  | length i /= 11 = Left "Invalid size Brazilian Cnpj need 14 digits"
  | m1v == m1 && m2v == m2 = Right i
  | otherwise = Left "Invalid checksum check your number"
  where multiplier1 =  [10,9,8,7,6,5,4,3,2]
        multiplier2 =  [11,10,9,8,7,6,5,4,3,2]
        multSum i j =  if remainder <2 then 0 else 11 - remainder
            where remainder = sum (zipWith (*) i j) `mod` 11
        m1 = multSum i multiplier1
        m2 = multSum i multiplier2
        [m1v,m2v] = drop 9 i

cnpjValidate i
  | length i /= 14 = Left "Invalid size Brazilian Cnpj need 14 digits"
  | m1v == m1 && m2v == m2 = Right i
  | otherwise = Left "Invalid checksum check your number"
  where multiplier1 = [ 5, 4, 3, 2, 9, 8, 7, 6, 5, 4, 3, 2 ]
        multiplier2 = [ 6, 5, 4, 3, 2, 9, 8, 7, 6, 5, 4, 3, 2 ]
        multSum i j =  if remainder <2 then 0 else 11 - remainder
            where remainder = sum (zipWith (*) i j) `mod` 11
        m1 = multSum i multiplier1
        m2 = multSum i multiplier2
        [m1v,m2v] = drop 12 i

tcnpj = [0,4,8,2,5,5,8,0,0,0,0,1,0,7]

cpf = [0,2,8,4,0,3,0,1,1,2,1]

