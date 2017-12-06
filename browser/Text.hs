module Text where

import Types
import Types.Patch
import qualified NonEmpty as Non
import Data.Hashable
import Data.Ord
import Control.Monad
import Utils
import Control.Arrow (first)
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

explode sep depth = L.intercalate (sep :[]) . fmap (\(i,j) -> replicate i depth ++ j)

ident :: [(Int,String)] -> String
ident = explode '\n' '\t'

renderRowPatch :: Show a => TBIdx a Showable -> [(Int,String)]
renderRowPatch (_,_,i) =  concat $ renderPatch  <$> i

renderTable :: Show a => TBData a Showable ->  [(Int,String)]
renderTable i =  concat $ renderAttr  <$> F.toList (unKV (snd i))

renderRel (Rel i op j) = show i ++ "  " ++ renderBinary op ++ " " ++ show j

renderPatch :: Show a => PathAttr a Showable ->  [(Int,String)]
renderPatch (PFK rel k v )
  = [(0,L.intercalate " AND " (fmap renderRel rel))]
  ++ [(0,"[" ++ L.intercalate "," (concat $ fmap snd .renderPatch <$> k) ++ "] => ")]
  ++ fmap (first (+1)) (renderFTBPatch renderRowPatch v)
renderPatch (PAttr k v ) = [(0,show k ++ " => " ++ ident (renderFTBPatch renderPrimPatch v))]
renderPatch (PInline k v ) = [(0,show k ++ " => ")] ++ fmap (first (+1)) (renderFTBPatch renderRowPatch v)


renderPrimPatch i = [(0,renderPrim  i)]

renderAttr :: Show a => TB a Showable ->  [(Int,String)]
renderAttr (FKT k rel v )
  = [(0,L.intercalate " AND " (fmap renderRel rel))]
  ++ [(0,"[" ++ L.intercalate "," (concat $ fmap snd .renderAttr <$> F.toList (_kvvalues k))  ++ "] => ")] ++ fmap (first (+1)) (renderFTB renderTable v)

renderAttr (Attr k v ) = maybe [] (\i -> [(0,show k ++ " => " ++ ident i)]) (nonEmpty $ renderFTB renderPrimPatch v)
renderAttr (IT k v ) = maybe [] (\i -> [(0,show k ++ " => ")] ++ fmap (first (+1)) i  ) $  nonEmpty (renderFTB renderTable v)

renderFTBPatch :: (a -> [(Int,String)]) -> PathFTB a -> [(Int,String)]
renderFTBPatch f (PAtom i) = f i
renderFTBPatch f (POpt i) = concat $ maybeToList $ fmap (renderFTBPatch f ) i
renderFTBPatch f (PIdx ix i)  = maybe  [(0,show ix ++ "-")] (fmap (fmap (\e -> show ix ++ "-" ++ e )) . renderFTBPatch f) i
renderFTBPatch f (PatchSet l ) =  concat $ F.toList $ fmap (renderFTBPatch f) l
renderFTBPatch f (PInter b i)  = [(0,showFin i)]
  where
    showFin (ER.Finite i,s) = (if b then ocl s else "" ) ++ ident (renderFTBPatch f i) ++ (if not b then ocr s else "")
    showFin i = []
    ocl j = if j then "[" else "("
    ocr j = if j then "]" else ")"


renderFTB :: (a -> [(Int,String)]) -> FTB a -> [(Int,String)]
renderFTB f (TB1 i) = f i
renderFTB f (LeftTB1 i) = concat $ maybeToList $ fmap (renderFTB f ) i
renderFTB f (ArrayTB1 i)  = concat $ F.toList $ fmap (renderFTB f) i
renderFTB f (IntervalTB1 i)  = [(0,showInterval  i)]
  where
    showInterval (Interval.Interval (i,j) (l,m)) = ocl j <> (showFin i) ++ "," ++ (showFin l) <> ocr m
      where
        showFin (ER.Finite i) = snd $ head $ renderFTB f i
        showFin i =[]
        ocl j = if j then "[" else "("
        ocr j = if j then "]" else ")"

renderShowable = ident . renderFTB renderPrimPatch

renderPrim :: Showable -> String
renderPrim (SText a) = T.unpack a
renderPrim (SNumeric a) = show a
renderPrim (SBoolean a) = show a
renderPrim (SDouble a) = show a
renderPrim (STime i)
  = case i of
    STimestamp a ->  show a
    SDate a -> show a
    SDayTime a -> show a
    SPInterval a -> show a
renderPrim (SBinary i) = "Binary= " ++ show (hash i )
renderPrim (SDynamic s) = renderShowable s
renderPrim (SGeo o ) = renderGeo o
renderPrim i = show i

renderGeo (SPosition a) = show a
renderGeo (SPolygon i a) = show (i:a)
renderGeo (SMultiGeom a) = show a
renderGeo (SLineString a ) = show a
renderGeo (SBounding a ) = show a

defaultType (Primitive t _ ) =
    case t of
      (KOptional : i) -> Just (LeftTB1 Nothing)
      i -> Nothing

readTypeOpt (Primitive t _) Nothing = case t of
    KOptional :i -> Just $ LeftTB1 Nothing
    i -> Nothing
readTypeOpt t (Just i) = readType t i

readType (Primitive l (AtomicPrim p) ) = go l
  where
    prim = fmap TB1 <$> readPrim p
    go t = case t of
      KOptional :i -> opt LeftTB1 (go i)
      KSerial :i -> opt LeftTB1 (go i)
      KArray :i  -> parseArray (go i)
      KInterval :i -> inter (go i)
      i -> prim
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
     PColor-> readText
     PCnpj -> readCnpj
     PCpf-> readCpf
     PDouble ->  readDouble
     PDimensional _ _ ->  readDouble
     PInt _-> readInt
     PTime a ->case a of
       PTimestamp zone -> readTimestamp
       PDate-> readDate
       PInterval -> readInterval
       PDayTime -> \t -> readDayTime t <|> readDayTimeMin t <|> readDayTimeHour t
     PGeom i a ->  fmap (fmap SGeo )$ case a of
       PPosition -> readPosition
       PLineString -> readLineString
       MultiGeom PPolygon  -> readMultiPolygon
     PBoolean -> readBoolean
     PBinary -> readBin
     PMime i -> readBin
     i -> error $ show ("no case: " ++ show i)
  where
      readInt = nonEmpty (fmap SNumeric . readMaybe)
      readBoolean = nonEmpty (fmap SBoolean . readMaybe)
      readDouble = nonEmpty (fmap SDouble. readMaybe)
      readText = nonEmpty (\i-> fmap SText . readMaybe $  "\"" <> i <> "\"")
      readBin = nonEmpty (\i-> fmap (SBinary . BS.pack ) . readMaybe $  "\"" <> i <> "\"")
      readCnpj = nonEmpty (\i-> fmap (SText . T.pack . fmap Char.intToDigit ) . join . fmap (join . fmap (eitherToMaybe . cnpjValidate ). (allMaybes . fmap readDigit)) . readMaybe $  "\"" <> i <> "\"")
      readCpf = traceShowId . nonEmpty (\i-> fmap (SText . T.pack . fmap Char.intToDigit ) . join . fmap (join . fmap (eitherToMaybe . cpfValidate ). (allMaybes . fmap readDigit)) . readMaybe $  "\"" <> i <> "\"")
      readDate =  fmap (STime . SDate . localDay . fst) . strptime "%Y-%m-%d"
      readDayTime =  fmap (STime . SDayTime . localTimeOfDay . fst) . strptime "%H:%M:%OS"
      readDayTimeMin =  fmap (STime . SDayTime . localTimeOfDay . fst) . strptime "%H:%M"
      readDayTimeHour =  fmap (STime . SDayTime . localTimeOfDay . fst) . strptime "%H"
      readPosition = nonEmpty (fmap SPosition . readMaybe)
      readLineString = nonEmpty (fmap SLineString . readMaybe)
      readMultiPolygon = nonEmpty (fmap SMultiGeom . fmap (fmap (\(i:xs) -> SPolygon i xs)). readMaybe)
      readTimestamp =  fmap (STime . STimestamp  .  localTimeToUTC utc . fst) . (\i -> strptime "%Y-%m-%d %H:%M:%OS" i <|> strptime "%Y-%m-%d %H:%M:%S" i)
      readInterval =  fmap (STime . SPInterval) . (\(h,r) -> (\(m,r)->  (\s m h -> secondsToDiffTime $ h*3600 + m*60 + s ) <$> readMaybe (safeTail r) <*> readMaybe m <*> readMaybe h )  $ break (==',') (safeTail r))  . break (==',')
      nonEmpty f ""  = Nothing
      nonEmpty f i  = f i


readDigit i
  | Char.isDigit i = Just $ Char.digitToInt i
  | otherwise = Nothing

cpfValidate i
  | length i /= 11 = Left "Invalid size Brazilian Cpf need 11 digits"
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

