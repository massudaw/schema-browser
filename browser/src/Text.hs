{-# LANGUAGE TupleSections,TypeApplications,FlexibleInstances,TypeSynonymInstances #-}
module Text (PrettyRender(..),ident, render,renderShowable , readPrim,renderPrim,renderPredicateWhere,readType) where

import Types
import Types.Patch
import qualified NonEmpty as Non
import qualified Data.Sequence.NonEmpty as NonS
import Data.Time.Format
import Data.Hashable
import Data.Ord
import Data.Dynamic
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
import Data.Time.LocalTime
import qualified Data.ByteString.Char8 as BS

import Data.Monoid
import Prelude hiding (takeWhile)
import qualified Data.Foldable as F
import qualified Data.List  as L
import qualified Data.Interval as Interval
import qualified Data.Interval as ER


import qualified Data.Text as T


-- This module contains text backend printer and parser

class PrettyRender  a where
  render :: a ->  [(Int,String)]

class PrettyRender1  f  where
  render1 :: PrettyRender a => f a ->  [(Int,String)]

instance PrettyRender1 FTB where
  render1 = renderFTB render

instance PrettyRender1 KType where
  render1 = renderPrimitive 

instance (Show i , Show j ) => PrettyRender (Prim i j ) where
  render i = [(0,show i)]
renderPrimitive l= [(0,showTy (ident . render) l)]

instance PrettyRender () where
  render _ = []

instance PrettyRender Showable where
  render i = [(0,renderPrim  i)]

explode sep depth = L.intercalate (sep :[]) . fmap (\(i,j) -> concat (replicate i depth) ++ j)

ident :: [(Int,String)] -> String
ident = explode '\n' " " . compressClosingBrackets

noident :: Char ->  [(Int,String)] -> String
noident sep = explode sep " " 

  
instance PrettyRender i => PrettyRender (KType i ) where
  render  p =  [(0,showTy (ident. render) p)]


compressClosingBrackets :: [(Int,String)] -> [(Int,String)]
compressClosingBrackets =  foldr (flip mergeBracket) []  
  where 
   mergeBracket [] i = [i]
   mergeBracket v@((ix, t ):xs) (ix2,t2) 
     | L.all (=='}') t  && L.all (=='}') t2 = (max ix ix2 , t <> t2) :  xs
     | otherwise = (ix2,t2)  : v

instance PrettyRender Key where
  render i = [(0,show i)]

instance PrettyRender T.Text  where
  render i = [(0,T.unpack i)]
  
instance (Show a, Ord a, PrettyRender a , PrettyRender b) => PrettyRender (RowOperation  a b ) where
  render (CreateRow i) = wrapBrackets "CreateRow " (renderTable i)
  render (PatchRow i) = wrapBrackets "PatchRow " (renderRowPatch i)
  render DropRow = [(0,"DropRow")]

instance (Show a, PrettyRender a) => PrettyRender (TBIndex a) where
  render (Idex i ) =   concat $ render  <$> i

instance (Ord a,Show a, Show b, PrettyRender a , PrettyRender b) =>  PrettyRender (RowPatch a b) where
  render (RowPatch (ix,op)) = wrapBrackets "PK => " (render ix) <> render op

renderRowPatch :: (PrettyRender b,Show a) => TBIdx a b-> [(Int,String)]
renderRowPatch i =  concat $ renderPatch  <$> i

instance  (Ord a , Show a ,PrettyRender1 f, PrettyRender b) => PrettyRender (FKV a f b ) where
  render = renderTable

renderTable :: (Ord a , Show a,PrettyRender1 f,PrettyRender b) => FKV a f b ->  [(Int,String)]
renderTable i =  concat $ renderAttr  <$> F.toList (unKV i)

wrapBrackets i l 
  | nextLength > 3 = [(0,i ++ "{")]  ++ offset 1 l ++  [(0,"}")]
  | nextLength > 1 = [(0,i)] ++ offset 1 l 
  | nextLength == 1 = [(0,i ++ snd (head next) )]  ++ offset 1 (L.filter ((/=0).fst)  l)
  | length l > 1 = [(0,i)] ++ offset 1 l 
  | otherwise = [(0, i  ++ maybe "" snd (safeHead l) )]
  where nextLength  =  L.length next 
        next = L.filter ((==0).fst) l

offset ix =  fmap (first (+ix))
renderPatch :: (PrettyRender b ,Show a) => PathAttr a b ->  [(Int,String)]
renderPatch (PFK rel k v )
  = wrapBrackets  (L.intercalate " && " (fmap renderRel rel) ++ " => ")
  ((concat $ renderPatch <$> k) 
  ++  offset 1 (render v))
renderPatch (PAttr k v ) = wrapBrackets (show k ++ " => ") (render v) 
renderPatch (PInline k v ) = wrapBrackets (show k ++ " => ") (render v) 
renderPatch (PFun k j v ) = wrapBrackets  (renderRel (RelFun (Inline k) (fst j) (snd j) ) ++ " => ") (render v)


renderPredicateWhere (WherePredicate i) = renderPredicate i
renderPredicate (AndColl l  ) = "(" <> L.intercalate " AND "  (renderPredicate <$> l ) <> ")"
renderPredicate (OrColl l )= "(" <> L.intercalate " OR "  (renderPredicate <$> l ) <> ")"
renderPredicate (PrimColl (_,l) )= L.intercalate " AND " $ fmap (\(i,j)-> renderRel i <> either (\(s,o) -> renderBinary o <> (renderShowable s )) renderUnary  j ) l  

renderAttr :: (Ord k, Show k,PrettyRender1 f,PrettyRender b) => TBF k f b->  [(Int,String)]
renderAttr (FKT k rel v )
  =
    ref
    ++ [(0,L.intercalate " && " (fmap renderRel rel))]
  ++ (first (+1) <$> render1 v)
  where ref = concat $ renderAttr <$> unkvlist k
renderAttr (Attr k v ) = breakLine  (render1 v)
  where breakLine i 
          | L.length i > 1 =  [(0,show k ++ " => ")]  ++ offset 1 i
          |  otherwise = [(0,show k ++ " => " ++ ident i)]
renderAttr (IT k v ) = (\i -> [(0,show k ++ " => ")] ++ i  )  (first (+1) <$> render1 v)
renderAttr (Fun i k v) = renderAttr (Attr i v)


instance PrettyRender a => PrettyRender (FTB a) where
  render  = renderFTB render
instance PrettyRender a => PrettyRender (PathFTB a) where
  render  = renderFTBPatch render
instance (Show k ,PrettyRender a) => PrettyRender (TBIdx k a) where
  render  = renderRowPatch 


renderFTBPatch :: (a -> [(Int,String)]) -> PathFTB a -> [(Int,String)]
renderFTBPatch f (PAtom i) = f i
renderFTBPatch f (POpt i) = concat $ maybeToList $ fmap (renderFTBPatch f ) i
renderFTBPatch f (PIdx ix i)  =  wrapBrackets (show ix  ++ " => ") (maybe [] (renderFTBPatch f) i)
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
renderFTB f (ArrayTB1 i)
  | L.length (concat children) == NonS.length i =  [(0,"{" <> noident  ',' (concat children) <> "}")]
  | otherwise = concat$ zipWith (\ i j -> (0,show i  ++ " :") : offset 1 j )  [0..]  children
    where children = (F.toList $ fmap (renderFTB f) i)
renderFTB f (IntervalTB1 i)  = [(0,showInterval  i)]
  where
    showInterval (Interval.Interval (i,j) (l,m)) = ocl j <> (showFin i) ++ "," ++ (showFin l) <> ocr m
      where
        showFin (ER.Finite i) = snd $ head $ renderFTB f i
        showFin i =[]
        ocl j = if j then "[" else "("
        ocr j = if j then "]" else ")"

renderPK (Idex i ) = L.intercalate "," $ renderShowable <$> i

renderShowable :: FTB Showable -> String
renderShowable = ident . renderFTB render

renderPrim :: Showable -> String
renderPrim (SText a) = T.unpack a
renderPrim (SNumeric a) = show a
renderPrim (SBoolean a) = show a
renderPrim (SDouble a) = show a
renderPrim (STime i)
  = case i of
    STimestamp a -> formatTime defaultTimeLocale "%Y-%m-%d %H:%M:%S%Q" a
    SDate a -> show a
    SDayTime a -> show a
    SPInterval a -> show a
renderPrim (SBinary i) = "Binary= " ++ show (hash i )
renderPrim (SDynamic (HDynamic s)) = fromMaybe  "can't render SDynamic" $ fmap renderShowable (fromDynamic s) <|> fmap (L.intercalate "," . map renderPK) (fromDynamic s) <|> fmap (ident. render @(RowOperation T.Text Showable) ) (fromDynamic s)
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
    
    parseArray f i =   fmap ArrayTB1 $  allMaybes $ fmap f $ NonS.fromList $ unIntercalate (=='\n') i
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
      readCpf = nonEmpty (\i-> fmap (SText . T.pack . fmap Char.intToDigit ) . join . fmap (join . fmap (eitherToMaybe . cpfValidate ). (allMaybes . fmap readDigit)) . readMaybe $  "\"" <> i <> "\"")
      readDate =  fmap (STime . SDate . localDay ) . parseTimeM True defaultTimeLocale "%Y-%m-%d"
      readDayTime =  fmap (STime . SDayTime . localTimeOfDay ) . parseTimeM True defaultTimeLocale"%H:%M:%OS"
      readDayTimeMin =  fmap (STime . SDayTime . localTimeOfDay ) . parseTimeM True defaultTimeLocale"%H:%M"
      readDayTimeHour =  fmap (STime . SDayTime . localTimeOfDay ) . parseTimeM True defaultTimeLocale"%H"
      readPosition = nonEmpty (fmap SPosition . readMaybe)
      readLineString = nonEmpty (fmap SLineString . readMaybe)
      readMultiPolygon = nonEmpty (fmap SMultiGeom . fmap (fmap (\(i:xs) -> SPolygon i xs)). readMaybe)
      readTimestamp =  fmap (STime . STimestamp  .  localTimeToUTC utc ) . (\i -> parseTimeM True defaultTimeLocale "%Y-%m-%d %H:%M:%OS" i <|> parseTimeM True defaultTimeLocale "%Y-%m-%d %H:%M:%S" i)
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

