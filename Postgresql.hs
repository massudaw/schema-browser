{-# LANGUAGE DeriveTraversable,DeriveFoldable,StandaloneDeriving,RecursiveDo,FlexibleInstances,RankNTypes,NoMonomorphismRestriction,UndecidableInstances,FlexibleContexts,OverloadedStrings ,TupleSections, ExistentialQuantification #-}
module Postgresql where
import Types
import Utils
import Query
import GHC.Stack
import Debug.Trace
import Data.Functor.Identity
import Data.Functor.Compose
import Data.Scientific hiding(scientific)
import Data.Bits
import Data.Aeson
import Data.Bifunctor
import qualified  Data.Map as M

import Data.Tuple
import Data.Time.Clock
import qualified Data.Char as Char
import Schema
import Control.Concurrent
import qualified Data.HashMap.Strict as HM
import Data.String
import Data.Attoparsec.Combinator (lookAhead)

import Control.Applicative
import Control.Monad.IO.Class
import qualified Data.Serialize as Sel
import Data.Maybe
import Text.Read
import qualified Data.ExtendedReal as ER
import Data.ExtendedReal (Extended)
import qualified Data.ByteString.Base16 as B16
import Data.Time.Parse
import           Database.PostgreSQL.Simple.Arrays as Arrays
import           Database.PostgreSQL.Simple.Types as PGTypes
import Data.Graph(stronglyConnComp,flattenSCCs)
import           Data.Attoparsec.ByteString.Char8 hiding (Result)
import Data.Traversable (Traversable,traverse)
import qualified Data.Traversable  as Tra
-- import Warshal
import Data.Time.LocalTime
import Control.Monad(replicateM,join)
import qualified Data.List as L
import qualified Data.Vector as Vector
import qualified Data.Interval as Interval
import Data.Interval (Interval)
import qualified Data.ByteString.Char8 as BS

import Data.Monoid
import Prelude hiding (takeWhile)

import System.Time.Extra

import qualified Data.Foldable as F
import Data.Foldable (Foldable)
import qualified Data.Text.Lazy as T
import qualified Data.Text.Encoding as TE
import Data.Text.Lazy (Text)
import qualified Data.Set as S
import Database.PostgreSQL.Simple.Time
import qualified Database.PostgreSQL.Simple.FromField as F
import Database.PostgreSQL.Simple.FromField hiding(Binary,Identity)
-- import Database.PostgreSQL.Simple.FromField (fromField,typeOid,typoid,TypeInfo,rngsubtype,typdelim,Conversion,Field,FromField)
import qualified Database.PostgreSQL.Simple.ToField as TF
import qualified Database.PostgreSQL.Simple.FromRow as FR
import Database.PostgreSQL.Simple
-- import Data.GraphViz (preview)
import Blaze.ByteString.Builder(fromByteString)
import Blaze.ByteString.Builder.Char8(fromChar)

data DB = DB { dbName :: String
          , dbUser :: String
          , dbPassword :: String
          , dbHost :: String
          , dbPort :: String
          }deriving(Show)

renderPostgresqlConn (DB n u p h pt)
  = "user=" <> u <> " password=" <> p <> " dbname=" <> n

db = DB "usda" "postgres" "queijo" "localhost" "5432"

-- Wrap new instances without quotes delimiting primitive values
newtype UnQuoted a = UnQuoted {unQuoted :: a}

deriving instance Foldable Interval
deriving instance Foldable Extended
deriving instance Traversable Extended
deriving instance Traversable Interval

instance  TF.ToField (TB Identity Key Showable)  where
  toField (Attr k i) = TF.toField i
  toField (IT n (LeftTB1 i)  ) = maybe (TF.Plain ( fromByteString "null")) (TF.toField . IT n ) i
  toField (IT (n)  (TB1 i) ) = TF.toField (TBRecord  (inlineFullName $ keyType $ n ) $  runIdentity.getCompose <$> F.toList  i )
  toField (IT (n)  (ArrayTB1 is )) = TF.toField $ PGTypes.PGArray $ (\i -> (TBRecord  ( inlineFullName $ keyType  n) $  fmap (runIdentity . getCompose ) $ F.toList  $ _unTB1 $ i ) ) <$> is
  toField e = errorWithStackTrace (show e)



instance TF.ToField a => TF.ToField (TBRecord a) where
  toField (TBRecord s l) =  TF.Many   (TF.Plain (fromByteString "ROW(") : L.intercalate [TF.Plain $ fromChar ','] (fmap (pure.TF.toField) l) <> [TF.Plain (fromByteString $ ") :: " <>  BS.pack (T.unpack s) )] )


data TBRecord a = TBRecord Text [a]

instance TF.ToField (UnQuoted Showable) where
  toField (UnQuoted (STimestamp i )) = TF.Plain $ localTimestampToBuilder (Finite i)
  toField (UnQuoted (SDate i )) = TF.Plain $ dateToBuilder (Finite i)
  toField (UnQuoted (SDayTime  i )) = TF.Plain $ timeOfDayToBuilder (i)
  toField (UnQuoted (SDouble i )) =  TF.toField i
  toField (UnQuoted (SNumeric i )) =  TF.toField i
  toField i = TF.toField i

instance TF.ToField Position where
  toField = TF.toField . UnQuoted

instance TF.ToField LineString where
  toField = TF.toField . UnQuoted

instance TF.ToField Bounding where
  toField = TF.toField . UnQuoted

instance TF.ToField (UnQuoted Bounding ) where
  toField (UnQuoted (Bounding l)) = TF.Many  [str "ST_3DMakeBox(", TF.Many points ,   str ")"]
    where del = TF.Plain $ fromChar ','
          str = TF.Plain . fromByteString
          points :: [TF.Action]
          points = [point (Interval.lowerBound l), del, point (Interval.upperBound l)]
          -- point :: Position -> TF.Action
          point (ER.Finite (Position (lat,lon,alt))) = TF.Many [str "ST_setsrid(ST_MakePoint(", TF.toField lat , del , TF.toField lon , del, TF.toField alt , str "),4326)"]


instance TF.ToField (UnQuoted LineString) where
  toField (UnQuoted (LineString l)) = TF.Many  [str "ST_SetSRID(ST_MakeLine (", TF.Many points ,   str "),4326)"]
    where del = TF.Plain $ fromChar ','
          str = TF.Plain . fromByteString
          points :: [TF.Action]
          points = L.intercalate [del] (fmap point (F.toList l))
          point :: Position -> [TF.Action]
          point (Position (lat,lon,alt)) = [str "ST_MakePoint(", TF.toField lat , del , TF.toField lon , del, TF.toField alt , str ")"]


instance TF.ToField (UnQuoted Position) where
  toField (UnQuoted (Position (lat,lon,alt))) = TF.Many [str "ST_SetSRID(ST_MakePoint(", TF.toField lat , del , TF.toField lon , del, TF.toField alt , str "),4326)"]
    where del = TF.Plain $ fromChar ','
          str = TF.Plain . fromByteString

instance TF.ToField (UnQuoted a) => TF.ToField (Interval.Interval a) where
  toField = intervalBuilder

instance TF.ToField (UnQuoted a) => TF.ToField (UnQuoted (Interval.Extended a )) where
  toField (UnQuoted (ER.Finite i)) = TF.toField (UnQuoted i)

intervalBuilder i =  TF.Many [TF.Plain $ fromByteString ("\'"  <> lbd (snd $ Interval.lowerBound' i)) ,  TF.toField $  (UnQuoted $ Interval.lowerBound i) , TF.Plain $ fromChar ',' , TF.toField  (UnQuoted $ Interval.upperBound i) , TF.Plain $ fromByteString (ubd (snd $ Interval.upperBound' i) <> "\'")]
    where lbd True  =  "["
          lbd False = "("
          ubd True = "]"
          ubd False =")"

instance TF.ToField Showable where
  toField (SText t) = TF.toField t
  toField (SNumeric t) = TF.toField t
  toField (SDate t) = TF.toField t
  toField (SDayTime t) = TF.toField t
  toField (SSerial t) = maybe (TF.Plain $ fromByteString "null") TF.toField t
  toField (STimestamp t) = TF.toField t
  toField (SDouble t) = TF.toField t
  toField (SOptional t) = TF.toField t
  toField (SComposite t) = TF.toField t
  toField (SInterval t) = TF.toField t
  toField (SPosition t) = TF.toField t
  toField (SLineString t) = TF.toField t
  toField (SBounding t) = TF.toField t
  toField (SBoolean t) = TF.toField t
  toField (SBinary t) = TF.toField (Binary t)

defaultType t =
    case t of
      KOptional i -> Just (SOptional Nothing)
      i -> Nothing

readTypeOpt t Nothing = case t of
    KOptional i -> Just $ SOptional Nothing
    i -> Nothing
readTypeOpt t (Just i) = readType t i

readType t = case t of
    Primitive i -> readPrim i
    KOptional i -> opt (readType i)
    KSerial i -> opt (readType i)
    KArray i  -> parseArray (readType i)
    -- KInterval i -> inter (readType i)
  where
      opt f "" =  Just $ SOptional Nothing
      opt f i = fmap (SOptional .Just) $ f i
      parseArray f i =   fmap (SComposite. Vector.fromList) $  allMaybes $ fmap f $ unIntercalate (=='\n') i
      -- inter f = (\(i,j)-> fmap SInterval $ join $ Interval.interval <$> (f i) <*> (f $ safeTail j) )  .  break (==',')

readPrim t =
  case t of
     PText -> readText
     PCnpj -> readCnpj
     PCpf-> readCpf
     PDouble ->  readDouble
     PInt -> readInt
     PTimestamp -> readTimestamp
     PInterval -> readInterval
     PDate-> readDate
     PDayTime -> readDayTime
     PPosition -> readPosition
     PBoolean -> readBoolean
     PLineString -> readLineString
  where
      readInt = nonEmpty (fmap SNumeric . readMaybe)
      readBoolean = nonEmpty (fmap SBoolean . readMaybe)
      readDouble = nonEmpty (fmap SDouble. readMaybe)
      readText = nonEmpty (\i-> fmap SText . readMaybe $  "\"" <> i <> "\"")
      readCnpj = nonEmpty (\i-> fmap (SText . T.pack . fmap Char.intToDigit ) . join . fmap (join . fmap (eitherToMaybe . cnpjValidate ). (allMaybes . fmap readDigit)) . readMaybe $  "\"" <> i <> "\"")
      readCpf = nonEmpty (\i-> fmap (SText . T.pack . fmap Char.intToDigit ) . join . fmap (join . fmap (eitherToMaybe . cpfValidate ). (allMaybes . fmap readDigit)) . readMaybe $  "\"" <> i <> "\"")
      readDate =  fmap (SDate . localDay . fst) . strptime "%Y-%m-%d"
      readDayTime =  fmap (SDayTime . localTimeOfDay . fst) . strptime "%H:%M:%OS"
      readPosition = nonEmpty (fmap SPosition . readMaybe)
      readLineString = nonEmpty (fmap SLineString . readMaybe)
      readTimestamp =  fmap (STimestamp  .  fst) . strptime "%Y-%m-%d %H:%M:%OS"
      readInterval =  fmap SPInterval . (\(h,r) -> (\(m,r)->  (\s m h -> secondsToDiffTime $ h*3600 + m*60 + s ) <$> readMaybe (safeTail r) <*> readMaybe m <*> readMaybe h )  $ break (==',') (safeTail r))  . break (==',')
      nonEmpty f ""  = Nothing
      nonEmpty f i  = f i

eitherToMaybe = either (const Nothing) Just

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

safeTail [] = []
safeTail i = tail i



unIntercalateAtto :: Alternative f => [f a1] -> f a -> f [a1]
unIntercalateAtto l s = go l
  where go (e:cs) =  liftA2 (:) e  (s *> go cs <|> pure [])
        go [] = pure []


unKOptionalAttr (Attr k i ) = Attr (unKOptional k) i
unKOptionalAttr (IT  r (LeftTB1 (Just j))  ) = (\j-> IT   r j )    j
unKOptionalAttr (FKT i r l (LeftTB1 (Just j))  ) = FKT (fmap (mapComp (first unKOptional) ) i) r l j

unOptionalAttr (Attr k i ) = Attr (unKOptional k) <$> unSOptional i
unOptionalAttr (IT r (LeftTB1 j)  ) = (\j-> IT   r j ) <$>     j
unOptionalAttr (FKT i r l (LeftTB1 j)  ) = liftA2 (\i j -> FKT i r l j) (traverse ( traverse unSOptional . (mapComp (first unKOptional)) ) i)  j

-- parseAttr i | traceShow i False = error ""
parseAttr (Attr i _ ) = do
  s<- parseShowable (textToPrim <$> keyType i) <?> show i
  return $  Attr i s

parseAttr (TBEither n l  _ )
    =  doublequoted parseTb <|> parseTb
      where
        parseTb = char '(' *> parseInner <* char ')'
        parseInner = do
              res <- unIntercalateAtto (parseAttr . runIdentity .getCompose <$> l) (char ',')
              return $ TBEither n l  (Compose . Identity <$> (L.find ( maybe False (const True) . unOptionalAttr)) res)

parseAttr (IT na j) = do
  mj <- doublequoted (parseLabeledTable j) <|> parseLabeledTable j -- <|>  return ((,SOptional Nothing) <$> j)
  return $ IT  na mj

parseAttr (FKT l refl rel j ) = do
  ml <- unIntercalateAtto (fmap (Compose . Identity ) . parseAttr .runIdentity .getCompose  <$> l) (char ',')
  mj <- doublequoted (parseLabeledTable j) <|> parseLabeledTable j
  return $  FKT ml refl rel mj

parseArray p = (char '{' *>  sepBy1 p (char ',') <* char '}')

tryquoted i = doublequoted i <|> i
-- Note Because the list has a mempty operation when parsing
-- we have overlap between maybe and list so we allow only nonempty lists
parseLabeledTable (ArrayTB1 [t]) =
  ArrayTB1 <$> (parseArray (doublequoted $ parseLabeledTable t) <|> (parseArray (doublequoted $ parseLabeledTable (mapKey makeOpt t))  >>  return (fail "")  ) )
parseLabeledTable (LeftTB1 (Just i )) =
  LeftTB1 <$> ((Just <$> parseLabeledTable i) <|> ( parseLabeledTable (mapKey makeOpt i) >> return Nothing) <|> return Nothing )
parseLabeledTable (TB1 (KV (PK i d ) m)) = (char '('  *> (do
  im <- unIntercalateAtto (fmap (Compose . Identity) . parseAttr .runIdentity . getCompose <$> (i <> d <> m) ) (char ',')
  return (TB1 (KV ( PK (L.take (length i) im ) (L.take (length d) $L.drop (length i) $  im))(L.drop (length i + length d) im)) )) <*  char ')' )

quotedRec :: Int -> (Int -> Parser a)  -> Parser a
quotedRec i  pint =   (takeWhile (== '\\') >>  char '\"') *> inner <* ( takeWhile (=='\\') >> char '\"'  )
  where inner = quotedRec (i+1) pint <|> p
        p = pint i

plainsInd i = (char '\\' >> return "") <|> plains (fmap (replicate i '\"' <>)  [")",",","}"])


doublequoted :: Parser a -> Parser a
doublequoted  p =   (takeWhile (== '\\') >>  char '\"') *>  inner <* ( takeWhile (=='\\') >> char '\"')
  where inner = doublequoted p <|> p
parseShowable
  :: KType KPrim
       -> Parser Showable
-- parseShowable  i | traceShow i False = error ""
parseShowable (Primitive i ) =  (do
   case i of
        PMime _ -> let
              pr = SBinary . fst . B16.decode . BS.drop 1 <$>  (takeWhile (=='\\') *> plain' "\\\",)}" <* takeWhile (=='\\'))
                in doublequoted  pr <|> pr
        PInt ->  SNumeric <$>  signed decimal
        PBoolean -> SBoolean <$> ((const True <$> string "t") <|> (const False <$> string "f"))
        PDouble -> SDouble <$> pg_double
        PText -> SText . T.fromStrict  . TE.decodeUtf8   <$> ( doublequoted (plain' "\\\"")  <|> plain' ",)}" <|>  (const "''" <$> string "\"\"" ) )
        PCnpj -> parseShowable (Primitive PText)
        PCpf -> parseShowable (Primitive PText)
        PInterval ->
          let i = SPInterval <$> diffInterval
           in doublequoted i <|> i

        PTimestamp ->
             let p =  do
                    i <- fmap (STimestamp  . fst) . strptime "%Y-%m-%d %H:%M:%OS"<$> plain' "\\\",)}"
                    maybe (fail "cant parse date") return i
                 in p <|> doublequoted p
        PDayTime ->
             let p =  do
                    i <- fmap (SDayTime . localTimeOfDay .  fst) . strptime "%H:%M:%OS"<$> plain' "\\\",)}"
                    maybe (fail "cant parse date") return i
                 in p <|> doublequoted p
        PDate ->
             let p = do
                    i <- fmap (SDate . localDay . fst). strptime "%Y-%m-%d" <$> plain' "\\\",)}"
                    maybe (fail "cant parse date") return i
                 in p <|> doublequoted p
        PPosition -> do
          s <- plain' "\",)}"
          case  Sel.runGet getPosition (fst $ B16.decode s)of
              i -> case i of
                Right i -> pure $ SPosition i
                Left e -> fail e
        PLineString -> do
          s <- plain' "\",)}"
          case  Sel.runGet getLineString (fst $ B16.decode s)of
              i -> case i of
                Right i -> pure $ SLineString i
                Left e -> fail e
        PBounding -> SBounding <$> ((doublequoted box3dParser ) <|> box3dParser)
        --i -> error $ "primitive not implemented - " <> show i
            ) <?> (show i)
parseShowable (KArray i)
    =  SComposite . Vector.fromList <$> (par <|> doublequoted par)
      where par = char '{'  *>  sepBy (parseShowable i) (char ',') <* char '}'
parseShowable (KOptional i)
    = SOptional <$> ( (Just <$> (parseShowable i)) <|> pure (showableDef i) )
parseShowable (KSerial i)
    = SSerial <$> ((Just <$> parseShowable i) )
parseShowable (KInterval k)=
    let
      emptyInter = const (SInterval Interval.empty) <$> string "empty"
      inter = do
        lb <- (char '[' >> return True ) <|> (char '(' >> return False )
        i <- parseShowable k
        char ','
        j <- parseShowable k
        rb <- (char ']' >> return True) <|> (char ')' >> return False )
        return $ SInterval $ Interval.interval (ER.Finite i,lb) (ER.Finite j,rb)
    in doublequoted inter <|> inter <|> emptyInter

parseShowable i  = error $  "not implemented " <> show i

pg_double :: Parser Double
pg_double
    =   (string "NaN"       *> pure ( 0 / 0))
    <|> (string "Infinity"  *> pure ( 1 / 0))
    <|> (string "-Infinity" *> pure (-1 / 0))
    <|> double



unOnly :: Only a -> a
unOnly (Only i) = i

instance (F.FromField (f (g a))) => F.FromField (Compose f g a) where
  fromField = fmap (fmap (fmap (Compose ) )) $ F.fromField

instance Sel.Serialize a => Sel.Serialize (ER.Extended a ) where
  get = ER.Finite <$> Sel.get
  put (ER.Finite i ) = Sel.put i

instance Sel.Serialize Bounding where
  get = do
      i <- liftA2 (Interval.interval) Sel.get Sel.get
      return  $ Bounding i
  put (Bounding i ) = do
      Sel.put (Interval.upperBound i)
      Sel.put (Interval.lowerBound i)

instance Functor (Interval.Interval) where
  fmap f (Interval.Interval (ei,ec) (ji,jc)) = Interval.Interval (f <$> ei,ec) (f <$> ji,jc)


instance Sel.Serialize Position where
  get = do
      x <- Sel.getFloat64le
      y <- Sel.getFloat64le
      z <- Sel.getFloat64le
      return  $ Position (x,y,z)
  put (Position (x,y,z)) = do
      Sel.putFloat64le x
      Sel.putFloat64le y
      Sel.putFloat64le z

instance Sel.Serialize LineString where
  get = do
      n <- Sel.getWord32host
      LineString .Vector.fromList <$> replicateM (fromIntegral n ) Sel.get
  put (LineString  v ) = do
      mapM_ (Sel.put) (F.toList v)



getLineString = do
          i <- Sel.getWord8
          if i  == 1
           then do
             typ <- Sel.getWord32host
             srid <- Sel.getWord32host
             let ty = typ .&. complement 0x20000000 .&. complement 0x80000000
             case ty  of
               2 -> Sel.get
               i -> error $ "type not implemented " <> show ty
           else
             return (error $ "BE not implemented " <> show i )


box3dParser = do
          string "BOX3D"
          let makePoint [x,y,z] = Position (x,y,z)
          res  <- char '(' *> sepBy1 (sepBy1 ( scientific) (char ' ') ) (char ',') <* char ')'
          return $ case fmap (fmap  realToFrac) res  of
            [m,s] ->  Bounding ((ER.Finite $ makePoint m ,True) `Interval.interval` (ER.Finite $ makePoint s,True))



instance F.FromField Position where
  fromField f t = case  fmap (Sel.runGet getPosition ) decoded of
    Just i -> case i of
      Right i -> pure i
      Left e -> F.returnError F.ConversionFailed  f e
    Nothing -> error "empty value"
    where
        decoded = fmap (fst . B16.decode) t

getPosition = do
          i <- Sel.getWord8
          if i  == 1
           then do
             typ <- Sel.getWord32host
             srid <- Sel.getWord32host
             let ty = typ .&. complement 0x20000000 .&. complement 0x80000000
             case ty  of
               1 -> Sel.get
               i -> error $ "type not implemented " <> show ty
           else
             return (error $ "BE not implemented " <> show i  )


safeMaybe e f i = maybe (errorWithStackTrace (e  <> ", input = " <> show i )) id (f i)

instance F.FromField DiffTime where
  fromField  f mdat = case  mdat of
    Nothing -> F.returnError F.UnexpectedNull f ""
    Just dat -> do
      case parseOnly diffInterval dat of

          Left err -> F.returnError F.ConversionFailed f err
          Right conv -> return conv

diffIntervalLayout = sepBy1 (toRealFloat <$> scientific) (string " days " <|> string " day " <|>  string ":" )

diffInterval = (do
  res  <- diffIntervalLayout
  return $ case res  of
    [s] ->  secondsToDiffTime (round s)
    [m,s] ->  secondsToDiffTime (round $  (60 ) * m + s)
    [h,m,s] ->  secondsToDiffTime (round $ h * 3600 + (60 ) * m + s)
    [d,h,m,s] -> secondsToDiffTime (round $ d *3600*24 + h * 3600 + (60  ) * m + s)
    v -> errorWithStackTrace $ show v)

plains :: [String] -> Parser BS.ByteString
plains delims = BS.takeWhile (/='\\') . BS.pack <$> manyTill' anyChar (   foldr1 (<|>) $  lookAhead .string . BS.pack <$> delims)

plain' :: String -> Parser BS.ByteString
plain' delim = takeWhile1 (notInClass (delim ))

plain0' :: String -> Parser BS.ByteString
plain0' delim = Data.Attoparsec.ByteString.Char8.takeWhile (notInClass (delim ))

parseInter token = do
    lb <- (char '[' >> return True) <|> (char '(' >> return False)
    [i,j] <- token
    rb <- (char ']' >> return True ) <|> (char ')' >> return False )
    return [(lb,ER.Finite i),(rb,ER.Finite j)]

range :: Char -> Parser (Interval.Interval ArrayFormat)
range delim = (\[i,j]-> Interval.Interval i j ) . fmap swap  <$>  parseInter (strings <|>arrays)

  where
        strings = sepBy1 (Quoted <$> quoted <|> Plain <$> plain' ",;[](){}\"" ) (char delim)
        arrays  = sepBy1 (Arrays.Array <$> array ';') (char delim)
                -- NB: Arrays seem to always be delimited by commas.


fromArray :: (FromField a)
          => TypeInfo -> Field -> Parser (Conversion (Interval.Interval a))
fromArray typeInfo f = Tra.sequence . (parseIt <$>) <$> range delim
  where
    delim = typdelim (rngsubtype typeInfo)
    fElem = f{ typeOid = typoid (rngsubtype typeInfo) }

    parseIt item =
        fromField f' $ if item' == "NULL" then Nothing else Just item'
      where
        item' = fmt delim item
        f' | Arrays.Array _ <- item = f
           | otherwise              = fElem

instance F.FromField a => F.FromField (Only a) where
  fromField = fmap (fmap (fmap Only)) F.fromField

instance FromJSON Showable where
  parseJSON (Data.Aeson.String i ) = return $ SText $ T.fromStrict  i
  parseJSON (Data.Aeson.Array i ) = do
      i <- Vector.mapM parseJSON i
      return $ SComposite   i
  parseJSON (Data.Aeson.Number i) = return $ SDouble (toRealFloat i)
  parseJSON i = errorWithStackTrace (show i)

fromAesonTB (TB1 (KV (PK p d) v)) (Object m)  =
  let ls = fmap snd $ HM.toList m
      pk = L.take (length p) ls
      dk = L.take (length d) $ L.drop (length pk) ls
      vk = L.take (length v) $ L.drop (length pk + length d) ls
  in TB1 (KV (PK (fromAesonAttr <$> (overComp id <$> p) <*> pk) (fromAesonAttr <$> (overComp id <$> d) <*> dk)) (fromAesonAttr <$> (overComp id <$> v) <*> vk))


fromAesonAttr (Attr k _) i =
    case keyType k of
         KSerial _ ->
           case  (fromJSON i) of
                   Success a -> Compose $ Identity $ (Attr k (SOptional a ) :: TB Identity Key Showable)
         KOptional _ ->
           case  (fromJSON i) of
                   Success a -> Compose $ Identity $ (Attr k (SOptional a ) :: TB Identity Key Showable)
         _ ->
           case  (fromJSON i) of
                   Success a -> Compose $ Identity $ (Attr k (a ) :: TB Identity Key Showable)

fromAttr foldable = do
    let parser  = parseLabeledTable foldable
    FR.fieldWith (\i j -> case traverse (parseOnly  parser )  j of
                               (Right (Just r ) ) -> return r
                               Right Nothing -> error (show j )
                               Left i -> error (show i <> "  " <> maybe "" (show .T.pack . BS.unpack) j  ) )


selectAll inf table   = liftIO $ do
      let rp = rootPaths'  (tableMap inf) table
      (t,v) <- duration  $ queryWith_  (fromAttr (fst rp)) (conn inf)(fromString $ T.unpack $ snd rp)
      print (tableName table,t)
      return v

addTable inf table = do
    let mvar = mvarMap inf
    mmap <- takeMVar mvar
    (isEmpty,mtable) <- case (M.lookup table mmap ) of
         Just i -> do
           emp <- isEmptyMVar i
           putMVar mvar mmap
           return (emp,i)
         Nothing -> do
           res <- selectAll  inf table
           mnew <- newMVar res
           putMVar mvar (M.insert table mnew mmap)
           return (True,mnew )
    readMVar mtable



topSortTables tables = flattenSCCs $ stronglyConnComp item
  where item = fmap (\n@(Raw _ _ _ t _ k _ fk _ ) -> (n,k,fmap (\(Path _ _ end)-> end) (S.toList fk) )) tables


