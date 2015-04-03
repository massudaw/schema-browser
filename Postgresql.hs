{-# LANGUAGE DeriveTraversable,DeriveFoldable,StandaloneDeriving,RecursiveDo,FlexibleInstances,RankNTypes,NoMonomorphismRestriction,UndecidableInstances,FlexibleContexts,OverloadedStrings ,TupleSections, ExistentialQuantification #-}
module Postgresql where
import Query
import GHC.Stack
import Data.Functor.Identity
import Data.Scientific hiding(scientific)
import Data.Bits
import Data.Tuple
import Debug.Trace
import Data.Time.Clock
import qualified Data.Char as Char
import Schema
import Control.Applicative
import qualified Data.Serialize as Sel
import Data.Maybe
import Text.Read
import qualified Data.ExtendedReal as ER
import Data.ExtendedReal (Extended)
import Data.Typeable
import qualified Data.ByteString.Base16 as B16
import Data.Time.Parse
import           Database.PostgreSQL.Simple.Arrays as Arrays
import Data.Graph(stronglyConnComp,flattenSCCs)
import Control.Exception
import           Data.Attoparsec.Char8 hiding (Result)
import Data.Traversable (Traversable,traverse,sequence)
import qualified Data.Traversable  as Tra
import Warshal
import Data.Time.LocalTime
import Data.IORef
import Control.Monad(when,void,mapM,replicateM,liftM,join)
import Data.Functor.Compose
import qualified Database.PostgreSQL.Simple.TypeInfo.Static as TI
import qualified Data.List as L
import Data.Vector(Vector)
import qualified Data.Vector as Vector
import qualified Data.Interval as Interval
import Data.Interval (Interval)
import qualified Data.ByteString.Char8 as BS

import Data.Monoid
import Data.Time.Parse

import System.IO.Unsafe
import Debug.Trace
import qualified Data.Foldable as F
import Data.Foldable (Foldable)
import qualified Data.Text.Lazy as T
import Data.ByteString.Lazy(toStrict)
import Data.Text.Lazy.Encoding
import qualified Data.Text.Encoding as TE
import Data.Text.Lazy (Text)
import qualified Data.Set as S
import Database.PostgreSQL.Simple
import Database.PostgreSQL.Simple.Time
import Database.PostgreSQL.Simple.Ok
import Database.PostgreSQL.Simple.FromField as F
import qualified Database.PostgreSQL.Simple.ToField as TF
import qualified Database.PostgreSQL.Simple.FromRow as FR
import Data.GraphViz (preview)
import qualified Data.Map as M
import Blaze.ByteString.Builder(fromByteString)
import Blaze.ByteString.Builder.Char8(fromChar)
import Data.Map (Map)
import Data.String

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

instance TF.ToField (UnQuoted Showable) where
  toField (UnQuoted (STimestamp i )) = TF.Plain $ localTimestampToBuilder i
  toField (UnQuoted (SDate i )) = TF.Plain $ dateToBuilder i
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

instance TF.ToField a => TF.ToField (Interval.Interval a) where
  toField = intervalBuilder

instance TF.ToField a => TF.ToField (UnQuoted (Interval.Extended a )) where
  toField (UnQuoted (ER.Finite i)) = TF.toField i

intervalBuilder i =  TF.Many [TF.Plain $ fromByteString "\'[" ,  TF.toField $  (UnQuoted $ Interval.lowerBound i) , TF.Plain $ fromChar ',' , TF.toField  (UnQuoted $ Interval.upperBound i) , TF.Plain $ fromByteString "]\'"]

instance TF.ToField Showable where
  toField (SText t) = TF.toField t
  toField (SNumeric t) = TF.toField t
  toField (SDate t) = TF.toField t
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
     PPosition -> readPosition
     PBoolean -> readBoolean
     PLineString -> readLineString
     -- PBounding -> readBounding
  where
      readInt = nonEmpty (fmap SNumeric . readMaybe)
      readBoolean = nonEmpty (fmap SBoolean . readMaybe)
      readDouble = nonEmpty (fmap SDouble. readMaybe)
      readText = nonEmpty (\i-> fmap SText . readMaybe $  "\"" <> i <> "\"")
      readCnpj = nonEmpty (\i-> fmap (SText . T.pack . fmap Char.intToDigit ) . join . fmap (join . fmap (eitherToMaybe . cnpjValidate ). (allMaybes . fmap readDigit)) . readMaybe $  "\"" <> i <> "\"")
      readCpf = nonEmpty (\i-> fmap (SText . T.pack . fmap Char.intToDigit ) . join . fmap (join . fmap (eitherToMaybe . cpfValidate ). (allMaybes . fmap readDigit)) . readMaybe $  "\"" <> i <> "\"")
      readDate =  fmap (SDate . Finite . localDay . fst) . strptime "%Y-%m-%d"
      readPosition = nonEmpty (fmap SPosition . readMaybe)
      readLineString = nonEmpty (fmap SLineString . readMaybe)
      -- readBounding = nonEmpty (fmap SBounding . fmap Bounding . (fmap (\(SInterval i ) -> fmap (\(SPosition p )-> p) i)) . inter readPosition )
      inter f = (\(i,j)-> fmap SInterval $  Interval.interval <$> (f i) <*> (f $ safeTail j) )  .  break (==',')
      readTimestamp =  fmap (STimestamp  . Finite . fst) . strptime "%Y-%m-%d %H:%M:%OS"
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


allMaybes i | F.all (const False) i  = Nothing
allMaybes i = case F.all isJust i of
        True -> Just $ fmap (justError "wrong invariant allMaybes") i
        False -> Nothing


safeTail [] = []
safeTail i = tail i

primType (Metric k ) = textToPrim <$> keyType k






attrToKey k@(Metric i) = renderedName i
attrToKey t@(Agg _)  = renderedType (primType t)

renderedName key = \f b ->
 case F.name f  of
      Just name -> let
          in case (keyValue key == T.fromStrict (TE.decodeUtf8 name) || maybe False (== T.fromStrict (TE.decodeUtf8 name)) (keyAlias key)  ) of
              True ->  renderedType (textToPrim <$> keyType key) f b
              False -> error $ "no match type for " <> BS.unpack name <> " with key " <> show key

      Nothing -> error "no name for field"

renderedType key f b = go key
  where
          go ::  KType KPrim
                -> F.Conversion Showable
          go t = case t of
            (KInterval (Primitive i)) -> SInterval <$>  prim i f b
            (KOptional (Primitive i)) -> SOptional <$> prim i f b
            (KSerial (Primitive i)) -> SSerial <$> prim i f b
            (KArray (Primitive i)) -> SComposite <$> prim i f b
            (KOptional (KArray (Primitive i))) ->  SOptional . fmap SComposite . getCompose  <$> prim i f b
            (KOptional (KInterval (Primitive i))) -> SOptional . fmap SInterval . getCompose  <$> prim i f b
            (KSerial (KOptional (Primitive i))) -> error $ "invalid type " <>  show t
            (Primitive i) ->  unOnly <$> prim  i f b
            (KOptional i) -> SOptional . Just <$>  go  i
            i ->  error $ "missing case renderedType: " <> (show i)


unOnly :: Only a -> a
unOnly (Only i) = i

prim :: (F.FromField (f Bool ),F.FromField (f Bounding),F.FromField (f LineString),F.FromField (f DiffTime),F.FromField (f Position ),F.FromField (f LocalTimestamp),F.FromField (f Date),F.FromField (f Text), F.FromField (f Double), F.FromField (f Int), Functor f) =>
          KPrim
        -> F.Field
        -> Maybe BS.ByteString
        -> F.Conversion (f Showable)
prim  p f b = case p of
            PText ->  s $ F.fromField f b
            PCnpj->  s $ F.fromField f b
            PCpf ->  s $ F.fromField f b
            PInt -> n $ F.fromField  f b
            PDouble -> d $ F.fromField  f b
            PDate -> da $ F.fromField  f b
            PInterval -> i $ F.fromField  f b
            PTimestamp -> t $ F.fromField  f b
            PPosition -> pos $ F.fromField  f b
            PLineString -> lin $ F.fromField  f b
            PBounding -> boun $ F.fromField  f b
            PBoolean -> bo $ F.fromField  f b
  where
    s = fmap (fmap SText)
    n = fmap (fmap SNumeric)
    d = fmap (fmap SDouble)
    da = fmap (fmap SDate)
    i = fmap (fmap SPInterval)
    t = fmap (fmap STimestamp)
    lin = fmap (fmap SLineString)
    boun = fmap (fmap SBounding)
    pos = fmap (fmap SPosition )
    bo = fmap (fmap SBoolean)

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



instance F.FromField LineString where
  fromField f t = case  fmap (Sel.runGet getV ) decoded of
    Just i -> case i of
      Right i -> pure i
      Left e -> F.returnError F.ConversionFailed f e
    Nothing -> F.returnError F.UnexpectedNull f "empty value"
    where
      getV = do
          i <- Sel.getWord8
          if i  == 1
           then do
             typ <- Sel.getWord32host
             srid <- Sel.getWord32host
             let ty = typ .&. complement 0x20000000 .&. complement 0x80000000
             case ty  of
               2 -> Sel.get
               i -> error $ "type not implemented " <> show ty <> "  "<> show decoded
           else
             return (error $ "BE not implemented " <> show i <> "  " <> show decoded)
      decoded = fmap (fst . B16.decode) t

instance F.FromField Bounding where
  fromField f t = case  t of
    Nothing -> F.returnError F.UnexpectedNull f ""
    Just dat -> do
      case parseOnly box3dParser   dat of
          Left err -> F.returnError F.ConversionFailed f err
          Right conv -> return conv

box3dParser = do
          string "BOX3D"
          let makePoint [x,y,z] = Position (x,y,z)
          res  <- char '(' *> sepBy1 (sepBy1 ( scientific) (char ' ') ) (char ',') <* char ')'
          return $ case fmap (fmap  realToFrac) res  of
            [m,s] ->  Bounding ((ER.Finite $ makePoint m ,True) `Interval.interval` (ER.Finite $ makePoint s,True))



instance F.FromField Position where
  fromField f t = case  fmap (Sel.runGet getV ) decoded of
    Just i -> case i of
      Right i -> pure i
      Left e -> F.returnError F.ConversionFailed  f e
    Nothing -> error "empty value"
    where
      getV = do
          i <- Sel.getWord8
          if i  == 1
           then do
             typ <- Sel.getWord32host
             srid <- Sel.getWord32host
             let ty = typ .&. complement 0x20000000 .&. complement 0x80000000
             case ty  of
               1 -> Sel.get
               i -> error $ "type not implemented " <> show ty <> "  "<> show decoded
           else
             return (error $ "BE not implemented " <> show i <> "  " <> show decoded)
      decoded = fmap (fst . B16.decode) t


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

instance (F.FromField a ) => F.FromField (Interval.Extended a) where
  fromField  i mdat = ER.Finite <$> (fromField i mdat)

-- | any postgresql array whose elements are compatible with type @a@
instance (F.FromField a,Ord a, Typeable a) => F.FromField (Interval.Interval a) where
    fromField f mdat = do
        info <- F.typeInfo f
        case info of
          F.Range{} ->
              case mdat of
                Nothing  -> F.returnError F.UnexpectedNull f "Null Range"
                Just  dat -> do
                   case parseOnly (fromArray info f) dat of
                     Left  err  -> F.returnError F.ConversionFailed f err
                     Right conv ->  conv
          _ -> F.returnError F.Incompatible f ""

plain' :: String -> Parser BS.ByteString
plain' delim = takeWhile1 (notInClass (delim <> "\"{}"))

parseInter token = do
    lb <- (char '[' >> return False) <|> (char '(' >> return True)
    [i,j] <- token
    rb <- (char ']' >> return False) <|> (char ')' >> return True)
    return [(lb,ER.Finite i),(rb,ER.Finite j)]

range :: Char -> Parser (Interval.Interval ArrayFormat)
range delim = (\[i,j]-> Interval.Interval i j ) . fmap swap  <$>  parseInter (strings <|>arrays)

  where
        strings = sepBy1 (Quoted <$> quoted <|> Plain <$> plain' ",;[]()" ) (char delim)
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


fromShowableList foldable = do
    n <- FR.numFieldsRemaining
    traverse (FR.fieldWith . attrToKey) foldable

topSortTables tables = flattenSCCs $ stronglyConnComp item
  where item = fmap (\n@(Raw _ t k _ fk _ ) -> (n,k,fmap (\(Path _ _ end)-> end) (S.toList fk) )) tables

projectKey
  :: Connection
     -> InformationSchema ->
     (forall t . Traversable t => QueryT Identity (t KAttribute)
         -> S.Set Key -> IO [t (Key,Showable)])
projectKey conn inf q  = (\(j,(h,i)) -> fmap (fmap (zipWithTF (,) (fmap (\(Metric i)-> i) j))) . queryWith_ (fromShowableList j) conn . traceShowId . buildQuery $ i ) . projectAllKeys (pkMap inf ) (hashedGraph inf) q


