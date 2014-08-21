{-# LANGUAGE RecursiveDo,FlexibleInstances,RankNTypes,NoMonomorphismRestriction,UndecidableInstances,FlexibleContexts,OverloadedStrings ,TupleSections, ExistentialQuantification #-}
module Postgresql where
import Query
import Data.Bits
import Debug.Trace
import Schema
import qualified Data.Serialize as Sel
import Data.Maybe
import Text.Read
import Data.Typeable
import qualified Data.ByteString.Base16 as B16
import Data.Time.Parse
import Reactive.Threepenny
import           Database.PostgreSQL.Simple.Arrays as Arrays
import Data.Graph(stronglyConnComp,flattenSCCs)
import Control.Exception
import           Data.Attoparsec.Char8 hiding (Result)
import Data.Traversable (Traversable,traverse)
import Warshal
import Data.Time.LocalTime
import Data.IORef
import Control.Monad(when,void,mapM,replicateM,liftM,join)
import Data.Functor.Compose
import qualified Database.PostgreSQL.Simple.TypeInfo.Static as TI
import qualified Data.List as L
import Data.Vector(Vector)
import qualified Numeric.Interval as Interval
import qualified Numeric.Interval.Internal as NI
import qualified Data.ByteString.Char8 as BS

import qualified Graphics.UI.Threepenny as UI
import Graphics.UI.Threepenny.Core
import Data.Monoid
import Data.Time.Parse

import System.IO.Unsafe
import Debug.Trace
import qualified Data.Foldable as F
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

instance TF.ToField (UnQuoted Showable) where
  toField (UnQuoted (DTimestamp i )) = TF.Plain $ localTimestampToBuilder i
  toField (UnQuoted (DDate i )) = TF.Plain $ dateToBuilder i
  toField i = TF.toField i

instance TF.ToField Position where
  toField = TF.toField . UnQuoted

instance TF.ToField (UnQuoted Position) where
  toField (UnQuoted (Position (lat,lon,alt))) = TF.Many [str "ST_SetSRID(ST_MakePoint(", TF.toField lat , del , TF.toField lon , del, TF.toField alt , str "),4326)"]
    where del = TF.Plain $ fromChar ','
          str = TF.Plain . fromByteString

instance TF.ToField (UnQuoted a) => TF.ToField (Interval.Interval a) where
  toField = intervalBuilder


intervalBuilder i =  TF.Many [TF.Plain $ fromByteString "\'[" ,  TF.toField $  (UnQuoted $ Interval.inf i) , TF.Plain $ fromChar ',' , TF.toField  (UnQuoted $ Interval.sup i) , TF.Plain $ fromByteString "]\'"]

instance TF.ToField Showable where
  toField (Showable t) = TF.toField t
  toField (Numeric t) = TF.toField t
  toField (DDate t) = TF.toField t
  toField (DTimestamp t) = TF.toField t
  toField (DNumeric t) = TF.toField t
  toField (SOptional t) = TF.toField t
  toField (SComposite t) = TF.toField t
  toField (SInterval t) = TF.toField t
  toField (SPosition t) = TF.toField t

defaultType t =
    case keyType t of
      KOptional i -> Just (SOptional Nothing)
      i -> Nothing


readType t =
    case fmap textToPrim $ keyType t of
      Primitive PText -> readText
      Primitive PDouble ->  readDouble
      Primitive PInt -> readInt
      Primitive PTimestamp -> readTimestamp
      Primitive PDate-> readDate
      Primitive PPosition -> readPosition
      KInterval (Primitive PTimestamp ) -> inter readTimestamp
      KOptional (KInterval (Primitive PTimestamp )) -> opt (inter readTimestamp)
      KOptional (Primitive PText ) -> opt readText
      KOptional (Primitive PInt )-> opt readInt
      KOptional (Primitive PDouble ) -> opt readDouble
      KOptional (Primitive PTimestamp) -> opt readTimestamp
      KOptional (Primitive PDate) -> opt readDate
      KOptional (Primitive PPosition) -> opt readPosition
      i -> error ( "Missing type: " <> show (keyType t))
    where
      readInt = nonEmpty (fmap Numeric . readMaybe)
      readDouble = nonEmpty (fmap DNumeric . readMaybe)
      readText = nonEmpty (\i-> fmap Showable . readMaybe $  "\"" <> i <> "\"")
      readDate =  fmap (DDate . Finite . localDay . fst) . strptime "%Y-%m-%d"
      readPosition = nonEmpty (fmap SPosition . readMaybe)
      readTimestamp =  fmap (DTimestamp  . Finite . fst) . strptime "%Y-%m-%d %H:%M:%S"
      nonEmpty f ""  = Nothing
      nonEmpty f i  = f i
      opt f "" =  Just $ SOptional Nothing
      opt f i = fmap (SOptional .Just) $ f i
      inter f = (\(i,j)-> fmap SInterval $ join $ Interval.interval <$> (f i) <*> (f $ safeTail j) )  .  break (==',')

safeTail [] = []
safeTail i = tail i



renderedType key = \f b ->
   case F.name f  of
      Just name -> let
          go ::  KType Text
                -> F.Conversion Showable
          go t = case t of
            (KInterval (Primitive i)) -> SInterval <$> prim name (textToPrim i) f b
            (KOptional (Primitive i)) -> SOptional <$> prim name (textToPrim i) f b
            (KArray (Primitive i)) -> SComposite <$> prim name (textToPrim i) f b
            (KOptional (KArray (Primitive i))) ->  fmap (SOptional . fmap SComposite . getCompose ) $ prim name (textToPrim i) f b
            (KOptional (KInterval (Primitive i))) -> (SOptional . fmap SInterval . getCompose ) <$> prim name (textToPrim i) f b
            (Primitive i) ->  fmap unOnly $ prim  name (textToPrim i) f b
          in case (keyValue key == T.fromStrict (TE.decodeUtf8 name)) of
              True ->  go (keyType key)
              False -> error $ "no match type for " <> BS.unpack name <> " with key" <> show key
      Nothing -> error "no name for field"
     where


unOnly :: Only a -> a
unOnly (Only i) = i

prim :: (F.FromField (f1 Position ),F.FromField (f1 LocalTimestamp),F.FromField (f1 Date),F.FromField (f1 Text), F.FromField (f1 Double), F.FromField (f1 Int), Functor f1) =>
          BS.ByteString
        -> KPrim
        -> F.Field
        -> Maybe BS.ByteString
        -> F.Conversion (f1 Showable)
prim  name p f b = case p of
            PText ->  s $ F.fromField f b
            PInt -> n $ F.fromField  f b
            PDouble -> d $ F.fromField  f b
            PDate -> da $ F.fromField  f b
            PTimestamp -> t $ F.fromField  f b
            PPosition -> pos $ F.fromField  f b
  where
    s = fmap (fmap Showable)
    n = fmap (fmap Numeric)
    d = fmap (fmap DNumeric)
    da = fmap (fmap DDate)
    t = fmap (fmap DTimestamp)
    pos = fmap (fmap SPosition)

instance (F.FromField (f (g a))) => F.FromField (Compose f g a) where
  fromField = fmap (fmap (fmap (Compose ) )) $ F.fromField

instance F.FromField Position where
  fromField f t = case  fmap (Sel.runGet getV ) decoded of
    Just i -> case i of
      Right i -> pure i
      Left e -> error e
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
               1 -> do
                x <- Sel.getFloat64le
                y <- Sel.getFloat64le
                z <- Sel.getFloat64le
                return  $ Position (x,y,z)
               i -> error $ "type not implemented " <> show ty <> "  "<> show decoded
           else
             return (error $ "BE not implemented " <> show i <> "  " <> show decoded)
      decoded = fmap (fst . B16.decode) t

instance Functor Interval.Interval where
  fmap f i = NI.I (f (Interval.inf i)) ( f (Interval.sup i))

-- | any postgresql array whose elements are compatible with type @a@
instance (F.FromField a,Ord a, Typeable a) => F.FromField (Interval.Interval a) where
    fromField f mdat = do
        info <- F.typeInfo f
        case info of
          F.Range{} ->
              case mdat of
                Nothing  -> F.returnError F.UnexpectedNull f ""
                Just  dat -> do
                   case parseOnly (fromArray info f) dat of
                     Left  err  -> F.returnError F.ConversionFailed f err
                     Right conv -> (Interval....) <$>  (fmap (!!0) conv) <*> (fmap (!!1) conv)
          _ -> F.returnError F.Incompatible f ""

range :: Char -> Parser [ArrayFormat]
range delim = char '[' *> option [] (arrays <|> strings) <* char ']'
  where
        strings = sepBy1 (Quoted <$> quoted <|> Plain <$> plain delim) (char delim)
        arrays  = sepBy1 (Arrays.Array <$> array delim) (char ',')
                -- NB: Arrays seem to always be delimited by commas.
            --
fromArray :: (FromField a)
          => TypeInfo -> Field -> Parser (Conversion [a])
fromArray typeInfo f = sequence . (parseIt <$>) <$> range delim
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
    let keyMap = keySetToMap foldable
    n <- FR.numFieldsRemaining
    traverse (FR.fieldWith . renderedType) foldable

keySetToMap ks = M.fromList $  fmap (\(Key k _ _ t)-> (toStrict $ encodeUtf8 k,t))  (F.toList ks)

withConn action = do
  conn <- connectPostgreSQL "user=postgres password=queijo dbname=test"
  action conn

topSortTables tables = flattenSCCs $ stronglyConnComp item
  where item = fmap (\n@(Raw _ t k _ fk _ ) -> (n,k,fmap (\(Path _ _ end)-> end) (S.toList fk) )) tables

