{-# LANGUAGE RecursiveDo,FlexibleInstances,RankNTypes,NoMonomorphismRestriction,UndecidableInstances,FlexibleContexts,OverloadedStrings ,TupleSections, ExistentialQuantification #-}
module Postgresql where
import Query
import Data.Scientific hiding(scientific)
import Data.Bits
import Debug.Trace
import Data.Time.Clock
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

textToPrim "character varying" = PText
textToPrim "text" = PText
textToPrim "character" = PText
textToPrim "double precision" = PDouble
textToPrim "float8" = PDouble
textToPrim "int4" = PInt
textToPrim "int8" = PInt
textToPrim "integer" = PInt
textToPrim "boolean" = PBoolean
textToPrim "smallint" = PInt
textToPrim "timestamp without time zone" = PTimestamp
textToPrim "interval" = PInterval
textToPrim "date" = PDate
textToPrim "POINT" = PPosition
textToPrim i = error $ "no case for type " <> T.unpack i


renderPostgresqlConn (DB n u p h pt)
  = "user=" <> u <> " password=" <> p <> " dbname=" <> n

db = DB "usda" "postgres" "queijo" "localhost" "5432"

-- Wrap new instances without quotes delimiting primitive values
newtype UnQuoted a = UnQuoted {unQuoted :: a}

instance TF.ToField (UnQuoted Showable) where
  toField (UnQuoted (STimestamp i )) = TF.Plain $ localTimestampToBuilder i
  toField (UnQuoted (SDate i )) = TF.Plain $ dateToBuilder i
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
  toField (SText t) = TF.toField t
  toField (SNumeric t) = TF.toField t
  toField (SDate t) = TF.toField t
  toField (STimestamp t) = TF.toField t
  toField (SDouble t) = TF.toField t
  toField (SOptional t) = TF.toField t
  toField (SComposite t) = TF.toField t
  toField (SInterval t) = TF.toField t
  toField (SPosition t) = TF.toField t
  toField (SBoolean t) = TF.toField t

defaultType t =
    case keyType t of
      KOptional i -> Just (SOptional Nothing)
      i -> Nothing


readType t =
    case t of
      Primitive PText -> readText
      Primitive PDouble ->  readDouble
      Primitive PInt -> readInt
      Primitive PTimestamp -> readTimestamp
      Primitive PInterval -> readInteval
      Primitive PDate-> readDate
      Primitive PPosition -> readPosition
      Primitive PBoolean -> readBoolean
      KInterval (Primitive PTimestamp) -> inter readTimestamp
      KOptional (KInterval (Primitive PTimestamp)) -> opt (inter readTimestamp)
      KOptional (Primitive PInterval) -> opt readInteval
      KOptional (Primitive PText) -> opt readText
      KOptional (Primitive PInt)-> opt readInt
      KOptional (Primitive PDouble) -> opt readDouble
      KOptional (Primitive PTimestamp) -> opt readTimestamp
      KOptional (Primitive PDate) -> opt readDate
      KOptional (Primitive PPosition) -> opt readPosition
      KOptional (Primitive PBoolean) -> opt readBoolean
      i -> error ( "Missing type: " <> show t)
    where
      readInt = nonEmpty (fmap SNumeric . readMaybe)
      readBoolean = nonEmpty (fmap SBoolean . readMaybe)
      readDouble = nonEmpty (fmap SDouble. readMaybe)
      readText = nonEmpty (\i-> fmap SText . readMaybe $  "\"" <> i <> "\"")
      readDate =  fmap (SDate . Finite . localDay . fst) . strptime "%Y-%m-%d"
      readPosition = nonEmpty (fmap SPosition . readMaybe)
      readTimestamp =  fmap (STimestamp  . Finite . fst) . strptime "%Y-%m-%d %H:%M:%OS"
      readInteval =  fmap SPInterval . (\(h,r) -> (\(m,r)->  (\s m h -> secondsToDiffTime $ h*3600 + m*60 + s ) <$> readMaybe (safeTail r) <*> readMaybe m <*> readMaybe h )  $ break (==',') (safeTail r))  . break (==',')
      nonEmpty f ""  = Nothing
      nonEmpty f i  = f i
      opt f "" =  Just $ SOptional Nothing
      opt f i = fmap (SOptional .Just) $ f i
      inter f = (\(i,j)-> fmap SInterval $ join $ Interval.interval <$> (f i) <*> (f $ safeTail j) )  .  break (==',')

safeTail [] = []
safeTail i = tail i


primType (Metric k ) = textToPrim <$> keyType k
primType (Agg g) =  postgresqlFunctions g
primType f@(Fun _ _) =  pgfun f
primType f@(Operator r _ _ l) =  pgfun f



availableAggregators (Primitive PInt) k = [Aggregate [k] "count"]
availableAggregators (Primitive PDouble) k = [Aggregate [k] "sum"]
availableAggregators (KInterval i ) k = [Aggregate [Operator (Fun [k] "upper") "-" "diff" (Fun [k] "lower")] "sum"]
availableAggregators i k = []

subSpace (Primitive PTimestamp)  = Primitive PInterval
subSpace (Primitive PDate)  = Primitive PInterval

pgfun :: KAttribute -> KType KPrim
pgfun (Fun [k] "lower" ) = case primType k of
    KInterval i -> i
    i -> error "not inteval"
pgfun (Fun [k] "upper" )  = case primType k of
    KInterval i -> traceShowId i
    i -> error "not inteval"
pgfun (Operator l "-" n r) = traceShowId $ subSpace (traceShowId $ primType l)


postgresqlFunctions :: Aggregate KAttribute -> KType KPrim
postgresqlFunctions (Aggregate _ "count" ) = Primitive PInt
postgresqlFunctions (Aggregate [k] "sum" ) = primType k

attrToKey k@(Metric i) = renderedName i
attrToKey t@(Agg _)  = renderedType (primType t)

renderedName key = \f b ->
 case F.name f  of
      Just name -> let
          in case (keyValue key == T.fromStrict (TE.decodeUtf8 name)) of
              True ->  renderedType (textToPrim <$> keyType key) f b
              False -> error $ "no match type for " <> BS.unpack name <> " with key" <> show key

      Nothing -> error "no name for field"

renderedType key f b = go key
  where
          go ::  KType KPrim
                -> F.Conversion Showable
          go t = case t of
            (KInterval (Primitive i)) -> SInterval <$> prim i f b
            (KOptional (Primitive i)) -> SOptional <$> prim i f b
            (KArray (Primitive i)) -> SComposite <$> prim i f b
            (KOptional (KArray (Primitive i))) ->  fmap (SOptional . fmap SComposite . getCompose ) $ prim i f b
            (KOptional (KInterval (Primitive i))) -> (SOptional . fmap SInterval . getCompose ) <$> prim i f b
            (Primitive i) ->  fmap unOnly $ prim  i f b

renderShowable :: Showable -> String
renderShowable (SOptional i ) = maybe "" show i
renderShowable (SInterval i)  = renderShowable (Interval.inf i) <> "," <> renderShowable (Interval.sup i)
renderShowable i = show i


unOnly :: Only a -> a
unOnly (Only i) = i

prim :: (F.FromField (f1 Bool ),F.FromField (f1 DiffTime),F.FromField (f1 Position ),F.FromField (f1 LocalTimestamp),F.FromField (f1 Date),F.FromField (f1 Text), F.FromField (f1 Double), F.FromField (f1 Int), Functor f1) =>
          KPrim
        -> F.Field
        -> Maybe BS.ByteString
        -> F.Conversion (f1 Showable)
prim  p f b = case p of
            PText ->  s $ F.fromField f b
            PInt -> n $ F.fromField  f b
            PDouble -> d $ F.fromField  f b
            PDate -> da $ F.fromField  f b
            PInterval -> i $ F.fromField  f b
            PTimestamp -> t $ F.fromField  f b
            PPosition -> pos $ F.fromField  f b
            PBoolean -> bo $ F.fromField  f b
  where
    s = fmap (fmap SText)
    n = fmap (fmap SNumeric)
    d = fmap (fmap SDouble)
    da = fmap (fmap SDate)
    i = fmap (fmap SPInterval)
    t = fmap (fmap STimestamp)
    pos = fmap (fmap SPosition)
    bo = fmap (fmap SBoolean)

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

instance F.FromField DiffTime where
  fromField  f mdat = case  mdat of
    Nothing -> F.returnError F.UnexpectedNull f ""
    Just dat -> do
      case parseOnly (do
        [h,m,s] <- sepBy1 (fromJust . toBoundedInteger <$> scientific) (char ':')
        return $ secondsToDiffTime (fromIntegral $ h * 3600 + (60 :: Int) * m + s)) dat of
          Left err -> F.returnError F.ConversionFailed f err
          Right conv -> return conv


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
    n <- FR.numFieldsRemaining
    traverse (FR.fieldWith . attrToKey) foldable

withConn action = do
  conn <- connectPostgreSQL "user=postgres password=queijo dbname=test"
  action conn

topSortTables tables = flattenSCCs $ stronglyConnComp item
  where item = fmap (\n@(Raw _ t k _ fk _ ) -> (n,k,fmap (\(Path _ _ end)-> end) (S.toList fk) )) tables

