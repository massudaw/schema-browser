{-# LANGUAGE TypeFamilies, ScopedTypeVariables, DeriveFunctor,
  FlexibleInstances, TypeOperators #-}

module Serializer where

import qualified Data.Binary as B
import qualified Data.ByteString.Char8 as BS
import qualified Data.ByteString.Lazy as BSL
import qualified Data.Interval as Interval
import Data.Time
import Database.PostgreSQL.Simple
import qualified NonEmpty as Non
import RuntimeTypes
import SchemaQuery
import Step.Host
import Types
import Types.Index
import Types.Patch
import Utils

import Data.Text (Text)
import qualified Data.Text as T
import Postgresql.Parser

class DecodeTB1 f where
  decFTB :: FTB a -> f a
  encFTB :: f a -> FTB a

instance DecodeTB1 Only where
  decFTB (TB1 i) = Only i
  encFTB (Only i) = TB1 i

infixr 1 :*:

newtype (:*:) f g a = CompFunctor
  { unCompF :: f (g a)
  } deriving (Functor)

instance DecodeTB1 g => DecodeTB1 (Interval.Interval :*: g) where
  decFTB (IntervalTB1 i) = CompFunctor $ fmap decFTB i
  encFTB (CompFunctor i) = IntervalTB1 $ fmap encFTB i

instance DecodeTB1 g => DecodeTB1 (Non.NonEmpty :*: g) where
  decFTB (ArrayTB1 i) = CompFunctor $ fmap decFTB i
  encFTB (CompFunctor i) = ArrayTB1 $ fmap encFTB i

instance DecodeTB1 g => DecodeTB1 (Maybe :*: g) where
  decFTB (LeftTB1 i) = CompFunctor $ fmap decFTB i
  encFTB (CompFunctor i) = LeftTB1 $ fmap encFTB i

class DecodeTable a where
  decodeT :: TBData Text Showable -> a
  encodeT :: a -> TBData Text Showable

instance (Ord a, a ~ Index a ,Show a, Patch a, B.Binary a) =>
         DecodeTable (TableModificationK (Text, Text) (RowPatch Text a)) where
  decodeT d =
    TableModification
      (Just mod_id)
      time
      username
      (schema, table)
      (datamod mod_data)
    where
      schema = unOnly . att . ix "schema_name" $ d
      table = unOnly . att . ix "table_name" $ d
      mod_id = unOnly . att . ix "modification_id" $ d
      mod_data = att . ix "modification_data" $ d
      mod_key :: Non.NonEmpty (Binary (FTB a))
      mod_key = fmap unOnly . unCompF . att . ix "data_index" $ d
      username = unOnly . att . ix "user_name" $ d
      time = unOnly . att . ix "modification_time" $ d
      datamod = unBinary . unOnly
  encodeT (TableModification id ts u table ip) =
    tblist $
    _tb <$>
    [ Attr "user_name" (txt u)
    , Attr "modification_time" (timestamp ts)
    , Attr "table_name" (txt $ snd table)
    , Attr "data_index" (array (TB1 . encodeS) mod_key)
    , Attr "modification_data" (TB1 . SBinary . BSL.toStrict . B.encode $ ip)
    , Attr "schema_name" (txt $ fst table)
    , Attr "modification_id" (opt int id)
    ]
    where
      (_, Idex pidx , _) =
        case ip of
          PatchRow i -> i
          CreateRow i -> patch i
          DropRow i -> patch i
      mod_key :: Non.NonEmpty (Binary (FTB a))
      mod_key = Non.fromList $ Binary . fmap create <$> pidx

ix i d = justError ("no field " ++ show i) $ indexField (IProd Nothing i) d

class DecodeShowable a where
  decodeS :: Showable -> a
  encodeS :: a -> Showable

instance B.Binary a => DecodeShowable (Binary a) where
  decodeS (SBinary i) = Binary $ B.decode (BSL.fromStrict i)
  encodeS (Binary i) = SBinary (BSL.toStrict $ B.encode i)

instance DecodeShowable Int where
  decodeS (SNumeric i) = i
  encodeS = SNumeric

instance DecodeShowable Double where
  decodeS (SDouble i) = i
  encodeS = SDouble

instance DecodeShowable Text where
  decodeS (SText i) = i
  encodeS = SText

instance DecodeShowable LocalTime where
  decodeS (STime (STimestamp i)) = i
  encodeS i = STime (STimestamp i)

unBinary (Binary i) = i

att :: (Functor f, DecodeTB1 f, DecodeShowable a) => TB g k Showable -> f a
att (Attr i j) = decodeS <$> decFTB j
