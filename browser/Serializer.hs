{-# LANGUAGE TypeFamilies, ScopedTypeVariables, DeriveFunctor,
  FlexibleInstances, TypeOperators #-}

module Serializer where

import qualified Data.Binary as B
import qualified Data.ByteString.Char8 as BS
import Data.Dynamic
import Data.Profunctor.Cayley
import Data.Profunctor
import qualified Data.ByteString.Lazy as BSL
import qualified Data.Interval as Interval
import Data.Time
import Control.Category
import qualified Data.Map as M
import Database.PostgreSQL.Simple
import qualified NonEmpty as Non
import RuntimeTypes
import SchemaQuery
import Step.Host
import Types
import Step.Common
import Types.Index
import Types.Patch
import Utils
import Prelude hiding(id,(.))

import Data.Text (Text)
import qualified Data.Text as T
import Postgresql.Parser

class ADecodeTB1 f where

class DecodeTB1 f where
  decFTB :: FTB a -> f a
  decFTB = decodeIso isoFTB
  encFTB :: f a -> FTB a
  encFTB = encodeIso isoFTB
  isoFTB :: SIso [KTypePrim]  (f a) (FTB a)

instance DecodeTB1 Only where
  decFTB (TB1 i) = Only i
  encFTB (Only i) = TB1 i


infixr 1 :*:

data Reference k
  = AttrRef (KType KPrim) k
  | InlineTable (KType Text) k (Union (Reference k))


data SIso s a b
  = SIso
  { token :: s
  , encodeIso :: (a ->b)
  , decodeIso :: (b ->a)
  }

type Serializer = Parser (->)

overArray (P (vi,vo) k) = P (Primitive [KArray ], Primitive [KArray]) (\(ArrayTB1 l ) -> ArrayTB1 (fmap k l) )

atTB ix (P (vi,vo) k) = P (AttrRef vi ix,AttrRef vo ix) (alterTB ix k)
  where
    alterTB ix k = M.alter (fmap k) ix

newtype (:*:) f g a = CompFunctor
  { unCompF :: f (g a)
  } deriving (Functor)


instance DecodeTB1 [] where
  isoFTB = SIso [KOptional,KArray] encFTB decFTB
    where
      decFTB (LeftTB1 i ) = maybe [] decFTB i
      decFTB (ArrayTB1 i ) = Non.toList (unTB1 <$> i)
      encFTB l = LeftTB1 $ (\i -> ArrayTB1 (TB1 <$> i)) <$> Non.nonEmpty l

instance DecodeTB1 Interval.Interval where
  decFTB (IntervalTB1 i) = fmap unTB1 i
  encFTB i = IntervalTB1 $ fmap TB1 i
  isoFTB = SIso [KInterval] encFTB decFTB

instance DecodeTB1 Non.NonEmpty  where
  decFTB (ArrayTB1 i) = fmap unTB1 i
  encFTB i = ArrayTB1 $ fmap TB1 i
  isoFTB = SIso [KArray] encFTB decFTB

instance DecodeTB1 g => DecodeTB1 (Maybe :*: g) where
  isoFTB = SIso ([KOptional] ++ l) encFTB decFTB
    where
      SIso l enc dec = isoFTB
      decFTB (LeftTB1 i) = CompFunctor $ fmap dec i
      encFTB (CompFunctor i) = LeftTB1 $ fmap enc i

class DecodeTable a where
  decodeT :: TBData Text Showable -> a
  encodeT :: a -> TBData Text Showable


data TIso i b  = TIso { unTiso :: (i -> b) , tIso :: (b -> i)}

instance Category TIso where
  id  = TIso id id
  TIso i j  .  TIso a b = TIso (i.a ) (b . j)

traverseIso :: Functor f => TIso a b -> TIso (f a ) (f b)
traverseIso (TIso i j)  =  TIso (fmap i) (fmap j)

ftbIso :: DecodeTB1 b => TIso (b a ) (FTB a)
ftbIso  = TIso encFTB decFTB

tableIso :: DecodeTable b => TIso b (TBData Text Showable)
tableIso  = TIso encodeT decodeT



instance DecodeTable Plugins where
  decodeT d =  (ref,code)
    where
      ref = unOnly . att . ix "ref" $ d
      code = unOnly . att . ix "plugin" $ d


instance (Ord a, a ~ Index a ,Show a, Patch a, B.Binary a) =>
         DecodeTable (TableModificationK (Text, Text) (RowPatch Text a)) where
  decodeT d =
    TableModification
      (Just mod_id)
      time
      username
      (schema, table)
      mod_data
    where
      schema = unOnly . att . ix "schema_name" $ d
      table = unOnly . att . ix "table_name" $ d
      mod_id = unOnly . att . ix "modification_id" $ d
      mod_data = unBinary . unOnly . att . ix "modification_data" $ d
      username = unOnly . att . ix "user_name" $ d
      time = unOnly . att . ix "modification_time" $ d
  encodeT tm@(TableModification id ts u table ip) =
    tblist $
    [ Attr "user_name" (txt u)
    , Attr "modification_time" (timestamp ts)
    , Attr "table_name" (txt $ snd table)
    -- , Attr "data_index" (array (TB1 . encodeS) mod_key)
    , Attr "modification_data" (TB1 . SBinary . BSL.toStrict . B.encode $ ip)
    , Attr "schema_name" (txt $ fst table)
    , Attr "modification_id" (opt int id)
    ]
    where
      {-(Idex pidx , _) =
        case ip of
          PatchRow (p,i) -> (p,i)
          CreateRow i -> ((getIndex (tableMeta table) i ),patch i)
          DropRow i -> ((getIndex (tableMeta table) i ),patch i)
      mod_key :: Non.NonEmpty (Binary (FTB a))
      mod_key = Non.fromList $ Binary . fmap create <$> justError ("no index: " ++ show tm) (nonEmpty pidx)
-}
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

instance DecodeShowable UTCTime where
  decodeS (STime (STimestamp i)) = i
  encodeS i = STime (STimestamp i)

instance DecodeShowable PrePlugins where
  decodeS (SHDynamic (HDynamic i)) = justError "invalid plugin code" $ fromDynamic i  :: PrePlugins

unBinary (Binary i) = i

att :: (Functor f, DecodeTB1 f, DecodeShowable a) => TB k Showable -> f a
att (Attr i j) = decodeS <$> decFTB j
