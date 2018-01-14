{-# LANGUAGE DefaultSignatures,TypeFamilies, ScopedTypeVariables, DeriveFunctor,
  OverlappingInstances,DeriveGeneric,FlexibleContexts,FlexibleInstances,TypeOperators #-}

module Serializer where

import qualified Data.Binary as B
import qualified Data.ByteString.Char8 as BS
import qualified Data.Set as S
import Data.Monoid
import Control.Arrow
import Data.Maybe
import Data.Functor.Apply
import Data.Dynamic
import Data.Profunctor.Cayley
import qualified Data.Foldable as F
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
import GHC.Generics

class ADecodeTB1 f where

class DecodeTB1 f where
  decFTB :: FTB a -> f a
  decFTB = decodeIso isoFTB
  encFTB :: f a -> FTB a
  encFTB = encodeIso isoFTB
  isoFTB :: SIso [KTypePrim]   (FTB a) (f a)

instance DecodeTB1 Only where
  decFTB (TB1 i) = Only i
  encFTB (Only i) = TB1 i
  isoFTB = SIso [] encFTB decFTB

class DecodeTable a where
  decodeT :: TBData Text Showable -> a
  decodeT = decodeIso isoTable
  encodeT :: a -> TBData Text Showable
  encodeT = encodeIso isoTable
  isoTable :: SIso (Union (Reference Text)) (TBData Text Showable) a
  -- default isoTable :: (Generic a, DecodeTable' (Rep a)) => SIso (Union (Reference Text)) (TBData Text Showable) a
  -- isoTable  = isoMap (to,from) isoTable'



infixr 1 :**:

data Reference k
  = AttrRef (KType KPrim) k
  | InlineTable (KType Text) k (Union (Reference k))
  deriving(Eq,Ord,Show)

prim :: (Ord k,Functor f, DecodeShowable a, DecodeTB1 f) =>
  k -> SIso (Union (Reference k))  (TBData k Showable) (f a)
prim ix = SIso (Many [One $ AttrRef (Primitive l kp ) ix])  (mk. fs . fmap fsp ) (fmap bsp . bs . lk)
    where SIso l fs bs = isoFTB
          SIso kp fsp bsp = isoS
          lk =  _tbattr . fromJust . M.lookup (S.singleton $ Inline ix) . _kvvalues
          mk = KV. M.singleton (S.singleton $ Inline ix) . Attr ix


class DecodeTable' f where
  isoTable' :: SIso (Union (Reference Text)) (TBData Text Showable) (f a)


instance  (Selector c , DecodeShowable a)  => DecodeTable' (S1 c (Rec0 a)) where
  isoTable' = SIso (Many [One $ AttrRef (Primitive [] kp ) ix])  (mk. TB1 . fsp .unK1 . unM1) (M1 . K1 .  bsp  . unTB1 . lk)
        where
              SIso kp fsp bsp = isoS
              lk =  _tbattr . fromJust . M.lookup (S.singleton $ Inline ix) . _kvvalues
              mk = KV. M.singleton (S.singleton $ Inline ix) . Attr ix
              ix = T.pack  $ selName (undefined :: S1 c f1 a)


instance  (Functor f , Selector c , DecodeTB1 f , DecodeShowable a)  => DecodeTable' (S1 c (Rec0 (f a)) ) where
  isoTable' = SIso (Many [One $ AttrRef (Primitive l kp ) ix])  (mk. fs . fmap fsp .unK1 . unM1) (M1 . K1 . fmap bsp . bs . lk)
        where SIso l fs bs = isoFTB
              SIso kp fsp bsp = isoS
              lk =  _tbattr . fromJust . M.lookup (S.singleton $ Inline ix) . _kvvalues
              mk = KV. M.singleton (S.singleton $ Inline ix) . Attr ix
              ix = T.pack  $ selName (undefined :: S1 c f1 a)
                {-
instance  (Functor f , Selector c , DecodeTB1 f , DecodeTable a)  => DecodeTable' (S1 c (Rec0 (f a)) ) where
  isoTable' = SIso (Many [One $ AttrRef (Primitive l kp ) ix])  (mk. fs . fmap fsp .unK1 . unM1) (M1 . K1 . fmap bsp . bs . lk)
        where SIso l fs bs = isoFTB
              SIso kp fsp bsp = isoTable
              lk =  _tbattr . fromJust . M.lookup (S.singleton $ Inline ix) . _kvvalues
              mk = KV. M.singleton (S.singleton $ Inline ix) . IT ix
              ix = T.pack  $ selName (undefined :: S1 c f1 a)
-}
instance (DecodeTable' f1) => DecodeTable' (D1 c  f1 ) where
  isoTable' = SIso k  (\(M1 l ) -> i l )  (M1 . j)
    where
      (SIso k i j) = isoTable'

instance (DecodeTable' f1) => DecodeTable' (C1 c  f1 ) where
  isoTable' = SIso k  (\(M1 l ) -> i l )  (M1 . j)
    where
      (SIso k i j) = isoTable'



instance (DecodeTable' f , DecodeTable' g) => DecodeTable' (f :*: g) where
  isoTable' =  SIso (k <> l) (\(a :*: b) -> i a <> m b) (\l ->  j l :*: n l)
    where
      (SIso k i j)  = isoTable'
      (SIso l m n) = isoTable'


data TestIso
 = TestIso {
   metrics :: [Double],
   key :: Maybe Int
           }  deriving(Generic)

instance DecodeTable TestIso where


class IsoFunctor f where
  isoMap  :: (a -> b ,b -> a) -> f a -> f b
class Monoidal f where
  unit :: f ()
  (**) :: f a -> f b -> f (a,b)

instance IsoFunctor (SIso m l) where
  isoMap (f,g) (SIso l i j) = SIso l (i . g ) (f . j )


instance (Monoid l,Monoid m) => Monoidal (SIso m l)  where
  unit  = SIso  mempty (const mempty) (const ())
  (**) = mergeIso


mergeIso
  :: (Monoid s, Monoid b) => SIso s b t1 -> SIso s b t -> SIso s b (t1, t)
mergeIso  (SIso k i j) (SIso l m n ) =  SIso (k <> l) (\(a,b) -> i a <> m b) (j &&& n)

data SIso s b a
  = SIso
  { stoken :: s
  , encodeIso :: a ->b
  , decodeIso :: b ->a
  }


newtype (:**:) f g a = CompFunctor
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

instance DecodeTB1 Maybe  where
  isoFTB = SIso [KOptional] encFTB decFTB
    where
      decFTB (LeftTB1 i) =  fmap unTB1 i
      encFTB i = LeftTB1 $ fmap TB1  i


instance DecodeTB1 g => DecodeTB1 (Maybe :**: g) where
  isoFTB = SIso (KOptional : l) encFTB decFTB
    where
      SIso l enc dec = isoFTB
      decFTB (LeftTB1 i) = CompFunctor $ fmap dec i
      encFTB (CompFunctor i) = LeftTB1 $ fmap enc i


data TIso i b  = TIso { unTiso :: i -> b , tIso :: b -> i}

instance Category TIso where
  id  = TIso id id
  TIso i j  .  TIso a b = TIso (i.a ) (b . j)

traverseIso :: Functor f => TIso a b -> TIso (f a ) (f b)
traverseIso (TIso i j)  =  TIso (fmap i) (fmap j)

ftbIso :: DecodeTB1 b => TIso (b a ) (FTB a)
ftbIso  = TIso encFTB decFTB


tableIso :: DecodeTable b => TIso b (TBData Text Showable)
tableIso  = TIso encodeT decodeT


only = (unOnly ,Only)

type IsoTable a = SIso (Union (Reference Text)) (TBData Text Showable)  a

instance DecodeTable Plugins where
  isoTable = mergeIso (isoMap only $ prim "ref") (isoMap only (prim "plugin"))

test = do
  let (SIso k _ _ ) = isoTable :: IsoTable Plugins
  print k

instance DecodeShowable Showable where
  decodeS = id
  encodeS = id
instance DecodeTB1 FTB where
  decFTB = id
  encFTB = id
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
    tblist
    [ Attr "user_name" (txt u)
    , Attr "modification_time" (timestamp ts)
    , Attr "table_name" (txt $ snd table)
    , Attr "data_index" (array (TB1 . encodeS) mod_key)
    , Attr "modification_data" (TB1 . SBinary . BSL.toStrict . B.encode $ ip)
    , Attr "schema_name" (txt $ fst table)
    , Attr "modification_id" (opt int id)
    ]
    where
      (Idex pidx , _) =
        case ip of
          PatchRow (p,i) -> (p,i)
          CreateRow (ix,i) -> (ix,patch i)
          DropRow ix -> (ix,[])
      mod_key :: Non.NonEmpty (Binary (FTB a))
      mod_key = Non.fromList $ Binary . fmap create <$> justError ("no index: " ++ show tm) (nonEmpty pidx)
  isoTable = undefined

ix i d = justError ("no field " ++ show (i,d)) $ indexField (IProd Nothing i) d

class DecodeShowable a where
  decodeS :: Showable -> a
  encodeS :: a -> Showable
  isoS :: SIso KPrim Showable a

instance  DecodeShowable Bool where
  decodeS (SBoolean i) =  i
  encodeS i = SBoolean  i
  isoS = SIso PBoolean encodeS decodeS


instance  DecodeShowable BS.ByteString  where
  decodeS (SBinary i) =  i
  encodeS i = SBinary i
  isoS = SIso PBinary encodeS decodeS


instance  DecodeShowable BSL.ByteString  where
  decodeS (SBinary i) = BSL.fromStrict i
  encodeS i = SBinary (BSL.toStrict i)
  isoS = SIso PBinary encodeS decodeS


instance B.Binary a => DecodeShowable (Binary a) where
  decodeS (SBinary i) = Binary $ B.decode (BSL.fromStrict i)
  encodeS (Binary i) = SBinary (BSL.toStrict $ B.encode i)
  isoS = SIso PBinary encodeS decodeS

instance DecodeShowable Int where
  decodeS (SNumeric i) = i
  encodeS = SNumeric
  isoS = SIso (PInt 8) encodeS decodeS

instance DecodeShowable Double where
  decodeS (SDouble i) = i
  encodeS = SDouble
  isoS = SIso PDouble encodeS decodeS

instance DecodeShowable Text where
  decodeS (SText i) = i
  encodeS = SText
  isoS = SIso PText encodeS decodeS

instance DecodeShowable UTCTime where
  decodeS (STime (STimestamp i)) = i
  encodeS i = STime (STimestamp i)
  isoS = SIso (PTime (PTimestamp Nothing) ) encodeS decodeS

instance DecodeShowable PrePlugins where
  encodeS i  = SHDynamic (HDynamic  $toDyn i)
  decodeS (SHDynamic (HDynamic i)) = justError "invalid plugin code" $ fromDynamic i
  isoS = SIso PDynamic  encodeS decodeS

unBinary (Binary i) = i

att :: (Functor f, DecodeTB1 f, DecodeShowable a) => TB k Showable -> f a
att (Attr i j) = decodeS <$> decFTB j

itt :: (Functor f, DecodeTB1 f, DecodeTable a) => TB Text Showable -> f a
itt (IT i j) = decodeT <$> decFTB j
