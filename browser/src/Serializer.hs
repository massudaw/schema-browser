{-# LANGUAGE DefaultSignatures,TypeFamilies, ScopedTypeVariables, DeriveFunctor,
DeriveGeneric,FlexibleContexts,FlexibleInstances,TypeOperators #-}

module Serializer where

import qualified Data.Binary as B
import qualified Data.ByteString.Char8 as BS
import qualified Data.Set as S
import Data.Monoid -- hiding((<>))
import qualified Data.Semigroup as S
import Control.Arrow
import Data.Interval (intersection)
import Data.Functor.Contravariant.Divisible
import Control.Applicative
import Query
import Data.Maybe
import Control.Monad.Reader
import Control.Monad.Writer  hiding((<>))
import Data.Functor.Apply
import Data.Functor.Compose
import Data.Functor.Identity
import Data.Dynamic
import qualified Data.Foldable as F
import qualified Data.ByteString.Lazy as BSL
import qualified Data.Interval as Interval
import Data.Time
import Control.Category
import qualified Data.Map as M
import Database.PostgreSQL.Simple
import qualified NonEmpty as Non
import RuntimeTypes
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


class DecodeTB1 f where
  decFTB :: Ord a => FTB a -> f a
  decFTB = decodeIso isoFTB
  encFTB :: Ord a=> f a -> FTB a
  encFTB = encodeIso isoFTB
  isoFTB :: Ord a=> SIso [KTypePrim]  (FTB a)  (f a)

instance DecodeTB1 Identity where
  decFTB (TB1 i) = Identity i
  encFTB (Identity i) = TB1 i
  isoFTB = SIso [] (tell . encFTB) decFTB

instance DecodeTB1 Only where
  decFTB (TB1 i) = Only i
  encFTB (Only i) = TB1 i
  isoFTB = SIso [] (tell . encFTB)  decFTB

instance DecodeTB1 [] where
  isoFTB = SIso [KOptional,KArray] (tell .encFTB) decFTB
    where
      decFTB (LeftTB1 i ) = maybe [] decFTB i
      decFTB (ArrayTB1 i ) = Non.toList (unTB1 <$> i)
      encFTB l = LeftTB1 $ (\i -> ArrayTB1 (TB1 <$> i)) <$> Non.nonEmpty l

instance DecodeTB1 Interval.Interval where
  decFTB (IntervalTB1 i) = fmap unTB1 i
  encFTB i = IntervalTB1 $ fmap TB1 i
  isoFTB = SIso [KInterval] (tell . encFTB) decFTB

instance DecodeTB1 Non.NonEmpty  where
  decFTB (ArrayTB1 i) = fmap unTB1 i
  encFTB i = ArrayTB1 $ fmap TB1 i
  isoFTB = SIso [KArray] (tell . encFTB) decFTB

instance DecodeTB1 Maybe  where
  isoFTB = SIso [KOptional] (tell . encFTB) decFTB
    where
      decFTB (LeftTB1 i) =  fmap unTB1 i
      encFTB i = LeftTB1 $ fmap TB1  i

unjoin (TB1 i) = TB1 (TB1 i)
unjoin (LeftTB1 i ) = LeftTB1 $ fmap TB1 i
unjoin (ArrayTB1 i ) = ArrayTB1 $ fmap TB1 i
unjoin (IntervalTB1  i ) = IntervalTB1 $ fmap TB1 i

instance (DecodeTB1 f , Functor f,DecodeTB1 g ) => DecodeTB1 (Compose f g) where
  isoFTB = SIso (l1 <> l) (tell . joinFTB . (snd . runWriter) . enc .  fmap ((snd . runWriter) .enc1) . getCompose) (Compose . fmap dec1. dec . unjoin)
    where
      SIso l enc dec = isoFTB
      SIso l1 enc1 dec1 = isoFTB

instance DecodeTB1 FTB where
  isoFTB = SIso [] tell id

instance DecodeTB1 Union where
  isoFTB = itotal $ isplit (IsoArrow build destroy)
      (compose <$$> isoFTB)  (compose <$$> isoFTB)
    where
      build (Left i) = Many i
      build (Right i) = ISum i
      destroy (Many i) = (Left i)
      destroy (ISum i) = (Right i)


data SIso s b  c
  = SIso
  { stoken :: s
  , encodeIso' :: c  ->Writer b ()
  , decodeIso :: b -> c
  }

instance Ord a => Monoid (FTB a) where
  mempty = LeftTB1 Nothing
  mappend (LeftTB1 i ) (LeftTB1 j) =  LeftTB1 $ i <> j
  mappend (ArrayTB1 i ) (ArrayTB1 j) =  ArrayTB1 $ i S.<> j
  mappend (IntervalTB1 i ) (IntervalTB1 j) =  IntervalTB1 $ intersection i j
  mappend (TB1 i ) (TB1 j) =  TB1 j


encodeIso :: Monoid b => SIso s b a -> a  -> b
encodeIso l i =  snd $ runWriter  (encodeIso' l $ i )

infixr 5 <$$>

(<$$>) :: IsoProfunctor f => (a |-> b) -> f a -> f b
(<$$>)  = isoMap


decodeT :: DecodeTable a=> TBData Text Showable -> a
decodeT = decodeIso isoTable

encodeT :: DecodeTable a => a -> TBData Text Showable
encodeT = encodeIso isoTable

class DecodeTable a where
  isoTable :: SIso (Union (Reference Text)) (TBData Text Showable) a


class IsoProfunctor f => IsoApplicative f where
  ipure :: f a
  iassoc :: ((a,b) |-> c) -> f a  -> f b -> f c

class IsoProfunctor f => IsoDivisible f where
  itotal :: f (Maybe a) -> f a
  isplit :: (Either a b |-> c) -> f (Maybe a)  -> f (Maybe b) -> f (Maybe c)

instance (Monoid j ,Monoid i) => IsoDivisible  (SIso i j) where
  itotal = isoMap (IsoArrow (justError "partial output") Just )
  isplit (IsoArrow aenc adec) fa fb =  SIso (stoken fa  `mappend` stoken fb) (void . traverse (either (encodeIso'  fa.Just ) (encodeIso' fb . Just) ). fmap adec) (\i -> fmap aenc $ (Left <$> (decodeIso fa $ i)) <|> (Right <$> (decodeIso fb $ i)) )
    where
          pR (Right i) = Just i
          pR i = Nothing
          pL (Left i) = Just i
          pL i = Nothing


type a :|:  b = Either a b

isplit3 :: IsoDivisible f => ((a :|: b :|: c) |-> d) -> f (Maybe a)  -> f (Maybe b) -> f (Maybe c) -> f (Maybe d)
isplit3 (IsoArrow f g) a b c = isplit (IsoArrow f g )  (isplit id a b) c

isplit4 :: IsoDivisible f => ((a :|: b :|: c :|: d ) |-> e) -> f (Maybe a)  -> f (Maybe b) -> f (Maybe c) -> f (Maybe d) -> f (Maybe e)
isplit4 (IsoArrow f g) a b c d = isplit (IsoArrow f g )  (isplit3 id a b c) d

isplit5 :: IsoDivisible f => ((a :|: b :|: c :|: d :|: e ) |-> g) -> f (Maybe a)  -> f (Maybe b) -> f (Maybe c) -> f (Maybe d) -> f (Maybe e) -> f (Maybe g)
isplit5 (IsoArrow f g) a b c d e = isplit (IsoArrow f g )  (isplit4 id a b c d) e

iassoc3 :: IsoApplicative f => ((a,b,c) |-> d) -> f a  -> f b -> f c -> f d
iassoc3 (IsoArrow f g)  a b c = iassoc   (IsoArrow f2 g2) a (iassoc  id  b c)
  where f2 = (\(i,(j,k)) -> f (i,j,k) )
        g2 = (\(i,j,k) ->  (i,(j,k))) . g

iassoc4 :: IsoApplicative f =>((a,b,c,d) |-> e) -> f a  -> f b -> f c -> f d -> f e
iassoc4 (IsoArrow f g)  a b c d= iassoc   (IsoArrow f2 g2) (iassoc id a b) (iassoc  id  c d)
  where f2 = (\((i,j),(k,l)) -> f (i,j,k,l))
        g2 = (\(i,j,k,l) ->  ((i,j),(k,l))) . g

iassoc10 :: IsoApplicative z =>((a,b,c,d,e,f,g,h,i,j) |-> k) -> z a  -> z b -> z c -> z d -> z e -> z f -> z g ->z h -> z i -> z j  ->z k
iassoc10 (IsoArrow f1 g1)  a b c d e f g h i j  = iassoc   (IsoArrow f2 g2) (iassoc5 id a b c d e ) (iassoc5  id  f g h i j)
  where f2 = (\((i,j,k,l,m),(n,o,p,q,r)) -> f1 (i,j,k,l,m,n,o,p,q,r))
        g2 = (\(i,j,k,l,m,n,o,p,q,r) ->  ((i,j,k,l,m),(n,o,p,q,r))) . g1

iassoc11 :: IsoApplicative z =>((a,b,c,d,e,f,g,h,i,j,k) |-> l) -> z a  -> z b -> z c -> z d -> z e -> z f -> z g ->z h -> z i -> z j  ->z k -> z l
iassoc11 (IsoArrow f1 g1)  a b c d e f g h i j k = iassoc   (IsoArrow f2 g2) (iassoc5 id a b c d e ) (iassoc6  id  f g h i j k)
  where f2 = (\((i,j,k,l,m),(n,o,p,q,r,s)) -> f1 (i,j,k,l,m,n,o,p,q,r,s))
        g2 = (\(i,j,k,l,m,n,o,p,q,r,s) ->  ((i,j,k,l,m),(n,o,p,q,r,s))) . g1

iassoc5 :: IsoApplicative f =>((a,b,c,d,e) |-> g) -> f a  -> f b -> f c -> f d -> f e -> f g
iassoc5 (IsoArrow f g)  a b c d  e= iassoc   (IsoArrow f2 g2) (iassoc id a b) (iassoc3  id  c d e)
  where f2 = (\((i,j),(k,l,m)) -> f (i,j,k,l,m))
        g2 = (\(i,j,k,l,m) ->  ((i,j),(k,l,m))) . g

iassoc6 :: IsoApplicative z =>((a,b,c,d,e,f) |-> g) -> z a  -> z b -> z c -> z d -> z e -> z f -> z g
iassoc6 (IsoArrow f1 g1)  a b c d  e f = iassoc  (IsoArrow f2 g2) (iassoc id a b) (iassoc4  id  c d e f)
  where f2 = (\((i,j),(k,l,m,n)) -> f1 (i,j,k,l,m,n))
        g2 = (\(i,j,k,l,m,n) ->  ((i,j),(k,l,m,n))) . g1


instance (Monoid x , Monoid v) => IsoApplicative (SIso x v) where
  iassoc (IsoArrow f g) pqf pqa = SIso (stoken pqf `mappend` stoken pqa) qb pb
    where
      pb =  liftA2 (curry f ) (decodeIso pqf) (decodeIso pqa)
      qb = (\(i,j) -> liftA2 mappend (encodeIso' pqf $ i ) (encodeIso' pqa $ j ) ) . g


class IsoProfunctor f  where
  isoMap :: (a |-> c ) -> f a -> f c

instance IsoProfunctor (IsoArrow a ) where
  isoMap  = (.)

instance IsoProfunctor (SIso i l ) where
  isoMap (IsoArrow f  g) (SIso l i j) = SIso l (i . g ) (f . j )


data Reference k
  = AttrRef (KType KPrim) k
  | InlineTable (KType Text) k (Union (Reference k))
  | JoinTable  [Rel k] (Union (Reference k))
  deriving(Eq,Ord,Show)


prim :: (Show k ,Ord k,Functor f, DecodeShowable a, DecodeTB1 f) =>
  k -> SIso (Union (Reference k))  (TBData k Showable) (f a)
prim ix = SIso (Many [AttrRef (Primitive l kp ) ix])  (tell . mk. (execWriter . fs) . fmap (onlyLast . execWriter . fsp) ) (fmap (bsp. Last. Just) . bs . lk)
    where i@(SIso l fs bs) = isoFTB
          j@(SIso kp fsp bsp) = isoS
          lk =  _tbattr . justError ("no attr" ++ show (S.singleton $ Inline ix)) . kvLookup (S.singleton $ Inline ix)
          mk = kvSingleton . Attr ix

nestJoin :: (Functor f, DecodeTB1 f) =>
  [Rel Text] -> SIso (Union (Reference Text)) (TBData Text Showable)  a ->  SIso (Union (Reference Text ))  (TBData Text Showable) (f a)
nestJoin ix nested = SIso (Many [JoinTable ix kp])  (tell . mk. (execWriter . fs) . fmap (execWriter . fsp) ) (fmap bsp . bs . lk)
    where i@(SIso l fs bs) = isoFTB
          j@(SIso kp fsp bsp) = nested
          keyset = S.fromList ix
          lk v =  _fkttable . justError ("no attr: " ++ show (keyset ,v)). kvLookup  keyset $ v
          mk = kvSingleton . (\a -> FKT (kvlist $ reflectOp a <$> ix ) ix a)
          reflectOp a r@(Rel (Inline i) op l) =  Attr i  $ joinFTB (_tbattr . justError ("no reflect attr" ++ show (r,a)). kvLookup (S.singleton (Inline l)) <$> a)


nestWith :: (Functor f, DecodeTB1 f) =>
  Text -> SIso (Union (Reference Text)) (TBData Text Showable)  a ->  SIso (Union (Reference Text ))  (TBData Text Showable) (f a)
nestWith ix nested = SIso (Many [InlineTable (Primitive l "") ix (kp)])  (tell . mk. (execWriter . fs) . fmap (execWriter . fsp) ) (fmap bsp . bs . lk)
    where i@(SIso l fs bs) = isoFTB
          j@(SIso kp fsp bsp) = nested
          lk =  _fkttable . justError ("no attr: " ++ show (S.singleton $ Inline ix)). kvLookup (S.singleton $ Inline ix)
          mk = kvSingleton . IT ix

nest :: (Functor f, DecodeTable a, DecodeTB1 f) =>
  Text -> SIso (Union (Reference Text ))  (TBData Text Showable) (f a)
nest ix = nestWith ix isoTable

traverseIso  (SIso g k l) (SIso f i j)=  SIso (f,g) (tell . (execWriter . i) . fmap (execWriter . k)) (fmap l . j)



instance Category IsoArrow where
  id = IsoArrow id id
  (.)  (IsoArrow f g ) (IsoArrow l m )= IsoArrow (  f . l ) (  m . g )

isoArrow (i,j) = IsoArrow i j


only = (IsoArrow unOnly Only)
  where
    unOnly :: Only a -> a
    unOnly (Only i) = i
identity = (IsoArrow runIdentity  Identity)

dynamic :: Typeable a => IsoArrow Dynamic a
dynamic = (IsoArrow   ( justError "cant cast" . fromDynamic   )) (toDyn )

compose = IsoArrow getCompose Compose

mapIso (IsoArrow i j) = IsoArrow (fmap i ) (fmap j)

binary = (IsoArrow unBinary  Binary)
  where unBinary (Binary i) = i

nonempty = (IsoArrow Non.toList Non.fromList)

type IsoTable a = SIso (Union (Reference Text)) (TBData Text Showable)  a

instance DecodeTable Plugins where
  isoTable = iassoc id (identity <$$> prim "ref") (identity <$$> prim "plugin")

mapField (SIso p  i j ) (SIso (Many [(AttrRef (Primitive k ki) v)]) a b ) = SIso (Many . pure $ (AttrRef (Primitive (k <> p) ki) v)) (tell . (execWriter . a) . (execWriter . i)) (j .  b)
mapField (SIso p  i j ) (SIso (Many [(InlineTable (Primitive k ki) v l )]) a b ) = SIso (Many . pure $(InlineTable (Primitive (k <> p) ki) v l )) (tell . (execWriter  .a). (execWriter . i)) (j .  b)

mapIsoArrow (IsoArrow f g ) = IsoArrow (fmap f ) (fmap g)


instance DecodeShowable (Rel Text) where
  isoS = isoMap (IsoArrow Inline _relOrigin ) isoS

instance DecodeTable (Access Text) where
  isoTable = itotal $ isplit (IsoArrow build destroy)
      (nestWith "nested" (iassoc id (prim "ref") ( nest "nest"))) (prim "iprod" )
    where
      build (Right i ) = IProd Nothing i
      build (Left (i,j) )  = Nested i j
      destroy  (IProd _ i ) = Right i
      destroy  (Nested i j) = Left (i,j)

rowPatchArr = IsoArrow (uncurry rebuild) (\i -> (index i ,content i ))
instance DecodeTable (RevertModification (Text, Text) (RowPatch Text Showable )) where
  isoTable = iassoc  (IsoArrow (\(a,b) -> RevertModification a b) (\(RevertModification a b ) -> (a,b)))
      (identity <$$> nestJoin [Rel "modification_id" Equals "modification_id"] isoTable)
      (iassoc rowPatchArr
          (identity <$$> prim "data_index")
          (identity<$$> prim "modification_data"))

instance DecodeTable (TableModificationK (Text, Text) (RowPatch Text Showable )) where
  isoTable = iassoc5  (IsoArrow (\(a,b,c,d,e) -> TableModification a b c d e) (\(TableModification a b c d e ) -> (a,b,c,d,e)))
      (prim "modification_id")
      (identity <$$> prim "modification_time")
      (identity <$$> prim "user_name")
      (iassoc id
          (identity <$$> prim "schema_name")
          (identity <$$> prim "table_name"))
      (iassoc rowPatchArr
          (identity <$$> prim "data_index")
          (identity<$$> prim "modification_data"))

class DecodeShowable a where
  decodeS :: Showable -> a
  encodeS :: a -> Showable
  isoS :: SIso KPrim (Last Showable) a


onlyLast :: Last a -> a
onlyLast = justError "no element" . getLast

instance DecodeShowable Showable where
  isoS = SIso (PDynamic "showable") (tell . pure ) onlyLast

instance  DecodeShowable Bool where
  decodeS (SBoolean i) =  i
  encodeS i = SBoolean  i
  isoS = SIso PBoolean (tell . pure .encodeS ) (decodeS. onlyLast )

instance  DecodeShowable BS.ByteString  where
  decodeS (SBinary i) =  i
  encodeS i = SBinary i
  isoS = SIso PBinary (tell . pure .encodeS ) (decodeS. onlyLast )

instance  DecodeShowable BSL.ByteString  where
  decodeS (SBinary i) = BSL.fromStrict i
  encodeS i = SBinary (BSL.toStrict i)
  isoS = SIso PBinary (tell . pure .encodeS ) (decodeS. onlyLast )

instance B.Binary a => DecodeShowable (Binary a) where
  decodeS (SBinary i) = Binary $ B.decode (BSL.fromStrict i)
  encodeS (Binary i) = SBinary (BSL.toStrict $ B.encode i)
  isoS = SIso PBinary (tell . pure .encodeS ) (decodeS. onlyLast )

instance DecodeShowable Int where
  decodeS (SNumeric i) = i
  encodeS = SNumeric
  isoS = SIso (PInt 8) (tell . pure .encodeS ) (decodeS. onlyLast )

instance DecodeShowable Double where
  decodeS (SDouble i) = i
  encodeS = SDouble
  isoS = SIso PDouble  (tell . pure .encodeS ) (decodeS. onlyLast )

instance DecodeShowable Text where
  decodeS (SText i) = i
  encodeS = SText
  isoS = SIso PText (tell . pure .encodeS ) (decodeS. onlyLast )

instance DecodeShowable UTCTime where
  decodeS (STime (STimestamp i)) = i
  encodeS i = STime (STimestamp i)
  isoS = SIso (PTime (PTimestamp Nothing) )(tell . pure .encodeS ) (decodeS. onlyLast )

instance DecodeShowable (FTB Showable)  where
  isoS = SIso (PDynamic "ftb_showable") (tell . pure .encodeS ) (decodeS. onlyLast )
    where
      encodeS i  = SDynamic (HDynamic  (toDyn i))
      decodeS (SDynamic (HDynamic i)) = justError "invalid plugin code" $ fromDynamic i


instance DecodeShowable [TBIndex Showable]  where
  isoS = SIso (PDynamic "row_index") (tell . pure . encodeS) (decodeS.onlyLast)
    where
      encodeS i  = SDynamic (HDynamic  (toDyn i))
      decodeS (SDynamic (HDynamic i)) = justError "invalid plugin code" $ fromDynamic i

instance DecodeShowable (RowOperation Text Showable) where
  isoS = SIso (PDynamic "row_operation") (tell . pure . encodeS) (decodeS.onlyLast)
    where
      encodeS i  = SDynamic (HDynamic  (toDyn i))
      decodeS (SDynamic (HDynamic i)) = justError "invalid plugin code" $ fromDynamic i


instance DecodeShowable PrePlugins where
  isoS = SIso (PDynamic "plugin") (tell . pure . encodeS) (decodeS.onlyLast)
    where
      encodeS i  = SDynamic (HDynamic  $toDyn i)
      decodeS (SDynamic (HDynamic i)) = justError "invalid plugin code" $ fromDynamic i

