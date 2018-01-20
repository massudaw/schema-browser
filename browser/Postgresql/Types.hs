{-# LANGUAGE BinaryLiterals,FlexibleContexts #-}
module Postgresql.Types where

import Types
import Types.Inference
import Data.Monoid
import Data.Tuple
import Data.Bits
import qualified Data.Vector as V
import Data.Int
import Data.Word
import qualified NonEmpty as Non
import Data.Time
import qualified Data.HashMap.Strict as HM
import Data.Map (Map)
import qualified Data.Map as M
import qualified Data.Foldable as F
import Control.Applicative
import Data.Text(Text,unpack)
import Control.Monad
import Debug.Trace
import Data.Maybe
import GHC.Stack
import Data.Word

type PrimType = KType (Prim KPrim (Text,Text))

type PGType = (Text,Text,Maybe Word32)

type PGRecord = (Text,Text)

type PGKey = FKey (KType PGPrim )

type PGPrim =  Prim PGType PGRecord

-- This module implement a rule system  that converts general higher order datatypes  to backend primitive ones
-- it assembles a isomorphism between the two types
-- Conversion rules need to converge so that we have only one possible conversion

preconversion' a i =  join $ (\t -> M.lookup (i,t) a ) <$> (flip M.lookup $ M.fromList $ M.keys a) i

preconversion
  :: KType (Prim KPrim (Text, Text))
     -> Maybe
          (FTB Showable -> FTB Showable, FTB Showable -> FTB Showable)
preconversion  =  preconversion' postgresLiftPrimConv

preunconversion i =  join $ (\t -> M.lookup (t,i) postgresLiftPrimConv) <$> ktypeUnLift  i

conversion i = fromMaybe (id , id) $ preconversion i

topconversion
  :: (Alternative f, Show t, Show t1) =>
     (KType t2 -> f (FTB t1 -> FTB a1, FTB t -> FTB a))
     -> KType t2 -> f (FTB t1 -> FTB a1, FTB t -> FTB a)
topconversion f (Primitive v a) = go v
  where
    go v = case v of
      KArray :n ->  f (Primitive v a) <|> fmap lifa (go  n )
      KInterval :n ->  f (Primitive v a) <|> fmap lifi (go n )
      KDelayed :n -> f (Primitive v a) <|> fmap lifd (go  n )
      KSerial :n -> f (Primitive v a) <|> fmap lifd (go  n )
      KOptional :n -> f (Primitive v a) <|> fmap lifd (go  n )
      [] ->  f (Primitive [] a)
    mapd a (LeftTB1 i) = LeftTB1 (fmap a i)
    mapd _ b =errorWithStackTrace (show (b))
    lifd (a,b) = (mapd a , mapd b)
    map a (IntervalTB1 i) = IntervalTB1 (fmap a i)
    map a  b =errorWithStackTrace (show (b))
    lifi (a,b) = (map a , map b)
    mapa a (ArrayTB1 i) = ArrayTB1 (fmap a i)
    mapa a  b =errorWithStackTrace (show (b))
    lifa (a,b) = (mapa a , mapa b)

denormConversions l = M.fromList $ fmap go (M.toList l)
  where
    go ((k,o),(l,f)) =
      case liftA2 (,) (ktypeRec (flip M.lookup  (M.fromList $ M.keys postgresLiftPrimConv')) o ) (topconversion (preconversion' postgresLiftPrimConv') o) of
          Just (i,(a,b)) ->  go ((k,i),(a.l,f.b))
          Nothing -> ((k,o),(l,f))

postgresLiftPrimConv = denormConversions postgresLiftPrimConv'

postgresLiftPrimConv' :: Map (KType (Prim KPrim (Text,Text)),KType (Prim KPrim (Text,Text)))  ( FTB  Showable -> FTB Showable , FTB Showable -> FTB Showable )
postgresLiftPrimConv' =
  M.fromList [((Primitive [] (AtomicPrim (PGeom 3 $ PBounding )), (Primitive [KInterval] (AtomicPrim (PGeom 3 $ PPosition ))) )
               , ((\(TB1 (SGeo (SBounding (Bounding i)) )) -> IntervalTB1 (fmap   (pos ) i)  )
                 , (\(IntervalTB1 i) -> TB1 $ SGeo $ SBounding $ Bounding $ (fmap (\(TB1 (SGeo (SPosition i))) -> i)) i) ))

             ,((Primitive [] (AtomicPrim (PGeom 2 $ PBounding )), (Primitive [KInterval] (AtomicPrim (PGeom 2 $ PPosition ))) )
                 , ((\(TB1 (SGeo (SBounding (Bounding i)) )) -> IntervalTB1 (fmap   (pos ) i)  )
                   , (\(IntervalTB1 i) -> TB1 $ SGeo $ SBounding $ Bounding $ (fmap (\(TB1 (SGeo (SPosition i))) -> i)) i) ))

             ,((Primitive [] (AtomicPrim (PGeom 2 $ PLineString )), (Primitive [KArray] (AtomicPrim (PGeom 2 $ PPosition ))) )
                 , ((\(TB1 (SGeo (SLineString (LineString i)) )) -> ArrayTB1 (Non.fromList $ F.toList  $ fmap   (pos ) i))
                   , (\(ArrayTB1 i) -> TB1 $ SGeo $ SLineString $ LineString $ V.fromList  $ F.toList $ (fmap (\(TB1 (SGeo (SPosition i))) -> i)) i) ))

             ,((Primitive [] (AtomicPrim (PGeom 2 $ PPolygon )), (Primitive [KArray] (AtomicPrim (PGeom 2 $ PLineString ))) )
                 , ((\(TB1 (SGeo (SPolygon i j ))) -> ArrayTB1 (Non.fromList $ F.toList  $ fmap   (TB1. SGeo .SLineString) (i:j)))
                   , (\(ArrayTB1 i) -> TB1 $ (\(i:j) -> SGeo $ SPolygon i j) $ F.toList $ (fmap (\(TB1 (SGeo (SLineString i))) -> i)) i)))

             ,((Primitive [] (AtomicPrim (PGeom 2 $ (MultiGeom (PPolygon )))), (Primitive [KArray] (AtomicPrim (PGeom 2 $ PPolygon ))))
                 , ((\(TB1 (SGeo (SMultiGeom i  ))) -> ArrayTB1 (Non.fromList $ F.toList  $ fmap   (TB1 . SGeo) i))
                   , (\(ArrayTB1 i) -> TB1 $ SGeo $ SMultiGeom   $  F.toList $  fmap ((\(SGeo i ) -> i). unTB1) i) ))

             ,((Primitive [] (AtomicPrim (PGeom 3 $ PLineString )), (Primitive [KArray] (AtomicPrim (PGeom 3 $ PPosition ))) )
                 , ((\(TB1 (SGeo (SLineString (LineString i)) )) -> ArrayTB1 (Non.fromList $ F.toList  $ fmap   (pos ) i))
                   , (\(ArrayTB1 i) -> TB1 $ SGeo $ SLineString $ LineString $ V.fromList  $ F.toList $ (fmap (\(TB1 (SGeo (SPosition i))) -> i)) i) ))]

postgresLiftPrim :: Map (KType (Prim KPrim (Text,Text))) (KType (Prim KPrim (Text,Text)))
postgresLiftPrim = M.fromList $ M.keys postgresLiftPrimConv
postgresLiftPrim' = M.fromList $ M.keys postgresLiftPrimConv'

postgresUnLiftPrim :: Map (KType (Prim KPrim (Text,Text))) (KType (Prim KPrim (Text,Text)))
postgresUnLiftPrim = M.fromList $ fmap swap $ M.keys postgresLiftPrimConv
postgresUnLiftPrim' = M.fromList $ fmap swap $ M.keys postgresLiftPrimConv'


rewriteOp :: M.Map (PrimType ,BinaryOperator , PrimType ) Text
rewriteOp = M.fromList [
      ((Primitive [] (AtomicPrim (PGeom 2 $ PBounding )),  AnyOp (Flip Contains) ,Primitive[]  (AtomicPrim (PGeom 2 $ PLineString ))) , "&&"),
      ((Primitive [] (AtomicPrim (PGeom 3 $ PBounding )),  AnyOp (Flip Contains) ,Primitive[]  (AtomicPrim (PGeom 3 $ PLineString ))) , "&&"),
      ((Primitive [] (AtomicPrim (PGeom 2 $ PBounding )),  AnyOp (AnyOp (Flip Contains)) ,Primitive[]  (AtomicPrim (PGeom 2 $ PPolygon ))) , "&&"),
      ((Primitive [] (AtomicPrim (PGeom 2 $ PBounding )),  AnyOp (AnyOp(AnyOp (Flip Contains))) ,Primitive []  (AtomicPrim (PGeom 2 $ MultiGeom $ PPolygon ))) , "&&"),
      ((Primitive [] (AtomicPrim (PGeom 2 $ PBounding )),  (Flip Contains) ,Primitive [] (AtomicPrim (PGeom 2 $ PPosition ))) , "&&"),
      ((Primitive [] (AtomicPrim (PGeom 3 $ PBounding )),  (Flip Contains) ,Primitive [] (AtomicPrim (PGeom 3 $ PPosition ))) , "&&")]

postgresPrimTyp :: HM.HashMap Text (Word32 -> KPrim)
postgresPrimTyp = HM.fromList
    [("dimensional",decoderDimensional)
    ,("geometry",decoderGeometry)]


decoderGeometry :: Word32 -> KPrim
decoderGeometry typmod  = PGeom  z $ case ty of
                                       0 -> undefined -- "Unknown",
                                       1 -> PPosition
                                       2 -> PLineString
                                       3 -> PPolygon
                                       4 -> MultiGeom   PPosition
                                       5 -> MultiGeom PLineString
                                       6 -> MultiGeom PPolygon
   where z= if (typmod .&. 0x00000002) `shiftR` 1 == 0b1 then 3 else 2
         ty = (typmod .&. 0x000000FC)`shiftR` 2

decoderDimensional :: Word32 -> KPrim
decoderDimensional i = PDimensional (take 7)  (take 6,take 5 , take 4 ,take 3 ,take 2 ,take 1 ,take 0 )
  where
    take = fromIntegral . flip take4 i

take4 :: Int -> Word32 -> Int8
take4 ix i  =  (if testBit i (o + 3)  then 0b11111000 else 0)   .|. (  fromIntegral ((i `shiftR` o)  .&. 0b111))
  where o = ix*4

postgresPrim :: HM.HashMap Text KPrim
postgresPrim =
  HM.fromList $
  [("character varying",PText)
  ,("name",PText)
  ,("character_data",PText)
  ,("varchar",PText)
  ,("text",PText)
  ,("address",PAddress)
  ,("character",PText)
  ,("char",PText)
  ,("bpchar",PText)
  ,("sql_identifier" , PText)
  ,("base64url",PText)
  ,("bytea",PBinary)
  ,("mp4",PMime "video/mp4")
  ,("pdf",PMime "application/pdf")
  ,("ofx",PMime "application/x-ofx")
  ,("gpx",PMime "application/gpx+xml")
  ,("xml",PMime "text/xml")
  ,("jpg",PMime "image/jpg")
  ,("png",PMime "image/png")
  ,("email",PMime "text/plain")
  ,("html",PMime "text/html")
  ,("dynamic",PDynamic)
  ,("double precision",PDouble)
  ,("numeric",PDouble)
  ,("float8",PDouble)
  ,("int8",PInt 8)
  ,("int4",PInt 4)
  ,("int2",PInt 2)
  ,("oid",PText)
  ,("cid",PText)
  ,("xid",PText)
  ,("tid",PText)
  ,("cnpj",PCnpj)
  ,("cpf",PCpf)
  ,("int8",PInt 8)
  ,("integer",PInt 4)
  ,("bigint",PInt 8)
  ,("cardinal_number",PInt 2)
  ,("smallint",PInt 2)
  ,("boolean",PBoolean)
  ,("bool",PBoolean)
  ,("color",PColor)]
   ++( fmap PTime <$>
  [("timestamptz",PTimestamp Nothing )
  ,("timestamp",PTimestamp (Just utc))
  ,("timestamp with time zone",PTimestamp Nothing )
  ,("timestamp without time zone",PTimestamp (Just utc))
  ,("interval",PInterval)
  ,("date" ,PDate)
  ,("time",PDayTime)
  ,("time with time zone" ,PDayTime)
  ,("time without time zone" ,PDayTime)])
  ++ [("box3d",PGeom 3 $ PBounding )
  ,("box2d",PGeom 2 $ PBounding )
  ]

ktypeUnLift :: KType (Prim KPrim (Text,Text)) -> Maybe (KType (Prim KPrim (Text,Text)))
ktypeUnLift i = M.lookup i postgresUnLiftPrim

ktypeLift :: KType (Prim KPrim (Text,Text)) -> Maybe (KType (Prim KPrim (Text,Text)))
ktypeLift i = M.lookup i postgresLiftPrim

inlineType (Primitive k (RecordPrim (s,t) )) = Just (" :: " <>s <> "." <> t <> foldMap ktype k )
  where
    ktype KArray  =  "[]"
    ktype KOptional =  ""
inlineType _ = Nothing


renderType (Primitive (KInterval :xs) t ) =
  case t of
    (AtomicPrim (PInt i)) ->  case i of
      4 -> "int4range"
      8 -> "int8range"
    (AtomicPrim (PTime (PDate))) -> "daterange"
    (AtomicPrim (PTime (PTimestamp i))) -> case i of
      Just i -> "tsrange"
      Nothing -> "tstzrange"
    (AtomicPrim (PGeom ix i)) ->
       case ix of
            2 ->  "box2d"
            3 ->  "box3d"

    (AtomicPrim PDouble) -> "floatrange"
    i -> Nothing
renderType (Primitive [] (RecordPrim (s,t)) ) = Just $ s <> "." <> t
renderType (Primitive [] (AtomicPrim t) ) =
  case t  of
    PBinary -> "bytea"
    PDynamic -> "bytea"
    PDouble -> "double precision"
    PDimensional _ _ -> "dimensional"
    PText -> "character varying"
    PInt v -> case v of
      2 -> "smallint"
      4 -> "integer"
      8 -> "bigint"
      v -> errorWithStackTrace ("no index" ++ show   v)
    PTime i -> case i of
      PDate -> "date"
      PTimestamp v -> case v of
        Just i -> "timestamp without time zone"
        Nothing -> "timestamp with time zone"
    i -> Nothing
renderType (Primitive (KArray :xs)i) = (<>"[]") <$> renderType (Primitive xs i)
renderType (Primitive (KOptional :xs)i) = renderType (Primitive xs i)
renderType (Primitive (KSerial :xs)i) = renderType (Primitive xs i)
renderType (Primitive (KDelayed :xs)i) = renderType (Primitive xs i)



-- inferParamType e i |traceShow ("inferParam"e,i) False = undefined
inferParamType op i = maybe "" (":: " <>) $ renderType $  inferOperatorType op i


ktypeRec f v@(Primitive (t:xs) i) =   f v <|> fmap (addToken t) (ktypeRec f (Primitive xs i))
  where
    addToken t (Primitive i a) = Primitive (t:i) a
ktypeRec f v@(Primitive []  i ) = f v


mapKeyType :: FKey (KType PGPrim) -> FKey (KType (Prim KPrim (Text,Text)))
mapKeyType  = fmap mapKType
mapKType :: KType PGPrim -> KType CorePrim
mapKType i = fromMaybe (fmap textToPrim i) $ ktypeRec ktypeLift (fmap textToPrim i)

textToPrim :: Prim PGType (Text,Text) -> Prim KPrim (Text,Text)
textToPrim (AtomicPrim (s,i,tymod)) = case  HM.lookup i  postgresPrim of
  Just k -> AtomicPrim k -- $ fromMaybe k (M.lookup k (M.fromList postgresLiftPrim ))
  Nothing -> case tymod of
               Just ty -> case HM.lookup i postgresPrimTyp of
                            Just i -> AtomicPrim $ i ty
                            Nothing -> error $ "no conversion for type " <> (show i)
               Nothing -> error $ "no conversion for type " <> (show i)
textToPrim (RecordPrim i) =  (RecordPrim i)


