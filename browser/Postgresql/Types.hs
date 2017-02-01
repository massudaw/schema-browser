{-# LANGUAGE FlexibleContexts #-}
module Postgresql.Types where

import Types
import Data.Tuple
import qualified Data.Vector as V
import qualified NonEmpty as Non
import Data.Time
import qualified Data.HashMap.Strict as HM
import Data.Map (Map)
import qualified Data.Map as M
import qualified Data.Foldable as F
import Control.Applicative
import Data.Text(Text)
import Control.Monad
import Debug.Trace
import Data.Maybe
import GHC.Stack

type PrimType = KType (Prim KPrim (Text,Text))


-- This module implement a rule system  that converts general higher order datatypes  to backend primitive ones
-- it assembles a isomorphism between the two types
-- Nested types need to be unambigous so that we have only one possible conversion


preconversion' a i =  join $ (\t -> M.lookup (i,t) a ) <$> (flip M.lookup $ M.fromList $ M.keys a) i
preconversion  =  preconversion' postgresLiftPrimConv

preunconversion i =  join $ (\t -> M.lookup (t,i) postgresLiftPrimConv) <$> ktypeUnLift  i

conversion i = fromMaybe (id , id) $ preconversion i



topconversion f v
  = case v of
    KArray n ->  f v <|> fmap lifa (topconversion f n )
    KInterval n ->  f v <|> fmap lifi (topconversion f n )
    KDelayed n -> f v <|> fmap lifd (topconversion f n )
    KSerial n -> f v <|> fmap lifd (topconversion f n )
    KOptional n -> f v <|> fmap lifd (topconversion f n )
    Primitive i ->  f v
  where
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
   M.fromList [((Primitive (AtomicPrim (PGeom $ PBounding 3)), KInterval (Primitive (AtomicPrim (PGeom $ PPosition 3))) )
               , ((\(TB1 (SGeo (SBounding (Bounding i)) )) -> IntervalTB1 (fmap   (pos ) i)  )
                 , (\(IntervalTB1 i) -> TB1 $ SGeo $ SBounding $ Bounding $ (fmap (\(TB1 (SGeo (SPosition i))) -> i)) i) ))

                ,((Primitive (AtomicPrim (PGeom $ PBounding 2)), KInterval (Primitive (AtomicPrim (PGeom $ PPosition 2))) )
                 , ((\(TB1 (SGeo (SBounding (Bounding i)) )) -> IntervalTB1 (fmap   (pos ) i)  )
                   , (\(IntervalTB1 i) -> TB1 $ SGeo $ SBounding $ Bounding $ (fmap (\(TB1 (SGeo (SPosition i))) -> i)) i) ))

                ,((Primitive (AtomicPrim (PGeom $ PLineString 2)), KArray (Primitive (AtomicPrim (PGeom $ PPosition 2))) )
                 , ((\(TB1 (SGeo (SLineString (LineString i)) )) -> ArrayTB1 (Non.fromList $ F.toList  $ fmap   (pos ) i))
                   , (\(ArrayTB1 i) -> TB1 $ SGeo $ SLineString $ LineString $ V.fromList  $ F.toList $ (fmap (\(TB1 (SGeo (SPosition i))) -> i)) i) ))

                ,((Primitive (AtomicPrim (PGeom $ (PPolygon 2))), KArray (Primitive (AtomicPrim (PGeom $ PLineString 2))) )
                 , ((\(TB1 (SGeo (SPolygon i j ))) -> ArrayTB1 (Non.fromList $ F.toList  $ fmap   (TB1. SGeo .SLineString) (i:j)))
                   , (\(ArrayTB1 i) -> TB1 $ (\(i:j) -> SGeo $ SPolygon i j) $ F.toList $ (fmap (\(TB1 (SGeo (SLineString i))) -> i)) i) ))

                ,((Primitive (AtomicPrim (PGeom $ (MultiGeom (PPolygon 2)))), KArray (Primitive (AtomicPrim (PGeom $ PPolygon 2))) )
                 , ((\(TB1 (SGeo (SMultiGeom i  ))) -> ArrayTB1 (Non.fromList $ F.toList  $ fmap   (TB1 . SGeo) i))
                   , (\(ArrayTB1 i) -> TB1 $ SGeo $ SMultiGeom   $  F.toList $  fmap ((\(SGeo i ) -> i). unTB1) i) ))

                ,((Primitive (AtomicPrim (PGeom $ PLineString 3)), KArray (Primitive (AtomicPrim (PGeom $ PPosition 3))) )
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
      ((Primitive (AtomicPrim (PGeom $ PBounding 2)),  AnyOp (Flip Contains) ,Primitive (AtomicPrim (PGeom $ PLineString 2))) , "&&"),
      ((Primitive (AtomicPrim (PGeom $ PBounding 3)),  AnyOp (Flip Contains) ,Primitive (AtomicPrim (PGeom $ PLineString 3))) , "&&"),
      ((Primitive (AtomicPrim (PGeom $ PBounding 2)),  AnyOp (AnyOp (Flip Contains)) ,Primitive (AtomicPrim (PGeom $ PPolygon 2))) , "&&"),
      ((Primitive (AtomicPrim (PGeom $ PBounding 2)),  AnyOp (AnyOp(AnyOp (Flip Contains))) ,Primitive (AtomicPrim (PGeom $ MultiGeom $ PPolygon 2))) , "&&"),
      ((Primitive (AtomicPrim (PGeom $ PBounding 2)),  (Flip Contains) ,Primitive (AtomicPrim (PGeom $ PPosition 2))) , "&&"),
      ((Primitive (AtomicPrim (PGeom $ PBounding 3)),  (Flip Contains) ,Primitive (AtomicPrim (PGeom $ PPosition 3))) , "&&")]


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
  ,("session",PSession)
  ,("bytea",PBinary)
  ,("mp4",PMime "video/mp4")
  ,("pdf",PMime "application/pdf")
  ,("ofx",PMime "application/x-ofx")
  ,("gpx",PMime "application/gpx+xml")
  ,("jpg",PMime "image/jpg")
  ,("png",PMime "image/png")
  ,("email",PMime "text/plain")
  ,("html",PMime "text/html")
  ,("dynamic",PDynamic)
  ,("double precision",PDouble)
  ,("numeric",PDouble)
  ,("float8",PDouble)
  ,("int4",PInt 4)
  ,("oid",PInt 4)
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
    ++ (fmap PGeom <$>
  [("POINT3",PPosition 3)
  ,("POINT2",PPosition 2)
  ,("POLYGON3",PPolygon 3)
  ,("POLYGON2",PPolygon 2)
  ,("MULTIPOLYGON2",MultiGeom$PPolygon 2)
  ,("MULTIPOLYGON3",MultiGeom$ PPolygon 3)
  ,("LINESTRING3",PLineString 3)
  ,("LINESTRING2",PLineString 2)
  ,("box3d",PBounding 3)
  ,("box2d",PBounding 2)
  ])

ktypeUnLift :: KType (Prim KPrim (Text,Text)) -> Maybe (KType (Prim KPrim (Text,Text)))
ktypeUnLift i = M.lookup i postgresUnLiftPrim

ktypeLift :: KType (Prim KPrim (Text,Text)) -> Maybe (KType (Prim KPrim (Text,Text)))
ktypeLift i = M.lookup i postgresLiftPrim


ktypeRec f v@(KOptional i) =   f v <|> fmap KOptional (ktypeRec f i)
ktypeRec f v@(KArray i) =   f v <|> fmap KArray (ktypeRec f i)
ktypeRec f v@(KInterval i) =   f v <|> fmap KInterval (ktypeRec f i)
ktypeRec f v@(KSerial i) = f v <|> fmap KSerial (ktypeRec f i)
ktypeRec f v@(KDelayed i) = f v <|> fmap KDelayed (ktypeRec f i)
ktypeRec f v@(Primitive i ) = f v




