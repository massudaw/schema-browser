{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module TP.View where

import qualified Data.Aeson as A
import Utils
import Safe
import qualified NonEmpty as Non
import Debug.Trace
import Data.Maybe
import qualified Graphics.UI.Threepenny as UI
import Graphics.UI.Threepenny.Core hiding (get,delete,apply)
import Data.Semigroup
import Control.Arrow (first)
import Control.Applicative
import qualified Data.Map as M
import GHC.Stack
import NonEmpty
import qualified Data.Foldable as F
import Types
import Types.Patch
import qualified Types.Index as G
import Utils
import Data.Maybe
import qualified Data.Vector as V
import qualified Data.List as L
import Data.Ord
import Text
import RuntimeTypes
import Step.Common
import Step.Host
import Data.Time
import Query
import Data.Interval as Interval
import qualified Data.Text as T

newtype Row = Row (TBData Key Showable)
instance A.ToJSON Row  where
  toJSON (Row (_,kv))  = A.toJSON $ M.mapKeys (T.intercalate "," . L.map (keyValue ._relOrigin) . F.toList ) (fmap unTB m)
    where
      m = unKV kv

instance A.ToJSON (Column Key Showable)  where
  toJSON (Attr k v ) =
    case (keyType k ) of
      Primitive [] (AtomicPrim PColor )-> A.toJSON $  "#" <> renderShowable v
      i ->  A.toJSON v
  toJSON (IT k v) = A.toJSON (fmap Row v)

instance A.ToJSON a =>
         A.ToJSON (FTB a) where
    toJSON (TB1 i) = A.toJSON i
    toJSON (LeftTB1 i) = fromMaybe (A.toJSON ("" :: String)) (A.toJSON <$> i)
    toJSON (ArrayTB1 i) = (A.toJSON $ F.toList i)

instance A.ToJSON LineString where
    toJSON (LineString l ) = A.toJSON l

instance A.ToJSON Position where
    toJSON ((Position (y,x,z))) =
        A.Array $
        V.fromList
            [ A.String $ T.pack (show x)
            , A.String $ T.pack (show y)
            , A.String $ T.pack (show z)]
    toJSON ((Position2D (y,x))) =
        A.Array $
        V.fromList
            [ A.String $ T.pack (show x)
            , A.String $ T.pack (show y)
            , A.String $ T.pack (show 0)
            ]

instance A.ToJSON SGeo where
    toJSON (SMultiGeom l) = A.toJSON l
    toJSON (SPolygon h t) = A.toJSON (h:t)
    toJSON (SLineString i) = A.toJSON i
    toJSON (SPosition i ) = A.toJSON i
instance A.ToJSON Showable where
    toJSON (SText i) = A.toJSON i
    toJSON (SGeo o) = A.toJSON o
    toJSON i = A.toJSON (renderPrim i)

indexTyU (Many [One k] )= indexTy k
indexTy (IProd _ k )=  keyType k
indexTy (Nested [IProd _ xs] n) = Primitive ((_keyFunc $ keyType xs) ++ ty) at
    where
      Primitive ty at = indexTyU n


geoPred inf tname geofields (ne,sw) = traceShowId geo
  where
    geo = OrColl $ geoField <$> F.toList geofields
    geoField f =
        PrimColl .
          (, Left (makeInterval (_keyAtom nty)  (sw,ne) ,op nty))
            $ index
      where
        nty= indexTy index
        [index] =  liftAccess inf (tableName tname)  <$>  indexer f

    op (Primitive f a) =  go f
      where
        go [] = Flip Contains
        go (f:i) = case f of
          KInterval -> IntersectOp
          KOptional  -> go i
          KSerial  -> go i
          KArray -> AnyOp $ go i
          v -> errorWithStackTrace (show v)

timePred inf tname evfields (incrementT,resolution) = traceShowId time
  where
    time = OrColl $ timeField <$> F.toList evfields
    timeField f =
      PrimColl . (, Left ( (IntervalTB1 $ fmap (ref ty) i),op ty)) $ index
      where
        [index] =  liftAccess inf (tableName tname)  <$>  indexer f
        ty = indexTy index
    op (Primitive f a) = go f
      where
        go [] = Flip Contains
        go (f:i) = case f of
             KInterval -> IntersectOp
             KOptional -> go i
             KSerial  -> go i
    ref (Primitive f a) =  case a of
            (AtomicPrim (PTime PDate)) ->
              (TB1 . STime . SDate . localDay . utcToLocalTime utc)
            (AtomicPrim (PTime (PTimestamp _))) ->
              (TB1 . STime . STimestamp . utcToLocalTime utc)
            v -> errorWithStackTrace (show v)
    i =
        (\r d ->
              Interval.interval
                  (Interval.Finite $ resRange True r d, True)
                  (Interval.Finite $ resRange False r d, True))
            resolution
            incrementT

predicate
  :: InformationSchema
    -> Table
    -> Maybe (NonEmpty T.Text)
    -> Maybe (NonEmpty T.Text)
    -> (Maybe ([Double], [Double]), Maybe (UTCTime, String))
    -> BoolCollection (Access Key,AccessOp Showable)
predicate inf tname evfields geofields (i,j) =
    AndColl $
      catMaybes [liftA2 (geoPred inf tname ) geofields i, liftA2 (timePred inf tname) evfields j]

resRange b "year" d =
    d
    { utctDay = addGregorianMonthsClip
          (if b
               then -6
               else 6)
          (utctDay d)
    }
resRange b "month" d =
    d
    { utctDay = addGregorianMonthsClip
          (if b
               then -1
               else 1)
          (utctDay d)
    }
resRange b "day" d =
    d
    { utctDay = addDays
          (if b
               then -1
               else 1)
          (utctDay d)
    }
resRange b "week" d =
    d
    { utctDay = addDays
          (if b
               then -7
               else 7)
          (utctDay d)
    }
resRange b "hour" d =
   addUTCTime (if b
               then -3600
               else 3600) d

makeInterval :: Prim KPrim (T.Text,T.Text) ->  ([Double] , [Double]) -> FTB Showable
makeInterval nty (sw,ne) = IntervalTB1 $ Interval.interval (makePos nty sw) (makePos nty ne)

makePos :: Prim KPrim (T.Text,T.Text) -> [Double] -> (Extended (FTB Showable),Bool)
makePos (AtomicPrim (PGeom 3 _ )) [b,a,z] =
    (Interval.Finite $ pos (Position (a, b,z)), True)
makePos (AtomicPrim (PGeom 2 _ )) [b,a,z] =
    (Interval.Finite $ pos (Position2D (a, b)), True)
makePos a i = errorWithStackTrace (show (a,i))

writePK :: TBData Key Showable -> FTB Showable -> T.Text
writePK r efield =
    (\i ->
          _kvname (fst r) <> "->" <> i <> "->" <>
          T.pack (renderShowable efield)) $
    T.intercalate ",," $
    fmap
        ((\(i,j) ->
               keyValue i <> "=" <> T.pack (renderShowable j))) $
    M.toList $ getPKM r


readPK :: InformationSchema -> T.Text -> (Table, G.TBIndex Showable, Key)
readPK inf s = (tb, G.Idex $ fmap snd $ L.sortBy (comparing ((`L.elemIndex` rawPK tb).fst)) pk, editField)
  where
    [t,pks,f] = T.splitOn "->" s
    pk =
        (\(k,v) ->
          (k, justError ("cant read" <> show (k,v)) $ readType (keyType k) (T.unpack $ T.drop 1 v))) .
        first
            (\k ->
              justError ("cant find " <> show (k,pksk)) $ F.find ((k ==) . keyValue) pksk) .
        T.break ('=' ==) <$>
        T.splitOn ",," pks
    tb = lookTable inf t
    editField = lookKey inf t f
    pksk = rawPK tb
makePatch
    :: TimeZone
    -> ((Table, G.TBIndex Showable, Key), Either (Interval UTCTime) UTCTime)
    -> TBIdx Key Showable
makePatch zone ((t,pk,k),a) =
  (tableMeta t,  pk, PAttr k <$> (typ (keyType k) $ a))
  where
    typ (Primitive l a ) =  ty l
      where
        ty (KOptional : k) i = fmap (POpt . Just) . ty k $ i
        ty (KSerial : k) i = fmap (POpt. Just) . ty k $ i
        ty (KInterval : k) (Left i) =
          [ PatchSet $ Non.fromList $
            (fmap ((PInter True . (, True))) . (traverse (ty k . Right) ) $
               Interval.lowerBound i) <>
                 (fmap ((PInter False . (, True))) . (traverse (ty k . Right ) ) $
               Interval.upperBound i)]
        ty []  (Right r) = pure . PAtom . cast a $ r
    cast (AtomicPrim (PTime PDate)) = STime . SDate . utctDay
    cast (AtomicPrim (PTime (PTimestamp l))) =
      STime . STimestamp .
        utcToLocalTime utc . localTimeToUTC zone . utcToLocalTime utc

readPosition:: EventData -> Maybe ([Double],[Double])
readPosition (v) = traceShowId $ (,) <$>  readP ni na nz <*>readP si sa sz
  where
     [ni,na,nz,si,sa,sz] = unsafeFromJSON v
     readP i a z = (\i j z-> [i,j, z]) <$> readMay i<*> readMay a <*> readMay z

currentPosition :: Element -> Event ([Double],[Double])
currentPosition el = filterJust $ readPosition<$>  domEvent "currentPosition" el


convertInter i | traceShow i False = undefined
convertInter i =    liftA2 (,) (fmap convertPoint $ G.unFin $ fst $upperBound' i) (fmap convertPoint $ G.unFin $ fst $lowerBound' i)
  where
     convertPoint ((SGeo (SPosition (Position (y,x,z)) ))) = [x,y,z]
     convertPoint ((SGeo (SPosition (Position2D (y,x)) ))) = [x,y,0]


