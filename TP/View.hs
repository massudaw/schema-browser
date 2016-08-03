{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module TP.View where

import qualified Data.Aeson as A
import Safe
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
import Text
import RuntimeTypes
import Step.Common
import Step.Host
import Data.Time
import Query
import Data.Interval as Interval
import qualified Data.Text as T

instance A.ToJSON a =>
         A.ToJSON (FTB a) where
    toJSON (TB1 i) = A.toJSON i
    toJSON (LeftTB1 i) = fromMaybe (A.toJSON ("" :: String)) (A.toJSON <$> i)
    toJSON (ArrayTB1 i) = (A.toJSON $ F.toList i)

instance A.ToJSON Showable where
    toJSON (SText i) = A.toJSON i
    toJSON (SPosition (Position (y,x,z))) =
        A.Array $
        V.fromList
            [ A.String $ T.pack (show x)
            , A.String $ T.pack (show y)
            , A.String $ T.pack (show z)]
    toJSON i = A.toJSON (renderPrim i)

geoPred geofields (_,ne,sw) = geo
  where
    geo =
        OrColl $
        PrimColl .
        (, "<@", (IntervalTB1 $ Interval.interval (makePos sw) (makePos ne))) .
        indexer . T.pack . renderShowable <$>
        F.toList geofields

timePred evfields (_,incrementT,resolution) = time
  where
    time = OrColl $ timeField <$> F.toList evfields
    timeField f =
      PrimColl . (, op (keyType f), (IntervalTB1 $ fmap (ref (keyType f)) i)) $
        indexer (keyValue f)
    op f = case f of
             KInterval i -> "&&"
             KOptional i -> op i
             KSerial i -> op i
             Primitive i -> "<@"
    ref f =
        case f of
            Primitive (AtomicPrim PDate) ->
                (TB1 . SDate . localDay . utcToLocalTime utc)
            Primitive (AtomicPrim (PTimestamp _)) ->
                (TB1 . STimestamp . utcToLocalTime utc)
            KOptional i -> ref i
            KSerial i -> ref i
            KInterval i -> ref i
            v -> errorWithStackTrace (show v)
    i =
        (\r d ->
              Interval.interval
                  (Interval.Finite $ resRange True r d, True)
                  (Interval.Finite $ resRange False r d, True))
            resolution
            incrementT

predicate
    :: Maybe (NonEmpty Key)
    -> Maybe (NonEmpty (FTB Showable))
    -> (Maybe (t, [Double], [Double]), Maybe (t1, UTCTime, String))
    -> WherePredicate
predicate evfields geofields (i,j) =
    WherePredicate $
    AndColl $
    catMaybes [liftA2 geoPred geofields i, liftA2 timePred evfields j]

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

makePos [b,a,z] =
    (Interval.Finite $ TB1 $ SPosition (Position (a, b, z)), True)
makePos i = errorWithStackTrace (show i)

writePK :: TBData Key Showable -> FTB Showable -> T.Text
writePK r efield =
    (\i ->
          _kvname (fst r) <> "->" <> i <> "->" <>
          T.pack (renderShowable efield)) $
    T.intercalate "," $
    fmap
        ((\(i,j) ->
               keyValue i <> "=" <> T.pack (renderShowable j))) $
    M.toList $ getPKM r

readPK :: InformationSchema -> T.Text -> (Table, [(Key, FTB Showable)], Key)
readPK inf s = (tb, pk, editField)
  where
    [t,pks,f] = T.splitOn "->" s
    pk =
        (\(k,v) ->
              (k, fromJust $ readType (keyType k) (T.unpack $ T.drop 1 v))) .
        first
            (\k ->
                  fromJust $ F.find ((k ==) . keyValue) pksk) .
        T.break ('=' ==) <$>
        T.splitOn "," pks
    tb = lookTable inf t
    editField = lookKey inf t f
    pksk = rawPK tb
makePatch
    :: TimeZone
    -> ((Table, [(Key, FTB Showable)], Key), Either (Interval UTCTime) UTCTime)
    -> TBIdx Key Showable
makePatch zone ((t,pk,k),a) =
    (tableMeta t, G.Idex $ M.fromList pk, PAttr k <$> (ty (keyType k) $ a))
  where
    ty (KOptional k) i = fmap (POpt . Just) . ty k $ i
    ty (KSerial k) i = fmap (PSerial . Just) . ty k $ i
    ty (KInterval k) (Left i) =
        [ PatchSet $
          (fmap (PInter True . (, True)) . (ty k . Right . unFinite) $
           Interval.lowerBound i) <>
          (fmap (PInter False . (, True)) . (ty k . Right . unFinite) $
           Interval.upperBound i)]
    ty (Primitive p) (Right r) = pure . PAtom . cast p $ r
    cast (AtomicPrim PDate) = SDate . utctDay
    cast (AtomicPrim (PTimestamp l)) =
        STimestamp .
        utcToLocalTime utc . localTimeToUTC zone . utcToLocalTime utc

readPosition:: EventData -> Maybe ([Double],[Double],[Double])
readPosition (v) = (,,) <$> readP i a z <*> readP ni na nz <*>readP si sa sz
  where
     [i,a,z,ni,na,nz,si,sa,sz] = unsafeFromJSON v
     readP i a z = (\i j z-> [i,j, z]) <$> readMay i<*> readMay a <*> readMay z

currentPosition :: Element -> Event ([Double],[Double],[Double])
currentPosition el = filterJust $ readPosition<$>  domEvent "currentPosition" el
