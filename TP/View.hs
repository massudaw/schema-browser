{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module TP.View where

import qualified Data.Aeson as A
import Data.Semigroup
import Control.Arrow (first)
import Control.Applicative
import qualified Data.Map as M
import GHC.Stack
import NonEmpty
import qualified Data.Foldable as F
import Types
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
    geo = OrColl $ PrimColl . (,"<@",(IntervalTB1 $ Interval.interval (makePos sw) (makePos ne))) . indexer . T.pack . renderShowable <$> F.toList geofields

timePred evfields (_,incrementT,resolution)  = time
  where
    time = OrColl $ PrimColl . (,"<@",(IntervalTB1 $ fmap (TB1 . STimestamp.  utcToLocalTime utc )i)) . indexer . T.pack . renderShowable <$> F.toList evfields
    i = (\r d -> Interval.interval (Interval.Finite $ resRange True r d,True) (Interval.Finite $ resRange False r d,True)) resolution   incrementT
predicate ::
     Maybe (NonEmpty (FTB Showable))
     -> Maybe (NonEmpty (FTB Showable))
     -> (Maybe(t, [Double], [Double]),
         Maybe (t1, UTCTime, String ))
     -> WherePredicate


predicate evfields geofields (i,j) = WherePredicate $ AndColl $ catMaybes [liftA2 geoPred geofields i ,liftA2 timePred evfields j ]


resRange b "month" d =  d {utctDay = addGregorianMonthsClip (if b then -1 else 1 )  (utctDay d)}
resRange b "day" d = d {utctDay =addDays (if b then -1 else 1 ) (utctDay d)}
resRange b "week" d = d {utctDay =addDays (if b then -7 else 7 ) (utctDay d)}

makePos [b,a,z] = (Interval.Finite $ TB1 $ SPosition (Position (a,b,z)),True)
makePos i = errorWithStackTrace (show i)

writePK :: TBData Key Showable -> FTB Showable ->  T.Text
writePK r efield = (\i -> _kvname (fst r) <> "->"  <> i <>  "->" <> T.pack (renderShowable efield ))$T.intercalate  ","  $ fmap ((\(i,j) -> keyValue i <> "=" <> T.pack (renderShowable j))) $ M.toList $ getPKM r


readPK :: InformationSchema -> T.Text -> (Table,[(Key ,FTB Showable)],Key)
readPK  inf s = (tb,pk,editField)
  where [t,pks,f] = T.splitOn "->"  s
        pk = (\(k,v) -> (k,fromJust  $ readType (keyType k) (T.unpack $ T.drop 1 v))) . first (\k -> fromJust $ F.find ((k==).keyValue)pksk).  T.break ('='==) <$> T.splitOn "," pks
        tb = lookTable inf t
        editField = lookKey inf t f
        pksk = rawPK tb



