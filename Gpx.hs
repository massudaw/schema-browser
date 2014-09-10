{-# LANGUAGE Arrows, TupleSections,OverloadedStrings,NoMonomorphismRestriction #-}
module Gpx where

import Query
import Data.Monoid
import Schema
import GHC.Stack
import Postgresql
import Database.PostgreSQL.Simple
import Control.Applicative
import Numeric.Interval((...))

import Data.Maybe
import Data.Text.Lazy (Text)
import Text.Read
import qualified Data.Map as M
import Data.Time.Parse
import Data.Time
import Text.XML.HXT.Core

import Text.XML.HXT.Curl
import Text.XML.HXT.Arrow.Pickle
import Text.XML.HXT.Arrow.XmlState.TypeDefs

import Control.Arrow.IOStateListArrow
import Text.XML.HXT.Arrow.XmlState

import Database.PostgreSQL.Simple.Time

import Prelude hiding ((.),id)
import Control.Category



atTag tag = deep (isElem >>> hasName tag)

text = getChildren >>> getText

consII l k i=  (l,k) : i
consIL l k i=  zipWith (:) (repeat (l,k))  i
consLL l k i=  zipWith (:) (fmap (l,) k)  i
consLI l k i=  zipWith (:) (fmap (l,) k)  (repeat i)


zipII i l k = i <> zip  l k
zipIL i l k = zipWith mappend (repeat i)  (fmap (zip l) k)
zipLL i l k = zipWith mappend i (fmap (zip l) k)
zipLI i l k = zipWith mappend i (repeat $ zip l k)

getPoint = atTag "trkpt" >>>
  proc x -> do
    lat <- getAttrValue "lat"  -< x
    lon <- getAttrValue "lon" -< x
    ele <- text <<< atTag "ele" -< x
    time <- text <<< atTag "time" -< x
    returnA -< [SPosition $ Position (read lat,read lon,read ele),STimestamp $ Finite $ fromJust $ fmap fst  $ strptime "%Y-%m-%dT%H:%M:%SZ" time ]

file = "/home/massudaw/2014-08-27-1653.gpx"

lookupKeys inf t l = fmap (\(k,s)-> (maybe (error "no key") id $ M.lookup (t,k) (keyMap inf),s)) l

withFields k t l = (l, maybe (error $ "noTable" ) id $  M.lookup t (tableMap k))

execF = exec file
exec file = do
  let schema = "health"
  conn <- connectPostgreSQL "user=postgres password=queijo dbname=test"
  --let file = "/home/massudaw/src/geo-gpx/etc/gpx.xml"
  let
    --arr :: IOStateArrow () XmlTree
    arr = readDocument [withValidate no,withTrace 1] file
        >>> getPoint
  inf <- keyTables conn  schema
  print (tableMap inf)
  res <- runX arr
  let runVals = [("period",SInterval $ (last $ head res ) ... (last $ last res)),("distance",SNumeric 0),("id_shoes",SNumeric 1),("id_person",SNumeric 1),("id_place",SNumeric 1)]
      runInput = withFields inf  "run" $   lookupKeys inf "run"  runVals
  print runInput
  pkrun <- uncurry (insertPK fromShowableList conn) runInput
  mapM_ (\i-> uncurry (insert conn) (withFields inf "track" (pkrun <> lookupKeys inf "track" i))) (consLL "id_sample" (SNumeric <$> [0..])  $  zipLL (repeat []) ["position","instant"] res )
  return ()
