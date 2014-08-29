{-# LANGUAGE Arrows, OverloadedStrings,NoMonomorphismRestriction #-}
module Gpx where

import Query
import Schema
import Postgresql
import Database.PostgreSQL.Simple

import Data.Maybe
import Data.Text.Lazy (Text)
import Text.Read
import qualified Data.Map as M
import Data.Time.Parse
import Data.Time
import Text.XML.HXT.Core

import Text.XML.HXT.Curl
import Text.XML.HXT.Arrow.Pickle
import Data.Geo.GPX hiding((***))
import Text.XML.HXT.Arrow.XmlState.TypeDefs

import Control.Arrow.IOStateListArrow
import Text.XML.HXT.Arrow.XmlState

--import Data.Lens.Common
import Data.Lens.Common
import Control.Category.Product
import Database.PostgreSQL.Simple.Time

import Prelude hiding ((.),id)
import Control.Category

--getter :: GPX -> [[[(Longitude)]]]
getter gpx = fmap (fmap ( fmap prod  . (^. trkptsL )). (^.trksegsL)) . (^. trksL ) $ gpx
  where
    prod = getL lonL &&&  getL latL   &&& (^. eleL) &&& (^. timeL)



atTag tag = deep (isElem >>> hasName tag)

text = getChildren >>> getText

getPoint = atTag "trkpt" >>>
  proc x -> do
    lat <- getAttrValue "lat"  -< x
    lon <- getAttrValue "lon" -< x
    ele <- text <<< atTag "ele" -< x
    time <- text <<< atTag "time" -< x
    returnA -< [SPosition $ Position (read lat,read lon,read ele),STimestamp $ Finite $ fromJust $ fmap fst  $ strptime "%Y-%m-%dT%H:%M:%SZ" time ]

file = "/home/massudaw/2014-08-26-1719.gpx"

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
  let withFields k t l s = (zip  (fmap (\i->maybe (error "no key") id $ M.lookup (t,i) (keyMap k)) l) s, maybe (error $ "noTable" ) id $  M.lookup t (tableMap k))
  res <- runX arr
  mapM_ (\i-> uncurry (insert conn) (withFields inf "track" ["id_run","id_sample","position","instant"] (SNumeric 5 : i))) (zipWith (:) (fmap SNumeric [0..]) res)
  --print $ fmap getter i
