{-# LANGUAGE TupleSections,Arrows,OverloadedStrings #-}
module Location where

import Network.Wreq
import Control.Lens
import Utils
import Control.Applicative
import Control.Monad
import Data.Monoid

import Data.ExtendedReal
import Data.Interval
import qualified Data.Text as TL

import qualified Data.List as L

import Types
import RuntimeTypes
import Control.Monad.IO.Class
import Control.Monad.Reader

import Step

import qualified Data.Text as T
import Data.Text
import Data.Aeson
import Control.Arrow
import Control.Monad.Trans.Maybe
import Debug.Trace
import Control.Monad.Trans.Class


import qualified Data.Map as M
import qualified Data.Set as S



queryGeocodeBoundary = BoundedPlugin2 "Google Geocode" "address"  url
  where
    url :: ArrowReader
    url = proc t -> do
      id <- idxR  "id" -< t
      log <- idxR "logradouro"-< t
      num <- idxM "number"-< t
      bai <- idxR "bairro"-< t
      mun <- idxR "municipio"-< t
      uf <- idxR "uf"-< t
      odxR "geocode" -< t
      odxR "bounding" -< t
      let im = "http://maps.googleapis.com/maps/api/geocode/json"
          vr =  maybe "" renderShowable
          addr = vr log <> " , " <> vr num <> " - " <>  vr bai<> " , " <> vr mun <> " - " <> vr uf
      r <- act (\(im,addr)-> lift $ runMaybeT $ do
            r <-  lift $ getWith (defaults & param "address" .~ [T.pack addr]  ) $ im
            let dec = join $ decode <$> (r ^? responseBody) :: Maybe Value
                loc = dec !> "results" !!> 0 !> "geometry" !> "location"
                bounds = dec !> "results" !!> 0 !> "geometry" !> "bounds"
                viewport = dec !> "results" !!> 0 !> "geometry" !> "viewport"
                getPos l = Position <$> liftA2 (\(Number i) (Number j)-> (realToFrac i ,realToFrac j ,0)) (l !> "lng" )( l  !> "lat" )
            p <- MaybeT $ return $ getPos loc
            b <- MaybeT $ return $ case (fmap Bounding $  (\i j -> interval (Finite i ,True) (Finite j ,True))<$> getPos (bounds !> "southwest") <*> getPos (bounds !> "northeast"), fmap Bounding $ (\i j -> interval (Finite i ,True) (Finite j ,True))<$> getPos (viewport !> "southwest") <*> getPos (viewport !> "northeast")) of
                                        (i@(Just _), _ ) -> i
                                        (Nothing , j) -> j
            return [("geocode" ,SPosition p),("bounding", SBounding b)]) -<  (im,addr)

      let tb =  tblist . fmap (_tb . (uncurry Attr ) . second (LeftTB1 . Just . TB1)) <$> r
      returnA -< tb



queryCEPBoundary = BoundedPlugin2  "Correios CEP" "address" open
  where
      translate :: Text -> Text
      translate "localidade" =  "municipio"
      translate i = i
      open :: ArrowReader
      open = proc t -> do
          i <- idxK "cep" -< t
          odxR "bairro" -< t
          odxR "municipio" -< t
          odxR "uf" -< t
          odxR "logradouro" -< t
          r <- (act (  liftIO . traverse (\input -> do
                       v <- get . traceShowId .  (\i-> addrs <> (L.filter (not . flip elem ",.-" ) i) <> ".json")  . TL.unpack $ input
                       return $ ( \i -> fmap (L.filter ((/="").snd) . M.toList ) $ join $ fmap decode (i ^? responseBody)  ) v ))) -< (\(TB1 (SText t))-> t) <$> Just i
          let tb = tbmap . M.fromList .  fmap ( (\i -> (S.singleton (Inline $ fst i) ,). Compose . Identity $ Attr (fst i ) (snd i)). first translate. second (LeftTB1 . Just . TB1 . SText)) <$> join r
          returnA -< tb

      addrs ="http://cep.correiocontrol.com.br/"

