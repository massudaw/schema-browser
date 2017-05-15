{-# LANGUAGE FlexibleInstances,TupleSections,Arrows,OverloadedStrings #-}
module Location where

import Network.Wreq
import System.Environment
import Control.Lens
import Utils
import Control.Applicative
import Control.Monad
import Data.Monoid
import Text

import Data.ExtendedReal
import Data.Interval
import qualified Data.Text as TL

import qualified Data.List as L

import Types
import RuntimeTypes
import Control.Monad.IO.Class
import Control.Monad.Reader

import Step.Client

import qualified Data.Text as T
import Data.Text
import Data.Aeson
import Control.Arrow
import Control.Monad.Trans.Maybe
import Debug.Trace
import qualified Network.Wreq.Session as Sess

import OpenSSL.Session (context)
import Network.HTTP.Client.OpenSSL

import qualified Data.Map as M
import qualified Data.HashMap.Strict as HM
import qualified Data.Set as S



queryGeocodeBoundary = FPlugins "Google Geocode" "address"  $ BoundedPlugin2 url
  where
    url :: ArrowReader
    url = proc t -> do
      id <- idxR  "id" -< t
      log <- idxR "logradouro"-< t
      num <- idxM "number"-< t
      cep <- idxM "cep"-< t
      bai <- idxR "bairro"-< t
      mun <- idxR "municipio"-< t
      uf <- idxR "uf"-< t
      odxR "geocode" -< t
      let im = "https://maps.googleapis.com/maps/api/geocode/json"
          vr =  maybe "" renderShowable
          addr =    "Brasil, "<> vr cep <> ", "<>  vr mun <> " - " <>  vr uf <> ", " <> vr log <> "," <> vr num  <> " - " <> vr bai
      r <- act (\(im,addr)-> lift $ runMaybeT $ do
            lift $ print (im,addr)
            key <- lift $ justError "no key" <$> lookupEnv "GOOGLE_SERVER_KEY"
            r <-  lift $ withOpenSSL $ Sess.withSessionWith (opensslManagerSettings context) (\sess -> do
                    Sess.getWith (defaults & param "address" .~ [T.pack addr]  & param "key" .~ [T.pack key] ) sess $ im)
            lift $ print r
            let dec = join $ decode <$> (r ^? responseBody) :: Maybe Value
                loc = dec !> "results" !!> 0 !> "geometry" !> "location"
                bounds = dec !> "results" !!> 0 !> "geometry" !> "bounds"
                viewport = dec !> "results" !!> 0 !> "geometry" !> "viewport"
                getPos l = Position <$> liftA2 (\(Number i) (Number j)-> (realToFrac i ,realToFrac j ,0)) (l !> "lng" )( l  !> "lat" )
            p <- MaybeT $ return $ getPos loc
            b <- MaybeT $ return $ case (fmap IntervalTB1 $ fmap (fmap (pos))$  (\i j -> interval (Finite i ,True) (Finite j ,True))<$> getPos (bounds !> "southwest") <*> getPos (bounds !> "northeast"), fmap IntervalTB1 $ fmap (fmap (pos) )$ (\i j -> interval (Finite i ,True) (Finite j ,True))<$> getPos (viewport !> "southwest") <*> getPos (viewport !> "northeast")) of
                                        (i@(Just _), _ ) -> i
                                        (Nothing , j) -> j
            return [("geocode" ,pos p)]) -<  (im,addr)

      let tb =  tblist . fmap (_tb . (uncurry Attr ) . second (LeftTB1 . Just )) <$> r
      returnA -< tb



queryCEPBoundary = FPlugins "Correios CEP" "address" $ BoundedPlugin2  open
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
                       v <- get . (\i-> addrs <> (L.filter (not . flip elem (",.-" :: String)) i) <> ".json")  . TL.unpack $ input
                       return $ ( \i -> fmap (L.filter ((/="").snd) . HM.toList ) $ join $ fmap decode (i ^? responseBody)  ) v ))) -< (\(TB1 (SText t))-> t) <$> Just i
          let tb = tblist . fmap ( (\i ->  _tb $ Attr (fst i ) (snd i)). first translate. second (LeftTB1 . Just . TB1 . SText)) <$> join r
          returnA -< tb

      addrs ="http://cep.correiocontrol.com.br/"

