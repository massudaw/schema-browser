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
import qualified Data.Text.Lazy as TL

import qualified Data.List as L

import Query

import Types
import Schema
import RuntimeTypes

import Step

import qualified Data.Text as T
import Data.Text.Lazy
import Data.Aeson
import Control.Arrow
import Control.Monad.Trans.Maybe
import Debug.Trace
import Control.Monad.Trans.Class


import qualified Data.Map as M
import qualified Data.Set as S

{-

queryGeocodeBoundary = BoundedPlugin2 "Google Geocode" "address" (staticP url) element
  where
    url :: ArrowPlug (Kleisli IO) (Maybe (TB2 Text Showable))
    url = proc t -> do
      id <- varT "id" -< t
      log <- varT "logradouro"-< t
      num <- varN "number"-< t
      bai <- varN "bairro"-< t
      mun <- varT "municipio"-< t
      uf <- varT "uf"-< t
      odx "geocode" -< t
      odx "bounding" -< t
      let im = "http://maps.googleapis.com/maps/api/geocode/json"
          vr =  maybe "" renderShowable
          addr = vr log <> " , " <> vr num <> " - " <>  vr bai<> " , " <> vr mun <> " - " <> vr uf
      r <- act (\(im,addr)-> runMaybeT $ do
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

      let tb = TB1 . KV (PK [] []) . fmap (Compose . Identity. ( uncurry Attr ) . second (SOptional. Just )) <$> r
      returnA -< tb

    element inf
          = maybe (return Nothing) (\inp -> do
                   b <- dynPK url (Just inp)
                   return $ mapKey (lookKey inf "address")  <$> b)

-}

queryCEPBoundary = BoundedPlugin2  "Correios CEP" "address" (staticP open  )  element
  where
      translate :: Text -> Text
      translate "localidade" =  "municipio"
      translate i = i
      open :: ArrowPlug  (Kleisli IO ) (Maybe (TB2 Text Showable))
      open = proc t -> do
          i <- varT "cep" -< t
          odx "bairro" -< t
          odx "municipio" -< t
          odx "uf" -< t
          odx "logradouro" -< t
          r <- (act (  traverse (\input -> do
                       v <- get . traceShowId .  (\i-> addrs <> (L.filter (flip elem ",.-" ) i) <> ".json")  . TL.unpack $ input
                       return $ ( \i -> fmap (L.filter ((/="").snd) . M.toList ) $ join $ fmap decode (i ^? responseBody)  ) v ))) -< (\(SText t)-> t) <$> i
          let tb = tbmap . M.fromList .  fmap ( (\i -> (S.singleton (fst i) ,). Compose . Identity $ Attr (fst i ) (snd i)). first translate. second (SOptional. Just . SText)) <$> join r
          returnA -< tb

      addrs ="http://cep.correiocontrol.com.br/"
      element inf
          = maybe (return Nothing) (\inp -> do
                   b <- dynPK open (Just inp)
                   return $ mapKey (lookKey inf "address")  <$> b)

