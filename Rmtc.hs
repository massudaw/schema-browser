{-# LANGUAGE ScopedTypeVariables,Arrows #-}
module Rmtc where

import Control.Monad
import TP.QueryWidgets
import qualified NonEmpty as Non
import qualified Types.Index as G
import Schema
import RuntimeTypes
import Types.Patch
import SchemaQuery
import Control.Concurrent.Async
import Reactive.Threepenny (runDynamic)
import Text.Read
import Utils
import Text.XML.HXT.Core
import qualified Data.Vector as V
import Control.Concurrent
import Data.Aeson.Lens
import Data.Time
import Data.List (nub,null)
import System.Process
import Types
import Data.Text (Text,unpack)
import Data.Maybe
import Control.Monad.Catch --Exception

import qualified Data.Foldable as F
import SchemaQuery
import Database.PostgreSQL.Simple
import Database.PostgreSQL.Simple.Types
import Schema
import Control.Lens hiding (deep)
import Data.Aeson
import qualified Data.ByteString.Lazy as BS

data  Onibus
  = Onibus
    { numeroOnibus :: Integer
    , accessivel :: Integer
    , position :: (Double,Double)
    , situacao  :: Text
    , linha :: Linha
    , destino :: Destino
    }deriving(Show)

data Linha
  = Linha
  { numeroLinha  :: Integer
  , linhaIda :: Text
  , linhaVolta :: Text
  }deriving(Show)

data Ponto
  = Ponto
    { pontoId :: Integer
    , pontoEndereco :: Text
    , pontoPosition :: (Text,Text)
    , pontoReferencia :: Text
    }deriving(Show)
data Destino
  = Destino {nomeDestino :: Text}
  deriving(Show)

readPonto = runFold (Ponto <$> Fold (key "PontoId"._Integer)  <*> Fold (key "PontoEndereco". _String)  <*> ((,) <$> Fold (key "PontoLongitude" ._String) <*> Fold (key "PontoLatitude" . _String)  ) <*> Fold (key "PontoReferencia"._String))

readOnibus = runFold (Onibus <$> Fold (key "Numero"._Integer)
                             <*> Fold (key "Acessivel" ._Integer)
                             <*>  ((,) <$> Fold (key "Longitude" ._Double)
                                    <*> Fold (key "Latitude" . _Double))
                             <*> Fold (key "Situacao" ._String)
                             <*> Fold (key "Linha" . runFold (Linha
                                      <$> Fold (key "LinhaNumero" ._Integer)
                                      <*> Fold (key "LinhaKMLIda". _String  )
                                      <*> Fold (key "LinhaKMLVolta" ._String ) ))
                            <*> Fold (key "Destino" .runFold (Destino
                                     <$> Fold (key "DestinoCurto" . _String) ))
                      )

testkml = "http://www.rmtcgoiania.com.br/components/com_rmtclinhas/satelite/EixoCircularIndependencia-AreaSul-400ida.kml"
readKML l = do
  callCommand $ "curl " ++ l ++ " > load.kml"
  o <- readFile "load.kml"
  print o
  readHtmlReceita o


atTag tag = deep (isElem >>> hasName tag)

trim :: String -> String
trim = triml . trimr

-- | Remove leading space (including newlines) from string.
triml :: String -> String
triml = dropWhile (`elem` (" \r\n\t" :: String))

-- | Remove trailing space (including newlines) from string.
trimr :: String -> String
trimr = reverse . triml . reverse


readHtmlReceita file = do
  let
      arr = readString [withValidate no,withWarnings no,withParseHTML yes] file >>> tel
      pos [x,y,z] = Position (x,y,z)
      pos [x,y] = Position (x,y,0)
      pos i = error (show i)
      tel  = proc t -> do
        coords <- getChildren >>> atTag "coordinates" >>> getChildren >>> getText >>^ (fmap (\i -> pos . justError ("no parse" ++ show i). allMaybes . fmap readMaybe . unIntercalate (==',') $ i). unIntercalate (==' ').trim )-< t
        name <- atTag "placemark" >>> getChildren >>> atTag "name" >>> getChildren >>> getText -< t
        returnA -< (coords,name)

  l <- runX arr
  return $ listToMaybe l



checkAllLines = do
  conn <- connectPostgreSQL "user=postgres host=localhost password=jacapodre dbname=incendio"
  l <- query_ conn "select id from transito.linha"
  mapM (\(Only i) -> checkLinha conn (i :: Int) `catchAll` (\e -> return ())) l



checkLinha conn l = do
  callCommand $ "curl 'http://www.rmtcgoiania.com.br/index.php?option=com_rmtclinhas&view=ped&format=json&linha=" ++ show l ++ "' -H 'Cookie: __cfduid=d1871e10d13cb6c77201b9b7ab641c9461480098729; _gat=1; 4029dc09fae2b24f3d2ae3d2b169a292=9dc128e8101669ac0bf44eaf6fbc6536; __utmt=1; version_site=desktop; _ga=GA1.3.1405588424.1480098735; __utma=126153870.1405588424.1480098735.1480098740.1480098740.1; __utmb=126153870.3.10.1480098740; __utmc=126153870; __utmz=126153870.1480098740.1.1.utmcsr=google|utmccn=(organic)|utmcmd=organic|utmctr=(not%20provided)' -H 'DNT: 1' -H 'Accept-Encoding: gzip, deflate, sdch' -H 'X-Request: JSON' -H 'User-Agent: Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/54.0.2840.90 Safari/537.36 Mozilla/5.0 (X11; NetBSD i386) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/43.0.2357.124 Safari/537.36' -H 'Accept-Language: en-US,en;q=0.8,pt;q=0.6' -H 'Accept: application/json' -H 'Referer: http://www.rmtcgoiania.com.br/index.php/olho-no-onibus?enviar=Acessar' -H 'X-Requested-With: XMLHttpRequest' -H 'Connection: keep-alive' --compressed > linha" ++ show l++ ".json"

  f <- BS.readFile $ "linha" ++ show l ++ ".json"
  print f

  let Just a = decode f :: Maybe Value
      pontos = catMaybes $ F.toList $ fmap (^? readPonto) (a  ^. key "pontosparada" .  _Array )
  print (pontos,(a  ^. key "pontosparada" .  _Array ))
  _ <- mapM (\i->execute conn "INSERT INTO transito.pontos (id,linha,geocode,endereco,referencia) VALUES (?,?,?,?,?)" i ) (fmap (\i -> ( pontoId i,l, Position (read $ unpack $ fst (pontoPosition i) ,read $ unpack $ snd (pontoPosition i) ,0),pontoEndereco i, pontoReferencia i )) pontos)
  return ()

readLineKML  = do
  conn <- connectPostgreSQL "user=postgres host=localhost password=jacapodre dbname=incendio"
 -- l ::[(Integer,String,String)]<- query_ conn "select id,linha_ida,linha_volta from transito.linha where linha_ida is not null and linha_ida_coordinates is null"
  l ::[(Integer,String,String)]<- query_ conn "select id,linha_ida,linha_volta from transito.linha where linha_ida is not null and id= 651"
  mapM (\(i,li,lv) -> do
    (ci,cv) <- concurrently (readKML li) (readKML lv)
    print (ci,cv)
    traverse (\((coordi,namei),(coordv,namev)) -> execute conn "update transito.linha set linha_ida_nome = ? , linha_ida_coordinates = ? ,linha_volta_nome= ? , linha_volta_coordinates = ? where id = ?"  (namei ,LineString $ V.fromList $ coordi ,namev ,LineString $ V.fromList $ coordv,i) ) (liftM2 (,) ci cv)
    return()
      `catchAll` (\e -> return ())) l

checkOnibus inf = do
  t <- getCurrentTime
  callCommand "curl 'http://www.rmtcgoiania.com.br/index.php?option=com_rmtclinhas&view=cconaweb&format=json&linha=0' -H 'Cookie: __cfduid=d1871e10d13cb6c77201b9b7ab641c9461480098729; 4029dc09fae2b24f3d2ae3d2b169a292=9dc128e8101669ac0bf44eaf6fbc6536; version_site=desktop; _ga=GA1.3.1405588424.1480098735; __utmt=1; __utma=126153870.1405588424.1480098735.1480098740.1480098740.1; __utmb=126153870.6.10.1480098740; __utmc=126153870; __utmz=126153870.1480098740.1.1.utmcsr=google|utmccn=(organic)|utmcmd=organic|utmctr=(not%20provided)' -H 'DNT: 1' -H 'Accept-Encoding: gzip, deflate, sdch' -H 'X-Request: JSON' -H 'User-Agent: Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/54.0.2840.90 Safari/537.36 Mozilla/5.0 (X11; NetBSD i386) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/43.0.2357.124 Safari/537.36' -H 'Accept-Language: en-US,en;q=0.8,pt;q=0.6' -H 'Accept: application/json' -H 'Referer: http://www.rmtcgoiania.com.br/olho-no-onibus' -H 'X-Requested-With: XMLHttpRequest' -H 'Connection: keep-alive' --compressed > rmtc.json"
  f <- BS.readFile "rmtc.json"

  let Just a = decode f :: Maybe Value
      dec = catMaybes $ F.toList $ fmap (^? readOnibus ) (a  ^. key "onibus" .  _Array )
      pontos = catMaybes $ F.toList $ fmap (^? readPonto) (a  ^. key "pontosparada" .  _Array )

  print dec
  print (pontos,(a  ^. key "pontosparada" .  _Array ))
  conn <- connectPostgreSQL "user=postgres host=localhost password=jacapodre dbname=incendio"
  _ <- mapM (\i->execute conn "INSERT INTO transito.onibus (id,acessivel) VALUES (?,?)" i `catchAll`(\_-> return 0)) (fmap (\i -> (numeroOnibus i, accessivel i == 1 )) dec)
  _ <- mapM (\(li,lv,i) -> execute conn "INSERT INTO transito.linha (id,linha_ida,linha_volta) VALUES (?,?,?)" (i,li,lv) `catchAll`(\e-> execute conn "update transito.linha set linha_ida = ?  ,linha_volta = ? where id = ? " (li,lv,i) )) (nub $ fmap (\i -> (linhaIda$ linha i  ,linhaVolta $ linha i,numeroLinha $ linha i)) dec)

  _ <- mapM (\i -> execute conn "INSERT INTO transito.destino_linha (linha,name) VALUES (?,?)" i `catchAll` (\e -> return 0)) (nub $ fmap (\i -> (numeroLinha $ linha i , nomeDestino $ destino i )) dec)
  _ <- mapM (\i -> execute conn "INSERT INTO transito.registro_onibus (onibus,horario,linha,geocode,situacao,destino) VALUES (?,?,?,?,?,?)" i ) (nub $ fmap (\i -> (numeroOnibus i,t,numeroLinha $ linha i ,Position (fst $ position i, snd $ position i,0),situacao i, nomeDestino $ destino i )) dec)
  ref <-prerefTable inf (lookTable inf "max_registro_onibus")
  print "start patch"
  (_,l) <- runDynamic $ refTables' inf (lookTable inf "max_registro_onibus") Nothing (WherePredicate (AndColl [ PrimColl (liftAccess inf "max_registro_onibus"$ IProd Nothing ["onibus"],Left (ArrayTB1 $ Non.fromList ( (\i -> int (fromIntegral $ numeroOnibus i)) <$> dec) , Flip $ AnyOp Equals ))]))
  sequence l

  putPatch (patchVar $ ref ) $fmap (\i -> (liftPatch inf "max_registro_onibus" (mempty , G.Idex [ int (fromIntegral $ numeroOnibus i)], [ PAttr "onibus" (patch$ int (fromIntegral $ numeroOnibus i)), PAttr "horario" (POpt $ Just $ patch $ timestamp $ utcToLocalTime utc t),PAttr "situacao" (POpt $ Just $ patch $ Types.txt (situacao i)),PAttr "geocode" (POpt $ Just $ patch $  pos (Position (fst $ position i, snd $ position i,0)))])))  dec
  print "end checkOnibus"

  return ()

pollRmtc smvar amap user = do
  (inf ,lm)<- runDynamic $keyTablesInit  smvar ("transito", user ) amap []
  (_,l) <- runDynamic $ refTables' inf (lookTable inf "max_registro_onibus") Nothing mempty
  sequence l
  forkIO $ forever ( checkOnibus inf >> threadDelay (1*60*10^6))
