{-# LANGUAGE OverloadedStrings #-}
module PrefeituraSNFSE where
import Network.Wreq
import Control.Monad
import qualified Network.Wreq.Session as Sess


-- import Widgets
import Types
import Utils
import Pdf

import OpenSSL.Session (context)
import Network.HTTP.Client.OpenSSL

import Control.Lens
import Control.Applicative
import Data.Monoid

import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC
import qualified Data.ByteString.Lazy as BSL
import Data.ByteString.Search (replace)


import Debug.Trace

import System.Process(callCommand)

siapi3Page ano cgc_cpf nota =
  withOpenSSL $
  Sess.withSessionWith (opensslManagerSettings context) $
    \session -> do
      Sess.get session prefeituraLoginCookie
      pr <- Sess.post session prefeituraLoginFormUrl0 (prefeituraForm ano cgc_cpf)
      print (pr ^. responseBody)
      r <- Sess.get session "https://www10.goiania.go.gov.br/SicaePortal/HomePage.aspx"
      r <- Sess.get session (BSC.unpack $ prefeituraConsutalNota nota)
      let html =  replace ("/sistemas/"::BS.ByteString) ("http://www11.goiania.go.gov.br/sistemas/"::BS.ByteString) . BSL.toStrict  <$> (r ^? responseBody)
      file <- traverse (htmlToPdf (nota )) html
      return $ SBinary <$> file

notaXML ano cgc_cpf nota =
  withOpenSSL $
  Sess.withSessionWith (opensslManagerSettings context) $
    \session -> do
      Sess.get session prefeituraLoginCookie
      pr <- Sess.post session prefeituraLoginFormUrl0 (prefeituraForm ano cgc_cpf)
      r <- Sess.get session (BSC.unpack $ prefeituraConsultaXML nota)
      return . join $ (\i -> if BSC.isPrefixOf "<GerarNfseResposta" i then Just i else Nothing). BSL.toStrict <$> ( r  ^? responseBody)

prefeituraNotaXML  j k l= fmap SBinary <$>  notaXML  j k l

test =do
  let unSBinary (SBinary i) = i
  out <- prefeituraNota "23531045172" "denise17" "245"
  traverse (BS.writeFile "test.pdf" . unSBinary) out

prefeituraNota ano cgc_cpf nota =
    siapi3Page ano cgc_cpf nota

prefeituraForm ::  BS.ByteString -> BS.ByteString -> [FormParam]
prefeituraForm user pass = [
  "SEDETECGOTheme_wt38$block$wtLoginContent$wtUserNameInput":=user,
  "SEDETECGOTheme_wt38$block$wtLoginContent$wtPasswordInput":=pass,
  "SEDETECGOTheme_wt38$block$wtLoginContent$wt8":=("ENTRAR" :: String) ,
  "SEDETECGOTheme_wt38$block$WebPatterns_wt1$block$wt4$wt43$wtCheckbox$wt36":=("on" :: String)
    ]

prefeituraConsultaXML nota = "http://www11.goiania.go.gov.br/sistemas/snfse/asp/snfse00200w2.asp?nota=" <> nota
prefeituraLoginCookie = "http://www10.goiania.go.gov.br/Internet/"
prefeituraLoginFormUrl0 = "http://www10.goiania.go.gov.br/Internet/Login.aspx"
prefeituraLoginFormUrl1 = "http://www11.goiania.go.gov.br/sistemas/saces/asp/saces00005a1.asp"
prefeituraConsutalNota nota = "http://www11.goiania.go.gov.br/sistemas/snfse/asp/snfse00200w0.asp?nota=" <> nota

