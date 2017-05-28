{-# LANGUAGE OverloadedStrings #-}
module PrefeituraSNFSE where
import Network.Wreq
import qualified Network.Wreq.Session as Sess


-- import Widgets
import Types
import Utils
import Pdf
import Gpx

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

siapi3Page protocolo ano cgc_cpf nota = do
  withOpenSSL $
    Sess.withSessionWith (opensslManagerSettings context) $
      \session -> do
        Sess.get session $ traceShowId  prefeituraLoginCookie
        pr <- Sess.post session (traceShowId prefeituraLoginFormUrl) (prefeituraForm protocolo ano cgc_cpf)
        print (pr ^? responseBody)
        r <- Sess.get session $ traceShowId $ (BSC.unpack $ prefeituraConsutalNota nota)
        let html =  (replace ("/sistemas/"::BS.ByteString) ("http://www11.goiania.go.gov.br/sistemas/"::BS.ByteString). BSL.toStrict ) <$> (r ^? responseBody)
        file <- traverse (htmlToPdf (nota <> protocolo) ) html
        return $ SBinary  <$> file

notaXML protocolo ano cgc_cpf nota = do
  withOpenSSL $
    Sess.withSessionWith (opensslManagerSettings context) $
      \session -> do
        Sess.get session $ prefeituraLoginCookie
        pr <- Sess.post session prefeituraLoginFormUrl (prefeituraForm protocolo ano cgc_cpf)
        r <- Sess.get session $ (BSC.unpack $ prefeituraConsultaXML nota)
        return $ BSL.toStrict <$> ( r  ^? responseBody)

prefeituraNotaXML i j k l= fmap SBinary <$>  notaXML i j k l

prefeituraNota protocolo ano cgc_cpf nota = do
    siapi3Page protocolo ano cgc_cpf nota

prefeituraForm :: BS.ByteString -> BS.ByteString -> BS.ByteString -> [FormParam]
prefeituraForm inscricao user pass =
    [ "txt_nr_inscricao" := inscricao
    , "txt_nr_usuario" := user
    , "txt_info_senha" := pass
    ]

prefeituraConsultaXML nota = "http://www11.goiania.go.gov.br/sistemas/snfse/asp/snfse00200w2.asp?nota=" <> nota
prefeituraLoginCookie = "http://www11.goiania.go.gov.br/sistemas/saces/asp/saces00000f5.asp?sigla=snfse"
prefeituraLoginFormUrl ="http://www11.goiania.go.gov.br/sistemas/saces/asp/saces00005a1.asp"
prefeituraConsutalNota nota = "http://www11.goiania.go.gov.br/sistemas/snfse/asp/snfse00200w0.asp?nota=" <> nota

test = do
  out <- notaXML "1553542" "1" "denise17" "101"
  traverse (BSC.writeFile "test-nota.xml") out

