{-# LANGUAGE OverloadedStrings #-}
module PrefeituraSNFSE where
import Network.Wreq
import qualified Network.Wreq.Session as Sess


import OpenSSL.Session (context)
import Network.HTTP.Client.OpenSSL
import Network.HTTP.Client.TLS
import Network.HTTP.Client (defaultManagerSettings, managerResponseTimeout)

import Control.Lens
import Control.Applicative
import Data.Char
import Control.Monad
import Data.Maybe
import Data.Monoid

import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC
import qualified Data.ByteString.Lazy.Char8 as BSLC
import qualified Data.ByteString.Lazy as BSL
import Data.ByteString.Search (replace)

import qualified Data.List as L

import Gpx
import Debug.Trace

siapi3Page protocolo ano cgc_cpf nota = do
  let opts = defaults & manager .~ Left (opensslManagerSettings context)
  withOpenSSL $ Sess.withSessionWith (opensslManagerSettings context) $ \session -> do
    Sess.get session $ traceShowId  prefeituraLoginCookie
    pr <- Sess.post session (traceShowId prefeituraLoginFormUrl) (prefeituraForm protocolo ano cgc_cpf)
    print (pr ^? responseBody)
    r <- Sess.get session $ traceShowId $ (BSC.unpack $ prefeituraConsutalNota nota)
    return $ BSLC.unpack .(replace ("/sistemas/"::BS.ByteString) ("http://www2.goiania.go.gov.br/sistemas/"::BS.ByteString). BSL.toStrict ) <$> (r ^? responseBody)


prefeituraNota protocolo ano cgc_cpf nota = do
    siapi3Page protocolo ano cgc_cpf nota

prefeituraForm :: BS.ByteString -> BS.ByteString -> BS.ByteString -> [FormParam]
prefeituraForm inscricao user pass  = [ "txt_nr_inscricao" := inscricao
                                  , "txt_nr_usuario" := user
                                  , "txt_info_senha" := pass
                                  ]

prefeituraLoginCookie = "http://www2.goiania.go.gov.br/sistemas/saces/asp/saces00000f5.asp?sigla=snfse"
prefeituraLoginFormUrl ="http://www2.goiania.go.gov.br/sistemas/saces/asp/saces00005a1.asp"
prefeituraConsutalNota nota = "http://www2.goiania.go.gov.br/sistemas/snfse/asp/snfse00200w0.asp?nota=" <> nota



