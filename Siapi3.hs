{-# LANGUAGE OverloadedStrings #-}
module Siapi3 where
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

import Gpx

siapi3 protocolo ano cgc_cpf = do
  let opts = defaults & manager .~ Left (opensslManagerSettings context)
  withOpenSSL $ Sess.withSessionWith (opensslManagerSettings context) $ \session -> do
    r <- Sess.get session siapiAndamento3Url
    let view =  snd . BS.breakSubstring("ViewState") . BSL.toStrict <$>
           r ^? responseBody
        viewValue = BSC.takeWhile (/='\"') . BS.drop 7 . snd .BS.breakSubstring "value=\"" <$> view
    pr <- traverse (Sess.post session siapiAndamento3Url. protocolocnpjForm protocolo ano cgc_cpf ) viewValue
    r <- Sess.get session siapiListAndamento3Url
    traverse (readSiapi3Andamento . BSLC.unpack  ) (r ^? responseBody)

protocolocnpjForm :: BS.ByteString ->BS.ByteString ->BS.ByteString ->BS.ByteString -> [FormParam]
protocolocnpjForm prot ano cgc_cpf vv = ["javax.faces.partial.ajax"  := ("true"::BS.ByteString)
                       ,"javax.faces.source" := ("formPaginaInicialWeb:botaoPesquisarWeb" ::BS.ByteString)
                       ,"javax.faces.partial.execute" :=("formPaginaInicialWeb:botaoPesquisarWeb formPaginaInicialWeb:protocoloWeb formPaginaInicialWeb:cpfCnpjWeb" ::BS.ByteString)
                       ,("javax.faces.partial.render"::BSC.ByteString):=("formPaginaInicialWeb:msgensGeral" ::BS.ByteString)
                       ,("formPaginaInicialWeb:botaoPesquisarWeb"::BSC.ByteString):=("formPaginaInicialWeb:botaoPesquisarWeb" ::BS.ByteString)
                       ,("formPaginaInicialWeb"::BSC.ByteString):=("formPaginaInicialWeb":: BS.ByteString)
                       ,("formPaginaInicialWeb:protocoloWeb"::BSC.ByteString) := (prot <> "/" <> ano )
                       ,("formPaginaInicialWeb:cpfCnpjWeb" ::BSC.ByteString):= (cgc_cpf )
                       ,("javax.faces.ViewState"::BSC.ByteString):=vv
                       ]

siapiAndamento3Url = "https://siapi3.bombeiros.go.gov.br/paginaInicialWeb.jsf"
siapiListAndamento3Url = "https://siapi3.bombeiros.go.gov.br/listarAndamentosWeb.jsf"
