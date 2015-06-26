{-# LANGUAGE OverloadedStrings #-}
module Siapi3 where
import Network.Wreq
import qualified Network.Wreq.Session as Sess


import OpenSSL.Session (context)
import Network.HTTP.Client.OpenSSL

import Control.Lens
import Utils
import Control.Applicative
import Control.Monad
import Data.Monoid

import qualified Data.Text as T
import qualified Data.Text.Lazy as TL
import qualified Data.Text.Lazy.Encoding as TL
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC
import qualified Data.ByteString.Lazy.Char8 as BSLC
import qualified Data.ByteString.Lazy as BSL

import qualified Data.List as L

import Gpx

siapi3Page protocolo ano cgc_cpf = do
  withOpenSSL $ Sess.withSessionWith (opensslManagerSettings context) $ \session -> do
    print siapiAndamento3Url
    r <- Sess.get session $ siapiAndamento3Url
    let view =  snd . BS.breakSubstring("ViewState") . BSL.toStrict <$>
           r ^? responseBody
        viewValue = BSC.takeWhile (/='\"') . BS.drop 7 . snd .BS.breakSubstring "value=\"" <$> view
    pr <- traverse (Sess.post session siapiAndamento3Url. protocolocnpjForm protocolo ano cgc_cpf ) viewValue
    print siapiListAndamento3Url
    r <- Sess.get session $  siapiListAndamento3Url
    return $ BSLC.unpack <$>  (r ^? responseBody)


siapi2 protocolo ano = do
          let addrs ="http://siapi.bombeiros.go.gov.br/consulta/consulta_protocolo.php"
          print addrs
          lq <- getWith (defaults & param "protocolo" .~ [T.pack $ BSC.unpack protocolo] & param "ano" .~ [ T.pack $ BSC.unpack ano] ) addrs
          let
            lq2 =  fst .  break (=='&') . concat . tail .  splitL ("php?id=")  .TL.unpack . TL.decodeLatin1   <$>  (lq ^? responseBody)
            addrs_a ="http://siapi.bombeiros.go.gov.br/consulta/consulta_andamento.php"
          tq <-  traverse (\lq2 -> do
                          print addrs_a
                          getWith (defaults & param "id"  .~ [T.pack lq2]) addrs_a) lq2
          let
            i =  TL.unpack .  TL.decodeLatin1 <$> (join $ (^? responseBody) <$> tq)
          traverse readHtml  i


siapi3 protocolo ano cgc_cpf = do
    v <- (siapi3Page protocolo ano cgc_cpf)
    r <- traverse readSiapi3Andamento  v
    return $ liftA2 (,) r ( L.isInfixOf "AGUARDANDO PAGAMENTO DA TAXA" <$> v)


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

testSiapi3 = do
  siapi3 "40277" "15" "17800968000103"


