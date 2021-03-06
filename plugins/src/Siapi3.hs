{-# LANGUAGE OverloadedStrings #-}

module Siapi3 where

import Network.Wreq
import qualified Network.Wreq.Session as Sess
import Safe
import Control.Concurrent.Async
import Control.Monad.IO.Class
import OpenSSL.Session (context)
import Network.HTTP.Client.OpenSSL
import Control.Lens
import Utils
import Control.Applicative
import Data.Maybe
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
import Debug.Trace
import Gpx

siapi3Page protocolo ano cgc_cpf =
    withOpenSSL $
    Sess.withSessionWith (opensslManagerSettings context) $
    \session -> do
        print siapiAndamento3Url
        r <- Sess.get session siapiAndamento3Url
        let view =
                snd . BS.breakSubstring "ViewState" . BSL.toStrict <$>
                r ^? responseBody
            viewValue =
                BSC.takeWhile (/= '\"') .
                BS.drop 7 . snd . BS.breakSubstring "value=\"" <$>
                view
        print siapiAndamento3Url
        pr <-
            traverse
                (Sess.post session siapiAndamento3Url .
                 protocolocnpjForm protocolo ano cgc_cpf)
                viewValue
        print siapiListAndamento3Url
        r <- Sess.get session siapiListAndamento3Url
        o <- do
          (l,v) <- readSiapi3Andamento (BSLC.unpack $ justError "no response" $ r ^? responseBody)
          print siapiListAndamento3Url
          res <- Sess.post session siapiListAndamento3Url  (nextPage $ justError "no view " $safeHead v )
          (l2,v) <- readSiapi3AndamentoAJAX (BSLC.unpack $  justError "no response" $ res ^? responseBody)
          return (l<> (concat . maybeToList . fmap safeTail . safeHead $ l2))

        return $
          liftA2 (,) (Just o) (L.isInfixOf "AGUARDANDO PAGAMENTO DA TAXA" . BSLC.unpack <$> (r ^? responseBody))

siapi2 protocolo ano = do
    let addrs =
            "http://siapi.bombeiros.go.gov.br/consulta/consulta_protocolo.php"
    print addrs
    lq <-
        getWith
            (defaults & param "protocolo" .~ [T.pack $ BSC.unpack protocolo] &
             param "ano" .~
             [T.pack $ BSC.unpack ano])
            addrs
    let lq2 =
            takeWhile (/= '&') .
            concat . tail . splitL "php?id=" . TL.unpack . TL.decodeLatin1 <$>
            (lq ^? responseBody)
        addrs_a =
            "http://siapi.bombeiros.go.gov.br/consulta/consulta_andamento.php"
    print addrs_a
    ptq <-
        async $
        traverse
            (\lq2 -> getWith (defaults & param "id" .~ [T.pack lq2]) addrs_a)
            lq2
    let addrs_s =
            "http://siapi.bombeiros.go.gov.br/consulta/consulta_solicitacao.php"
    print addrs_s
    ptqs <-
        async $
        traverse
            (\lq2 -> getWith (defaults & param "id" .~ [T.pack lq2]) addrs_s)
            lq2
    (tq,tqs) <- waitBoth ptq ptqs
    let is = TL.unpack . TL.decodeLatin1 <$> join ((^? responseBody) <$> tqs)
        ia = TL.unpack . TL.decodeLatin1 <$> join ((^? responseBody) <$> tq)
    vs <- traverse readHtml is
    va <- traverse readHtml ia
    let rem ts =
            L.filter
                (not . all (`elem` ("\n\r\t " :: String)))
                (fmap (L.filter (not . (`elem` ("\"\\" :: String)))) ts)
        split4 ts =
            if L.length ts == 4
                then [L.take 2 ts, L.drop 2 ts]
                else [ts]
    return
        ( fmap
              ((\[i,j] ->
                     (i, j)) .
               L.take 2) .
          L.filter ((== 2) . L.length) .
          concatMap (split4 . rem) . concat <$>
          vs
        , fmap rem . tailEmpty . concat <$> va)

tailEmpty [] = []
tailEmpty i = tail i

siapi3 protocolo ano cgc_cpf =
    siapi3Page protocolo ano cgc_cpf

nextPage :: String
                  -> [FormParam]
nextPage viewState =
  ["javax.faces.partial.ajax" := ("true":: BS.ByteString)
  ,"javax.faces.source:formListaDeAndamentos":=("tabela":: BS.ByteString)
  ,"javax.faces.partial.execute":=("formListaDeAndamentos:tabela":: BS.ByteString)
  ,"javax.faces.partial.render":=("formListaDeAndamentos:tabela":: BS.ByteString)
  ,"formListaDeAndamentos:tabela":=("formListaDeAndamentos:tabela":: BS.ByteString)
  ,"formListaDeAndamentos:tabela_pagination":=("true":: BS.ByteString)
  ,"formListaDeAndamentos:tabela_first":=(15::Int)
  ,"formListaDeAndamentos:tabela_rows":=(15::Int)
  ,"formListaDeAndamentos:tabela_encodeFeature":=("true":: BS.ByteString)
  ,"formListaDeAndamentos":=("formListaDeAndamentos":: BS.ByteString)
  ,"javax.faces.ViewState":=viewState
  ]
protocolocnpjForm :: BS.ByteString
                  -> BS.ByteString
                  -> BS.ByteString
                  -> BS.ByteString
                  -> [FormParam]
protocolocnpjForm prot ano cgc_cpf vv =
    [ "javax.faces.partial.ajax" := ("true" :: BS.ByteString)
    , "javax.faces.source" :=
      ("formPaginaInicialWeb:tabViewHome:botaoPesquisarWeb" :: BS.ByteString)
    , "javax.faces.partial.execute" :=
      ("formPaginaInicialWeb:tabViewHome:botaoPesquisarWeb formPaginaInicialWeb:tabViewHome:protocoloWeb formPaginaInicialWeb:tabViewHome:cpfCnpjWeb" :: BS.ByteString)
    , ("javax.faces.partial.render" :: BSC.ByteString) :=
      ("formPaginaInicialWeb:tabViewHome:msgensGeral" :: BS.ByteString)
    , ("formPaginaInicialWeb:tabViewHome:botaoPesquisarWeb" :: BSC.ByteString) :=
      ("formPaginaInicialWeb:tabViewHome:botaoPesquisarWeb" :: BS.ByteString)
    , ("formPaginaInicialWeb" :: BSC.ByteString) :=
      ("formPaginaInicialWeb" :: BS.ByteString)
    , ("formPaginaInicialWeb:tabViewHome:protocoloWeb" :: BSC.ByteString) :=
      (prot <> "/" <> ano)
    , ("formPaginaInicialWeb:tabViewHome:cpfCnpjWeb" :: BSC.ByteString) := cgc_cpf
    , ("javax.faces.ViewState" :: BSC.ByteString) := vv]

siapiAndamento3Url =
    "http://siapi3.bombeiros.go.gov.br/paginaInicialWeb.jsf"

siapiListAndamento3Url =
    "http://siapi3.bombeiros.go.gov.br/listarAndamentosWeb.jsf"



