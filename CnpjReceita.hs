{-# LANGUAGE TupleSections,LambdaCase,OverloadedStrings #-}
module CnpjReceita where
import Network.Wreq
import qualified Network.Wreq.Session as Sess


import OpenSSL.Session (context)
import Network.HTTP.Client.OpenSSL
import Network.HTTP.Client.TLS
import Network.HTTP.Client (defaultManagerSettings, managerResponseTimeout)

import Control.Lens hiding (element,set,get,(#))
import Control.Applicative
import Data.Char
import Control.Monad
import Data.Maybe
import Data.Monoid

import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC
import qualified Data.ByteString.Lazy.Char8 as BSLC
import qualified Data.ByteString.Lazy as BSL
import Data.Text as T

import Gpx
import Widgets
import Debug.Trace

import Reactive.Threepenny
import qualified Graphics.UI.Threepenny as UI
import Graphics.UI.Threepenny.Core hiding (get,delete)

import qualified Data.ByteString.Base64.Lazy as B64
evalUI el f  = getWindow el >>= \w -> runUI w f


cnpjquery el cpfe = do
  let opts = defaults & manager .~ Left man
      man  = opensslManagerSettings context
  withOpenSSL $ Sess.withSessionWith man $ \session -> do
    ev <- evalUI el (do
          captchaCap <- UI.button # set UI.text "Submit"
          let cap = unsafeMapIO ( traverse (\cgc_cpf ->  do
                  r <- Sess.getWith (opts & param "cnpj" .~ [T.pack $ BSC.unpack cgc_cpf]) session $ traceShowId cnpjhome
                  (^? responseBody) <$> (Sess.get session $ traceShowId cnpjcaptcha))) ( (\case {""-> Nothing ; i -> Just i } )  <$> (facts cpfe <@ UI.click captchaCap ) )
          inpCap <-UI.input # set UI.style [("width","120px")]
          submitCap <- UI.button # set UI.text "Submit"
          capb <- stepper Nothing (join <$> cap)
          capE <- UI.img# sink UI.src ((("data:image/png;base64,"++) . maybe "" (BSLC.unpack.B64.encode)) <$> capb )
          dv<-UI.div
          element el # set UI.children [captchaCap ,capE,dv,inpCap,submitCap]
          binpCap <- stepper "" (UI.valueChange inpCap)
          return ( binpCap <@ UI.click submitCap) )
    let out =  unsafeMapIO (\(cp,captcha) ->  do
          pr <- traverse (Sess.post session (traceShowId cnpjpost) . protocolocnpjForm cp ) (Just $ BSC.pack captcha  )
          pr <- traverse (Sess.post session (traceShowId cnpjpost) . protocolocnpjForm cp ) (Just $ BSC.pack captcha  )
          traverse (readHtmlReceita . BSLC.unpack ) (fromJust pr ^? responseBody)
              ) $ (,) <$> facts cpfe <@> ev
    {-evalUI el (do
          st <- stepper  "" (fmap  show out)
          d <- UI.div # sink UI.html st
          element el #+ [element d])-}
    return out

protocolocnpjForm :: BS.ByteString -> BS.ByteString -> [FormParam]
protocolocnpjForm cgc_cpf captcha
                     = ["origem"  := ("comprovante"::BS.ByteString)
                       ,"cnpj"    := cgc_cpf
                       ,"txtTexto_captcha_serpro_gov_br" := captcha
                       ,"submit1" := ("Consultar" :: BS.ByteString)
                       ,"search_type" := ("cnpj" :: BS.ByteString)
                       ]

cnpjhome  ="http://www.receita.fazenda.gov.br/pessoajuridica/cnpj/cnpjreva/cnpjreva_solicitacao.asp"
cnpjcaptcha = "http://www.receita.fazenda.gov.br/pessoajuridica/cnpj/cnpjreva/captcha/gerarCaptcha.asp"
cnpjpost = "http://www.receita.fazenda.gov.br/pessoajuridica/cnpj/cnpjreva/valida.asp"

test = do
  startGUI defaultConfig (\w -> do
                      e <- UI.div
                      i<-UI.input
                      bhi <- stepper "" (UI.valueChange i)
                      liftIO $ cnpjquery e $ pure "01008713010399"
                      getBody w #+ [element i ,element e]
                      return () )
