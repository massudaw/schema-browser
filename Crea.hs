{-# LANGUAGE OverloadedStrings #-}
module Crea where
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
import Data.ByteString.Base64.Lazy as BS64

import Gpx
import Debug.Trace

import Reactive.Threepenny
import qualified Graphics.UI.Threepenny as UI
import Graphics.UI.Threepenny.Core hiding (get,delete)
import Data.ByteString.Search (replace)

creaLogin rnp user pass = do
  let opts = defaults & manager .~ Left (opensslManagerSettings context)
  withOpenSSL $ Sess.withSessionWith (opensslManagerSettings context) $ \session -> do
    -- r <- Sess.get session $ traceShowId creaLoginUrl
    -- print $ r  ^. responseCookieJar
    -- Sess.post session (traceShowId creaLoginUrlPost) ( creaLoginForm rnp user pass )
    cr <- Sess.post session (traceShowId creaArtLoginUrlPost) (creaArtLoginForm rnp user pass)
    --form <- traverse (readInputForm . BSLC.unpack ) (cr ^? responseBody)
    --pr <- (Sess.post session (traceShowId creaSessionUrlPost ) .   creaLoginForm') (fromJust form)
    return (cr ^? responseBody)

creaLoginArt rnp user pass art = do
  let opts = defaults & manager .~ Left (opensslManagerSettings context)
  withOpenSSL $ Sess.withSessionWith (opensslManagerSettings context) $ \session -> do
    cr <- Sess.post session (traceShowId creaArtLoginUrlPost) ( creaArtLoginForm rnp user pass )
    form <- traverse (readInputForm . BSLC.unpack ) (cr ^? responseBody)
    pr <- (Sess.post session (traceShowId creaSessionUrlPost ) .   creaLoginForm') (fromJust form)
    pr <- Sess.get session $ (traceShowId (creaArtQuery (BSC.unpack art) ))
    return $ BSLC.unpack .(replace (fst replacePath ) (snd replacePath ) . (BSL.toStrict  )) <$> (pr ^? responseBody)

creaBoletoArt rnp user pass art = do
  let opts = defaults & manager .~ Left (opensslManagerSettings context)
  withOpenSSL $ Sess.withSessionWith (opensslManagerSettings context) $ \session -> do
    cr <- Sess.post session (traceShowId creaArtLoginUrlPost) ( creaArtLoginForm rnp user pass )
    form <- traverse (readInputForm . BSLC.unpack ) (cr ^? responseBody)
    pr <- (Sess.post session (traceShowId creaSessionUrlPost ) .   creaLoginForm') (fromJust form)
    pr <- Sess.get session $ (traceShowId (creaArtBoleto (BSC.unpack art) ))
    let Just boleto = BSC.unpack . fst . BSC.break ('\"'==)  . BS.drop 11 . snd . BS.breakSubstring "cod_boleto=" . traceShowId . BSL.toStrict <$> (pr ^? responseBody)
    Sess.get session $ (traceShowId (creaArtGeraBoleto ( boleto) ))
    return (creaTmpBoleto ( boleto) )



creaConsultaArt rnp user pass art = do
  let opts = defaults & manager .~ Left (opensslManagerSettings context)
  withOpenSSL $ Sess.withSessionWith (opensslManagerSettings context) $ \session -> do
    cr <- Sess.post session (traceShowId creaArtLoginUrlPost) ( creaArtLoginForm rnp user pass )
    form <- traverse (readInputForm . BSLC.unpack ) (cr ^? responseBody)
    (Sess.post session (traceShowId creaSessionUrlPost ) .   creaLoginForm') (fromJust form)
    pr <- Sess.get session $ (traceShowId (creaArtHistorico (BSC.unpack art) ))
    concat .concat. maybeToList <$> (traverse readCreaHistoricoHtml $  BSLC.unpack .(replace (fst replacePath ) (snd replacePath ) . (BSL.toStrict  )) <$> (pr ^? responseBody))



creaLoginUrl = "http://www.crea-go.org.br/art1025/cadastros/login.php"
creaLoginUrlPost = "http://www.crea-go.org.br/cgi-binn/creanet1025.cgi"
creaArtLoginUrlPost = "http://www.crea-go.org.br/cgi-binn/login_art1025.cgi"
creaSessionUrlPost = "http://www.crea-go.org.br/art1025/funcoes/inicia_sessao.php"
creaArtLoginForm :: BS.ByteString ->BS.ByteString ->BS.ByteString  -> [FormParam]
creaArtLoginForm npn user pass = ["rnp"  := npn
                              ,"usr" := user
                              ,"sell" := pass
                              ,"tipo" := ("ART On-Line" :: BS.ByteString )]
creaLoginForm' :: [(String,String)] ->  [FormParam]
creaLoginForm' npn = fmap (\(i,j) -> BSC.pack i := j ) npn

creaLoginForm :: BS.ByteString ->BS.ByteString ->BS.ByteString  -> [FormParam]
creaLoginForm npn user pass = ["rnp"  := npn
                              ,"usuario" := user
                              ,"senha" := pass]



creaArtQuery art = "http://www.crea-go.org.br/art1025/funcoes/form_impressao.php?NUMERO_DA_ART=" <> art
creaArtHistorico art = "http://www.crea-go.org.br/art1025/cadastros/historico_art.php?NUMERO_DA_ART=" <> art
creaArtBoleto art = "http://www.crea-go.org.br/art1025/cadastros/consulta_boleto_art.php?NUMERO_DA_ART=" <> art
creaArtGeraBoleto boleto = "http://www.crea-go.org.br/art1025/funcoes/gera_pdf.php?cod_boleto=" <> boleto
creaTmpBoleto boleto = "http://www.crea-go.org.br/guia/tmp/" <> boleto <> ".pdf"



replacePath :: (BSC.ByteString,BSC.ByteString)
replacePath = ("/art1025"  , "http://www.crea-go.org.br/art1025")

mainTest = do
  -- i <- creaLogin "1009533630" "Denise" "5559"
  startGUI defaultConfig {tpPort = Just 8000} (\w -> do
                      i <- liftIO $ creaBoletoArt "1009533630" "Denise" "5559" "1020150028082"
                      -- liftIO $ traverse (writeFile "creaLogged.html") i
                      e1 <- pdfFrame (pure $  i)
                      getBody w #+ [UI.element e1]
                      return () )

pdfFrame pdf = mkElement "iframe" UI.# sink UI.src   pdf  UI.# UI.set style [("width","100%"),("height","300px")]
