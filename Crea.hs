{-# LANGUAGE BangPatterns,OverloadedStrings #-}
module Crea where

import Types
import Network.Wreq
import Utils
-- import QueryWidgets
-- import Widgets
import qualified Network.Wreq.Session as Sess


import OpenSSL.Session (context)
import Network.HTTP.Client.OpenSSL

import Control.Lens
import Control.Applicative
import Data.Maybe
import Data.Monoid


import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC
import qualified Data.ByteString.Lazy.Char8 as BSLC
import qualified Data.ByteString.Lazy as BSL

import Gpx
import Debug.Trace

import Data.ByteString.Search (replace)

creaLogin rnp user pass = do
  withOpenSSL $ Sess.withSessionWith (opensslManagerSettings context) $ \session -> do
    -- r <- Sess.get session $ traceShowId creaLoginUrl
    -- print $ r  ^. responseCookieJar
    -- Sess.post session (traceShowId creaLoginUrlPost) ( creaLoginForm rnp user pass )
    cr <- Sess.post session (traceShowId creaArtLoginUrlPost) (creaArtLoginForm rnp user pass)
    --form <- traverse (readInputForm . BSLC.unpack ) (cr ^? responseBody)
    --pr <- (Sess.post session (traceShowId creaSessionUrlPost ) .   creaLoginForm') (fromJust form)
    return (cr ^? responseBody)


creaLoginArt rnp user pass art = do
  withOpenSSL $ Sess.withSessionWith (opensslManagerSettings context) $ \session -> do
    cr <- Sess.post session (traceShowId creaArtLoginUrlPost) ( creaArtLoginForm rnp user pass )
    form <- traverse (readInputForm . BSLC.unpack ) (cr ^? responseBody)
    pr <- (Sess.post session (traceShowId creaSessionUrlPost ) .   creaLoginForm') (fromJust form)
    pr <- Sess.get session $ (traceShowId (creaArtQuery (BSC.unpack art) ))
    let html = (replace (fst replacePath ) (snd replacePath ) . (BSL.toStrict  )) <$> (pr ^? responseBody)
    file <- htmlToPdf art html
    return $ fmap (SBinary  ) $ Just file

creaBoletoArt rnp user pass art = do
  withOpenSSL $ Sess.withSessionWith (opensslManagerSettings context) $ \session -> do
    cr <- Sess.post session (traceShowId creaArtLoginUrlPost) ( creaArtLoginForm rnp user pass )
    form <- traverse (readInputForm . BSLC.unpack ) (cr ^? responseBody)
    pr <- (Sess.post session (traceShowId creaSessionUrlPost ) .   creaLoginForm') (fromJust form)
    pr <- Sess.get session $ (traceShowId (creaArtBoleto (BSC.unpack art) ))
    let Just boleto = BSC.unpack . fst . BSC.break ('\"'==)  . BS.drop 11 . snd . BS.breakSubstring "cod_boleto=" . traceShowId . BSL.toStrict <$> (pr ^? responseBody)
    Sess.get session $ ((creaArtGeraBoleto ( boleto) ))
    bol <- Sess.get session $ (creaTmpBoleto ( boleto) )
    traverse (BSL.writeFile "boleto.pdf") bol
    return (fromJust $ bol ^? responseBody )



creaConsultaArt rnp user pass art = do
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



