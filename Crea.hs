{-# LANGUAGE TupleSections,OverloadedStrings #-}
module Crea where

import Types
import qualified Data.Text as T
import qualified Data.Map as M
import Network.Wreq
import Utils
import Safe
import Pdf
import Control.Exception
import qualified Network.Wreq.Session as Sess
import Control.Monad


import qualified Data.List as L
import RuntimeTypes
import System.Environment
import OpenSSL.Session (context)
import Network.HTTP.Client.OpenSSL

import Control.Lens
import Control.Applicative
import Data.Maybe
import Data.Monoid
import Control.Concurrent.STM.TMVar
import Control.Concurrent.STM.TQueue


import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC
import qualified Data.ByteString.Lazy.Char8 as BSLC
import qualified Data.ByteString.Lazy as BSL

import Gpx
import Debug.Trace

import Data.ByteString.Search (replace)

import Prelude hiding (head)

listTotuple [i] = [([],i)]
listTotuple [i,j] = [(i,j)]
listTotuple [i,j,k] = [(i,j),([],k)]
listTotuple [i,j,k,l] = [(i,j),(k,l)]
listTotuple i = []


creaLogin rnp user pass =
  withOpenSSL $ Sess.withSessionWith (opensslManagerSettings context) $ \session -> do
  -- r <- Sess.get session $ traceShowId creaLoginUrl
  -- print $ r  ^. responseCookieJar
  -- Sess.post session (traceShowId creaLoginUrlPost) ( creaLoginForm rnp user pass )
  cr <- Sess.post session (traceShowId creaArtLoginUrlPost) (creaArtLoginForm rnp user pass)
  --form <- traverse (readInputForm . BSLC.unpack ) (cr ^? responseBody)
  --pr <- (Sess.post session (traceShowId creaSessionUrlPost ) .   creaLoginForm') (fromJust form)
  return (cr ^? responseBody)

creaArtdata :: BS.ByteString -> BS.ByteString -> BS.ByteString -> BS.ByteString -> IO [ M.Map String String]
creaArtdata rnp user pass art =
  withOpenSSL $ Sess.withSessionWith (opensslManagerSettings context) $ \session -> do
  cr <- Sess.post session (traceShowId creaArtLoginUrlPost) ( creaArtLoginForm rnp user pass )
  form <- traverse (readInputForm . BSLC.unpack ) (cr ^? responseBody)
  _ <- (Sess.post session (traceShowId creaSessionUrlPost ) .   creaLoginForm') (fromJust form)
  pr <- Sess.get session (traceShowId (creaArtQuery (BSC.unpack art) ))
  let index = fmap ((M.fromList . concatMap listTotuple) . concat )
  (index . join .maybeToList) Control.Applicative.<$> traverse (fmap (concat . concat) . readArt . BSLC.unpack) (pr ^? responseBody)


creaLoginArt rnp user pass art =
  withOpenSSL $ Sess.withSessionWith (opensslManagerSettings context) $ \session -> do
  cr <- Sess.post session (traceShowId creaArtLoginUrlPost) ( creaArtLoginForm rnp user pass )
  form <- traverse (readInputForm . BSLC.unpack ) (cr ^? responseBody)
  pr <- (Sess.post session (traceShowId creaSessionUrlPost ) .   creaLoginForm') (fromJust form)
  pr <- Sess.get session (traceShowId (creaArtQuery (BSC.unpack art) ))
  let html = (uncurry replace replacePath . BSL.toStrict) <$> (pr ^? responseBody)
  file <- traverse (htmlToPdf art) html
  return $ SBinary Control.Applicative.<$> file

creaBoletoArt rnp user pass art =
  withOpenSSL $ Sess.withSessionWith (opensslManagerSettings context) $ \session -> do
  cr <- Sess.post session (traceShowId creaArtLoginUrlPost) ( creaArtLoginForm rnp user pass )
  form <- traverse (readInputForm . BSLC.unpack ) (cr ^? responseBody)
  pr <- (Sess.post session (traceShowId creaSessionUrlPost ) .   creaLoginForm') (fromJust form)
  pr <- Sess.get session (traceShowId (creaArtBoleto (BSC.unpack art) ))
  let Just boleto = BSC.unpack . fst . BSC.break ('\"'==)  . BS.drop 11 . snd . BS.breakSubstring "cod_boleto=" . traceShowId . BSL.toStrict <$> (pr ^? responseBody)
  Sess.get session (creaArtGeraBoleto ( boleto) )
  bol <- Sess.get session (creaTmpBoleto boleto )
  traverse (BSL.writeFile "boleto.pdf") bol
  return (fromJust $ bol ^? responseBody )

creaConsultaArt rnp user pass art =
  withOpenSSL $ Sess.withSessionWith (opensslManagerSettings context) $ \session -> do
  cr <- Sess.post session (traceShowId creaArtLoginUrlPost) ( creaArtLoginForm rnp user pass )
  form <- traverse (readInputForm . BSLC.unpack ) (cr ^? responseBody)
  (Sess.post session (traceShowId creaSessionUrlPost ) .   creaLoginForm') (fromJust form)
  pr <- Sess.get session (traceShowId (creaArtHistorico (BSC.unpack art) ))
  concat .concat. maybeToList <$> traverse readCreaHistoricoHtml (BSLC.unpack .replace (fst replacePath ) (snd replacePath ) . (BSL.toStrict  ) <$> (pr ^? responseBody))



creaSituacaoListPage rnp user pass status page =
  withOpenSSL $ Sess.withSessionWith (opensslManagerSettings context) $ \session -> do
  cr <- Sess.post session (traceShowId creaArtLoginUrlPost) ( creaArtLoginForm rnp user pass )
  form <- traverse (readInputForm . BSLC.unpack ) (cr ^? responseBody)
  (Sess.post session (traceShowId creaSessionUrlPost ) .   creaLoginForm') (fromJust form)
  concat <$> mapM (\ix -> do
    pr <- Sess.get session (traceShowId (creaArtList status ix ))
    fmap (drop 1) . tail . concat .concat. maybeToList <$> traverse readCreaHistoricoHtml (BSLC.unpack .replace (fst replacePath ) (snd replacePath ) . (BSL.toStrict  ) <$> (pr ^? responseBody))) page



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


creaArtList situacao page =  "http://www.crea-go.org.br/art1025/cadastros/ajax_lista_arts.php?SITUACAO_DA_ART="<> show situacao <> "&pg=" <> show page


convertArt :: [M.Map String String ]-> TBData T.Text Showable
convertArt v =
  tblist
  [numberA "substituida" $ join $ fmap (fmap (L.drop 2 .dropWhile (/= 'à')) .L.find ("Substituição à" `L.isInfixOf`) .  concatMap (\(i,j) -> [i,j]) . M.toList ) v `atMay` 0
  -- ,numberA "contrato" $ at 2 "Contrato:"
  ,textA "cpf_cnpj" $ filter (not . (`L.elem` (" /-." ::String))) <$> at 2 "CPF/CNPJ:"
  ,textA "contratante" $  at 2 "Contratante:"
  ]
  where at ix k = join $ M.lookup k <$> v `atMay` ix
        textA k = Attr k . LeftTB1 . fmap (TB1 . SText . T.pack  )
        numberA k = Attr k . LeftTB1 . join . fmap (fmap (TB1 . SNumeric ). join . fmap clean .readMay )
          where
            clean i
              | i == 0 = Nothing
              | i < 50 = Nothing
              | otherwise = Just i



replacePath :: (BSC.ByteString,BSC.ByteString)
replacePath = ("/art1025"  , "http://www.crea-go.org.br/art1025")

{-
testCrea = do
  args <- getArgs
  Just rnp <- lookupEnv "CREA_RNP"
  Just user <- lookupEnv "CREA_USER"
  Just pass <- lookupEnv "CREA_PASS"
  -- v <- creaArtdata (BSC.pack rnp) (BSC.pack user) (BSC.pack pass) "1020150180152"
  -- conn <- connectPostgreSQL (connRoot (argsToState (tail (tail args))))
  -- traverse ((`catch` (\e -> return $ traceShow (e :: SomeException ) 0) ) . execute conn "UPDATE incendio.art SET contrato = ? where art_number = ?") (contrato v)


  v <- fmap (head ) <$> creaSituacaoListPage (BSC.pack rnp) (BSC.pack user) (BSC.pack pass) 20 [0]
  conn <- connectPostgreSQL (connRoot (argsToState (tail (tail args))))
  mapM ((`catch` (\e -> return $ traceShow (e :: SomeException ) 0) ) . execute conn "INSERT INTO incendio.art (art_number,crea_register) values (?,?)" . (,rnp) ) v
-}


