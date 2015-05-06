{-# LANGUAGE FlexibleContexts,TupleSections,LambdaCase,OverloadedStrings #-}
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
import Data.Functor.Compose
import Data.Functor.Identity
import Control.Concurrent.Async
import Control.Concurrent

import qualified Data.List as L

import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC
import qualified Data.ByteString.Lazy.Char8 as BSLC
import qualified Data.ByteString.Lazy as BSL
import qualified Data.Text as T
import qualified Data.Traversable as Tra
import qualified Data.Text.Lazy as TL

import Safe
import Query
import Schema
import Widgets
import QueryWidgets
import Gpx
import Widgets
import Debug.Trace

import Reactive.Threepenny
import qualified Graphics.UI.Threepenny as UI
import Graphics.UI.Threepenny.Core hiding (get,delete)

import qualified Data.ByteString.Base64.Lazy as B64
import Control.Monad.Reader
import qualified Data.Foldable as F


getInp :: TL.Text -> [(Key,Showable)] -> Maybe BSC.ByteString
getInp l  = join . fmap (fmap (BSL.toStrict . BSLC.pack . TL.unpack . (\(SText t)-> t )) . unRSOptional' . snd) . L.find ((==l) . keyValue . fst)

cpfCall = WrappedCall initCnpj [getCaptchaCpf',getCpf']

getCaptchaCpf' ::
     a -> InformationSchema -> MVar (Maybe (TB1 (Key, Showable))) ->   (Maybe (TB1 (Key,Showable)) -> ReaderT Sess.Session IO () ) -> ReaderT Sess.Session IO ()
getCaptchaCpf' _ inf i  handler = do
  rv <- ask
  liftIO $ forkIO $ runReaderT  (forever $ do
      liftIO $ print "tryTakeMVAR Captcha"
      mvar <- liftIO $takeMVar i
      out <- ( fmap join . Tra.traverse getCaptchaCpfShowable $traceShowId $ traceShow "takeMVar" mvar)
      let nkey = lookFresh inf "CPF Receita" "owner" "captchaViewer"
      handler . fmap (TB1 .KV (PK [][]) . pure . Compose. Identity . Attr. (nkey ,) . SBinary  . BSL.toStrict ) $ out
      return ()) rv
  return ()


getCaptchaCpf cgc_cpf  = do
     session <- ask
     liftIO $ do
       r <-  Sess.getWith (defaults & param "cpf" .~ [T.pack $ BSC.unpack cgc_cpf]) session $ traceShowId cpfhome
       (^? responseBody) <$> (Sess.get session $ traceShowId cpfcaptcha)
getCaptchaCpfShowable tinput =
      let input = F.toList tinput
      in fmap join $ Tra.sequence $  fmap getCaptchaCpf  (getInp "cpf_number" input)


getCpf' ::
     a -> InformationSchema -> MVar (Maybe (TB1 (Key, Showable))) ->   (Maybe (TB1 (Key,Showable)) -> ReaderT Sess.Session IO () ) -> ReaderT Sess.Session IO ()
getCpf' _ inf i  handler = do
  rv <- ask
  liftIO $ forkIO $ runReaderT (forever $ do
      liftIO $ print "tryTakeMVAR Cpf"
      mvar <- liftIO $ takeMVar i
      out <- fmap (join . fmap headMay.join) . Tra.traverse getCpfShowable $traceShowId $ traceShow "takeMVar" mvar
      liftIO $ print out
      let name = lookKey inf "owner" "owner_name"
      handler . fmap (TB1 .KV (PK [][]) . pure . Compose. Identity . Attr. (name ,) . SOptional .Just . SText . TL.pack ) $ out
      return ()) rv
  return ()

getCpfShowable tinput = fmap join $ Tra.sequence $  liftA2 getCpf (getInp "captchaInput" input ) (getInp "cpf_number" input)
  where input = F.toList tinput
getCpf captcha cgc_cpf = do
    session <- ask
    liftIO $ do
          pr <- traverse (Sess.post session (traceShowId cpfpost) . protocolocpfForm cgc_cpf ) (Just $  captcha  )
          traverse (BSL.writeFile "cpf_name.html" ) (join $ fmap (^? responseBody)  pr)
          traverse (readCpfName . BSLC.unpack ) (fromJust pr ^? responseBody)

wrapplug = WrappedCall initCnpj [getCaptcha',getCnpj']

initCnpj   =  (\i -> do
  let opts = defaults & manager .~ Left man
      man  = opensslManagerSettings context
  withOpenSSL $ Sess.withSessionWith man i) . runReaderT


getCaptcha cgc_cpf  = do
     session <- ask
     liftIO $ do
       r <-  Sess.getWith (defaults & param "cnpj" .~ [T.pack $ BSC.unpack cgc_cpf]) session $ traceShowId cnpjhome
       (^? responseBody) <$> (Sess.get session $ traceShowId cnpjcaptcha)
getCaptchaShowable tinput =
      let input = F.toList tinput
      in fmap join $ Tra.sequence $  fmap getCaptcha  (getInp "cnpj_number" input)


getCaptcha' ::
     a -> InformationSchema -> MVar (Maybe (TB1 (Key, Showable))) ->   (Maybe (TB1 (Key,Showable)) -> ReaderT Sess.Session IO () ) -> ReaderT Sess.Session IO ()
getCaptcha' _ inf i  handler = do
  rv <- ask
  liftIO $ forkIO $ runReaderT  (forever $ do
      liftIO $ print "tryTakeMVAR Captcha"
      mvar <- liftIO $takeMVar i
      out <- ( fmap join . Tra.traverse getCaptchaShowable $traceShowId $ traceShow "takeMVar" mvar)
      let nkey = lookFresh inf "CNPJ Receita" "owner" "captchaViewer"
      handler . fmap (TB1 .KV (PK [][]) . pure . Compose. Identity . Attr. (nkey ,) . SBinary  . BSL.toStrict ) $ out
      return ()) rv
  return ()



getCnpj' ::
     a -> InformationSchema -> MVar (Maybe (TB1 (Key, Showable))) ->   (Maybe (TB1 (Key,Showable)) -> ReaderT Sess.Session IO () ) -> ReaderT Sess.Session IO ()
getCnpj' _ inf i  handler = do
  rv <- ask
  liftIO $ forkIO $ runReaderT (forever $ do
      liftIO $ print "tryTakeMVAR Cnpj "
      mvar <- liftIO $ takeMVar i
      out <- fmap join . Tra.traverse getCnpjShowable $traceShowId $ traceShow "takeMVar" mvar
      liftIO $ print out
      -- handler . fmap (TB1 .KV (PK [][]) . pure . Compose. Identity . Attr. (,) . SText . TL.pack. BSLC.unpack) $ out
      return ()) rv
  return ()







getCnpjShowable tinput = fmap join $ Tra.sequence $  liftA2 getCnpj (getInp "captchaInput" input ) (getInp "cnpj_number" input)
  where input = F.toList tinput
getCnpj captcha cgc_cpf = do
    session <- ask
    liftIO $ do
          pr <- traverse (Sess.post session (traceShowId cnpjpost) . protocolocnpjForm cgc_cpf ) (Just $  captcha  )
          traverse (readHtmlReceita . BSLC.unpack ) (fromJust pr ^? responseBody)


cnpjquery el cpfe = do
    let opts = defaults & manager .~ Left man
        man  = opensslManagerSettings context
    (captcha,hcaptcha) <- liftIO $ newEvent
    (precaptcha,prehcaptcha) <- liftIO $ newEvent
    (result,hresult) <- liftIO $ newEvent
    inpCap <-UI.input # set UI.style [("width","120px")]
    submitCap <- UI.button # set UI.text "Submit"
    capb <- stepper Nothing captcha
    cappreb <- stepper "" precaptcha
    capE <- UI.div
        -- Loading Gif
        # sink items (pure. const (UI.img # set UI.src ("static/ajax-loader.gif" )   )<$>  cappreb)
        -- Captcha
        # sink items (pure. const (UI.img # sink UI.src ((("data:image/png;base64,"++) . maybe "" (BSLC.unpack.B64.encode)) <$> capb ) )   <$>  capb)
    dv <-UI.div
    element el # set UI.children [capE,dv,inpCap,submitCap]
    binpCap <- stepper "" (UI.valueChange inpCap)
    liftIO $ withOpenSSL $ Sess.withSessionWith man $ \session -> do
        evalUI el $ do
            UI.onEvent (rumors cpfe) (liftIO . traverse (\cgc_cpf ->  do
                i <- forkIO $ (do
                              r <- Sess.getWith (opts & param "cnpj" .~ [T.pack $ BSC.unpack cgc_cpf]) session $ traceShowId cnpjhome
                              (^? responseBody) <$> (Sess.get session $ traceShowId cnpjcaptcha)
                              ) >>= hcaptcha
                prehcaptcha ("Carregando Captcha em " <> show i)
                    ))
            UI.onEvent ((,) <$> facts cpfe <@> (binpCap <@ UI.click submitCap)) (liftIO . forkIO . (\(cp,captcha) ->  do
                pr <- (Sess.post session (traceShowId cnpjpost) . protocolocnpjForm (fromJust cp) ) (BSC.pack captcha  )
                v <- traverse (readHtmlReceita . BSLC.unpack ) (pr ^? responseBody)
                hresult v
                ))
    return result

protocolocpfForm :: BS.ByteString -> BS.ByteString -> [FormParam]
protocolocpfForm cgc_cpf captcha
                     = [
                       "txtCPF"    := cgc_cpf
                       ,"txtTexto_captcha_serpro_gov_br" := captcha
                       ,"Enviar" := ("Consultar" :: BS.ByteString)
                       ]

protocolocnpjForm :: BS.ByteString -> BS.ByteString -> [FormParam]
protocolocnpjForm cgc_cpf captcha
                     = ["origem"  := ("comprovante"::BS.ByteString)
                       ,"cnpj"    := cgc_cpf
                       ,"txtTexto_captcha_serpro_gov_br" := captcha
                       ,"submit1" := ("Consultar" :: BS.ByteString)
                       ,"search_type" := ("cnpj" :: BS.ByteString)
                       ]
cpfhome  ="http://www.receita.fazenda.gov.br/Aplicacoes/ATCTA/cpf/ConsultaPublica.asp"
cpfcaptcha = "http://www.receita.fazenda.gov.br/Aplicacoes/ATCTA/cpf/captcha/gerarCaptcha.asp"
cpfpost = "http://www.receita.fazenda.gov.br/Aplicacoes/ATCTA/cpf/ConsultaPublicaExibir.asp"

cnpjhome  ="http://www.receita.fazenda.gov.br/pessoajuridica/cnpj/cnpjreva/cnpjreva_solicitacao.asp"
cnpjcaptcha = "http://www.receita.fazenda.gov.br/pessoajuridica/cnpj/cnpjreva/captcha/gerarCaptcha.asp"
cnpjpost = "http://www.receita.fazenda.gov.br/pessoajuridica/cnpj/cnpjreva/valida.asp"

test = do
  startGUI defaultConfig (\w -> do
                      e <- UI.div
                      i<-UI.input
                      bhi <- stepper "" (UI.valueChange i)
                      cnpjquery e $ pure (Just "01008713010399")
                      getBody w #+ [element i ,element e]
                      return () )
