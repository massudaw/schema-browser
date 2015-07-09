{-# LANGUAGE FlexibleContexts,TupleSections,LambdaCase,OverloadedStrings #-}
module CnpjReceita where
import Network.Wreq
import qualified Network.Wreq.Session as Sess


import OpenSSL.Session (context)
import Network.HTTP.Client.OpenSSL

import Control.Lens hiding (element,set,get,(#))
import Control.Applicative
import Control.Monad
import Data.Maybe
import Data.Functor.Compose
import Control.Concurrent

import qualified Data.List as L
import qualified Data.Map as M

import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC
import qualified Data.ByteString.Lazy.Char8 as BSLC
import qualified Data.ByteString.Lazy as BSL
import qualified Data.Text as T
import qualified Data.Traversable as Tra
import qualified Data.Text.Lazy as TL

import qualified Data.Vector as V
import Safe
import Types
import Query
import Utils
import Schema
import Gpx
import Debug.Trace
import Step
import RuntimeTypes
import Control.Monad.Reader


getInp :: TL.Text -> TB1 Showable -> Maybe BSC.ByteString
getInp l  = join . fmap (fmap (BSL.toStrict . BSLC.pack . TL.unpack . (\(SText t)-> t )) . join . fmap unRSOptional' . cc . runIdentity . getCompose )  . findTB1 (((==[l]) . fmap keyValue . keyattr ))
  where cc (TBEither _ _ (l) ) = join $fmap (cc.unTB) l
        cc (Attr _ l ) = Just l

cpfCall = WrappedCall initCnpj [getCaptchaCpf',getCpf']

getCaptchaCpf' ::
     InformationSchema -> MVar (Maybe (TB1  Showable)) ->   (Maybe (TB1 (Showable)) -> ReaderT Sess.Session IO () ) -> ReaderT Sess.Session IO ()
getCaptchaCpf' inf i  handler = do
  rv <- ask
  liftIO $ forkIO $ runReaderT  (forever $ do
      mvar <- liftIO $takeMVar i
      out <- ( fmap join . Tra.traverse getCaptchaCpfShowable  $ mvar)
      let nkey = lookFresh inf "CPF Receita" "owner" "captchaViewer"
      handler . fmap (TB1 .KV (PK [][]) . pure . Compose. Identity . Attr nkey   . SBinary  . BSL.toStrict ) $ out
      return ()) rv
  return ()


getCaptchaCpf cgc_cpf  = do
     session <- ask
     liftIO $ do
       print cpfhome
       r <-  Sess.getWith (defaults & param "cpf" .~ [T.pack $ BSC.unpack cgc_cpf]) session  cpfhome
       print cpfcaptcha
       (^? responseBody) <$> (Sess.get session $ cpfcaptcha)
getCaptchaCpfShowable tinput =
      let input = tinput
      in fmap join $ Tra.sequence $  fmap getCaptchaCpf  (getInp "number" input)


getCpf' ::
     InformationSchema -> MVar (Maybe (TB1 ( Showable))) ->   (Maybe (TB1 (Showable)) -> ReaderT Sess.Session IO () ) -> ReaderT Sess.Session IO ()
getCpf'  inf i  handler = do
  rv <- ask
  liftIO $ forkIO $ runReaderT (forever $ do
      mvar <- liftIO $ takeMVar i
      outM <- fmap (join . fmap headMay.join) . Tra.traverse getCpfShowable $  mvar
      maybe (return ()) (\out-> do
          let attr i = Compose . Identity .  Attr ( lookKey inf "owner" i)
          handler . Just $ (TB1 $ KV (PK [] . pure . attr "owner_name" . SOptional .Just . SText . TL.pack  $ out) [] )
          return ()) outM ) rv
  return ()

getCpfShowable tinput = fmap join $ Tra.sequence $  liftA2 getCpf (getInp "captchaInput" input ) (getInp "number" input)
  where input = tinput
getCpf captcha cgc_cpf = do
    session <- ask
    liftIO $ do
          print cpfpost
          pr <- traverse (Sess.post session (cpfpost) . protocolocpfForm cgc_cpf ) (Just $  captcha  )
          traverse (BSL.writeFile "cpf_name.html") (join $ fmap (^? responseBody)  pr)
          traverse (readCpfName . BSLC.unpack ) (fromJust pr ^? responseBody)

wrapplug = WrappedCall initCnpj [getCaptcha',getCnpj']

initCnpj   =  (\i -> do
  let
      man  = opensslManagerSettings context
  withOpenSSL $ Sess.withSessionWith man i) . runReaderT


getCaptcha cgc_cpf  = do
     session <- ask
     liftIO $ do
       print cnpjhome
       r <-  Sess.getWith (defaults & param "cnpj" .~ [T.pack $ BSC.unpack cgc_cpf]) session $ cnpjhome
       print cnpjcaptcha
       (^? responseBody) <$> (Sess.get session $ cnpjcaptcha)
getCaptchaShowable tinput =
      let input = tinput
      in fmap join $ Tra.sequence $  fmap getCaptcha  (getInp "number" input)


getCaptcha' ::
     InformationSchema -> MVar (Maybe (TB1 ( Showable))) ->   (Maybe (TB1 (Showable)) -> ReaderT Sess.Session IO () ) -> ReaderT Sess.Session IO ()
getCaptcha'  inf i  handler = do
  rv <- ask
  liftIO $ forkIO $ runReaderT  (forever $ do
      mvar <- liftIO $takeMVar i
      out <- ( fmap join . Tra.traverse getCaptchaShowable $ mvar)
      let nkey = lookFresh inf "CNPJ Receita" "owner" "captchaViewer"
      handler . fmap (TB1 .KV (PK [][]) . pure . Compose. Identity . Attr nkey .  SBinary  . BSL.toStrict ) $ out
      return ()) rv
  return ()



getCnpj' ::
     InformationSchema -> MVar (Maybe (TB1 ( Showable))) ->   (Maybe (TB1 (Showable)) -> ReaderT Sess.Session IO () ) -> ReaderT Sess.Session IO ()
getCnpj'  inf i  handler = do
  rv <- ask
  liftIO $ forkIO $ runReaderT (forever $ do
      mvar <- liftIO $ takeMVar i
      outM <- fmap ( fmap  (M.fromListWith (++) . fmap (fmap (\i -> [i]) )) . join) . Tra.traverse getCnpjShowable $ mvar
      liftIO $ print outM
      maybe (return () ) (\ out-> do
        let own i = Compose . Identity .  Attr (lookKey inf "owner" i )
            attr i = Compose . Identity .  Attr (lookKey inf "address" i )
            cna i = Compose . Identity .  Attr  (lookKey inf "cnae" i )
            idx  = SOptional . fmap (SText . TL.pack . head) . flip M.lookup out
            fk i  = Compose . Identity . FKT i True []
            afk i  = Compose . Identity . FKT i True [] . LeftTB1 . Just . ArrayTB1
            tb pk desc attr = TB1 $ KV (PK pk desc) attr
            (pcnae,pdesc) =  (justError "wrong primary activity " $ fmap (SText .TL.filter (not . flip L.elem "-.") . fst) t ,  SOptional $  SText .  TL.strip .  TL.drop 3. snd <$>  t)
                where t = fmap ( TL.breakOn " - " .  TL.pack . head ) (M.lookup "CÓDIGO E DESCRIÇÃO DA ATIVIDADE ECONÔMICA PRINCIPAL" out)
            scnae = fmap (\t -> ((SText .TL.filter (not . flip L.elem "-.") . fst) t ,    (SText .TL.strip . TL.drop 3 .  snd ) t)) ts
                where ts = join . maybeToList $ fmap (  TL.breakOn " - " .  TL.pack ) <$> (M.lookup "CÓDIGO E DESCRIÇÃO DAS ATIVIDADES ECONÔMICAS SECUNDÁRIAS" out)
            attrs = tb [] [own "owner_name" (idx "NOME EMPRESARIAL")]
                    [fk [own "address" (SOptional (Just $ SNumeric (-1)))]
                          (LeftTB1 $ Just $  tb [attr "id" (SSerial Nothing) ]
                              []
                              [attr "logradouro" (idx "LOGRADOURO")
                              ,attr "number" (idx "NÚMERO")
                              ,attr "complemento" (idx "COMPLEMENTO")
                              ,attr "cep" (idx "CEP")
                              ,attr "bairro" (idx "BAIRRO/DISTRITO")
                              ,attr "municipio" (idx "MUNICÍPIO")
                              ,attr "uf" (idx "UF")
                              ,attr "geocode" (SOptional Nothing)
                              ,attr "bounding" (SOptional Nothing)]
                              )
                     ,fk [own "atividade_principal" (SOptional $ Just pcnae)]
                                (LeftTB1 $ Just $ tb [cna "id" pcnae] [cna "description" pdesc] [] )
                     ,afk [own "atividades_secundarias" (SOptional $ Just $ SComposite $V.fromList $ fmap fst scnae)]
                                ((\(pcnae,pdesc)-> tb [cna "id" pcnae] [cna "description" pdesc] [] ) <$> scnae)

                    ]
        handler . Just $ traceShowId attrs
        return ()) outM ) rv
  return ()




getCnpjShowable tinput = fmap join $ Tra.sequence $  liftA2 getCnpj (getInp "captchaInput" input ) (getInp "number" input)
  where input = tinput
getCnpj captcha cgc_cpf = do
    session <- ask
    liftIO $ do
          print cnpjpost
          pr <- traverse (Sess.post session (cnpjpost) . protocolocnpjForm cgc_cpf ) (Just $  captcha  )
          pr <- traverse (Sess.post session (cnpjpost) . protocolocnpjForm cgc_cpf ) (Just $  captcha  )
          traverse (readHtmlReceita . BSLC.unpack ) (fromJust pr ^? responseBody)

{-
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
-}

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
{-
test = do
  startGUI defaultConfig (\w -> do
                      e <- UI.div
                      i<-UI.input
                      bhi <- stepper "" (UI.valueChange i)
                      cnpjquery e $ pure (Just "01008713010399")
                      getBody w #+ [element i ,element e]
                      return () )
                      -}
