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
import Control.Concurrent

import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S

import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC
import qualified Data.ByteString.Lazy.Char8 as BSLC
import qualified Data.ByteString.Lazy as BSL
import qualified Data.Text as T
import qualified Data.Traversable as Tra
import qualified Data.Text as TL

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
import Prelude hiding (head)


getInp :: [TL.Text] -> TB1 Showable -> Maybe BSC.ByteString
getInp l (TB1  (k,Compose (Identity kv )))  = join . fmap (fmap (BSL.toStrict . BSLC.pack . TL.unpack . (\(TB1 (SText t))-> t )) . join . fmap unRSOptional' . cc . runIdentity . getCompose  )  .  M.lookup (S.fromList l) . M.mapKeys (S.map (keyString._relOrigin)) $ _kvvalues kv
  where -- cc (TBEither _ l ) = join $fmap (cc.unTB) l
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
      handler . fmap (tbmap . mapFromTBList . pure . Compose. Identity . Attr nkey   . TB1 . SBinary  . BSL.toStrict ) $ out
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
      in fmap join $ Tra.sequence $  fmap getCaptchaCpf  (getInp ["cpf_number","cnpj_number"] input)


getCpf' ::
     InformationSchema -> MVar (Maybe (TB1 ( Showable))) ->   (Maybe (TB1 (Showable)) -> ReaderT Sess.Session IO () ) -> ReaderT Sess.Session IO ()
getCpf'  inf i  handler = do
  rv <- ask
  liftIO $ forkIO $ runReaderT (forever $ do
      mvar <- liftIO $ takeMVar i
      outM <- fmap (join . fmap headMay.join) . Tra.traverse getCpfShowable $  mvar
      maybe (return ()) (\out-> do
          let attr i = Compose . Identity .  Attr ( lookKey inf "owner" i)
          handler . Just $ (tbmap . mapFromTBList . pure . attr "owner_name" . LeftTB1 .Just . TB1 . SText . TL.pack  $ out )
          return ()) outM ) rv
  return ()

getCpfShowable tinput = fmap join $ Tra.sequence $  liftA2 getCpf (getInp ["captchaInput"] input ) (getInp ["cpf_number","cnpj_number"] input)
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
      in fmap join $ Tra.sequence $  fmap getCaptcha  (getInp ["cpf_number","cnpj_number"]  input)


getCaptcha' ::
     InformationSchema -> MVar (Maybe (TB1 ( Showable))) ->   (Maybe (TB1 (Showable)) -> ReaderT Sess.Session IO () ) -> ReaderT Sess.Session IO ()
getCaptcha'  inf i  handler = do
  rv <- ask
  liftIO $ forkIO $ runReaderT  (forever $ do
      mvar <- liftIO $takeMVar i
      out <- ( fmap join . Tra.traverse getCaptchaShowable $ mvar)
      let nkey = lookFresh inf "CNPJ Receita" "owner" "captchaViewer"
      handler . fmap (tbmap . mapFromTBList  . pure . Compose. Identity . Attr nkey .  TB1 .SBinary  . BSL.toStrict ) $ out
      return ()) rv
  return ()



getCnpj' ::
     InformationSchema -> MVar (Maybe (TB1 ( Showable))) ->   (Maybe (TB1 (Showable)) -> ReaderT Sess.Session IO () ) -> ReaderT Sess.Session IO ()
getCnpj'  inf i  handler = do
  rv <- ask
  liftIO $ forkIO $ runReaderT (forever $ do
      mvar <- liftIO $ takeMVar i
      outM <- fmap (fmap  (M.fromListWith (++) . fmap (fmap pure )) . join  . join  ) . Tra.traverse getCnpjShowable $ mvar
      liftIO $ print outM
      maybe (return () ) (\ out-> do
        let own = attr
            attr i = Compose . Identity .  Attr  i
            cna  =  attr
            idx  = LeftTB1 . fmap (TB1 . SText . TL.pack . head) . flip M.lookup out
            fk rel i  = Compose . Identity . FKT i rel
            afk rel i  = Compose . Identity . FKT i rel . LeftTB1 . Just . ArrayTB1
            tb attr = tbmap $ mapFromTBList  attr
            (pcnae,pdesc) =  (justError "wrong primary activity " $ fmap (TB1 . SText .TL.filter (not . flip L.elem "-.") . fst) t ,  LeftTB1 $  TB1 . SText .  TL.strip .  TL.drop 3. snd <$>  t)
                where t = fmap ( TL.breakOn " - " .  TL.pack . head ) (M.lookup "CÓDIGO E DESCRIÇÃO DA ATIVIDADE ECONÔMICA PRINCIPAL" out)
            scnae = fmap (\t -> ((TB1 . SText .TL.filter (not . flip L.elem "-.") . fst) t ,    (TB1 . SText .TL.strip . TL.drop 3 .  snd ) t)) ts
                where ts = join . maybeToList $ fmap (TL.breakOn " - " .  TL.pack ) <$> (M.lookup "CÓDIGO E DESCRIÇÃO DAS ATIVIDADES ECONÔMICAS SECUNDÁRIAS" out)
            attrs = tb [ own "owner_name" (idx "NOME EMPRESARIAL")
                       , fk [Rel "address" "=" "id"] [own "address" (LeftTB1 $ Just $ TB1 $ SNumeric (-1)) ]
                          (LeftTB1 $ Just $
                          tb [attr "id" (SerialTB1 Nothing)
                              ,attr "logradouro" (idx "LOGRADOURO")
                              ,attr "number" (idx "NÚMERO")
                              ,attr "complemento" (idx "COMPLEMENTO")
                              ,attr "cep" (idx "CEP")
                              ,attr "bairro" (idx "BAIRRO/DISTRITO")
                              ,attr "municipio" (idx "MUNICÍPIO")
                              ,attr "uf" (idx "UF")])
                       ,fk [Rel "atividade_principal" "=" "id"] [own "atividade_principal" (LeftTB1 $ Just (pcnae))]
                                  (LeftTB1 $ Just $ tb [cna "id" pcnae,cna "description" pdesc] )
                       ,afk [(Rel "atividades_secundarias" "=" "id")] [own "atividades_secundarias" (LeftTB1 $ Just $ ArrayTB1 $ fmap fst scnae)]
                                  ((\(pcnae,pdesc)-> tb [cna "id" pcnae,cna "description" pdesc] ) <$> scnae)]
        handler . Just $ liftKeys inf "owner" $ traceShowId attrs
        return ()) outM ) rv
  return ()




getCnpjShowable tinput = fmap (fmap join) $ Tra.sequence $  liftA2 getCnpj (getInp ["captchaInput"] input ) (getInp ["cpf_number","cnpj_number"] input)
  where input = tinput
getCnpj captcha cgc_cpf = do
    session <- ask
    liftIO $ do
          print cnpjpost
          pr <- traverse (Sess.post session cnpjpost . protocolocnpjForm cgc_cpf ) (Just captcha)
          traverse (readHtmlReceita . BSLC.unpack . traceShowId ) (fromJust pr ^? responseBody)


protocolocpfForm :: BS.ByteString -> BS.ByteString -> [FormParam]
protocolocpfForm cgc_cpf captcha
                     = [
                       "txtCPF"    := cgc_cpf
                       ,"txtTexto_captcha_serpro_gov_br" := captcha
                       ,"Enviar" := ("Consultar" :: BS.ByteString)
                       ]

protocolocnpjForm :: BS.ByteString -> BS.ByteString -> [FormParam]
protocolocnpjForm cgc_cpf captcha
                     = traceShowId ["origem"  := ("comprovante"::BS.ByteString)
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
