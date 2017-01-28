{-# LANGUAGE FlexibleContexts,TupleSections,LambdaCase,OverloadedStrings #-}
module CnpjReceita (getCaptchaCpf,getCaptchaCnpj,getCnpjForm,convertCPF,initSess,getCpfForm,convertHtml)where
import Network.Wreq
import qualified Network.Wreq.Session as Sess

import qualified NonEmpty as Non

import OpenSSL.Session (context)
import Network.HTTP.Client.OpenSSL
import qualified Network.HTTP.Client as HTTP

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
import Utils
import Gpx
import Debug.Trace
import RuntimeTypes
import Control.Monad.Reader
import Prelude hiding (elem,head)



getCaptchaCpf session = do
       print cpfhome
       r <-  Sess.getWith (defaults ) session  cpfhome
       print cpfcaptcha
       (fmap BSL.toStrict . (^? responseBody)) <$> (Sess.get session $ cpfcaptcha)


convertCPF out = Just $ (tblist . pure . attr "owner_name" . LeftTB1 .Just . TB1 . SText . TL.pack  $ out )
  where attr k =  _tb . Attr k

getCpfForm session captcha nascimento cgc_cpf = do
          print cpfpost
          pr <- traverse (Sess.post session (cpfpost) . traceShowId .protocolocpfForm nascimento cgc_cpf ) (Just $  captcha  )
          traverse (BSL.writeFile "cpf_name.html") (join $ fmap (^? responseBody)  pr)
          traverse (readCpfName . traceShowId . BSLC.unpack ) (fromJust pr ^? responseBody)


initSess =  do
  let
      man  = opensslManagerSettings context
  Sess.newSession (Just (HTTP.createCookieJar  [])) man

getCaptchaCnpj  session = do
       print cnpjhome
       r <-  Sess.getWith defaults  session $ cnpjhome
       print cnpjcaptcha
       (fmap BSL.toStrict .(^? responseBody) )<$> (Sess.get session $ cnpjcaptcha)


convertHtml out =
        let own = attr
            attr i = Compose . Identity .  Attr  i
            cna  =  attr
            idx  = LeftTB1 . fmap (TB1 . SText . TL.pack . head) . flip M.lookup out
            fk rel i  = Compose . Identity . FKT (kvlist i )rel
            afk rel i  = fk rel i  . LeftTB1 . Just . ArrayTB1 . Non.fromList
            tb attr = TB1 $ tblist attr
            (pcnae,pdesc) =  (justError "wrong primary activity " $ fmap (TB1 . SText .TL.filter (not . flip L.elem ("-." :: String)) . fst) t ,  justError " no description" $  TB1 . SText .  TL.strip .  TL.drop 3. snd <$>  t)
                where t = fmap ( TL.breakOn " - " .  TL.pack . head ) (M.lookup "CÓDIGO E DESCRIÇÃO DA ATIVIDADE ECONÔMICA PRINCIPAL" out)
            scnae = filter ((/=(TB1 (SText "Não Informada"))).fst) $ fmap (\t -> ((TB1 . SText .TL.filter (not . flip L.elem ("-." :: String)) . fst) t ,    (TB1 . SText .TL.strip . TL.drop 3 .  snd ) t)) ts
                where ts = join . maybeToList $ fmap (TL.breakOn " - " .  TL.pack ) <$> (M.lookup "CÓDIGO E DESCRIÇÃO DAS ATIVIDADES ECONÔMICAS SECUNDÁRIAS" out)
            attrs = tb [ own "owner_name" (idx "NOME EMPRESARIAL")
                       , fk [Rel "address" Equals "id"] [own "address" (LeftTB1 $ Just $ TB1 $ SNumeric (-1)) ]
                          (LeftTB1 $ Just $
                          tb [
                              attr "logradouro" (idx "LOGRADOURO")
                              ,attr "number" (idx "NÚMERO")
                              ,attr "complemento" (idx "COMPLEMENTO")
                              ,attr "cep" (idx "CEP")
                              ,attr "bairro" (idx "BAIRRO/DISTRITO")
                              ,attr "municipio" (idx "MUNICÍPIO")
                              ,attr "uf" (idx "UF")])
                       ,fk [Rel "atividade_principal" Equals "id"] [own "atividade_principal" (LeftTB1 $ Just (pcnae))]
                                  (LeftTB1 $ Just $ tb [cna "id" pcnae,cna "description" pdesc] )
                       ,afk [(Rel "atividades_secundarias" Equals "id")] [own "atividades_secundarias" (LeftTB1 $ Just $ ArrayTB1 $ Non.fromList $ fmap fst scnae)]
                                  ((\(pcnae,pdesc)-> tb [cna "id" pcnae,cna "description" pdesc] ) <$> filter ((/=txt "Não informada").snd) scnae)]
        in Just  attrs

getCnpjForm session captcha cgc_cpf = do
          print cnpjpost
          _ <- traverse (Sess.post session cnpjpost . protocolocnpjForm cgc_cpf ) (Just captcha)
          pr <- traverse (Sess.post session cnpjpost . protocolocnpjForm cgc_cpf ) (Just captcha)
          traverse (readHtmlReceita . BSLC.unpack . traceShowId ) (fromJust pr ^? responseBody)


protocolocpfForm :: BS.ByteString -> BS.ByteString -> BS.ByteString -> [FormParam]
protocolocpfForm nascimento cgc_cpf captcha
                     = ["tempTxtNascimento"    := nascimento
                       ,"tempTxtCPF"    := cgc_cpf
                       ,"txtTexto_captcha_serpro_gov_br" := captcha
                       ,"temptxtTexto_captcha_serpro_gov_br" := captcha
                       ]

protocolocnpjForm :: BS.ByteString -> BS.ByteString -> [FormParam]
protocolocnpjForm cgc_cpf captcha
                     = ["origem"  := ("comprovante"::BS.ByteString)
                       ,"cnpj"    := cgc_cpf
                       ,"txtTexto_captcha_serpro_gov_br" := captcha
                       ,"submit1" := ("Consultar" :: BS.ByteString)
                       ,"search_type" := ("cnpj" :: BS.ByteString)
                       ]
cpfhome  ="http://www.receita.fazenda.gov.br/aplicacoes/atcta/cpf/consultapublica.asp"
cpfcaptcha = "http://www.receita.fazenda.gov.br/aplicacoes/atcta/cpf/captcha/gerarcaptcha.asp"
cpfpost = "http://www.receita.fazenda.gov.br/aplicacoes/atcta/cpf/ConsultaPublicaExibir.asp"

cnpjhome  ="http://www.receita.fazenda.gov.br/pessoajuridica/cnpj/cnpjreva/cnpjreva_solicitacao.asp"
cnpjcaptcha = "http://www.receita.fazenda.gov.br/pessoajuridica/cnpj/cnpjreva/captcha/gerarCaptcha.asp"
cnpjpost = "http://www.receita.fazenda.gov.br/pessoajuridica/cnpj/cnpjreva/valida.asp"
