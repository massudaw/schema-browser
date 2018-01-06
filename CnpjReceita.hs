{-# LANGUAGE DeriveGeneric,StandaloneDeriving,RecordWildCards,FlexibleContexts,TupleSections,LambdaCase,OverloadedStrings #-}
module CnpjReceita (getCaptchaCpf,getCaptchaCnpj,getCnpjForm,convertCPF,initSess,getCpfForm,convertHtml)where
import Network.Wreq
import qualified Network.Wreq.Session as Sess

import qualified NonEmpty as Non

import OpenSSL.Session (context)
import Control.Category
import Network.HTTP.Client.OpenSSL
import Serializer
import GHC.Generics
import qualified Serializer as S
import Control.Arrow
import qualified Network.HTTP.Client as HTTP

import Control.Lens hiding (element,set,get,(#))
import Control.Applicative
import Data.Text (Text)
import Data.Time
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
import Types hiding (timestamp)
import Utils
import Gpx
import Debug.Trace
import RuntimeTypes
import Control.Monad.Reader
import Prelude hiding ((.),elem,head,id)



boolean = SBoolean
unboolean (SBoolean i ) = i
attr i j = KV . mapFromTBList $ [Attr i $ TB1 j]
binary  = SBinary
unbinary (SBinary i ) = i
timestamp = STime . STimestamp
untimestamp (STime (STimestamp t)) = t

timestampL = untimestamp `TIso` timestamp
attrL k = unattr k `TIso` attr k

unattr i (KV ix) = justError ("no attr " ++ show i ) $ unAtt <$> M.lookup (S.singleton $ Inline i)  ix
  where unAtt (Attr i (TB1 v)) = v



deriving instance Generic HTTP.Cookie
instance DecodeTable HTTP.Cookie where
  decodeT = HTTP.Cookie
    <$> (unbinary . unattr "cookie_name" )
    <*> (unbinary . unattr "cookie_value" )
    <*> (untimestamp . unattr "cookie_expiry_time" )
    <*> (unbinary . unattr "cookie_domain" )
    <*> (unbinary . unattr "cookie_path" )
    <*> (untimestamp . unattr "cookie_creation_time" )
    <*> (untimestamp . unattr "cookie_last_access_time" )
    <*> (unboolean . unattr "cookie_persistent" )
    <*> (unboolean . unattr "cookie_host_only" )
    <*> (unboolean . unattr "cookie_secure_only" )
    <*> (unboolean . unattr "cookie_http_only" )
  encodeT HTTP.Cookie{..}
    = foldl mappend mempty [
        attr "cookie_name"  (binary cookie_name ),
        attr "cookie_value" (binary cookie_value),
        attr "cookie_expiry_time" (timestamp cookie_expiry_time),
        attr "cookie_domain" (binary cookie_domain),
        attr "cookie_path" (binary cookie_path),
        attr "cookie_creation_time" (timestamp cookie_creation_time),
        attr "cookie_last_access_time" (timestamp cookie_last_access_time),
        attr "cookie_persistent" (boolean cookie_persistent),
        attr "cookie_host_only" (boolean cookie_host_only),
        attr "cookie_secure_only" (boolean cookie_secure_only),
        attr "cookie_http_only" (boolean cookie_http_only)]


httpJar = TIso HTTP.destroyCookieJar HTTP.createCookieJar

cookieJar :: TIso HTTP.CookieJar (FTB (TBData Text Showable))
cookieJar =  traverseIso tableIso . ftbIso .  httpJar

initSess :: FTB (TBData Text Showable)
initSess =  unTiso cookieJar (HTTP.createCookieJar  [])

getCaptchaCpf cookie = Sess.withSessionControl (Just $ tIso cookieJar cookie) HTTP.defaultManagerSettings $ \session ->  do
       print cpfhome
       r <-  Sess.getWith defaults session  cpfhome
       print cpfcaptcha
       (fmap BSL.toStrict . (^? responseBody)) <$> Sess.get session cpfcaptcha


convertCPF out = Just (tblist . pure . attr "owner_name" . LeftTB1 .Just . TB1 . SText . TL.pack  $ out )
  where attr k =  Attr k

getCpfForm cookie captcha nascimento cgc_cpf = Sess.withSessionControl (Just $ tIso cookieJar cookie) HTTP.defaultManagerSettings$ \ session -> do
          print cpfpost
          pr <- traverse (Sess.post session cpfpost . protocolocpfForm nascimento cgc_cpf ) (Just captcha  )
          traverse (BSL.writeFile "cpf_name.html") (join $ fmap (^? responseBody)  pr)
          traverse (readCpfName . BSLC.unpack ) (fromJust pr ^? responseBody)


getCaptchaCnpj  cookie =Sess.withSessionControl (Just $ tIso cookieJar $cookie )HTTP.defaultManagerSettings$ \ session -> do
       print cnpjhome
       r <-  Sess.getWith defaults  session cnpjhome
       print cnpjcaptcha
       o <- Sess.get session cnpjcaptcha
       return (unTiso cookieJar  $ o ^. responseCookieJar , BSL.toStrict Control.Applicative.<$> (o ^? responseBody) )


convertHtml out =
        let own = attr
            attr i = Attr  i
            cna  =  attr
            idx  = LeftTB1 . fmap (TB1 . SText . TL.pack . head) . flip M.lookup out
            fk rel i  = FKT (kvlist i )rel
            afk rel i l = fk rel i  . LeftTB1 $  ArrayTB1 . Non.fromList <$> l
            tb attr = TB1 $ tblist attr
            (pcnae,pdesc) =  (justError "wrong primary activity " $ fmap (TB1 . SText .TL.filter (not . flip L.elem ("-." :: String)) . fst) t ,  justError " no description" $  TB1 . SText .  TL.strip .  TL.drop 3. snd <$>  t)
                where t = fmap ( TL.breakOn " - " .  TL.pack . head ) (M.lookup "CÓDIGO E DESCRIÇÃO DA ATIVIDADE ECONÔMICA PRINCIPAL" out)
            scnae = fmap (first(TB1 . SText)) $ filter ((not . T.isInfixOf "Não informada").fst) $ fmap ((TL.filter (not . flip L.elem ("-." :: String)) . fst) Control.Arrow.&&& (TB1 . SText .TL.strip . TL.drop 3 .  snd )) ts
                where ts = join . maybeToList $ fmap (TL.breakOn " - " .  TL.pack ) <$> M.lookup "CÓDIGO E DESCRIÇÃO DAS ATIVIDADES ECONÔMICAS SECUNDÁRIAS" out
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
                       ,fk [Rel "atividade_principal" Equals "id"] [own "atividade_principal" (LeftTB1 $ Just pcnae)]
                                  (LeftTB1 $ Just $ tb [cna "id" pcnae,cna "description" pdesc] )
                       ,afk [Rel "atividades_secundarias" (AnyOp Equals) "id"] [own "atividades_secundarias" (LeftTB1 $ ArrayTB1 . Non.fromList . fmap fst <$> nonEmpty scnae)]
                                  (nonEmpty $ (\(pcnae,pdesc)-> tb [cna "id" pcnae,cna "description" pdesc] ) <$> filter ((/=txt "Não informada").snd) scnae)]
        in Just  attrs

getCnpjForm cookie captcha cgc_cpf
  = Sess.withSessionControl (Just $ tIso cookieJar $cookie ) HTTP.defaultManagerSettings$ \ session ->do
          print cnpjpost
          _ <- traverse (Sess.post session cnpjpost . protocolocnpjForm cgc_cpf ) (Just captcha)
          pr <- traverse (Sess.post session cnpjpost . protocolocnpjForm cgc_cpf ) (Just captcha)
          traverse (readHtmlReceita . BSLC.unpack ) (fromJust pr ^? responseBody)


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
