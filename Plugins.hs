{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE Arrows #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE NoMonomorphismRestriction,UndecidableInstances,FlexibleContexts,OverloadedStrings ,TupleSections, ExistentialQuantification #-}
module Plugins (plugList) where

import Location
import PrefeituraSNFSE
import Siapi3
import CnpjReceita
import OFX
import Crea
import PandocRenderer

import Types
import Step
import RuntimeTypes
import Utils

import Network.Mail.Mime
import Control.Monad.Reader
import Data.Functor.Apply
import Debug.Trace
import Data.Time.Parse
import Data.Maybe
import Data.Functor.Identity
import Control.Applicative
import Data.Traversable (traverse)
import qualified Data.Traversable as Tra
import qualified Data.List as L
import qualified Data.ByteString.Char8 as BS
import qualified Data.ByteString.Lazy.Char8 as BSL
import Data.Time
import qualified Data.ByteString.Base64.URL as B64Url
import Data.Monoid hiding (Product(..))
import qualified Data.Text as T
import Data.Text (Text)
import qualified Data.Map as M
import Data.String
import Control.Arrow


lplugOrcamento = BoundedPlugin2 "Orçamento" "pricing" renderProjectPricingA
lplugContract = BoundedPlugin2 "Contrato" "pricing" renderProjectContract
lplugReport = BoundedPlugin2 "Relatório " "pricing" renderProjectReport



siapi2Plugin = BoundedPlugin2  pname tname url
  where
    pname ="Siapi2 Andamento"
    tname = "fire_project"
    varTB i =  fmap (BS.pack . renderShowable ) . join . fmap unRSOptional' <$>  idxR i
    url :: ArrowReader
    url = proc t -> do
      protocolo <- varTB "protocolo" -< t
      ano <- varTB "ano" -< t
      odxR "aproval_date" -< ()
      atR "andamentos" (proc t -> do
        odxR "andamento_date" -<  t
        odxR "andamento_description" -<  t) -< t
      b <- act ( Tra.traverse  (\(i,j)-> if read (BS.unpack j) >= 15 then  return Nothing else liftIO (siapi2  i j >> error "siapi2 test error")  )) -<  (liftA2 (,) protocolo ano )
      let ao bv  = Just $ tblist   [iat bv]
          convertAndamento :: [String] -> TB2 Text (Showable)
          convertAndamento [da,des] =  tblist $ fmap attrT  $  ([("andamento_date",TB1 . STimestamp . fst . justError "wrong date parse" $  strptime "%d/%m/%y" da  ),("andamento_description",TB1 $ SText (T.filter (not . (`L.elem` "\n\r\t")) $ T.pack  des))])
          convertAndamento i = error $ "convertAndamento " <> show i
          iat bv = Compose . Identity $ (IT
                            (attrT ("andamentos",TB1 ()))
                            (LeftTB1 $ Just $ ArrayTB1 $ reverse $  fmap convertAndamento bv))
      returnA -< join  (  ao  .  tailEmpty . concat <$> join b)
    tailEmpty [] = []
    tailEmpty i  = tail i

cpfCaptcha = BoundedPlugin2 pname tname url
  where
    pname , tname :: Text
    pname = "CPF Captcha"
    tname = "owner"
    url :: ArrowReader
    url = proc t -> do
      sess <- act (\_ -> lift  initSess ) -< ()
      cap <- act (\sess -> lift (getCaptchaCpf sess)) -< sess
      atR "ir_reg" (idxK"cpf_number") -<()
      odxR "sess" -< ()
      odxR "captchaViewer" -< ()
      returnA -< Just $ tblist [attrT  ("sess", TB1 (SSession sess)) ,attrT ("captchaViewer",TB1 (SBinary $ justError "no captcha" cap))]

cnpjCaptcha = BoundedPlugin2 pname tname url
  where
    pname , tname :: Text
    pname = "CNPJ Captcha"
    tname = "owner"
    url :: ArrowReader
    url = proc t -> do
      sess <- act (\_ -> lift  initSess ) -< ()
      cap <- act (\sess -> lift (getCaptchaCnpj sess)) -< sess
      atR "ir_reg" (idxK"cnpj_number") -<()
      odxR "sess" -< ()
      odxR "captchaViewer" -< ()
      returnA -< Just $ tblist [attrT  ("sess", TB1 (SSession sess)) ,attrT ("captchaViewer",TB1 (SBinary $ justError "no captcha" cap))]

renderDay d =  paddedm day <> paddedm month <> show year
  where (year,month,day) = toGregorian d
        paddedm m = (if m < 10 then "0" else "" ) <> show m

cpfForm = BoundedPlugin2 pname tname url
  where
    pname , tname :: Text
    pname = "CPF Form"
    tname = "owner"
    url :: ArrowReader
    url = proc t -> do
      cap <-  idxK "captchaInput" -< ()
      nascimento <-  idxK "nascimento" -< ()
      cnpj <-  atR "ir_reg" (idxK "cpf_number") -< ()
      sess <- idxK "sess" -< ()
      html <- act (\(TB1 (SSession sess),TB1 (SText cap),TB1 (SDate nascimento),TB1 (SText cnpj))  -> lift  (getCpfForm sess (BS.pack $ T.unpack cap) (BS.pack $ renderDay nascimento ) (BS.pack $ T.unpack cnpj) )) -< (sess,cap,nascimento,cnpj)
      arrowS -< ()
      returnA -<   join .join $ fmap convertCPF .  traceShowId <$> html
    arrowS = proc t -> do
              odxR "owner_name" -< t
              returnA -< Nothing

atPrim s g = Primitive (AtomicPrim (s,g))
queryCPFStatefull = StatefullPlugin "CPF Receita" "owner"
  [([("captchaViewer",atPrim "public" "jpg")
    ,("sess",atPrim "gmail" "session")]
    ,cpfCaptcha)
  ,([("nascimento",atPrim "pg_catalog" "date")
    ,("captchaInput",atPrim "pg_catalog" "character varying")]
    ,cpfForm)]


queryCNPJStatefull = StatefullPlugin "CNPJ Receita" "owner"
  [([("captchaViewer",atPrim "public" "jpg")
    ,("sess",atPrim "gmail" "session")]
    ,cnpjCaptcha)
  ,([("captchaInput",atPrim "pg_catalog" "character varying")]
    ,cnpjForm)]



cnpjForm = BoundedPlugin2 pname tname url
  where
    pname , tname :: Text
    pname = "CNPJ Form"
    tname = "owner"
    url :: ArrowReader
    url = proc t -> do
      cap <-  idxK "captchaInput" -< ()
      cnpj <-  atR "ir_reg" (idxK "cnpj_number") -< ()
      sess <- idxK "sess" -< ()
      html :: Maybe [(String,String)] <- act (\(TB1 (SSession sess),TB1 (SText cap),TB1 (SText cnpj))  -> fmap join $ lift  (getCnpjForm sess (BS.pack $ T.unpack cap) (BS.pack $ T.unpack cnpj) )) -< (sess,cap,cnpj)

      arrowS -< ()
      returnA -<   join $ convertHtml . (M.fromListWith (++) . fmap (fmap pure )) <$> html
    arrowS = proc t -> do
              idxR "captchaInput" -< t
              odxR "owner_name" -< t
              odxR "address"-< t
              odxR "atividade_principal" -< ()
              odxR "atividades_secundarias" -< ()
              atR "atividades_secundarias" cnae -< t
              atR "atividade_principal" cnae -< t
              atR "address"  addrs -< t
              returnA -< Nothing
      where
          cnae = proc t -> do
              odxR "id" -< t
              odxR "description" -< t
          addrs = proc t -> do
              odxR "logradouro" -< t
              odxR "number " -< t
              odxR "uf" -< t
              odxR "cep" -< t
              odxR "complemento" -< t
              odxR "municipio" -< t
              odxR "bairro" -< t


analiseProjeto = BoundedPlugin2 pname tname url
  where
    pname , tname :: Text
    pname = "Cadastro Bombeiro"
    tname = "fire_project"
    varTB i =  fmap (BS.pack . renderShowable ) . join . fmap unRSOptional' <$>  idxR i
    url :: ArrowReader
    url = proc t -> do
      atR "id_owner,id_contact"
                $ atR "id_owner"
                    $ atAny "ir_reg" [varTB "cpf_number",varTB "cnpj_number"] -< t
      atR "address"
                ((,,,) <$> idxK "complemento" <*> idxK "cep" <*> idxK "municipio" <*> idxK "uf") -< t
      atR "dados_projeto" (idxK "area") -< ()
      odxR "protocolo" -< ()
      odxR "ano" -< ()
      returnA -< Nothing


siapi3Plugin  = BoundedPlugin2 pname tname  url

  where
    pname , tname :: Text
    pname = "Siapi3 Andamento"
    tname = "fire_project"
    varTB i =  fmap (BS.pack . renderShowable ) . join . fmap unRSOptional' <$>  idxR i
    url :: ArrowReader
    url = proc t -> do
      protocolo <- varTB "protocolo" -< ()
      ano <- varTB "ano" -< ()
      cpf <- atR "id_owner,id_contact"
                $ atR "id_owner"
                    $ atAny "ir_reg" [varTB "cpf_number",varTB "cnpj_number"] -< t
      odxR "taxa_paga" -< ()
      odxR "aproval_date" -< ()
      atR "andamentos" (proc t -> do
          odxR "andamento_date" -<  t
          odxR "andamento_description" -<  t
          odxR "andamento_user" -<  t
          odxR "andamento_status" -<  t) -< ()

      b <- act (fmap join .  Tra.traverse   (\(i,j,k)-> if read (BS.unpack j) <= 14 then  return Nothing else liftIO $ siapi3  i j k )) -<   (liftA3 (,,) protocolo ano cpf)
      let convertAndamento [_,da,desc,user,sta] =tblist  $ fmap attrT  $ ([("andamento_date",TB1 .STimestamp . fst . justError "wrong date parse" $  strptime "%d/%m/%Y %H:%M:%S" da  ),("andamento_description",TB1 . SText $ T.pack  desc),("andamento_user",LeftTB1 $ Just $ TB1 $ SText $ T.pack  user),("andamento_status",LeftTB1 $ Just $ TB1 $ SText $ T.pack sta)] )
          convertAndamento i = error $ "convertAndamento2015 :  " <> show i
      let ao  (bv,taxa) =  Just $ tblist  ( [attrT ("taxa_paga",LeftTB1 $ Just $  bool $ not taxa),iat bv])
          iat bv = Compose . Identity $ (IT (attrT ("andamentos",TB1 ()))
                         (LeftTB1 $ Just $ ArrayTB1 $ reverse $ fmap convertAndamento bv))
      returnA -< join (ao <$> b)

bool = TB1 . SBoolean
num = TB1 . SNumeric








{-
data Timeline
  = Timeline
  { header :: String
  , dates :: [(Either Day LocalTime,String)]
  }

queryTimeline = BoundedPlugin "Timeline" "pricing"(staticP arrow)  elem
  where
    convDateArr i = swap . fmap projDate  <$> (catMaybes $ fmap (traverse unRSOptional') $ catMaybes $ i)
    projDate (SDate (Finite f)) = Left f
    projDate (STimestamp (Finite f)) =  Right f
    projDate (SOptional (Just j )  ) = projDate j
    projDate i = error $ " projDate " <> show i
    arrow :: FunArrowPlug [(Either Day LocalTime,String)]
    arrow = proc t -> do
      prd <- varT "pricing_date" -< t
      papr <- varN "pricing_approval" -< t
      apd <- varN "id_project:aproval_date" -< t
      arr <- varN "pagamentos:payment_date" -< t
      arrD <- varN "pagamentos:payment_description" -< t
      andDa <- varN "id_project:andamentos:andamento_date" -< t
      andDe <- varN "id_project:andamentos:andamento_description" -< t
      let vv =  concat $ maybeToList $ (\(SComposite i) (SComposite j)-> fmap Just $ zip (renderShowable <$> F.toList j ) (F.toList i)) <$>  arr <*> arrD

      returnA -<  convDateArr ([("Proposta de Enviada",)<$> prd,("Projeto Aprovado",) <$> apd ,("Proposta Aprovada",) <$> papr] <>  vv {-<> vvand -})
    elem inf inputs = do
        e <- UI.div # set UI.id_ "timeline-embed"
        let  timeline i = Timeline "hello" (dynP arrow $ i)
        i <- UI.div # sink UI.html  (fmap (\i->  "<script>    var container = document.getElementById('timeline-embed');var items = new vis.DataSet("  <>  BSL.unpack ( encode (timeline i)) <> ") ;  var options = {} ; if (container.vis != null ) { container.vis.destroy(); } ; container.vis = new vis.Timeline(container,items,options); </script>") $ facts inputs)
        UI.div # set children [e,i]


instance ToJSON Timeline where
  toJSON (Timeline h v) = toJSON (dates <$> zip [0..] v)

    where dates (id,(Right i,j)) = object ["id" .= (id :: Int) ,"start" .=  ti i, "content" .= j, "type" .= ("point" :: String)]
          dates (id,(Left i,j)) = object ["id" .= (id :: Int) ,"start" .=  tti i, "content" .= j, "type" .= ("point" :: String)]
          ti  = formatTime defaultTimeLocale "%Y/%m/%d"
          tti  = formatTime defaultTimeLocale "%Y/%m/%d %H:%M:%S"
-}

itR i f = atR i (IT (attrT (fromString i,TB1 ())) <$> f)

pagamentoArr
  :: (KeyString a1,
      MonadReader (Maybe (FTB1 Identity a1 Showable)) m, Show a1,
      Functor m,Ord a1) =>
     Parser
       (Kleisli m)
       (Access Text)
       (Maybe (FTB Showable))
       ((TB Identity Text Showable))
pagamentoArr =  itR "pagamento" (proc descontado -> do
              pinicio <- idxR "inicio"-< ()
              p <- idxR "vezes" -< ()
              let valorParcela = liftA2 (liftA2 (/))  descontado p
              pg <- atR  "pagamentos" (proc (valorParcela,pinicio,p) -> do
                  odxR "description" -<  ()
                  odxR "price" -<  ()
                  odxR "scheduled_date" -<  ()
                  let total = maybe 0 fromIntegral  p :: Int
                  let pagamento = _tb $ FKT ([attrT  ("pagamentos",LeftTB1 (Just $ ArrayTB1  (replicate total (num $ -1) )) )]) [Rel "pagamentos" "=" "id"] (LeftTB1 $ Just $ ArrayTB1 ( fmap (\ix -> tblist [attrT ("id",SerialTB1 Nothing),attrT ("description",LeftTB1 $ Just $ TB1 $ SText $ T.pack $ "Parcela (" <> show ix <> "/" <> show total <>")" ),attrT ("price",LeftTB1 valorParcela), attrT ("scheduled_date",LeftTB1 pinicio) ]) ([1 .. total])))
                  returnA -<  pagamento ) -< (valorParcela,pinicio,p)
              returnA -<  tblist [pg ] )


gerarPagamentos = BoundedPlugin2 "Gerar Pagamento" tname  url
  where
    tname = "plano_aluno"
    url :: ArrowReader
    url = proc t -> do
          descontado <-  (\v k -> v*(1 - k) )
              <$> atR "frequencia,meses"
                  ((\v m -> v * fromIntegral m) <$> idxK "price" <*> idxK "meses")
              <*> idxK "desconto" -< ()
          pag <- pagamentoArr -< Just descontado
          returnA -< Just . tblist . pure . _tb  $ pag



createEmail = StatefullPlugin "Create Email" "messages"
  [([("plain",atPrim "gmail" "email")],generateEmail)]

generateEmail = BoundedPlugin2  "Generate Email" tname url
  where
    tname ="messages"
    url :: ArrowReader
    url = proc t -> do
          plain <- idxK "plain" -< ()
          odxR "raw" -< ()
          mesg <- act (lift .buildmessage )-< plain
          returnA -< Just . tblist . pure . attrT  . ("raw",) . LeftTB1 $  Just   mesg

    buildmessage :: FTB Showable -> IO (FTB Showable)
    buildmessage (TB1 (SBinary mesg ))= TB1 .SText . T.pack . BS.unpack . B64Url.encode .BSL.toStrict <$>  (fmap traceShowId . renderMail' $ Mail (Address Nothing "wesley.massuda@gmail.com") [Address Nothing "wesley.massuda@gmail.com"] [] [] [] [[mail]])
          where mail = (Part "text/plain" None Nothing [] (BSL.fromStrict $   mesg))


renderEmail = StatefullPlugin "Render Email" "messages"
  [([("message_viewer",Primitive $ RecordPrim ("gmail","mime"))]
    ,encodeMessage )]

encodeMessage = PurePlugin "Encode Email" tname url
  where
    tname = "messages"
    messages = nameI 0 $ proc t -> do
          enc <- liftA2 ((,)) (idxR "mimeType") (atR "body"  (join . traverse decoder' <$> (idxR "data")))  -< ()
          part <- atMA "parts"
                    (callI 0 messages) -< ()
          let mimeTable (TB1 (SText mime),v) next
                | T.isInfixOf "text/plain" mime || T.isInfixOf "plain/text" mime =  Just $ tb "plain"
                | T.isInfixOf "text/html" mime =  Just $ tb "html"
                | T.isInfixOf "application/pgp-signature" mime =  Just $ tb "plain"
                | T.isInfixOf "multipart/alternative" mime =  last <$> (ifNull . catMaybes $ next)
                | T.isInfixOf "multipart" mime =   Just  $ tbmix (catMaybes next)
                | otherwise =Nothing
                where tb n  =  tblist . pure . _tb . Attr n $ (LeftTB1 $  v)
                      tbmix l = tblist . pure . _tb . IT (attrT  ("mixed",TB1 ()) ) . LeftTB1 $ ArrayTB1 <$>  (ifNull l )
          returnA -<  (maybe Nothing (flip mimeTable part )  $ (\(i,j) -> fmap (,j) i) enc)
    mixed =  nameO 1 (proc t ->  do
                liftA3 (,,) (odxR "plain") (atR "mixed" (callO 1 mixed)) (odxR "html") -< ()
                returnA -< ()
                )
    url :: ArrowReaderM Identity
    url = proc t -> do
          res <-  atR "payload" messages -< ()
          atR "message_viewer" mixed -< ()
          returnA -< Just . tblist . pure . _tb . IT (attrT  ("message_viewer",TB1 ()) ) . LeftTB1 $  res

    ifNull i = if L.null i then  Nothing else Just i
    decoder (SText i) =  (Just . SBinary) . B64Url.decodeLenient . BS.pack . T.unpack $ i
    decoder' (TB1 i) = fmap TB1 $ decoder i
    decoder' (LeftTB1 i) =  (join $ fmap decoder' i)


pagamentoServico = BoundedPlugin2 "Gerar Pagamento" tname url
  where
    tname = "servico_venda"
    url :: ArrowReader
    url = proc t -> do
          descontado <- atR "pacote,servico"
                  ((\v m k -> v * fromIntegral m * (1 -k) ) <$> atR "servico" (idxK "price") <*> idxK "pacote"
                        <*> idxK "desconto") -< ()
          pag <- pagamentoArr -< Just descontado
          returnA -< Just . tblist . pure . _tb  $ pag



importarofx = BoundedPlugin2 "OFX Import" tname  url
  where
    tname = "account_file"
    url :: ArrowReader
    url = proc t -> do
      fn <- idxR "file_name" -< t
      i <- idxR "import_file" -< t
      r <- atR "account" $ idxR "id_account" -< t
      atR "statements,account" (proc t -> do
        odxR "fitid" -< t
        odxR "memo" -< t
        atR "trntype" (odxR "trttype") -< t
        odxR "dtposted" -< t
        odxR "dtuser" -< t
        odxR "dtavail" -< t
        odxR "trnamt" -< t
        odxR "correctfitid" -< t
        odxR "srvrtid" -< t
        odxR "checknum" -< t
        odxR "refnum" -< t
        odxR "sic" -< t
        odxR "payeeid" -< t
        ) -< t
      b <- act (fmap join . traverse (\(TB1 (SText i), (LeftTB1 (Just (DelayedTB1 (Just (TB1 (SBinary r) ))))) , acc ) -> liftIO $ ofxPlugin (T.unpack i) (BS.unpack r) acc )) -< liftA3 (,,) fn i r
      let ao :: TB2 Text Showable
          ao =  LeftTB1 $ ArrayTB1 . fmap (tblist . fmap attrT ) <$>  b
          ref :: [Compose Identity (TB Identity ) Text(Showable)]
          ref = [attrT  ("statements",LeftTB1 $ join $ fmap (ArrayTB1 ).   allMaybes . fmap (join . fmap unSSerial . M.lookup "fitid" . M.fromList ) <$> b)]
          tbst :: (Maybe (TB2 Text (Showable)))
          tbst = Just $ tblist [_tb $ FKT ref [Rel "statements" "=" "fitid",Rel "account" "=" "account"] ao]
      returnA -< tbst


notaPrefeitura = BoundedPlugin2 "Nota Prefeitura" tname url
  where
    tname = "nota"
    varTB i = fmap (BS.pack . renderShowable ) . join . fmap unRSOptional' <$>  idxR i
    url ::  ArrowReader
    url = proc t -> do
      i <- varTB "id_nota" -< t
      odxR "nota" -<  t
      r <- atR "inscricao" (proc t -> do
                               n <- varTB "inscricao_municipal" -< t
                               u <- varTB "goiania_user"-< t
                               p <- varTB "goiania_password"-< t
                               returnA -< liftA3 (, , ) n u p  ) -< t
      b <- act (fmap join  . traverse (\(i, (j, k,a)) -> liftIO$ prefeituraNota j k a i ) ) -< liftA2 (,) i r
      let ao =  Just $ tblist [attrT ("nota",    LeftTB1 $ fmap (DelayedTB1 .Just . TB1 ) b)]
      returnA -< ao

queryArtCrea = BoundedPlugin2 "Documento Final Art Crea" tname url
  where
    tname = "art"
    varTB i = fmap (BS.pack . renderShowable ) . join . fmap unRSOptional' <$>  idxR i
    url :: ArrowReader
    url = proc t -> do
      i <- varTB "art_number" -< t
      idxR "payment_date" -<  t
      odxR "art" -<  t
      r <- atR "crea_register" (proc t -> do
                               n <- varTB "crea_number" -< t
                               u <- varTB "crea_user"-< t
                               p <- varTB "crea_password"-< t
                               returnA -< liftA3 (, , ) n u p  ) -< t
      b <- act (fmap join  . fmap traceShowId . traverse (\(i, (j, k,a)) -> liftIO$ creaLoginArt  j k a i ) ) -< liftA2 (,) i r
      let ao =  traceShowId $ Just $ tblist [attrT ("art",    LeftTB1 $ fmap (DelayedTB1 . Just . TB1 ) b)]
      returnA -< ao


queryArtBoletoCrea = BoundedPlugin2  pname tname url
  where
    pname = "Boleto Art Crea"
    tname = "art"
    varTB i = fmap (BS.pack . renderShowable ) . join . fmap unRSOptional' <$>  idxR i
    url :: ArrowReader
    url = proc t -> do
      i <- varTB "art_number" -< t
      idxR "verified_date" -< t
      odxR "boleto" -< t
      r <- atR "crea_register" (proc t -> do
                               n <- varTB "crea_number" -< t
                               u <- varTB "crea_user"-< t
                               p <- varTB "crea_password"-< t
                               returnA -< liftA3 (, , ) n u p  ) -< t
      b <- act ( traverse (\(i, (j, k,a)) -> lift $ creaBoletoArt  j k a i ) ) -< liftA2 (,) i r
      let ao =  Just $ tblist [attrT ("boleto",   LeftTB1 $ fmap ( DelayedTB1 . Just) $ (TB1 . SBinary. BSL.toStrict) <$> b)]
      returnA -< ao



queryArtAndamento = BoundedPlugin2 pname tname url
  where
    tname = "art"
    pname = "Andamento Art Crea"
    varTB i =  fmap (BS.pack . renderShowable ) . join . fmap unRSOptional' <$>  idxR i
    url :: ArrowReader
    url = proc t -> do
      i <- varTB "art_number" -< ()
      odxR "payment_date" -< ()
      odxR "verified_date" -< ()
      r <- atR "crea_register"
          (liftA3 (,,) <$> varTB "crea_number" <*> varTB "crea_user" <*> varTB "crea_password") -< t
      v <- act (fmap (join .maybeToList) . traverse (\(i, (j, k,a)) -> liftIO  $ creaConsultaArt  j k a i ) ) -< liftA2 (,) i r
      let artVeri dm = ("verified_date" ,) . LeftTB1 . join $(\d ->  fmap (TB1 . STimestamp . fst) $ strptime "%d/%m/%Y %H:%M" ( d !!1) ) <$> dm
          artPayd dm = ("payment_date" ,) . LeftTB1 . join $ (\d -> fmap (TB1 . STimestamp . fst )  $ strptime "%d/%m/%Y %H:%M" (d !!1) ) <$> dm
          artInp inp = Just $ tblist $fmap attrT   $ [artVeri $  L.find (\[h,d,o] -> L.isInfixOf "Cadastrada" h )  inp ,artPayd $ L.find (\[h,d,o] -> L.isInfixOf "Registrada" h ) (inp) ]
      returnA -< artInp (traceShowId v)


{- testPlugin  db sch p = withConnInf db sch (\inf -> do
                                       let rp = tableView (tableMap inf) (fromJust $ M.lookup (_bounds p) (tableMap inf))
                                           bds = _arrowbounds p
                                           rpd = accessTB  (fst bds <> snd bds) (markDelayed True rp)
                                           rpq = selectQuery rpd
                                       print rpq
                                       q <- queryWith_ (fromAttr (unTlabel rpd) ) (conn  inf) (fromString $ T.unpack $ rpq)
                                       return $ q
                                           )

-}

plugList :: [Plugins]
plugList = [createEmail,renderEmail ,lplugContract ,lplugOrcamento ,lplugReport,siapi3Plugin ,siapi2Plugin , importarofx,gerarPagamentos , pagamentoServico , notaPrefeitura,queryArtCrea , queryArtBoletoCrea , queryCEPBoundary,queryGeocodeBoundary,queryCPFStatefull , queryCNPJStatefull, queryArtAndamento]
