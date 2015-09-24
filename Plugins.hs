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
module Plugins where

import Query
import Types
import qualified Data.Binary as B
import Step
import Location
import PrefeituraSNFSE
import Siapi3
import CnpjReceita
import Control.Monad.Reader
import Control.Concurrent
import Data.Functor.Apply
import System.Environment
import Debug.Trace
import Data.Ord
import OFX
import Data.Time.Parse
import Utils
import Schema
import Data.Char (toLower)
import PandocRenderer
import Data.Maybe
import Data.Functor.Identity
import Control.Applicative
import Data.Traversable (traverse)
import qualified Data.Traversable as Tra
import Data.Time.LocalTime
import qualified Data.List as L
import qualified Data.Vector as Vector
import qualified Data.ByteString.Char8 as BS
import qualified Data.ByteString.Lazy.Char8 as BSL
import Data.Time

import RuntimeTypes
import Data.Monoid hiding (Product(..))

import qualified Data.Foldable as F
import qualified Data.Text.Lazy as T
import Data.ByteString.Lazy(toStrict)
import Data.Text.Lazy.Encoding
import Data.Text.Lazy (Text)
import qualified Data.Set as S


import qualified Data.Map as M
import Data.String


import Control.Arrow
import Crea

lplugOrcamento = BoundedPlugin2 "Orçamento" "pricing" (fst renderProjectPricingA )  ( snd renderProjectPricingA )
lplugContract = BoundedPlugin2 "Contrato" "pricing" (fst renderProjectContract )  ( snd renderProjectContract )
lplugReport = BoundedPlugin2 "Relatório " "pricing" (fst renderProjectReport )  ( snd renderProjectReport )



siapi2Plugin = BoundedPlugin2  pname tname (staticP url) elemp
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

    elemp inf = maybe (return Nothing) (\inp -> do
                              b <- runReaderT (dynPK url $ () ) (Just inp)
                              return $ liftKeys inf tname   <$> b)
    tailEmpty [] = []
    tailEmpty i  = tail i


analiseProjeto = BoundedPlugin2 pname tname (staticP url ) elemp
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
    elemp inf = maybe (return Nothing) (geninf inf)
    geninf inf inp = do
            b <- runReaderT (dynPK url $ () ) (Just inp)
            return $ liftKeys inf tname  <$> b



siapi3Plugin  = BoundedPlugin2 pname tname  (staticP url) elemp

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
    elemp inf = maybe (return Nothing) (geninf inf)
    geninf inf inp = do
            b <- runReaderT (dynPK url $ () ) (Just inp)
            return $ liftKeys inf tname  <$> b

bool = TB1 . SBoolean
num = TB1 . SNumeric

lookKey' inf t k = justError ("lookKey' cant find key " <> show k <> " in " <> show t) $  foldr1 mplus $ fmap (\ti -> M.lookup (ti,k) (keyMap inf)) t

eitherToMaybeT (Left i) =  Nothing
eitherToMaybeT (Right r) =  Just r


sdate = SDate . localDay
stimestamp = STimestamp




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
fktR i rel f = atR (L.intercalate "," (fmap fst i)) (FKT (attrT <$> i) rel <$> f)

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


gerarPagamentos = BoundedPlugin2 "Gerar Pagamento" tname  (staticP url) elem
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

    elem inf = maybe (return Nothing) (\inp -> do
                  b <- runReaderT (dynPK   url $ ())  (Just inp)
                  return $ liftKeys inf tname  <$> b )

pagamentoServico = BoundedPlugin2 "Gerar Pagamento" tname (staticP url) elem
  where
    tname = "servico_venda"
    url :: ArrowReader
    url = proc t -> do
          descontado <- atR "pacote,servico"
                  ((\v m k -> v * fromIntegral m * (1 -k) ) <$> atR "servico" (idxK "price") <*> idxK "pacote"
                        <*> idxK "desconto") -< ()
          pag <- pagamentoArr -< Just descontado
          returnA -< Just . tblist . pure . _tb  $ pag

    elem inf = maybe (return Nothing) (\inp -> do
                      b <- runReaderT (dynPK   url $ ())  (Just inp)
                      return $  liftKeys inf tname  <$> b
                            )


importarofx = BoundedPlugin2 "OFX Import" tname  (staticP url) elem
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
    elem inf = maybe (return Nothing) (\inp -> do
                b <- runReaderT (dynPK url ()) (Just inp)
                return $ liftKeys inf  tname  <$> b)


notaPrefeitura = BoundedPlugin2 "Nota Prefeitura" tname (staticP url) elem
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
    elem inf = maybe (return Nothing) (\inp -> do
                              b <- runReaderT (dynPK url  ()) (Just inp)
                              return $ liftKeys inf tname  <$> b
                            )

queryArtCrea = BoundedPlugin2 "Documento Final Art Crea" tname (staticP url) elem
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
    elem inf = maybe (return Nothing) (\inp -> do
                              b <- runReaderT (dynPK url  $ ()) (Just inp)
                              return $ liftKeys inf tname . traceShowId <$> b
                            )


queryArtBoletoCrea = BoundedPlugin2  pname tname (staticP url) elem
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
    elem inf
       = maybe (return Nothing) (\inp -> do
                            b <- runReaderT (dynPK url $ () ) (Just inp)
                            return $ liftKeys inf tname <$> b )



queryArtAndamento = BoundedPlugin2 pname tname (staticP url) elemp
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
    elemp inf
          = maybe (return Nothing) (\inp -> do
                   b <- runReaderT (dynPK url $ () )  (Just inp)
                   return $  liftKeys inf tname  <$> b)


queryCPFStatefull =  StatefullPlugin "CPF Receita" "owner" [staticP arrowF,staticP arrowS]   [[("captchaViewer",Primitive "jpg") ],[("captchaInput",Primitive "character varying")]] cpfCall
    where
      arrowF ,arrowS :: ArrowReader
      arrowF = proc t -> do
              atAny "ir_reg" [idxR "cpf_number"] -< t
              odxR "captchaViewer" -< t
              returnA -< Nothing
      arrowS = proc t -> do
              idxR "captchaInput" -< t
              odxR "owner_name" -< t
              returnA -< Nothing


queryCNPJStatefull = StatefullPlugin "CNPJ Receita" "owner"
  [staticP arrowF ,staticP arrowS ]
  [[("captchaViewer",Primitive "jpg") ],[("captchaInput",Primitive "character varying")]] wrapplug
    where arrowF ,arrowS :: ArrowReader
          arrowF = proc t -> do
            atAny "ir_reg" [idxR "cnpj_number"] -< t
            odxR "captchaViewer"-< t
            returnA -< Nothing
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

plugList = [lplugContract ,lplugOrcamento ,lplugReport,siapi3Plugin ,siapi2Plugin , importarofx,gerarPagamentos , pagamentoServico , notaPrefeitura,queryArtCrea , queryArtBoletoCrea , queryCEPBoundary,{-queryGeocodeBoundary,-}queryCNPJStatefull,queryCPFStatefull,queryArtAndamento]
