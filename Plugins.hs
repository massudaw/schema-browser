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

module Plugins (importargpx ,plugList,lplugOrcamento, siapi3Plugin) where

import qualified NonEmpty as Non
import System.Process
import Control.Monad.Catch
import Location
import Data.Interval(Extended(..),interval,lowerBound',upperBound)
import PrefeituraSNFSE
import Text
import qualified Data.Vector as V
import Data.Tuple
import Incendio
import DWGPreview
import Siapi3
import CnpjReceita
import OFX
import Crea
import  GHC.Stack
import PandocRenderer
import Gpx
import OAuthClient

import Types
import Types.Index
import Types.Patch
import Step.Client
import RuntimeTypes
import Utils

import Network.Mail.Mime
import Control.Monad.Reader
import Data.Functor.Apply
import Debug.Trace
import Data.Time.Parse
import Prelude hiding (elem)
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
import qualified Data.Foldable as F


lplugOrcamento = FPlugins "Orçamento" "pricing" $ BoundedPlugin2 renderProjectPricingA
lplugContract = FPlugins "Contrato" "pricing" $ BoundedPlugin2 renderProjectContract
lplugReport = FPlugins "Relatório" "pricing" $ BoundedPlugin2 renderProjectReport

siapi2Hack = FPlugins pname tname $ BoundedPlugin2  url
  where
    pname ="Siapi2 Hack"
    tname = "hack"
    value_mapping = [("RAZÃO SOCIAL", "razao_social")
                    ,("NOME FANTASIA","nome_fantasia")
                    ,("CNPJ","cpf_cnpj")
                    ,("LOGRADOURO","logradouro")
                    ,("BAIRRO","bairro")
                    ,("NÚMERO","numero")
                    ,("CIDADE","cidade")
                    ,("PONTO DE REFERÊNCIA","referencia")
                    ,("FONE","fone")
                    ,("REVENDA","revenda")
                    ,("TIPO DE SERVIÇO","tipo_servico")
                    ,("DATA DO SERVIÇO","data_servico")
                    ,("TIPO DE EDIFICAÇÃO","tipo_edi")
                    ,("ÁREA CONSTRU","area_cons")
                    ,("VALOR","valor_taxa")
                    ,("LOCAL DE ATEND","local")
                    ,("REGIÃO DE ATEN","regiao")]
    varTB i =  fmap (BS.pack . renderShowable ) . join . fmap unSOptional' <$>  idxR i
    url :: ArrowReader
    url = proc t -> do
      protocolo <- varTB "protocolo" -< t
      ano <- varTB "ano" -< t
      odxR "razao_social" -< ()
      Tra.traverse odxM (L.delete "razao_social" $ snd <$> value_mapping) -< ()
      atR "andamentos" (proc t -> do
        odxR "andamento_date" -<  t
        odxR "andamento_description" -<  t) -< t
      b <- act (Tra.traverse  (\(i,j)-> if read (BS.unpack j) >= 15 then  return (Nothing,Nothing) else liftIO (siapi2  i (j) )  )) -<  (liftA2 (,) protocolo ano )
      let ao (sv,bv)  = Just $ tblist   $ svt  sv <> [iat $ bv]
          convertAndamento :: [String] -> TB2 Text (Showable)
          convertAndamento [da,des] =  TB1 $ tblist $ fmap attrT  $  ([("andamento_date",TB1 . STimestamp . fst . justError "wrong date parse" $  strptime "%d/%m/%y" da  ),("andamento_description",TB1 $ SText (T.filter (not . (`elem` "\n\r\t")) $ T.pack  des))])
          convertAndamento i = error $ "convertAndamento " <> show i
          svt bv = catMaybes $ fmap attrT . (\i -> traverse (\k -> fmap snd $ L.find (L.isInfixOf k. fst ) map) (swap i)) <$>  value_mapping
            where map = fmap (LeftTB1 . Just . TB1 . SText . T.pack ) <$> bv
          iat bv = _tb  (IT
                            "andamentos"
                            (LeftTB1 $ Just $ ArrayTB1 $ Non.fromList $ reverse $  fmap convertAndamento bv))
      returnA -< join  (  ao    <$> join (fmap (uncurry (liftA2 (,))) b))



siapi2Plugin = FPlugins pname tname $ BoundedPlugin2  url
  where
    pname ="Siapi2 Andamento"
    tname = "siapi3"
    varTB i =  fmap (BS.pack . renderShowable ) . join . fmap unSOptional' <$>  idxR i
    url :: ArrowReader
    url = proc t -> do
      protocolo <- varTB "protocolo" -< t
      ano <- varTB "ano" -< t
      odxR "aproval_date" -< ()
      atR "andamentos" (proc t -> do
        odxR "andamento_date" -<  t
        odxR "andamento_description" -<  t) -< t
      b <- act ( Tra.traverse  (\(i,j)-> if read (BS.unpack j) >= 15 then  return (Nothing ,Nothing) else liftIO (siapi2  i j >> error "siapi2 test error")  )) -<  (liftA2 (,) protocolo ano )
      let ao bv  = Just $ tblist   [iat bv]
          convertAndamento :: [String] -> TB2 Text (Showable)
          convertAndamento [da,des] =  TB1 $ tblist $ fmap attrT  $  ([("andamento_date",TB1 . STimestamp . fst . justError "wrong date parse" $  strptime "%d/%m/%y" da  ),("andamento_description",TB1 $ SText (T.filter (not . (`elem` "\n\r\t")) $ T.pack  des))])
          convertAndamento i = error $ "convertAndamento " <> show i
          iat bv = Compose . Identity $ (IT
                            "andamentos"
                            (LeftTB1 $ Just $ ArrayTB1 $ Non.fromList $  reverse $  fmap convertAndamento bv))
      returnA -< join  (  ao  .  tailEmpty . join <$> join (fmap snd b))
    tailEmpty :: [a] -> [a]
    tailEmpty [] = []
    tailEmpty i  = tail i

cpfCaptcha = BoundedPlugin2 url
  where
    url :: ArrowReader
    url = proc t -> do
      sess <- act (\_ -> lift  initSess ) -< ()
      cap <- act (\sess -> lift (getCaptchaCpf sess)) -< sess
      atR "ir_reg" (idxK"cpf_number") -<()
      odxR "sess" -< ()
      odxR "captchaViewer" -< ()
      returnA -< Just $ tblist [attrT  ("sess", TB1 (SSession sess)) ,attrT ("captchaViewer",TB1 (SBinary $ justError "no captcha" cap))]

cnpjCaptcha = BoundedPlugin2 url
  where
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

cpfForm = BoundedPlugin2 url
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
      returnA -<   join .join $ fmap convertCPF <$> html
    arrowS = proc t -> do
              odxR "owner_name" -< t
              returnA -< Nothing

atPrim  p = Primitive (AtomicPrim p )

queryCPFStatefull = FPlugins "CPF Receita" "owner" $ StatefullPlugin
  [(([],[("captchaViewer",atPrim (PMime "image/jpg") )
    ,("sess",atPrim PSession )])
    ,cpfCaptcha)
  ,(([("nascimento",atPrim PDate )
    ,("captchaInput",atPrim PText )],[])
    ,cpfForm)]


queryCNPJStatefull = FPlugins "CNPJ Receita" "owner" $ StatefullPlugin
  [(([],[("captchaViewer",atPrim (PMime "image/jpg") )
    ,("sess",atPrim PSession )])
    ,cnpjCaptcha)
  ,(([("captchaInput",atPrim PText )],[])
    ,cnpjForm)]



cnpjForm = BoundedPlugin2 url
  where
    pname , tname :: Text
    pname = "CNPJ Form"
    tname = "owner"
    url :: ArrowReader
    url = proc t -> do
      cap <- idxK "captchaInput" -< ()
      cnpj <- atR "ir_reg" (idxK "cnpj_number") -< ()
      sess <- idxK "sess" -< ()
      html :: Maybe [(String,String)] <- act (\(TB1 (SSession sess),TB1 (SText cap),TB1 (SText cnpj))  -> fmap join $ lift  (getCnpjForm sess (BS.pack $ T.unpack cap) (BS.pack $ T.unpack cnpj) )) -< (sess,cap,cnpj)

      arrowS -< ()
      returnA -<   join $ fmap unTB1 .  convertHtml . (M.fromListWith (++) . fmap (fmap pure )) <$> html
    arrowS = proc t -> do
              odxR "owner_name" -< t
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
              odxR "number" -< t
              odxR "uf" -< t
              odxR "cep" -< t
              odxR "complemento" -< t
              odxR "municipio" -< t
              odxR "bairro" -< t


analiseProjeto = FPlugins pname tname $ BoundedPlugin2 url
  where
    pname , tname :: Text
    pname = "Cadastro Bombeiro"
    tname = "fire_project"
    varTB i =  fmap (BS.pack . renderShowable ) . join . fmap unSOptional' <$>  idxR i
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


doubleP s = (\(TB1 (SDouble ar)) -> ar) <$> idxK s
intP s = (\(TB1 (SNumeric ar)) -> ar) <$> idxK s
doubleA s =  (\(ArrayTB1 i) -> fmap (\(TB1 (SDouble v)) -> v)  i) <$> idxK s

germinacao = FPlugins pname tname $ PurePlugin  url

  where
    pname , tname :: Text
    pname = "previsao = plantio + periodo_germinacao"
    tname = "plantio"
    url :: ArrowReaderM Identity
    url = proc t -> do
      plant <- idxK "plantio"  -< ()
      poly <- atR "planta" (idxK "periodo_germinacao" ) -< ()
      odxR "previsao_germinacao" -< ()
      returnA -< Just $ (\(TB1 (SDate d)) (IntervalTB1 i)  -> tblist [_tb $ Attr "previsao_germinacao" (LeftTB1 $ Just $ IntervalTB1 $ ((\(TB1 i) -> TB1 $ SDate$  addDays  (fromIntegral i)d ) <$>   i))] )  plant  poly

preparoInsumo = FPlugins pname tname $ PurePlugin  url

  where
    pname , tname :: Text
    pname = "previsao = producao + periodo_preparo"
    tname = "insumo_producao"
    url :: ArrowReaderM Identity
    url = proc t -> do
      plant <- idxK "producao"  -< ()
      poly <- atR "insumo" (idxK "periodo_preparo" ) -< ()
      odxR "previsao_preparo" -< ()
      returnA -< Just $ (\(TB1 (SDate d)) (IntervalTB1 i)  -> tblist [_tb $ Attr "previsao_preparo" (LeftTB1 $ Just $ IntervalTB1 $ ((\(TB1 i) -> TB1 $ SDate$  addDays  (fromIntegral i)d ) <$>   i))] )  plant poly



areaDesign = FPlugins pname tname $ PurePlugin  url

  where
    pname , tname :: Text
    pname = "Area Design"
    tname = "deposito"
    url :: ArrowReaderM Identity
    url = proc t -> do
      odxR "densidade"  -< ()
      (ar,a) <-  (,) <$> doubleP "area_operacao" <*> doubleP "altura_armazenamento"  -< ()
      poly <- atR "classe" ((\i -> (\x -> sum $ zipWith (\j i -> i * x^j ) [0..] (F.toList i))) <$> doubleA "curva") -< ()
      let
          af = (nbrFig3 a/100) * solve ar poly
      returnA -< Just $ tblist [_tb $ Attr "densidade" (LeftTB1 $ Just $ (TB1 . SDouble) $ af)]

designDeposito = FPlugins "Design Deposito" "deposito" $ StatefullPlugin
  [(([],[
    ("minimal_flow",atPrim PDouble), ("min_sprinkler_count",atPrim $ PInt 4),("min_supply_volume",atPrim PDouble)])
    ,minimalDesign)]

subdivision = FPlugins "Minimal Sprinkler" "sprinkler" $ StatefullPlugin
  [(([],[("min_regions",atPrim $ PInt 4)]), PurePlugin url)]
  where
    pname , tname :: Text
    pname = "Minimal Subdivision"
    tname = "sprinkler"
    url :: ArrowReaderM Identity
    url = proc t -> do
      asp <- atR "project" (atR "dados_projeto" (doubleP "area")) -< ()
      tdur <- atR "risk" (doubleP "area_limit") -< ()
      odxR "min_regions" -< ()
      returnA -< Just $ tblist $ _tb <$>
         [Attr "min_regions" ((TB1 . SNumeric )  (ceiling $ asp/tdur))]



minimalDesign = PurePlugin url
  where
    url :: ArrowReaderM Identity
    url = proc t -> do
      d <- doubleP "densidade"  -< ()
      a <- doubleP "area_operacao"  -< ()
      asp <- atR "densidade" (doubleP "area") -< ()
      tdur <- atR "altura_armazenamento,classe" (doubleP "tempo") -< ()
      odxR  "minimal_flow" -< ()
      odxR  "min_sprinkler_count" -< ()
      odxR  "min_supply_volume" -< ()
      let af = d * fromIntegral msc * asp * 60
          msc = ceiling $ a / asp
          msv =  tdur * af *60
      returnA -< Just $ tblist $ _tb <$>
            [ Attr "min_supply_volume" ((TB1 . SDouble)  msv)
            , Attr "minimal_flow" ((TB1 . SDouble)  af)
            , (Attr "min_sprinkler_count" . TB1 . SNumeric ) msc]




siapi3Taxa = FPlugins pname tname  $ PurePlugin url

  where
    pname , tname :: Text
    pname = "Protocolar Processo"
    tname = "fire_project"
    url :: ArrowReaderM Identity
    url = proc t -> do
      atR "protocolo,ano" ((,) <$> odxR "ano" <*> odxR "protocolo") -< ()
      v <- atR "id_project" (
          (,) <$> atK "address" ((,,) <$> idxK "cep" <*> idxK "quadra" <*> idxK "lotes")
              <*> atR "id_owner,id_contact" (atR "id_owner" ((,) <$> idxK "owner_name" <*> atAny "ir_reg" [idxR "cnpj_number" ,idxR "cpf_number"] )))  -< ()

      returnA -< Nothing -- Just $ tblist [_tb $ Attr "protocolo" (TB1 $ SText (T.pack $ show v))]


retencaoServicos = FPlugins pname tname  $ PurePlugin url
  where
    pname , tname :: Text
    pname = "Retencao Nota"
    tname = "nota"
    url :: ArrowReaderM Identity
    url = proc t -> do
      TB1 (SBoolean hasIssqn )<- idxK "issqn_substituicao" -< ()
      odxR "pis_retido" -< ()
      odxR "csll_retido" -< ()
      odxR "irpj_retido" -< ()
      odxR "cofins_retido" -< ()
      odxR "issqn_retido" -< ()
      odxR "valor_liquido" -< ()
      v <- atK "id_payment" (
          doubleP "price"
          ) -< ()
      let pis =  0.0065 * v
          cofins = 0.03 * v
          csll = 0.01 * v
          irpj = 0.015 * v
          issqn = if hasIssqn then 0.05 * v else 0
      returnA -< Just $ tblist $
          _tb <$> [att "pis_retido" pis
          ,att "cofins_retido" cofins
          ,att "csll_retido" csll
          ,att "irpj_retido" irpj
          ,att "issqn_retido" issqn
          ,att "valor_liquido" (v - pis - cofins - csll - irpj - issqn)
          ]


    att i v =   Attr i (LeftTB1 $ Just $ TB1 (SDouble v))



siapi3CheckApproval = FPlugins pname tname  $ DiffPurePlugin url
  where
    pname , tname :: Text
    pname = "Check Approval"
    tname = "siapi3"
    url :: ArrowReaderDiffM Identity
    url = proc t -> do
      odx  (Just $ Range True (Not IsNull)) "aproval_date" -< ()
      v <- catMaybes <$> atRA "andamentos" (
          liftA2 (,) <$> idxR "andamento_description"  <*> idxR "andamento_date"
          ) -< ()
      let app = L.find (\(TB1 (SText x),_) -> "APROVADO" ==   x) v
          tt = L.find ((\(TB1 (SText x)) -> T.isInfixOf "ENTREGUE AO SOLICITANTE APROVADO"  x).fst) v
      row <- act (const ask )-< ()
      returnA -< traceShowId $ fmap ((\(TB1 (STimestamp t)) -> (\v-> (kvempty,maybe (Idex mempty) getIndex row ,[PAttr "aproval_date" v])) .upperPatch.(,True) . Finite $ PAtom $ STimestamp t) .snd) (liftA2 const app tt)

siapi3Inspection = FPlugins pname tname  $ BoundedPlugin2 url
  where
    pname , tname :: Text
    pname = "Siapi3 Inspeção"
    tname = "fire_inspection"
    varTB i =  fmap (BS.pack . renderShowable ) . join . fmap unSOptional' <$>  idxR i
    tobs  =  fmap (BS.pack . renderShowable ) . join . fmap unSOptional'
    url :: ArrowReader
    url = proc t -> do
      cpf <- atR "id_project"
              $ atR "id_owner,id_contact"
                $ atR "id_owner"
                  $ atAny "ir_reg" [varTB "cpf_number",varTB "cnpj_number"] -< t
      v <- atMR "protocolo,ano" (proc cpf -> do
        protocolo <- idxR "protocolo" -< ()
        ano <- idxR "ano" -< ()
        odxR "taxa_paga" -< ()
        odxR "aproval_date" -< ()
        atR "andamentos" (proc t -> do
            odxR "andamento_date" -<  t
            odxR "andamento_description" -<  t
            odxR "andamento_user" -<  t
            odxR "andamento_status" -<  t) -< ()

        b <- act (fmap join .  Tra.traverse   (\(i,j,k)-> if read (BS.unpack j) <= (14 :: Int ) then  return Nothing else liftIO $ siapi3  i j k )) -<   (liftA3 (,,) (tobs $ protocolo ) (tobs $ ano ) cpf)
        let convertAndamento [_,da,desc,user,sta] =TB1 $ tblist  $ fmap attrT  $ ([("andamento_date",TB1 .STimestamp . fst . justError "wrong date parse" $  strptime "%d/%m/%Y %H:%M:%S" da  ),("andamento_description",TB1 . SText $ T.pack  desc),("andamento_user",LeftTB1 $ Just $ TB1 $ SText $ T.pack  user),("andamento_status",LeftTB1 $ Just $ TB1 $ SText $ T.pack sta)] )
            convertAndamento i = error $ "convertAndamento2015 :  " <> show i
        let ao  (bv,taxa) =  Just $ tblist  ( [_tb $ Attr "ano" (justError "ano" ano) ,_tb $ Attr "protocolo" (justError "protocolo"protocolo), attrT ("taxa_paga",LeftTB1 $ Just $  bool $ not taxa),iat bv])
            iat bv = Compose . Identity $ (IT "andamentos"
                           (LeftTB1 $ Just $ ArrayTB1 $ Non.fromList $ reverse $ fmap convertAndamento bv))
        returnA -< traceShowId.(\i -> FKT (kvlist $ _tb <$> [Attr "ano" (LeftTB1 $ ano) ,Attr "protocolo" (LeftTB1 $ protocolo)]) [Rel "protocolo" Equals "protocolo" ,Rel "ano" Equals "ano"] (LeftTB1 $ Just $ TB1 i)) <$> join (ao <$> b)) -< cpf
      returnA -< tblist  . pure . _tb  <$> v


siapi3Plugin  = FPlugins pname tname  $ BoundedPlugin2 url
  where
    pname , tname :: Text
    pname = "Siapi3 Andamento"
    tname = "fire_project"
    varTB i =  fmap (BS.pack . renderShowable ) . join . fmap unSOptional' <$>  idxR i
    tobs  =  fmap (BS.pack . renderShowable ) . join . fmap unSOptional'
    url :: ArrowReader
    url = proc t -> do
      cpf <- atR "id_project"
              $ atR "id_owner,id_contact"
                $ atR "id_owner"
                  $ atAny "ir_reg" [varTB "cpf_number",varTB "cnpj_number"] -< t
      v <- atMR "protocolo,ano" (proc cpf -> do
        protocolo <- idxR "protocolo" -< ()
        ano <- idxR "ano" -< ()
        odxR "taxa_paga" -< ()
        odx (Just (Range True $ Not IsNull)) "aproval_date" -< ()
        atR "andamentos" (proc t -> do
            odxR "andamento_date" -<  t
            odxR "andamento_description" -<  t
            odxR "andamento_user" -<  t
            odxR "andamento_status" -<  t) -< ()

        b <- act (fmap join .  Tra.traverse   (\(i,j,k)-> if read (BS.unpack j) <= (14 :: Int ) then  return Nothing else liftIO $ siapi3  i j k )) -<   (liftA3 (,,) (tobs $ protocolo ) (tobs $ ano ) cpf)
        let convertAndamento [_,da,desc,user,sta] =TB1 $ tblist  $ fmap attrT  $ ([("andamento_date",TB1 .STimestamp . fst . justError "wrong date parse" $  strptime "%d/%m/%Y %H:%M:%S" da  ),("andamento_description",TB1 . SText $ T.pack  desc),("andamento_user",LeftTB1 $ Just $ TB1 $ SText $ T.pack  user),("andamento_status",LeftTB1 $ Just $ TB1 $ SText $ T.pack sta)] )
            convertAndamento i = error $ "convertAndamento2015 :  " <> show i
        let ao  (bv,taxa) =  Just $ tblist  ( [_tb $ Attr "ano" (justError "ano" ano) ,_tb $ Attr "protocolo" (justError "protocolo"protocolo), attrT ("taxa_paga",LeftTB1 $ Just $  bool $ not taxa),iat bv])
            iat bv = Compose . Identity $ (IT "andamentos"
                           (LeftTB1 $ Just $ ArrayTB1 $ Non.fromList $ reverse $ fmap convertAndamento bv))
        returnA -< traceShowId.(\i -> FKT (kvlist $ _tb <$> [Attr "protocolo" (LeftTB1 $ protocolo), Attr "ano" (LeftTB1 $ ano)]) [Rel "protocolo" Equals "protocolo" ,Rel "ano" Equals "ano"] (LeftTB1 $ Just $ TB1 i)) <$> join (ao <$> b)) -< cpf
      returnA -< tblist  . pure . _tb  <$> v

bool = TB1 . SBoolean
num = TB1 . SNumeric

elem :: Char -> String -> Bool
elem = L.elem


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

itR i f = atR i (IT (fromString i)<$> f)

idxRA = fmap (fmap unArray) <$> idxR

gerarParcelas= FPlugins "Gerar Parcelas" tname  $ BoundedPlugin2 url
  where
    tname = "pricing"
    url :: ArrowReader
    url =  proc t -> do
              parcelas :: Maybe (Non.NonEmpty (FTB Showable) )<- idxRA "parcelas"-< ()
              preco :: Maybe (FTB Showable )<- idxR "pricing_price"-< ()
              let
                par :: Maybe (Non.NonEmpty (FTB Showable) )
                par = (\p par -> (p*)<$> par)<$> preco <*> parcelas
              pagamentos <- idxR "pagamentos" -< ()
              pg <- atR  "pagamentos" (proc (pagamentos,parcelas) -> do
                  odxR "payment_description" -<  ()
                  odxR "price" -<  ()
                  let
                    total :: Int
                    total = maybe 0 length parcelas
                  let pagamento = _tb $ FKT (kvlist [attrT  ("pagamentos",LeftTB1 pagamentos )]) [Rel "pagamentos" Equals "id_payment"] (LeftTB1 $ fmap ArrayTB1 $ ( liftA2 (Non.zipWith (\valorParcela ix -> TB1 $ tblist [attrT ("payment_description",TB1 $ SText $ T.pack $ "Parcela (" <> show (ix+1) <> "/" <> show total <>")" ),attrT ("price",valorParcela) ])) parcelas (Just $ Non.fromList [0 .. total])))
                  returnA -<  pagamento ) -< (pagamentos,par)
              returnA -<  Just $ tblist [pg ]

pagamentoArr =  itR "pagamento" (proc descontado -> do
              pinicio <- idxR "inicio"-< ()
              p <- idxR "vezes" -< ()
              let valorParcela = liftA2 (liftA2 (/))  descontado p
              pg <- atR  "pagamentos" (proc (valorParcela,pinicio,p) -> do
                  odxR "description" -<  ()
                  odxR "price" -<  ()
                  odxR "scheduled_date" -<  ()
                  let total = maybe 0 fromIntegral  p :: Int
                  let pagamento = _tb $ FKT (kvlist [attrT  ("pagamentos",LeftTB1 (Just $ ArrayTB1  $ Non.fromList (replicate total (num $ -1) )) )]) [Rel "pagamentos" Equals "id"] (LeftTB1 $ Just $ ArrayTB1 $ Non.fromList ( fmap (\ix -> TB1 $ tblist [attrT ("id",SerialTB1 Nothing),attrT ("description",LeftTB1 $ Just $ TB1 $ SText $ T.pack $ "Parcela (" <> show ix <> "/" <> show total <>")" ),attrT ("price",LeftTB1 valorParcela), attrT ("scheduled_date",LeftTB1 pinicio) ]) ([1 .. total])))
                  returnA -<  pagamento ) -< (valorParcela,pinicio,p)
              returnA -<  TB1 $ tblist [pg ] )


gerarPagamentos = FPlugins "Gerar Pagamento" tname  $ BoundedPlugin2 url
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



createEmail = FPlugins  "Create Email" "messages"
  $ StatefullPlugin [(([("plain",atPrim (PMime "text/plain") )],[]),generateEmail)]

generateEmail = BoundedPlugin2   url
  where
    tname ="messages"
    url :: ArrowReader
    url = proc t -> do
          plain <- idxK "plain" -< ()
          odxR "raw" -< ()
          mesg <- act (lift .buildmessage )-< plain
          returnA -< Just . tblist . pure . attrT  . ("raw",) . LeftTB1 $  Just   mesg

    buildmessage :: FTB Showable -> IO (FTB Showable)
    buildmessage (TB1 (SBinary mesg ))= TB1 .SText . T.pack . BS.unpack . B64Url.encode .BSL.toStrict <$>  ( renderMail' $ Mail (Address Nothing "wesley.massuda@gmail.com") [Address Nothing "wesley.massuda@gmail.com"] [] [] [] [[mail]])
          where mail = (Part "text/plain" None Nothing [] (BSL.fromStrict $   mesg))


renderEmail = FPlugins  "Render Email" "messages" $ StatefullPlugin
  [(([],[("message_viewer",Primitive $ RecordPrim ("gmail","mime"))])
    ,encodeMessage )]


encodeMessage = PurePlugin url
  where
    messages = nameI 0 $ proc t -> do
          enc <- liftA2 ((,))
                ((\i j -> (,j ) <$> i) <$> idxR "mimeType" <*> idxM "filename" )
                (atR "body"
                    (proc t -> do
                        d <- join . traverse decoder' <$> (idxM "data") -< ()
                        m <- atR "attachmentId" (join . traverse decoder' <$> (idxM "data")) -< ()
                        returnA -< d <> m
                        ))  -< ()
          part <- atMA "parts"
                    (callI 0 messages) -< ()
          let mimeTable ((TB1 (SText mime),filenameM),v) next
                | T.isInfixOf "text/plain" mime || T.isInfixOf "plain/text" mime =  Just $ tb "plain"
                | T.isInfixOf "text/html" mime =  Just $ tb "html"
                | T.isInfixOf "application/pdf" mime =  Just $ deltb "pdf"
                | T.isInfixOf "application/octet-stream" mime =
                      case T.drop (T.length filename - 3 ) filename of
                         "dwg" -> (\v -> case (\(TB1 (SBinary i )) ->  preview $ BSL.fromStrict i) $ v of
                                    Right l -> tbv "png" (Just $ TB1 (SBinary $ BSL.toStrict $l))
                                    Left l -> tbv "bmp" (Just $ TB1 (SBinary $ BSL.toStrict $l))) <$> v
                         i -> Nothing
                | T.isInfixOf "application/pgp-signature" mime =  Just $ tb "plain"
                | T.isInfixOf "multipart/alternative" mime =  last <$> (ifNull . catMaybes $ next)
                | T.isInfixOf "multipart" mime =   Just  $ tbmix (catMaybes next)
                | otherwise =Nothing
                where
                      Just (TB1 (SText filename ))= filenameM
                      tb n  =  TB1 . tblist . pure . _tb . Attr n $ (LeftTB1 $  v)
                      tbv n v  =  TB1 . tblist . pure . _tb . Attr n $ (LeftTB1 $  v)
                      deltb n  =  TB1 . tblist . pure . _tb . Attr n $ (LeftTB1 $ Just $ DelayedTB1 $    v)
                      tbmix l = TB1 . tblist . pure . _tb . IT "mixed" . LeftTB1 $ ArrayTB1 . Non.fromList <$>  (ifNull l )
          returnA -<  (maybe Nothing (flip mimeTable part )  $ (\(i,j) -> fmap (,j) i) enc)
    mixed =  nameO 1 (proc t ->  do
                liftA3 (,,)
                  (odxR "plain")
                  (atR "mixed" (callO 1 mixed))
                  (odxR "html") -< ()
                returnA -< ()
                )
    url :: ArrowReaderM Identity
    url = proc t -> do
          res <- atR "payload" messages -< ()
          atR "message_viewer" mixed -< ()
          returnA -< tblist . pure . _tb . IT "message_viewer"  <$>  res

    ifNull i = if L.null i then  Nothing else Just i
    decoder (SText i) =  (Just . SBinary) . B64Url.decodeLenient . BS.pack . T.unpack $ i
    decoder' (TB1 i) = fmap TB1 $ decoder i
    decoder' (LeftTB1 i) =  (join $ fmap decoder' i)


pagamentoServico = FPlugins "Gerar Pagamento" tname $ BoundedPlugin2 url
  where
    tname = "servico_venda"
    url :: ArrowReader
    url = proc t -> do
          descontado <- atR "pacote,servico"
                  ((\v m k -> v * fromIntegral m * (1 -k) ) <$> atR "servico" (idxK "price") <*> idxK "pacote"
                        <*> idxK "desconto") -< ()
          pag <- pagamentoArr -< Just descontado
          returnA -< Just . tblist . pure . _tb  $ pag

fetchofx = FPlugins "Itau Import" tname $ DiffIOPlugin url
  where
    tname = "itau_import"
    url :: ArrowReaderDiffM IO
    url = proc t  -> do
        idx <-idxK "id" -< ()
        (pass ,r) <- atR "login_credentials" (proc c -> do
            nu <- idxK "operator_number" -< c
            na <- idxK "operator_name" -< c
            pas <- idxK "password" -< c
            r <- atR "conta" $ idxK "id_account" -< c
            returnA -< ([nu,na,pas],r)) -< ()

        IntervalTB1 range <- idxK "range" -< ()
        (fname,file,date) <- act (\(range,i) -> liftIO$ do
              t <- getCurrentTime
              let fname = "extrato-" <> renderShowable (justError "cant be infinite " $ unFinite $ (upperBound range)) <> "," <> show (utctDay t) <>".ofx"
                  input = L.intercalate ";" $ ["echo \"" <> "OP" <> "\""] <> ((\i ->  "echo \"" <> renderShowable i<> "\"" ) <$> (i<>[ justError "cant be infinite " $unFinite $ (upperBound range)]))
              callCommand ( "(" <> input <> " | cat) | xvfb-run --server-args='-screen 0, 1440x900x24' ofx-itau ;") `catchAll` (\e -> print e)
              print $ "readFile " ++ fname
              file <- BS.readFile fname
              return (TB1 $ SText $ T.pack $ fname , LeftTB1 $ Just $ DelayedTB1 $ Just $ TB1 $ SBinary file,upperPatch (Finite $ (PAtom $ SDate $ utctDay t),False))
                 ) -< (range, pass)
        odx  (Just $ Range True  ((BinaryConstant Equals CurrentDate))) "range" -< ()

        atR "ofx" (proc t -> do
            odxR "file_name" -<()
            odxR "import_file" -< ()
            odxR "account" -< ()) -< ()
        refs <- atRA "ofx" (idxK "file_name") -< ()
        let ix = length refs
        pk <- act (const ask )-< ()
        returnA -<  traceShowId $ Just (kvempty,Idex (pure (SerialTB1 $ Just idx)), [PFK [Rel "ofx" Equals "file_name" ] ([PAttr "ofx" (POpt $ Just $ PIdx ix $ Just $ patch fname)]) (POpt $ Just $ PIdx ix $ Just $ PAtom $ (kvempty,Idex (pure fname) ,[PAttr "account" (patch r),PAttr "file_name" (patch fname),PAttr "import_file" (patch $ file)])), PAttr "range" (date)])


importargpx = FPlugins "Importar GPX" tname $ DiffIOPlugin url
  where
    tname = "import_gpx"
    url :: ArrowReaderDiffM IO
    url = proc t -> do
      fn <- idxK "file_name" -< t
      r <- atR "run" $ idxK "id_run" -< t
      atR "run,samples" (proc t -> do
        odxR "instant" -< t
        odxR "position" -< t
        odxR "id_sample" -< t
        odxR "id_run" -< t
        ) -< t

      b <- act (\(TB1 (SBinary i )) -> liftIO . gpx $ BS.unpack i ) -< fn
      let ao :: Index (TB2 Text Showable)
          ao =  POpt $ join $ patchSet .  fmap (\(ix,a) -> PIdx ix . Just . PAtom . (mempty,Idex [int ix],) . fmap patch $ (Attr "id_run"  r : Attr "id_sample" (int ix) : a)) <$>  join (nonEmpty . zip [0..] <$> b)
          ref :: [TB Identity  Text Showable]
          ref = [uncurry Attr  $ ("samples",ArrayTB1 $ Non.fromList $ fmap int   [0.. length (justError "no b" b)])]
          tbst :: (Maybe (TBIdx Text (Showable)))
          tbst = traceShowId $ Just $ (mempty , Idex [r],  [PFK  [Rel "samples" Equals "id_sample",Rel "run" Equals "id_run"] (fmap patch ref) ao])
      returnA -< tbst


importarofx = FPlugins "OFX Import" tname  $ BoundedPlugin2 url
  where
    tname = "account_file"
    url :: ArrowReader
    url = proc t -> do
      fn <- idxK "file_name" -< t
      i <- idxK "import_file" -< t
      r <- atR "account" $ idxK "id_account" -< t
      atR "statements,account" (proc t -> do
        odxR "fitid" -< t
        odxR "memo" -< t
        odxR "trntype" -< t
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

      b <- act ofx  -< (,,) fn i r
      let ao :: TB2 Text Showable
          ao =  LeftTB1 $ ArrayTB1 . Non.fromList . fmap (TB1 . tblist . fmap _tb) <$>  join (nonEmpty <$> b)
          ref :: [Compose Identity (TB Identity ) Text(Showable)]
          ref = [attrT  ("statements",LeftTB1 $ join $ fmap (ArrayTB1 .  Non.fromList  ).   allMaybes . fmap (join . fmap unSSerial . fmap _tbattr .L.find (("fitid"==). _tbattrkey ) ) <$> b)]
          tbst :: (Maybe (TBData Text (Showable)))
          tbst = Just $ tblist $ fmap _tb [FKT (kvlist ref) [Rel "statements" Equals "fitid",Rel "account" Equals "account"] ao]
      returnA -< tbst
    ofx (TB1 (SText i), ((DelayedTB1 (Just (TB1 (SBinary r) )))) , acc )
      = liftIO $ ofxPlugin (T.unpack i) (BS.unpack r) acc
    ofx i = errorWithStackTrace (show i)


notaPrefeitura = FPlugins "Nota Prefeitura" tname $ BoundedPlugin2 url
  where
    tname = "nota"
    varTB i = fmap (BS.pack . renderShowable ) . join . fmap unSOptional' <$>  idxR i
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

queryArtCreaData = FPlugins "Art Crea Data" tname $ BoundedPlugin2 url
  where
    tname = "art"
    varTB i = fmap (BS.pack . renderShowable ) . join . fmap unSOptional' <$>  idxR i
    url :: ArrowReader
    url = proc t -> do
      i <- varTB "art_number" -< t
      idxR "payment_date" -<  t
      odxR "contratante" -< ()
      odxR "cpf_cnpj" -< ()
      odxM "substuicao" -< ()
      r <- atR "crea_register" (proc t -> do
                               n <- varTB "crea_number" -< t
                               u <- varTB "crea_user"-< t
                               p <- varTB "crea_password"-< t
                               returnA -< liftA3 (, , ) n u p  ) -< t
      b <- act (  traverse (\(i, (j, k,a)) -> liftIO$ creaArtdata j k a i ) ) -< liftA2 (,) i r
      let ao =  convertArt <$> b
      returnA -< ao


queryArtCrea = FPlugins "Documento Final Art Crea" tname $ BoundedPlugin2 url
  where
    tname = "art"
    varTB i = fmap (BS.pack . renderShowable ) . join . fmap unSOptional' <$>  idxR i
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
      b <- act (fmap join  .  traverse (\(i, (j, k,a)) -> liftIO$ creaLoginArt  j k a i ) ) -< liftA2 (,) i r
      let ao =  Just $ tblist [attrT ("art",    LeftTB1 $ fmap (DelayedTB1 . Just . TB1 ) b)]
      returnA -< ao


queryArtBoletoCrea = FPlugins pname tname $ BoundedPlugin2  url
  where
    pname = "Boleto Art Crea"
    tname = "art"
    varTB i = fmap (BS.pack . renderShowable ) . join . fmap unSOptional' <$>  idxR i
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



queryArtAndamento = FPlugins pname tname $  BoundedPlugin2 url
  where
    tname = "art"
    pname = "Andamento Art Crea"
    varTB i =  fmap (BS.pack . renderShowable ) . join . fmap unSOptional' <$>  idxR i
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
      returnA -< artInp v


plugList :: [PrePlugins]
plugList =  {-[siapi2Hack] ---} [FPlugins "History Patch" "history" (StatefullPlugin [(([("showpatch", atPrim PText )],[]),PurePlugin readHistory)]) , subdivision,retencaoServicos, designDeposito,areaDesign,oauthpoller,createEmail,renderEmail ,lplugOrcamento ,{- lplugContract ,lplugReport,-}siapi3Plugin ,siapi3Inspection,siapi2Plugin ,siapi3CheckApproval, importargpx ,importarofx,gerarPagamentos ,gerarParcelas, pagamentoServico , notaPrefeitura,queryArtCrea , queryArtBoletoCrea , queryCEPBoundary,queryGeocodeBoundary,queryCPFStatefull , queryCNPJStatefull, queryArtAndamento,germinacao,preparoInsumo,fetchofx]
