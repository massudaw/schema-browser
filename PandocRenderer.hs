{-# LANGUAGE Arrows #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
module PandocRenderer where

import Text.Pandoc.Options
import Types
import Text.Pandoc.PDF

import Control.Monad
import Text.Pandoc.Writers.LaTeX
import GHC.Stack
import Text.Pandoc.Builder hiding ((<>))
import Control.Applicative
import Data.String
import Data.Maybe
import qualified Data.ByteString.Lazy as BS
import qualified Data.Foldable as F

import System.IO
import Data.Functor.Identity
import Text

import Control.Monad.Reader
import Step.Client
import Control.Arrow
import Data.Monoid


setFooter ,setT :: Blocks -> Pandoc -> Pandoc
setFooter = setMeta "footer"

setT = setMeta "title"

renderProjectContract = myDoc
   where
      tname = "pricing"
      var str =  maybe "" fromString . fmap (renderShowable) <$> idxM str
      varT str =  maybe "" fromString . fmap (renderShowable) <$> idxR str
      payA = displayPay <$> (maybe (TB1 $ SText "Não Agendado") id <$> idxM "payment_date") <*> idxK "payment_description"  <*> idxK "price"
          where displayPay i da j = plain $ (fromString.renderShowable $ i ) <>  " - " <>  (fromString . renderShowable $ da )<> " - R$ " <> ((fromString.renderShowable) j)
      myDoc :: ArrowReader
      myDoc = proc preenv -> do
          pdoc <- (proc env -> do
              pay <- atRA "pagamentos" $ payA -< ()
              own <- atR "id_project"
                     ( atR "id_owner,id_contact"
                        ( atR "id_owner" ( varT "owner_name"  ))) -< env
              art <- atR "id_project" $ atR "art" $ atR "tag_art,pagamento" $ payA-< ()
              end <- atR "id_project" $ atR "address" (var "logradouro" <> ", "<> var "number" <> " " <> var "complemento" <> " " <> var "cep" <>" " <> var "municipio" <> "-" <> var "uf" ) -< env
              dare <- atR "id_project" $ atR "tag_taxa,taxa_dare" $ payA -< ()
              returnA -<   (setT ( para $ "Contrato de Prestação de Serviços / nº " ) $ doc $
                     ((para "Cláusula Primeira"
                          <> plain "As partes abaixo qualificadas celebram o presente contrato de Prestação de Serviços, consubstanciado nos regramentos e condições elencados nas Cláusulas especiais e Gerais a seguir:"  <>
                      para "Contratante:"
                          <> plain  (own <> ",  Empresa Sediada "  <> end )<>
                      para "Contratada:"
                          <> plain  "CONDOMINIO RESIDENCIAL THE PLACE,  Empresa Sediada") <>
                     orderedList [
                       para "Pagamento" <>
                          bulletList pay <>
                       para "Despesas" <>
                          bulletList [art,dare] <>
                          plain "As despesas referentes a cópias dos projetos e taxas para aprovação não estão inclusas no orçamento e são por conta do Contratante"
                        ]))) -< ()
          outdoc <- act (\i -> do
              template <- liftIO$ readFile' utf8 "contract.template"
              liftIO$ makePDF "pdflatex" writeLaTeX  def {writerTemplate = Just template }   i ) -< pdoc
          odxR "contract" -< ()
          returnA -<  (\i -> tblist .  pure . Attr "contract" . LeftTB1 . Just . LeftTB1 . Just . TB1 . SBinary .  BS.toStrict <$>  either (const Nothing) Just  i) outdoc


renderProjectReport = myDoc
   where
      tname = "pricing"
      payA = displayPay <$> (maybe (TB1 $ SText "Não Agendado") id <$> idxM "payment_date") <*> idxK "payment_description"  <*> idxK "price"
          where displayPay i da j = plain $ (fromString.renderShowable $ i ) <>  " - " <>  (fromString . renderShowable $ da )<> " - R$ " <> ((fromString.renderShowable) j)
      myDoc :: ArrowReader
      myDoc = proc preenv -> do
          pdoc <- (proc env -> do
              pay <- atRA "pagamentos" $ payA -< ()
              dare <- atR "id_project" $ atR "tag_taxa,taxa_dare" $ payA -< ()
              returnA -<   (setT ( para $ "Contrato de Prestação de Serviços / nº  " ) $ doc $
                     orderedList [
                       para "Pagamento" <>
                          bulletList pay <>
                       para "Despesas" <>
                          bulletList [dare] <>
                          plain "As despesas referentes a cópias dos projetos e taxas para aprovação não estão inclusas no orçamento e são por conta do Contratante"
                        ])) -< ()
          outdoc <- act (\i -> do
              template <- liftIO$ readFile' utf8 "raw.template"
              liftIO$ makePDF "pdflatex" writeLaTeX  def {writerTemplate = Just template }   i ) -< pdoc
          odxR "report" -< ()
          returnA -<  (\i -> tblist .  pure . Attr "report" . LeftTB1 . Just . LeftTB1. Just . TB1 . SBinary .  BS.toStrict <$> either (const Nothing) Just i ) outdoc


ptext = plain . fromString
arrayR s = unArray <$> idxK s

renderProjectPricingA = myDoc
   where
      tname = "pricing"
      render = fromString . renderShowable
      var str =  maybe "" fromString . fmap (renderShowable) <$> idxM str
      varT str =  maybe "" fromString . fmap (renderShowable) <$> idxR str
      arrayVar  str = (bulletList . concat . maybeToList . join . fmap   (cshow ) ) <$> idxR str
        where
          cshow (ArrayTB1 a ) = Just $ (plain . fromString . renderShowable) <$> F.toList a
          cshow (LeftTB1 a ) =  join $ fmap cshow a

      address_model = atR "address"
                            ((,,)<$> (var "logradouro" <> ", "<> var "number" <> " " <> var "complemento")
                                <*> var "municipio"
                                <*> var "uf")
      -- myDoc :: a -> Pandoc
      myDoc :: ArrowReader
      myDoc = proc preenv -> do
          pdoc <- (proc env -> do
              f <- atR "id_project"
                     ( atR "id_owner,id_contact"
                        ( atR "id_contact" ((\f m l -> f <> " " <> m <> " " <> l ) <$> varT "firstname"  <*> var "middlename" <*> var "lastname"))) -< env
              d <- var "pricing_execution_time" -< env
              idp <- atR "id_project" (varT "id_project") -< env
              da <- varT "price_available" -< env
              p<- varT "pricing_price" -< env
              p_value <- idxK "pricing_price" -< env
              parcelas_rate <-  arrayR "parcelas" -< env
              let parcelas  = fmap  (*p_value)  parcelas_rate
              v <- arrayVar "pricing_service" -< env
              (o,o_cpf,(oaddress,oc,os)) <- atR "id_project"
                     (atR "id_owner,id_contact"
                        (atR "id_owner"  ((,,)<$> varT "owner_name"
                                            <*> atAny "ir_reg"
                                                [fmap (\i -> "CPF: " <> render i) . join . fmap unSOptional'<$>  idxR "cpf_number"
                                                                ,fmap (\i -> "CNPJ: " <> render i ) .join . fmap unSOptional' <$> idxR "cnpj_number"]
                                            <*> address_model
                                         ) )) -< env
              ((end,mun,uf),(area,area_terreno,pavimentos,altura)) <-
                atR "id_project" $
                  ((,) <$> address_model
                      <*> atR "dados_projeto" (
                       (,,,) <$> varT "area"
                           <*> varT "terrain_area"
                           <*> varT "pavimentos"
                           <*> varT "altura" ))  -< ()
              returnA -< (setT ( para $ "Proposta :" <> idp <> ", " <>  da ) $ doc $
                     para ( f <> ",")
                     <> orderedList [
                       para "Serviços Executados" <> v ,
                       para "Valor da Proposta" <>
                          plain ("Valor total:  " <> p ),
                       para "Dados do Contratante" <>
                         bulletList [
                           ptext (fromMaybe "CPF/CNPJ:" o_cpf) ,
                           plain ("Proprietário : " <> o ),
                           plain ("Endereço: " <> oaddress),
                           plain ("Município: " <> oc),
                           plain ("Estado: " <> os)
                                    ],
                       para "Dados do Servico" <>
                         bulletList [
                           plain ("Endereço: " <> end ),
                           plain ("Município: " <> mun ),
                           plain ("Estado: " <> uf),
                           plain ("Área Terreno: " <> area_terreno),
                           plain ("Área Construida: " <> area),
                           plain ("Altura: " <> altura),
                           plain ("Pavimentos: " <> pavimentos)
                              ],
                       para "Condições de Pagamento" <>
                         bulletList ( (\(ix,v) -> ptext $ "Parcelas " ++ show ix ++ " - "  ++ render v ) <$> zip [0..] (F.toList parcelas )) ,
                       para "Despesas do Contratante" <>
                          plain "As despesas referentes a cópias dos projetos e taxas para aprovação não estão inclusas no orçamento e são por conta do Contratante",
                       para "Validade da Proposta" <>
                          plain ("A proposta terá validade de 10 dias."),
                       para "Prazo de Entrega" <>
                          plain ( d <> " dias  úteis, após a confirmação da proposta ou assinatura do contrato.")
                        ])) -< preenv
          outdoc <- act (\i -> liftIO $ do
              template <- readFile' utf8 "raw.template"
              makePDF "pdflatex" writeLaTeX  def {writerTemplate = Just template }   i
                  ) -< pdoc
          odxR "orcamento" -< preenv
          returnA -<  (\i -> tblist . pure . Attr "orcamento" . LeftTB1 . Just . LeftTB1 .Just . TB1 . SBinary .  BS.toStrict <$> either (const Nothing) Just i) outdoc


readFile' e name = openFile name ReadMode >>= liftM2 (>>) (flip hSetEncoding $ e)   hGetContents

test = do
    template <-  readFile' utf8 "raw.template"
    either (print ) (BS.writeFile "raw.pdf") =<< makePDF "pdflatex"  writeLaTeX def  {writerTemplate = Just template } (setTitle "Title" (doc (para "para")))

