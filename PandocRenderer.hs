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
              liftIO$ makePDF "pdflatex" writeLaTeX  def {writerStandalone = True ,writerTemplate = template }   i ) -< pdoc
          odxR "contract" -< ()
          returnA -<  (\i -> tbmap . mapFromTBList . pure . Compose. Identity . Attr "contract" . LeftTB1 . Just . DelayedTB1 . Just . TB1 . SBinary .  BS.toStrict <$>  either (const Nothing) Just  i) outdoc


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
              liftIO$ makePDF "pdflatex" writeLaTeX  def {writerStandalone = True ,writerTemplate = template }   i ) -< pdoc
          odxR "report" -< ()
          returnA -<  (\i -> tbmap . mapFromTBList . pure . Compose. Identity . Attr "report" . LeftTB1 . Just . DelayedTB1 . Just . TB1 . SBinary .  BS.toStrict <$> either (const Nothing) Just i ) outdoc


renderProjectPricingA = myDoc
   where
      tname = "pricing"
      -- var :: Text -> Parser (->) (Access Text) () Inlines
      var str =  maybe "" fromString . fmap (renderShowable) <$> idxM str
      varT str =  maybe "" fromString . fmap (renderShowable) <$> idxR str
      arrayVar  str = (bulletList . concat . maybeToList . join . fmap   (cshow ) ) <$> idxR str
        where
          cshow (ArrayTB1 a ) = Just $ (plain . fromString . renderShowable) <$> F.toList a
          cshow (LeftTB1 a ) =  join $ fmap cshow a
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
              v <- arrayVar "pricing_service" -< env
              p <- varT "pricing_price" -< env
              o <- atR "id_project"
                     (atR "id_owner,id_contact"
                        (atR "id_owner"  (varT"owner_name"))) -< env
              end <- atR "id_project" $ atR "address" (var "logradouro" <> ", "<> var "number" <> " " <> var "complemento") -< env
              mun <- atR "id_project" $ atR "address" (var "municipio" <> "-" <> var "uf") -< env
              returnA -< (setT ( para $ "Proposta :" <> idp <> ", " <>  da ) $ doc $
                     para ( f <> ",")
                     <> orderedList [
                       para "Serviços Executados" <> v ,
                       para "Valor da Proposta" <>
                          plain ("Valor total:  " <> p ),
                       para "Dados do Servico" <>
                         bulletList [
                           plain ("Proprietário : " <> o ),
                           plain ("Endereço: " <> end ),
                           plain ("Local: " <> mun )
                              ],
                       para "Condições de Pagamento" <>
                          plain "Entrada de 50% (cinquenta porcento) do valor da proposta, 50% (cinquenta por cento) na entrega dos projetos aprovados.",
                       para "Despesas do Contratante" <>
                          plain "As despesas referentes a cópias dos projetos e taxas para aprovação não estão inclusas no orçamento e são por conta do Contratante",
                       para "Validade da Proposta" <>
                          plain ("A proposta terá validade de 10 dias."),
                       para "Prazo de Entrega" <>
                          plain ( d <> " dias  úteis, após a confirmação da proposta ou assinatura do contrato.")
                        ])) -< preenv
          outdoc <- act (\i -> liftIO $ do
              template <- readFile' utf8 "raw.template"
              makePDF "pdflatex" writeLaTeX  def {writerStandalone = True ,writerTemplate = template }   i
                  ) -< pdoc
          odxR "orcamento" -< preenv
          returnA -<  (\i -> tbmap .mapFromTBList . pure . Compose. Identity . Attr "orcamento" . LeftTB1 . Just . DelayedTB1 .Just . TB1 . SBinary .  BS.toStrict <$> either (const Nothing) Just i) outdoc


readFile' e name = openFile name ReadMode >>= liftM2 (>>) (flip hSetEncoding $ e)   hGetContents

test = do
    template <-  readFile' utf8 "raw.template"
    either (print ) (BS.writeFile "raw.pdf") =<< makePDF "pdflatex"  writeLaTeX def  {writerStandalone = True ,writerTemplate = template } (setTitle "Title" (doc (para "para")))

