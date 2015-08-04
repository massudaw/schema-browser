{-# LANGUAGE Arrows #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
module PandocRenderer where

import Debug.Trace
import Text.Pandoc.Options
import Types
import RuntimeTypes
import Text.Pandoc.PDF
import Utils

import Control.Monad
import Text.Pandoc.Writers.LaTeX
import Text.Pandoc.Builder hiding ((<>))
import Control.Applicative
import Data.String
import Query
import Data.Maybe
import qualified Data.ByteString.Lazy as BS
import qualified Data.Foldable as F

import qualified Data.Map as M
import Schema
import System.IO
import Data.Functor.Identity

import Control.Monad.Reader
import Step
import Control.Arrow
import Data.Monoid
import Data.Text.Lazy(Text)

{-
renderFireProjectReport conn _ inputs = (,pure Nothing) <$> element
  where
      varMap input = M.fromList $ (\(i,j)-> (keyValue i,j)) <$> input
      var env str = maybe "" fromString (renderShowable <$> M.lookup str (varMap env) )
      arrayVar env str = bulletList . concat . maybeToList $ join  (cshow <$> M.lookup str (varMap env) )
        where
          cshow (SComposite a ) = Just $ (plain . fromString . renderShowable) <$> F.toList a
          cshow (SOptional a ) =  join $ fmap cshow a
      -- myDoc :: Pandoc
      myDoc env = setTitle "Project Report" $ doc $
         bulletList [
               plain ("Propietário : " <> vr "owner_name"),
               plain ("Local: " <> vr "municipio" <> "-" <> vr "uf"),
               plain ("Endereço: " <> vr "logradouro" <> ", " <> vr "number" <> " " <>   vr "complemento")
                  ]
        where
          vr = var env
      element = do
             template <- liftIO $ readFile "raw.template"
             pdfTidings <- joinTEvent   ( maybe (return (Left "")) ( makePDF "pdflatex" writeLaTeX  def {writerStandalone = True ,writerTemplate = template } . myDoc) <$>  inputs)
             mkElement "iframe" # sink UI.src ( fmap (\i -> "data:application/pdf;base64," <> i) $ fmap (either BS.unpack (BS.unpack.BS64.encode)) $ facts pdfTidings) # set style [("width","100%"),("height","300px")]
            --UI.div # sink html (maybe ""  (writeHtmlString def . myDoc) <$> facts inputs)
            --
            -}

setFooter ,setT :: Blocks -> Pandoc -> Pandoc
setFooter = setMeta "footer"

setT = setMeta "title"

renderProjectReport = (staticP myDoc , element )
   where
      tname = "pricing"
      payA = displayPay <$> (maybe (SText "Não Agendado") id <$> idxM "payment_date") <*> idxK "payment_description"  <*> idxK "price"
          where displayPay i da j = plain $ (fromString.renderShowable $ i ) <>  " - " <>  (fromString . renderShowable $ da )<> " - R$ " <> ((fromString.renderShowable) j)
      myDoc :: ArrowReader
      myDoc = proc preenv -> do
          pdoc <- (proc env -> do
              pay <- atRA "pagamentos" $ payA -< ()
              art <- atR "id_project" $ atR "art" $ atR "pagamento" $ payA-< ()
              dare <- atR "id_project" $ atR "taxa_dare" $ payA -< ()
              returnA -<   (setT ( para $ "Proposta :" ) $ doc $
                     orderedList [
                       para "Pagamento" <>
                          bulletList pay <>
                       para "Despesas" <>
                          bulletList [art,dare] <>
                          plain "As despesas referentes a cópias dos projetos e taxas para aprovação não estão inclusas no orçamento e são por conta do Contratante"
                        ])) -< ()
          outdoc <- act (\i -> do
              template <- liftIO$ readFile' utf8 "raw.template"
              liftIO$ makePDF "pdflatex" writeLaTeX  def {writerStandalone = True ,writerTemplate = template }   i ) -< pdoc
          odxR "report" -< ()
          returnA -<  (Just .  tbmap . mapFromTBList . pure . Compose. Identity . Attr "report" . SOptional . Just . SDelayed . Just . SBinary .  BS.toStrict . either id id ) outdoc
      element inf = maybe (return Nothing) (\inp -> do
                              b <- runReaderT (dynPK myDoc $ ()) (Just inp)
                              return $ liftKeys inf tname <$> b)


renderProjectPricingA = (staticP myDoc , element )
   where
      tname = "pricing"
      -- var :: Text -> Parser (->) (Access Text) () Inlines
      var str =  maybe "" fromString . fmap (renderShowable) <$> idxM str
      varT str =  maybe "" fromString . fmap (renderShowable) <$> idxR str
      arrayVar  str = (bulletList . concat . maybeToList . join . fmap   (cshow ) ) <$> idxR str
        where
          cshow (SComposite a ) = Just $ (plain . fromString . renderShowable) <$> F.toList a
          cshow (SOptional a ) =  join $ fmap cshow a
      -- myDoc :: a -> Pandoc
      myDoc :: ArrowReader
      myDoc = proc preenv -> do
          pdoc <- (proc env -> do
              f <- atR "id_project"
                     ( atR "id_owner,id_contact"
                        ( atR "id_contact" ((\f m l -> f <> " " <> m <> " " <> l ) <$> varT "firstname"  <*> var "middlename" <*> var "lastname"))) -< env
              d <- var "pricing_execution_time" -< env
              idp <- atR "id_project" (varT "id_project") -< env
              da <- varT "pricing_date" -< env
              v <- arrayVar "pricing_service" -< env
              p <- varT "pricing_price" -< env
              o <- atR "id_project"
                     (atR "id_owner,id_contact"
                        (atR "id_owner"  (varT"owner_name"))) -< env
              end <- atR "id_project" $ atR "address" (var "logradouro" <> ", "<> var "number" <> " " <> var "complemento") -< env
              mun <- atR "id_project" $ atR "address" (var "municipio" <> "-" <> var "uf") -< env
              returnA -< (setT ( para $ "Proposta :" <> idp <> ", " <> ( da )) $ doc $
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
              makePDF "pdflatex" writeLaTeX  def {writerStandalone = True ,writerTemplate = template }   i ) -< pdoc
          odxR "orcamento" -< preenv
          returnA -<  (Just .  tbmap .mapFromTBList . pure . Compose. Identity . Attr "orcamento" . SOptional . Just . SDelayed .Just . SBinary .  BS.toStrict . either id id ) outdoc
      element inf = maybe (return Nothing) (\inp -> do
                              b <- runReaderT (dynPK myDoc ()) (Just inp)
                              return $ liftKeys inf tname  <$> b)



{-
renderProjectPricing _ _  inputs = (,pure Nothing) <$> element
   where
      varMap input = M.fromList $ (\(i,j)-> (keyValue i,j)) <$> input
      var env str = maybe "" fromString (renderShowable <$> M.lookup str (varMap env) )
      arrayVar env str = bulletList . concat . maybeToList $ join  (cshow  <$> M.lookup str (varMap env) )
        where
          cshow (SComposite a ) = Just $ (plain . fromString . renderShowable) <$> F.toList a
          cshow (SOptional a ) =  join $ fmap cshow a
      -- myDoc :: Pandoc
      myDoc env = setTitle "Orçamento do Serviço" $
         doc $  para (vr "firstname" <> " " <> vr "middlename" <> " " <> vr "lastname" <> ",") <>
         orderedList [
           para "Serviços Executados" <> arrayVar env "pricing_service" ,
           para "Valor da Proposta" <>
              plain ("Valor total:  " <> vr "pricing_price"),
           para "Dados do Servico" <>
             bulletList [
               plain ("Propietário : " <> vr "owner_name"),
               plain ("Endereço: " <> vr "logradouro" <> ", " <> vr "number" <> " " <>   vr "complemento"),
               plain ("Local: " <> vr "municipio" <> "-" <> vr "uf")
                  ],
           para "Condições de Pagamento" <>
              plain "Entrada de 50% (cinquenta porcento) do valor da proposta, 50% (cinquenta por cento) na entrega dos projetos aprovados.",
           para "Despesas do Contratante" <>
              plain "As despesas referentes a cópias dos projetos e taxas para aprovação não estão inclusas no orçamento e são por conta do Contratante",
           para "Validade da Proposta" <>
              plain ("A proposta terá validade de 10 dias."),
           para "Prazo de Entrega" <>
              plain ( vr "pricing_execution_time" <> " dias  úteis, após a confirmação da proposta ou assinatura do contrato.")
            ]
        where
          vr = var env
      element = do
             template <- liftIO $ readFile' utf8 "raw.template"
             pdfTidings <- joinTEvent   ( maybe (return (Left "")) ( makePDF "pdflatex" writeLaTeX  def {writerStandalone = True ,writerTemplate = template } . myDoc ) <$> inputs)
             mkElement "iframe" # sink UI.src ( fmap (\i -> "data:application/pdf;base64," <> i) $ fmap (either BS.unpack (BS.unpack.BS64.encode)) $ facts pdfTidings) # set style [("width","100%"),("height","300px")]
            --UI.div # sink html (maybe ""  (writeHtmlString def . myDoc) <$> facts inputs)
-}
readFile' e name = openFile name ReadMode >>= liftM2 (>>) (flip hSetEncoding $ e)   hGetContents

test = do
    template <-  readFile' utf8 "raw.template"
    either (print ) (BS.writeFile "raw.pdf") =<< makePDF "pdflatex"  writeLaTeX def  {writerStandalone = True ,writerTemplate = template } (setTitle "Title" (doc (para "para")))

