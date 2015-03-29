{-# LANGUAGE Arrows #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
module PandocRenderer where
import Text.Pandoc.Options
import Widgets
import Text.Pandoc.PDF
import Data.ByteString.Base64.Lazy as BS64
import qualified Network.HTTP as HTTP
import Control.Monad
import Control.Monad.IO.Class
import Text.Pandoc.Writers.HTML
import Text.Pandoc.Writers.LaTeX
import Graphics.UI.Threepenny ((#),style,set,mkElement,sink,string,html,facts,src)
import qualified Graphics.UI.Threepenny.Elements as UI
import qualified Graphics.UI.Threepenny.Attributes as UI
import Text.Pandoc.Builder hiding ((<>))
import Control.Applicative
import Debug.Trace
import Postgresql
import Data.String
import Query
import Data.Maybe
import qualified Data.ByteString.Lazy.Char8 as BS
import qualified Data.Map as M
import qualified Data.Foldable as F
import qualified Data.Sequence as Seq

import System.IO

import Step
import Control.Arrow
import Data.Monoid
import Data.Text.Lazy(Text)

renderFireProjectReport conn _ inputs = (,pure Nothing) <$> element
  where
      varMap input = M.fromList $ (\(i,j)-> (keyValue i,j)) <$> input
      var env str = maybe "" fromString (renderShowable <$> M.lookup str (varMap env) )
      arrayVar env str = bulletList . concat . maybeToList $ join  (cshow . normalize <$> M.lookup str (varMap env) )
        where
          cshow (SComposite a ) = Just $ (plain . fromString . renderShowable) <$> F.toList a
          cshow (SOptional a ) =  Nothing
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
             pdfTidings <- joinT   ( maybe (return (Left "")) ( makePDF "pdflatex" writeLaTeX  def {writerStandalone = True ,writerTemplate = template } . myDoc) <$>  inputs)
             mkElement "iframe" # sink UI.src ( fmap (\i -> "data:application/pdf;base64," <> i) $ fmap (either BS.unpack (BS.unpack.BS64.encode)) $ facts pdfTidings) # set style [("width","100%"),("height","300px")]
            --UI.div # sink html (maybe ""  (writeHtmlString def . myDoc) <$> facts inputs)
            --
setFooter ,setT :: Blocks -> Pandoc -> Pandoc
setFooter = setMeta "footer"

setT = setMeta "title"

renderProjectPricingA = (staticP myDoc , element )
   where
      varMap input = M.fromList $ (\(i,j)-> (keyValue i,j)) <$> input
      var str =  maybe "" fromString . fmap (renderShowable.snd) <$> idx str
      varT str =  maybe "" fromString . fmap (renderShowable.snd) <$> idxT str
      arrayVar i str = (bulletList . concat . maybeToList . join . fmap   (cshow . normalize . snd) ) <$> indexTableInter i str
        where
          cshow (SComposite a ) = Just $ (plain . fromString . renderShowable) <$> F.toList a
          cshow (SOptional a ) =  Nothing
      -- myDoc :: a -> Pandoc
      myDoc :: Step.Parser (->) (Bool,[[Text]]) (Maybe (TB1 (Key,Showable))) Pandoc
      myDoc = proc env -> do
          f <- at "id_project:id_owner,id_contact:id_contact" (varT "firstname"  <> " " <> var "middlename" <> " " <> var "lastname") -< env
          idp <- varT "id_project:id_project" -< env
          da <- varT "pricing_date" -< env
          v <- arrayVar True "pricing_service" -< env
          p <- varT "pricing_price" -< env
          o <- varT "id_project:id_owner,id_contact:id_owner:owner_name" -< env
          end <- at "id_project:address" (var "logradouro" <> ", "<> var "number" <> " " <> var "complemento") -< env
          mun <- at "id_project:address" (var "municipio" <> "-" <> var "uf") -< env
          d <- var "pricing_execution_time" -< env
          returnA -< (setT ( para $ "Proposta :" <> idp <> ", " <> ( da )) $ doc $
                 para ( f <> ",")
                 <> orderedList [
                   para "Serviços Executados" <> v ,
                   para "Valor da Proposta" <>
                      plain ("Valor total:  " <> p ),
                   para "Dados do Servico" <>
                     bulletList [
                       plain ("Propietário : " <> o ),
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
                    ])
      element inputs = do
             template <- liftIO $ readFile' utf8 "raw.template"
             pdfTidings <- joinT   ( ( makePDF "pdflatex" writeLaTeX  def {writerStandalone = True ,writerTemplate = template } . dynP myDoc  ) <$> inputs)
             mkElement "iframe" # sink UI.src ( fmap (\i -> "data:application/pdf;base64," <> i) $ fmap (either BS.unpack (BS.unpack.BS64.encode)) $ facts pdfTidings) # set style [("width","100%"),("height","300px")]
            --UI.div # sink html (maybe ""  (writeHtmlString def . myDoc) <$> facts inputs)


renderProjectPricing _ _  inputs = (,pure Nothing) <$> element
   where
      varMap input = M.fromList $ (\(i,j)-> (keyValue i,j)) <$> input
      var env str = maybe "" fromString (renderShowable <$> M.lookup str (varMap env) )
      arrayVar env str = bulletList . concat . maybeToList $ join  (cshow . normalize <$> M.lookup str (varMap env) )
        where
          cshow (SComposite a ) = Just $ (plain . fromString . renderShowable) <$> F.toList a
          cshow (SOptional a ) =  Nothing
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
             pdfTidings <- joinT   ( maybe (return (Left "")) ( makePDF "pdflatex" writeLaTeX  def {writerStandalone = True ,writerTemplate = template } . myDoc ) <$> inputs)
             mkElement "iframe" # sink UI.src ( fmap (\i -> "data:application/pdf;base64," <> i) $ fmap (either BS.unpack (BS.unpack.BS64.encode)) $ facts pdfTidings) # set style [("width","100%"),("height","300px")]
            --UI.div # sink html (maybe ""  (writeHtmlString def . myDoc) <$> facts inputs)

readFile' e name = openFile name ReadMode >>= liftM2 (>>) (flip hSetEncoding $ e)   hGetContents

test = do
    template <-  readFile' utf8 "raw.template"
    let tex =   writeLaTeX def  {writerStandalone = True ,writerTemplate = template } (setTitle "Title" (doc (para "para")))
    either (print ) (BS.writeFile "raw.pdf") =<< makePDF "pdflatex"  writeLaTeX def  {writerStandalone = True ,writerTemplate = template } (setTitle "Title" (doc (para "para")))

