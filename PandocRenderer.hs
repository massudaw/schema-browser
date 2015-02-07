{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}
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
import Text.Pandoc.Builder
import Control.Applicative
import Debug.Trace
import Postgresql
import Data.String
import Query
import Data.Maybe
import qualified Data.ByteString.Lazy.Char8 as BS
import qualified Data.Map as M
import qualified Data.Foldable as F


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
             pdfTidings <- joinT   ( maybe (return (Left "")) ( makePDF "pdflatex" writeLaTeX  def {writerStandalone = True ,writerTemplate = template } . myDoc) <$> inputs)
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
      myDoc env = setTitle "My title" $ doc $
         para (vr "firstname" <> ",") <>
         orderedList [
           para "Serviços Executados" <> arrayVar env "pricing_service" ,
           para "Valor da Proposta" <>
              plain ("Valor total:  " <> vr "pricing_price"),
           para "Dados do Servico" <>
             bulletList [
               plain ("Propietário : " <> vr "owner_name"),
               plain ("Local: " <> vr "owner_municipio" <> "-" <> vr "owner_uf"),
               plain ("Endereço: " <> vr "logradouro" <> ", " <> vr "owner_number" <> " " <>   vr "owner_complemento")
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
             template <- liftIO $ readFile "raw.template"
             pdfTidings <- joinT   ( maybe (return (Left "")) ( makePDF "pdflatex" writeLaTeX  def {writerStandalone = True ,writerTemplate = template } . myDoc) <$> inputs)
             mkElement "iframe" # sink UI.src ( fmap (\i -> "data:application/pdf;base64," <> i) $ fmap (either BS.unpack (BS.unpack.BS64.encode)) $ facts pdfTidings) # set style [("width","100%"),("height","300px")]
            --UI.div # sink html (maybe ""  (writeHtmlString def . myDoc) <$> facts inputs)

test = do
    template <-  readFile "raw.template"
    let tex =   writeLaTeX def  {writerStandalone = True ,writerTemplate = template } (setTitle "Title" (doc (para "para")))
    putStrLn tex
    makePDF "pdflatex"  writeLaTeX def  {writerStandalone = True ,writerTemplate = template } (setTitle "Title" (doc (para "para")))

template ="\\documentclass{minimal}  \\usepackage{fancyhdr}  \\setlength{\\headheight}{15.2pt}  \\pagestyle{fancy}   \\chead{My fancy header}  \\cfoot{\\thepage} "
