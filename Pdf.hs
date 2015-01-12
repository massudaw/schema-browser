{-# LANGUAGE OverloadedStrings #-}

-- | Change PDF document title
--
-- The example shows how to use incremental updates to change PDF file

module Pdf where

import Data.String
import Control.Monad
import System.IO
import qualified System.IO.Streams as Streams
import System.Environment

import qualified Data.ByteString as BS
import Data.IORef
import Control.Applicative
import Data.Monoid

import qualified Data.Text as T
import Pdf.Toolbox.Core
import Pdf.Toolbox.Document

-- Using the internals to switch from 'pdf-toolbox-document' level
-- to 'pdf-toolbox-core'
import Pdf.Toolbox.Document.Internal.Types

testDanilo = do
  parseBombeiroPdf "temp12151014.pdf"

parseBombeiroPdf input = do
  withBinaryFile input ReadMode $ \handle ->
    runPdfWithHandle handle knownFilters $ do
    do
      ris <- getRIS
      doc <-  runPdf ris knownFilters document
      i <- EitherT $ return doc
      cat <- documentCatalog i
      node <- catalogPageNode  cat
      n <- pageNodeNKids node
      i <- pageNodePageByNum node 0
      ni <- pageNodePageByNum node (n-1)
      res <- T.lines <$> pageExtractText i
      resn <- T.lines <$> pageExtractText ni
      let name = do
            [name,job] <- take 2  . drop 1 . dropWhile ((/="__") . T.take 2)
            return $ fmap (fmap T.strip) [("Name",fst $ T.breakOn ("Revisor") name) , ("Job",job)]
          dados = do
            i <- head . dropWhile ((/="Ocupação") . T.take 8)
            let (ocupacao,n1)= T.breakOn "Área" i
                breakDrop i = (\(h,t) -> (h,T.strip $ T.tail t)) .T.breakOn i
                (area ,carga) = T.breakOn "Carga" n1
                (tipo,subtipo) = breakDrop "-" $ snd $ breakDrop ":" ocupacao
            return  $ fmap (breakDrop ":" ) [area,carga] <> [("tipo",tipo),("subtipo",subtipo)]
      return (mappend (dados res ) (name resn))
