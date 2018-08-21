{-# LANGUAGE FlexibleContexts,Arrows, TupleSections,OverloadedStrings ,NoMonomorphismRestriction #-}
module Gpx
  (gpx,readArt,readNota,readCpfName,readCreaHistoricoHtml,readInputForm,readSiapi3Andamento,readSiapi3AndamentoAJAX,readHtmlReceita,readHtml) where

import Types
import Types.Patch
import Utils
import Data.Time
import Data.String
import Control.Monad
import Safe
import Control.Applicative

import Data.Maybe
import Text.Read
import Data.Time.Format
import Text.XML.HXT.Core


import qualified Data.List as L

import qualified Data.ByteString as BS
import qualified Data.Text.Encoding as TE
import qualified Data.Text as TE


import Prelude hiding ((.),id,elem)
import qualified Prelude
import Control.Category

import Debug.Trace

elem :: Char -> String -> Bool
elem = Prelude.elem


atTag tag = deep (isElem >>> hasName tag)



getTable :: ArrowXml a => a XmlTree [[String]]
getTable =  atTag "table"  >>> listA (rows >>> listA cols) where
        rows = getChildren >>> hasName "tr"
        cols = atTag "td" />   (( getChildren >>> getText) <+> (hasText ( not .all (`elem` (" \t\r\n" :: String))) >>>  getText))

getTable' :: ArrowXml a => a XmlTree b  -> a XmlTree [[b]]
getTable' b=  atTag "table"  >>> listA (rows >>> listA cols) where
        rows = getChildren >>> is "tr"
        cols = getChildren >>> is "td" >>> b
getTd:: ArrowXml a => a XmlTree b  -> a XmlTree [[b]]
getTd b=  listA (rows >>> listA cols) where
        rows = getChildren >>> is "tr"
        cols = getChildren >>> is "td" >>> b



is x = deep (isElem >>> hasName x)

getPoint = atTag "trkpt" >>>
  proc x -> do
    lat <- getAttrValue "lat"  -< x
    lon <- getAttrValue "lon" -< x
    ele <- deep getText <<< atTag "ele" -< x
    time <- deep getText <<< atTag "time" -< x
    returnA -< [Attr "position" (TB1 $ SGeo $ SPosition $ Position (read lon ,read lat ,read ele)),Attr "instant" (TB1 $ STime $ STimestamp $  localTimeToUTC utc . fromJust $ parseTimeM True defaultTimeLocale "%Y-%m-%dT%H:%M:%SZ" time )]

file :: Showable
file = "/home/massudaw/2014-08-27-1653.gpx"

-- lookupKeys inf t l = fmap (\(k,s)-> (maybe (error ("no key: " <> show k ) ) id $ M.lookup (t,k) (keyMap inf),s)) l

-- withFields k t l = (l, maybe (error $ "noTable" ) id $  M.lookup t (tableMap k))



readCpfName file = do
  let
      arr = readString [withValidate no,withWarnings no,withParseHTML yes] file
        >>> ( is "span" >>> hasAttrValue "class" ("clConteudoDados"==) >>> listA (getChildren >>> deep getText ))
  l <- runX arr
  return  $ fmap (trim.last) $ L.find (L.isInfixOf  "Nome da" . head) $  L.filter (not.L.null ) $ L.nub l


readHtmlReceita file = do
  let
      txt = trim ^<< hasText ( not .all (`elem` " *\160\t\r\n")) >>>  getText
      arr = readString [withValidate no,withWarnings no,withParseHTML yes] file
        >>> getTable' ( getTable' ((is "font" /> txt ) &&& (is "font" /> is "b" /> txt) )    {-<+> ( Left ^<< getChildren >>> getChildren >>> txt)-}  )
  l <- runX arr
  return $ if L.null $ concat $ concat (concat l ) then Nothing else Just $ concat $ concat $ head (l !! 1)

readInputForm file = runX (readString [withValidate no , withWarnings no , withParseHTML yes] file >>> atTag "form" >>> getChildren >>> atTag "input" >>> attrP )
    where
      attrP :: ArrowXml a => a XmlTree (String,String)
      attrP = proc t -> do
            i <- getAttrValue "name" -< t
            j <- getAttrValue "value" -< t
            returnA -<  (i,j)

trim :: String -> String
trim = triml . trimr

-- | Remove leading space (including newlines) from string.
triml :: String -> String
triml = dropWhile (`elem` " \r\n\t")

-- | Remove trailing space (including newlines) from string.
trimr :: String -> String
trimr = reverse . triml . reverse

testGpx = print =<< (readFile "track.gpx" >>= gpx )

gpx :: String -> IO (Maybe [[TB TE.Text Showable]])
gpx file = do
  i <- runX (readString [withValidate no,withWarnings no,withParseHTML yes] file
        >>> atTag"trk" >>> atTag "trkseg" >>> listA getPoint)
  return (safeHead i)

testSiapi2 = do
  kk <- BS.readFile "Consulta Solicitação.html"
  let inp = TE.unpack $ TE.decodeLatin1 kk
  putStrLn . unlines . fmap concat . concat =<< readHtml inp


data NotaFiscal
   = NotaFiscal
   { --  notaId :: Int
   -- , notaDate :: LocalTime
    notaValores :: [(String,Double)]
   }deriving(Show)

readNota inp =
  let
    txt = trim ^<< hasText ( not .all (`elem` " *\160\t\r\n")) >>>  getText
    arr = hread
      >>> atTag "servico" >>> atTag "valores" >>> getChildren
          >>> listA (
            proc i -> do
              n <- getName -< i
              v <- deep getText -< i
              returnA -< ((n,) <$> (readMay v :: Maybe Double)))
  in catMaybes .concat $ runLA arr inp




testReceita = do
  kk <- BS.readFile "receita.html"
  let inp = TE.unpack $ TE.decodeLatin1 kk
  readHtmlReceita inp

testCreaArt = do
  kk <- BS.readFile "art.html"
  let inp = TE.unpack $ TE.decodeLatin1 kk
  readArt inp

{-


testCpfName = do
  kk <- BS.readFile "cpf_name.html"
  let inp = (TE.unpack $ TE.decodeLatin1 kk)
  readCpfName inp


testFormCrea = do
  kk <- BS.readFile "creaLogged.html"
  let inp = (TE.unpack $ TE.decodeLatin1 kk)
  readInputForm inp


testCreaArt = do
  kk <- BS.readFile "creaHistoricoArt.html"
  let inp = (TE.unpack $ TE.decodeLatin1 kk)
  readCreaHistoricoHtml inp
readSiapi3Solicitacao file = do
  let
      txt = trim ^<< ( concat ^<< listA ((atTag "a" <+> atTag "span") >>> getChildren >>>  getText)) <+> ((notContaining (atTag "div") (deep (hasName "a") <+> deep (hasName "span"))  >>> deep getText )  )
      arr = readString [withValidate no,withWarnings no,withParseHTML yes] file
          >>> deep (hasAttrValue "id" (=="formListaDeAndamentos:tabela")) >>> getTable' txt
  tail .head <$> runX arr
-}

testSiapi3 = do
  kk <- BS.readFile "debug.html"
  let inp = TE.unpack $ TE.decodeLatin1 kk
  readSiapi3AndamentoAJAX inp


readSiapi3Andamento file = do
  let
      txt = trim ^<< (concat ^<< listA ((atTag "a" <+> atTag "span") >>> getChildren >>>  getText))
      arr = proc t -> do
          s <- readString [withValidate no,withWarnings no,withParseHTML yes] file -< t
          v <- deep (hasAttrValue "id" (=="formListaDeAndamentos:tabela")) >>> getTable' txt -< s
          returnA -< v
      arr2 =readString [withValidate no,withWarnings no,withParseHTML yes] file >>>
        deep (atTag "input" >>> hasAttrValue "id" (=="javax.faces.ViewState") >>>getAttrValue "value")
  a <- concat .maybeToList . fmap safeTail . safeHead <$>runX arr
  b  <- runX arr2
  return (a,b)

readSiapi3AndamentoAJAX file = do
  let
      txt = trim ^<< (concat ^<< listA ((atTag "a" <+> atTag "span") >>> getChildren >>>  getText))
      arr = proc t -> do
          s <- readString [withValidate no,withWarnings no,withParseHTML yes] file -< t
          res <- deep (atTag "update" >>> hasAttrValue "id" (=="formListaDeAndamentos:tabela")) >>> getChildren  >>> getText >>> (readFromString [withValidate no,withWarnings no,withParseHTML yes]  >>> getTd txt )-< s
          returnA -< res
      arr2 =readString [withValidate no,withWarnings no,withParseHTML yes] file >>>
        deep (atTag "update" >>> hasAttrValue "id" (== "javax.faces.ViewState") >>> getChildren >>> getText)
  a <- runX arr
  b  <- runX arr2
  return (a,b)

readCreaHistoricoHtml file = fmap tail <$> do
  let
      arr = readString [withValidate no,withWarnings no,withParseHTML yes] file
        >>> getTable'  (deep (trim ^<< getText))
  runX arr

readArt file = do
  let
      arr = readString [withValidate no,withWarnings no,withParseHTML yes] file
        >>> getTable' (getTable' (fmap (trim . filter (not .(`elem` "\r\t\n"))) . filter (not . all (`elem` "\r\t\n " )) ^<< listA (deep getText)))
  runX arr


readHtml file = do
  let
      arr = readString [withValidate no,withWarnings no,withParseHTML yes] file
        >>> getTable' (deep getText)
  runX arr

