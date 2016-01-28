{-# LANGUAGE Arrows, TupleSections,OverloadedStrings,NoMonomorphismRestriction #-}
module Gpx
  (readArt,readCpfName,readCreaHistoricoHtml,readInputForm,readSiapi3Andamento,readHtmlReceita,readHtml) where

import Types
-- import Query
import Data.String
import Control.Applicative

import Data.Maybe
import Text.Read
import Data.Time.Parse
import Text.XML.HXT.Core


import qualified Data.List as L

import qualified Data.ByteString as BS
import qualified Data.Text.Encoding as TE
import qualified Data.Text as TE


import Prelude hiding ((.),id,head)
import Control.Category

import Debug.Trace


atTag tag = deep (isElem >>> hasName tag)

text = getChildren >>> getText



getTable :: ArrowXml a => a XmlTree [[String]]
getTable =  atTag "table"  >>> listA (rows >>> listA cols) where
        rows = getChildren >>> hasName "tr"
        cols = atTag "td" />   (( getChildren >>> getText) <+> (hasText ( not .all (`elem` " \t\r\n")) >>>  getText))

getTable' :: ArrowXml a => a XmlTree b  -> a XmlTree [[b]]
getTable' b=  atTag "table"  >>> listA (rows >>> listA cols) where
        rows = getChildren >>> is "tr"
        cols = getChildren >>> is "td" >>> b


is x = deep (isElem >>> hasName x)

getPoint = atTag "trkpt" >>>
  proc x -> do
    lat <- getAttrValue "lat"  -< x
    lon <- getAttrValue "lon" -< x
    ele <- text <<< atTag "ele" -< x
    time <- text <<< atTag "time" -< x
    returnA -< [SPosition $ Position (read lat,read lon,read ele),STimestamp $  fromJust $ fmap fst  $ strptime "%Y-%m-%dT%H:%M:%SZ" time ]

file :: Showable
file = "/home/massudaw/2014-08-27-1653.gpx"

-- lookupKeys inf t l = fmap (\(k,s)-> (maybe (error ("no key: " <> show k ) ) id $ M.lookup (t,k) (keyMap inf),s)) l

-- withFields k t l = (l, maybe (error $ "noTable" ) id $  M.lookup t (tableMap k))



readCpfName file = do
  let
      arr = readString [withValidate no,withWarnings no,withParseHTML yes] file
        >>> ( is "span" >>> hasAttrValue "class" ("clConteudoDados"==) >>> listA (getChildren >>> deep getText ))
  l <- runX arr
  return  $ fmap (trim.last) $ L.find (\i -> L.isInfixOf  "Nome da" (head i)) $  L.filter (not.L.null ) $ L.nub l


readHtmlReceita file = do
  let
      txt = trim ^<< hasText ( not .all (`elem` " *\160\t\r\n")) >>>  getText
      arr = readString [withValidate no,withWarnings no,withParseHTML yes] file
        >>> getTable' ( getTable' ((is "font" /> txt ) &&& (is "font" /> is "b" /> txt) )    {-<+> ( Left ^<< getChildren >>> getChildren >>> txt)-}  )
  l <- runX arr
  return $ if L.null $ concat $ concat (concat l ) then Nothing else Just $ concat $ concat $ (traceShowId l) !! 1 !! 0

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

testSiapi2 = do
  kk <- BS.readFile "Consulta Solicitação.html"
  let inp = (TE.unpack $ TE.decodeLatin1 kk)
  putStrLn . unlines . fmap concat . concat =<< readHtml inp


testReceita = do
  kk <- BS.readFile "receita.html"
  let inp = (TE.unpack $ TE.decodeLatin1 kk)
  readHtmlReceita inp

testCreaArt = do
  kk <- BS.readFile "art.html"
  let inp = (TE.unpack $ TE.decodeLatin1 kk)
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

testSiapi3 = do
  kk <- BS.readFile "siapi32.html"
  let inp = (TE.unpack $ TE.decodeLatin1 kk)
  readSiapi3Andamento inp

readSiapi3Solicitacao file = do
  let
      txt = trim ^<< ( concat ^<< listA ((atTag "a" <+> atTag "span") >>> getChildren >>>  getText)) <+> ((notContaining (atTag "div") (deep (hasName "a") <+> deep (hasName "span"))  >>> deep getText )  )
      arr = readString [withValidate no,withWarnings no,withParseHTML yes] file
          >>> deep (hasAttrValue "id" (=="formListaDeAndamentos:tabela")) >>> getTable' txt
  tail .head <$> runX arr
-}

readSiapi3Andamento file = do
  let
      txt = trim ^<< (concat ^<< listA ((atTag "a" <+> atTag "span") >>> getChildren >>>  getText))
      arr = readString [withValidate no,withWarnings no,withParseHTML yes] file
          >>> deep (hasAttrValue "id" (=="formListaDeAndamentos:tabela")) >>> getTable' txt
  tail .head <$> runX arr

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
{-
exec inputs = do
  let schema = "health"
  conn <- connectPostgreSQL "user=postgres dbname=test"
  let Just (_,SText file) = L.find ((== "file") . fst) inputs
  let
    arr = readDocument [withValidate no,withTrace 1] (unpack file)
        >>> getPoint
  inf <- keyTables conn conn  (schema,"postgres")
  print (tableMap inf)
  res <- runX arr
  let runVals = [("period",IntervalTB1 $ (ER.Finite $ last $ head res ,True) `interval` (ER.Finite $ last $ last res,True))]  <> L.filter ((/= "file") . fst ) inputs
      runInput = withFields inf  "run" $   lookupKeys inf "run"  runVals
  print runInput
  -- pkrun <- uncurry (insertPK fromShowableList conn) runInput
  -- print pkrun
  -- mapM_ (\i-> uncurry (insert conn) (withFields inf "track" (pkrun <> lookupKeys inf "track" i))) (consLL "id_sample" (SNumeric <$> [0..])  $  zipLL (repeat []) ["position","instant"] res )
  return (Nothing ,[])
  -}
