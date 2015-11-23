{-# LANGUAGE DeriveDataTypeable,ConstraintKinds,TypeFamilies ,DeriveTraversable,DeriveFoldable,StandaloneDeriving,RecursiveDo,FlexibleInstances,RankNTypes,NoMonomorphismRestriction,ScopedTypeVariables,UndecidableInstances,FlexibleContexts,OverloadedStrings ,TupleSections, ExistentialQuantification #-}
module Postgresql where
import Types
import Data.Ord
import Control.Monad
import Data.Typeable
import Utils
import Query
import GHC.Stack
import Debug.Trace
import qualified Data.Binary as B
import Data.Functor.Identity
import Data.Scientific hiding(scientific)
import Data.Bits
import Data.Bifunctor
import qualified  Data.Map as M

import Data.Tuple
import Data.Time.Clock
import qualified Data.Char as Char
-- import Schema
import Data.String
import Data.Attoparsec.Combinator (lookAhead)

import Control.Applicative
import Control.Monad.IO.Class
import qualified Data.Serialize as Sel
import Data.Maybe
import Text.Read hiding (choice)
import qualified Data.ExtendedReal as ER
import qualified Data.ByteString.Base16 as B16
import Data.Time.Parse
import           Database.PostgreSQL.Simple.Types as PGTypes
import           Data.Attoparsec.ByteString.Char8 hiding (Result)
import Data.Traversable (traverse)
import qualified Data.Traversable  as Tra
-- import Warshal
import Data.Time.LocalTime
import qualified Data.List as L
import qualified Data.Vector as Vector
import qualified Data.Interval as Interval
import qualified Data.ByteString.Char8 as BS
import qualified Data.ByteString.Lazy.Char8 as BSL

import Data.Monoid
import Prelude hiding (takeWhile,head)


import qualified Data.Foldable as F
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Data.Text (Text)
import qualified Data.Set as S
import Database.PostgreSQL.Simple.Time
import qualified Database.PostgreSQL.Simple.FromField as F
import Database.PostgreSQL.Simple.FromRow (field)
import Database.PostgreSQL.Simple.FromField hiding(Binary,Identity)
-- import Database.PostgreSQL.Simple.FromField (fromField,typeOid,typoid,TypeInfo,rngsubtype,typdelim,Conversion,Field,FromField)
import qualified Database.PostgreSQL.Simple.ToField as TF
import qualified Database.PostgreSQL.Simple.FromRow as FR
import qualified Database.PostgreSQL.Simple.ToRow as TR
import Database.PostgreSQL.Simple
-- import Data.GraphViz (preview)
import Blaze.ByteString.Builder(fromByteString)
import Blaze.ByteString.Builder.Char8(fromChar)

data DB = DB { dbName :: String
          , dbUser :: String
          , dbPassword :: String
          , dbHost :: String
          , dbPort :: String
          }deriving(Show)

renderPostgresqlConn (DB n u p h pt)
  = "user=" <> u <> " password=" <> p <> " dbname=" <> n

db = DB "usda" "postgres" "queijo" "localhost" "5432"

-- Wrap new instances without quotes delimiting primitive values
newtype UnQuoted a = UnQuoted {unQuoted :: a}

instance (Show a,TF.ToField a , TF.ToField (UnQuoted (a))) => TF.ToField (FTB a) where
  toField (LeftTB1 i) = maybe (TF.Plain (fromByteString "null")) TF.toField  i
  toField (SerialTB1 i) = maybe (TF.Plain (fromByteString "null")) TF.toField  i
  toField (DelayedTB1 i) = maybe (TF.Plain (fromByteString "null")) TF.toField  i
  toField (ArrayTB1 is ) = TF.toField $ PGTypes.PGArray   is
  toField (IntervalTB1 is ) = TF.toField  $ fmap (\(TB1 i ) -> i) is
  toField (TB1 i) = TF.toField i
  toField i = errorWithStackTrace (show i)


instance  TF.ToField (TB Identity Key Showable)  where
  toField (Attr _  i) = TF.toField i
  toField (IT n (LeftTB1 i)) = maybe (TF.Plain ( fromByteString "null")) (TF.toField . IT n ) i
  toField (IT n (TB1 (m,i))) = TF.toField (TBRecord2  (kvMetaFullName  m ) (L.sortBy (comparing (keyPosition . inattr ) ) $ maybe id (flip mappend) attrs $ (runIdentity.getCompose <$> F.toList (_kvvalues $ unTB i) )  ))
      where attrs = Tra.traverse (\i -> Attr i <$> showableDef (keyType i) ) $  F.toList $ (S.fromList $ _kvattrs  m ) `S.difference` (S.map _relOrigin $ S.unions $ M.keys (_kvvalues $ unTB i))
  toField (IT (n)  (ArrayTB1 is )) = TF.toField $ PGTypes.PGArray $ (TF.toField . IT n) <$> is
  -- toField (RecRel k ix t) = TF.toField t
  toField e = errorWithStackTrace (show e)



instance TR.ToRow a => TF.ToField (TBRecord2 a) where
  toField (TBRecord2 s l) =  TF.Many   (TF.Plain (fromByteString "ROW(") : L.intercalate [TF.Plain $ fromChar ','] (fmap pure. TR.toRow  $ l) <> [TF.Plain (fromByteString $ ") :: " <>  BS.pack (T.unpack s) )] )


testRecord conn = do
  res  <- queryWith_ (parseField $ parseRow (parseShowable  <$> [Primitive PText,Primitive PText,KOptional $ Primitive PText, KOptional $ Primitive PText,KOptional $ Primitive PText] )) conn "select ROW(\'ioj\',\'ewfe\',null,null,null) "
  print (res :: [[FTB Showable]])


test = do
  let s1 = (Just "(\"{\"\"(,,\\\\\"\"({pk_column},{=},{id},2)\\\\\"\")\"\",\"\"(,\\\\\"\"(sel_column,attr_ref,1)\\\\\"\",)\"\",\"\"(attr,,)\"\"}\")")
      s2 = (Just "(\"{\"\"(,,\\\\\"\"({pk_column},{=},{id},2)\\\\\"\")\"\",\"\"(attr,,)\"\"}\")")
  i <- pathParser undefined s1
  i <- pathParser undefined s2
  print (i :: PathArray )
instance  F.FromField PathArray where
  fromField =  pathParser

pathParser t f = do
  let
    attPath = do
       LeftTB1 attr <-  (parseShowable  (KOptional $ Primitive PText) )
       return $ (\(TB1 (SText attr)) ->  AttrPath attr) <$> attr
    itPath = do
       it <-  (Just <$> doublequoted (parseRow ( parseShowable  <$> [Primitive PText,Primitive PText , Primitive PInt]))) <|> return Nothing
       return $ (\[TB1 (SText attr),TB1 (SText tb) ,TB1 (SNumeric ref)]  ->  ITPath attr tb ) <$> it
    fkPath = do
       it <- (Just <$> doublequoted (parseRow ( parseShowable  <$> [KArray $ Primitive PText,KArray $Primitive PText ,  KArray $Primitive PText, Primitive PInt,Primitive PText]))) <|> return Nothing
       let unText  (TB1 (SText attr))  = attr
       return $ (\[ArrayTB1 or ,ArrayTB1 rel , ArrayTB1 tar ,TB1 (SNumeric ref) ,TB1 (SText tb)]  ->  FKTPath (unText <$> or) (unText <$> rel ) (unText <$> tar)  tb ) <$> it

  parserFieldAtto (fmap PathArray $  fmap head $ parseRow [doublequoted $ parseArray  $ fmap (head . catMaybes ) $ doublequoted (parseRow  ([attPath,itPath,fkPath ]))] ) t f

newtype PathArray = PathArray [PathRel Text Text ] deriving(Show,Typeable)
data PathRel b a
  = AttrPath a
  | ITPath a b -- (PathRel b a)
  | FKTPath [a] [Text] [a]  b -- (PathRel b a)
  deriving (Eq,Ord,Show,Typeable)


testref conn = do
  res  <- query_ conn "select table_schema,table_name,array_agg from metadata.record_path"
  print (res :: [(Text,Text,Vector.Vector (PathArray ))])

data TBRecord2 a = TBRecord2 Text a

instance TF.ToField (UnQuoted Showable) where
  toField (UnQuoted (STimestamp i )) = TF.Plain $ localTimestampToBuilder (Finite i)
  toField (UnQuoted (SDate i )) = TF.Plain $ dateToBuilder (Finite i)
  toField (UnQuoted (SDayTime  i )) = TF.Plain $ timeOfDayToBuilder (i)
  toField (UnQuoted (SDouble i )) =  TF.toField i
  toField (UnQuoted (SNumeric i )) =  TF.toField i
  toField i = TF.toField i

instance TF.ToField Position where
  toField = TF.toField . UnQuoted

instance TF.ToField LineString where
  toField = TF.toField . UnQuoted

instance TF.ToField Bounding where
  toField = TF.toField . UnQuoted

instance TF.ToField (UnQuoted Bounding ) where
  toField (UnQuoted (Bounding l)) = TF.Many  [str "ST_3DMakeBox(", TF.Many points ,   str ")"]
    where del = TF.Plain $ fromChar ','
          str = TF.Plain . fromByteString
          points :: [TF.Action]
          points = [point (Interval.lowerBound l), del, point (Interval.upperBound l)]
          -- point :: Position -> TF.Action
          point (ER.Finite (Position (lat,lon,alt))) = TF.Many [str "ST_setsrid(ST_MakePoint(", TF.toField lat , del , TF.toField lon , del, TF.toField alt , str "),4326)"]


instance TF.ToField (UnQuoted LineString) where
  toField (UnQuoted (LineString l)) = TF.Many  [str "ST_SetSRID(ST_MakeLine (", TF.Many points ,   str "),4326)"]
    where del = TF.Plain $ fromChar ','
          str = TF.Plain . fromByteString
          points :: [TF.Action]
          points = L.intercalate [del] (fmap point (F.toList l))
          point :: Position -> [TF.Action]
          point (Position (lat,lon,alt)) = [str "ST_MakePoint(", TF.toField lat , del , TF.toField lon , del, TF.toField alt , str ")"]


instance TF.ToField (UnQuoted Position) where
  toField (UnQuoted (Position (lat,lon,alt))) = TF.Many [str "ST_SetSRID(ST_MakePoint(", TF.toField lat , del , TF.toField lon , del, TF.toField alt , str "),4326)"]
    where del = TF.Plain $ fromChar ','
          str = TF.Plain . fromByteString

instance TF.ToField (UnQuoted a) => TF.ToField (Interval.Interval a) where
  toField = intervalBuilder

instance TF.ToField (UnQuoted a) => TF.ToField (UnQuoted (Interval.Extended a )) where
  toField (UnQuoted (ER.Finite i)) = TF.toField (UnQuoted i)
  toField (UnQuoted (ER.NegInf )) = TF.Plain (fromByteString "null")
  toField (UnQuoted (ER.PosInf )) = TF.Plain (fromByteString "null")

intervalBuilder i =  TF.Many [TF.Plain $ fromByteString ("\'"  <> lbd (snd $ Interval.lowerBound' i)) ,  TF.toField $  (UnQuoted $ Interval.lowerBound i) , TF.Plain $ fromChar ',' , TF.toField  (UnQuoted $ Interval.upperBound i) , TF.Plain $ fromByteString (ubd (snd $ Interval.upperBound' i) <> "\'")]
    where lbd True  =  "["
          lbd False = "("
          ubd True = "]"
          ubd False =")"


instance TF.ToField Showable where
  toField (SText t) = TF.toField t
  toField (SNumeric t) = TF.toField t
  toField (SDate t) = TF.toField t
  toField (SDayTime t) = TF.toField t
  -- toField (SSerial t) = maybe (TF.Plain $ fromByteString "null") TF.toField t
  toField (STimestamp t) = TF.toField t
  toField (SDouble t) = TF.toField t
  -- toField (SOptional t) = TF.toField t
  -- toField (SComposite t) = TF.toField t
  -- toField (SInterval t) = TF.toField t
  toField (SPosition t) = TF.toField t
  toField (SLineString t) = TF.toField t
  toField (SBounding t) = TF.toField t
  toField (SBoolean t) = TF.toField t
  -- toField (SDelayed t) = TF.toField t
  toField (SBinary t) = TF.toField (Binary t)
  toField (SDynamic t) = TF.toField (Binary (B.encode t))


defaultType t =
    case t of
      KOptional i -> Just (LeftTB1 Nothing)
      i -> Nothing

readTypeOpt t Nothing = case t of
    KOptional i -> Just $ LeftTB1 Nothing
    i -> Nothing
readTypeOpt t (Just i) = readType t i

readType t = case t of
    Primitive i -> fmap TB1 <$> readPrim i
    KOptional i -> opt LeftTB1 (readType i)
    KSerial i -> opt SerialTB1 (readType i)
    KArray i  -> parseArray (readType i)
    --KInterval i -> inter (readType i)
  where
      opt c f "" =  Just $ c Nothing
      opt c f i = fmap (c .Just) $ f i
      parseArray f i =   fmap ArrayTB1 $  allMaybes $ fmap f $ unIntercalate (=='\n') i
      -- inter f = (\(i,j)-> IntervalTB1 $ join $ Interval.interval <$> (f i) <*> (f $ safeTail j) )  .  break (==',')

readPrim t =
  case t of
     PText -> readText
     PCnpj -> readCnpj
     PCpf-> readCpf
     PDouble ->  readDouble
     PInt -> readInt
     PTimestamp -> readTimestamp
     PInterval -> readInterval
     PDate-> readDate
     PDayTime -> readDayTime
     PPosition -> readPosition
     PBoolean -> readBoolean
     PLineString -> readLineString
     PBinary -> readBin
  where
      readInt = nonEmpty (fmap SNumeric . readMaybe)
      readBoolean = nonEmpty (fmap SBoolean . readMaybe)
      readDouble = nonEmpty (fmap SDouble. readMaybe)
      readText = nonEmpty (\i-> fmap SText . readMaybe $  "\"" <> i <> "\"")
      readBin = nonEmpty (\i-> fmap (SBinary . BS.pack ) . readMaybe $  "\"" <> i <> "\"")
      readCnpj = nonEmpty (\i-> fmap (SText . T.pack . fmap Char.intToDigit ) . join . fmap (join . fmap (eitherToMaybe . cnpjValidate ). (allMaybes . fmap readDigit)) . readMaybe $  "\"" <> i <> "\"")
      readCpf = traceShowId . nonEmpty (\i-> fmap (SText . T.pack . fmap Char.intToDigit ) . join . fmap (join . fmap (eitherToMaybe . cpfValidate ). (allMaybes . fmap readDigit)) . readMaybe $  "\"" <> i <> "\"")
      readDate =  fmap (SDate . localDay . fst) . strptime "%Y-%m-%d"
      readDayTime =  fmap (SDayTime . localTimeOfDay . fst) . strptime "%H:%M:%OS"
      readPosition = nonEmpty (fmap SPosition . readMaybe)
      readLineString = nonEmpty (fmap SLineString . readMaybe)
      readTimestamp =  fmap (STimestamp  .  fst) . strptime "%Y-%m-%d %H:%M:%OS"
      readInterval =  fmap SPInterval . (\(h,r) -> (\(m,r)->  (\s m h -> secondsToDiffTime $ h*3600 + m*60 + s ) <$> readMaybe (safeTail r) <*> readMaybe m <*> readMaybe h )  $ break (==',') (safeTail r))  . break (==',')
      nonEmpty f ""  = Nothing
      nonEmpty f i  = f i

eitherToMaybe = either (const Nothing) Just

readDigit i
  | Char.isDigit i = Just $ Char.digitToInt i
  | otherwise = Nothing

cpfValidate i
  | length i /= 11 = Left "Invalid size Brazilian Cnpj need 14 digits"
  | m1v == m1 && m2v == m2 = Right i
  | otherwise = Left "Invalid checksum check your number"
  where multiplier1 =  [10,9,8,7,6,5,4,3,2]
        multiplier2 =  [11,10,9,8,7,6,5,4,3,2]
        multSum i j =  if remainder <2 then 0 else 11 - remainder
            where remainder = sum (zipWith (*) i j) `mod` 11
        m1 = multSum i multiplier1
        m2 = multSum i multiplier2
        [m1v,m2v] = drop 9 i

cnpjValidate i
  | length i /= 14 = Left "Invalid size Brazilian Cnpj need 14 digits"
  | m1v == m1 && m2v == m2 = Right i
  | otherwise = Left "Invalid checksum check your number"
  where multiplier1 = [ 5, 4, 3, 2, 9, 8, 7, 6, 5, 4, 3, 2 ]
        multiplier2 = [ 6, 5, 4, 3, 2, 9, 8, 7, 6, 5, 4, 3, 2 ]
        multSum i j =  if remainder <2 then 0 else 11 - remainder
            where remainder = sum (zipWith (*) i j) `mod` 11
        m1 = multSum i multiplier1
        m2 = multSum i multiplier2
        [m1v,m2v] = drop 12 i

tcnpj = [0,4,8,2,5,5,8,0,0,0,0,1,0,7]

cpf = [0,2,8,4,0,3,0,1,1,2,1]

safeTail [] = []
safeTail i = tail i



unIntercalateAtto :: (Show a1,Alternative f )=> [f a1] -> f a -> f [a1]
unIntercalateAtto l s = go l
  where
    go [e] =  fmap pure  e
    go (e:cs) =  liftA2 (:) e  (s *> go cs)
    go [] = errorWithStackTrace  "empty list"


unKOptionalAttr (Attr k i ) = Attr (unKOptional k) i
unKOptionalAttr (IT  r (LeftTB1 (Just j))  ) = (\j-> IT   r j )    j
unKOptionalAttr (FKT i  l (LeftTB1 (Just j))  ) = FKT (fmap (mapComp (first unKOptional) ) i)  l j

unOptionalAttr (Attr k i ) = Attr (unKOptional k) <$> unSOptional i
unOptionalAttr (IT r (LeftTB1 j)  ) = (\j-> IT   r j ) <$>     j
unOptionalAttr (FKT i  l (LeftTB1 j)  ) = liftA2 (\i j -> FKT i  l j) (traverse ( traComp (traFAttr unSOptional) . (mapComp (firstTB unKOptional)) ) i)  j

parseAttr :: TB Identity Key () -> Parser (TB Identity Key Showable)
-- parseAttr i | traceShow i False = error ""
parseAttr (Attr i _ ) = do
  s<- parseShowable (textToPrim <$> keyType  i) <?> show i
  return $  Attr i s


parseAttr (IT na j) = do
  mj <- doublequoted (parseLabeledTable j) <|> parseLabeledTable j -- <|>  return ((,SOptional Nothing) <$> j)
  return $ IT  na mj

parseAttr (FKT l rel j ) = do
  ml <- if L.null l
     then return []
     else do
       ml <- unIntercalateAtto (traComp parseAttr <$> l) (char ',')
       char ','
       return ml
  mj <- doublequoted (parseLabeledTable j) <|> parseLabeledTable j
  return $  FKT ml rel  mj

parseArray p = (char '{' *>  sepBy1 p (char ',') <* char '}')

tryquoted i = doublequoted i <|> i
-- Note Because the list has a mempty operation when parsing
-- we have overlap between maybe and list so we allow only nonempty lists
parseLabeledTable :: TB2 Key () -> Parser (TB2 Key Showable)
parseLabeledTable (ArrayTB1 [t]) =
  ArrayTB1 <$> (parseArray (doublequoted $ parseLabeledTable t) <|> parseArray (parseLabeledTable t) <|> (parseArray (doublequoted $ parseLabeledTable (mapKey kOptional t))  >>  return (fail "")  ) )
parseLabeledTable (DelayedTB1 (Just tb) ) =  string "t" >>  return (DelayedTB1  Nothing) -- <$> parseLabeledTable tb
parseLabeledTable (LeftTB1 (Just i )) =
  LeftTB1 <$> ((Just <$> parseLabeledTable i) <|> ( parseLabeledTable (mapTable (LeftTB1 . Just) <$>  mapKey kOptional i) >> return Nothing) <|> return Nothing )
parseLabeledTable  tb1 = traverse parseRecord  $ tb1

parseRecord  (me,m) = (char '('  *> (do
  im <- unIntercalateAtto (traverse (traComp parseAttr) <$> (M.toList (replaceRecRel  (_kvvalues $ unTB m) (fmap (fmap (fmap S.fromList) ) $ _kvrecrels  me))) ) (char ',')
  return (me,Compose $ Identity $  KV (M.fromList im) )) <*  char ')' )

parseRow els  = (char '('  *> (do
  im <- unIntercalateAtto (els ) (char ',')
  return  im) <*  char ')' )


inattr = _relOrigin . head . keyattri

startQuoted p =  do
  let backquote = string "\""  <|> string "\\\\" <|> string "\\"
  i <- lookAhead (many backquote )
  readQuoted (L.length i) p


startQuotedText =  do
  let backquote = string "\""  <|> string "\\\\" <|> string "\\"
  i <- lookAhead (many backquote )
  readQuotedText (L.length i)

readText 0 = plain' ",)}"
readText ix =  ( liftA2 (\i j  -> i <> BS.concat  j ) (scapedText ix)  (many1 (liftA2 (<>) (fmap requote (readQuotedText (ix +1))) (scapedText ix )))   <|> scapedText ix )
      where
            requote t = "\"" <> t <> "\""
            scapedText ix = liftA2 (<>) (plain0' "\\\"") (BS.intercalate "" <$> ( many ((<>) <$> choice (escapedItem  ix <$>  escapes) <*>  plain0' "\\\"")))
              where
                escapes = [("n","\n"),("r","\r"),("t","\t"),("224","\224"),("225","\225"),("227","\227"),("233","\233"),("237","\237"),("243","\243"),("245","\245"),("231","\231")]
                escapedItem ix (c, o)  = Tra.sequence (replicate ix (char '\\'))  >> string c >> return o


readQuotedText ix = readQuoted ix readText

readQuoted 0 p = p 0
readQuoted ix p =  do
    i <- Tra.sequence (replicate ix backquote  )
    v <- p ix
    _ <-  string (BS.concat i)
    return v
      where backquote = string "\""  <|> string "\\\\" <|> string "\\"





doublequoted :: Parser a -> Parser a
doublequoted  p =   (takeWhile (== '\\') >>  char '\"') *>  inner <* ( takeWhile (=='\\') >> char '\"')
  where inner = doublequoted p <|> p

testStr = "(8504801,\"SALPICAO \",99,\"NAO SE APLICA\",1,\"Salad, chicken (\"\"mayo\"\" dressing), with egg, chicken, breast, skin removed before cooking,  mayo type dressing, real,  regular, commercial, salt regular\",202.853,14.261,14.414,3.934,0.551,28.293,16.513,0.049,123.926,0.913,202.763,0,173.16,0.044,0.746,15.643,44.841,55.818,0.056,0.16,4.729,7.519,0.338,0.374,20.357,0.349,1.113,3.081,114.279,2.68,4.015,6.351,5.575,0.666,0.07,2.909,2.091)"

testString3 = "\"StatusCodeException (Status {statusCode = 500, statusMessage = \"\"Internal Server Error\"\"}) [(\"\"Date\"\",\"\"Fri, 04 Sep 2015 20:34:49 GMT\"\"),(\"\"Server\"\",\"\"Microsoft-IIS/6.0\"\"),(\"\"MicrosoftOfficeWebServer\"\",\"\"5.0_Pub\"\"),(\"\"X-Powered-By\"\",\"\"ASP.NET\"\"),(\"\"Content-Length\"\",\"\"527\"\"),(\"\"Content-Type\"\",\"\"text/html; Charset=iso-8859-1\"\"),(\"\"Expires\"\",\"\"Sat, 15 May 1999 21:00:00 GMT\"\"),(\"\"Cache-control\"\",\"\"private\"\"),(\"\"X-Response-Body-Start\"\",\"\" <font face=\\\\\"\"Arial\\\\\"\" size=2>\\\\n<p>Microsoft OLE DB Provider for ODBC Drivers</font> <font face=\\\\\"\"Arial\\\\\"\" size=2>erro '80004005'</font>\\\\n<p>\\\\n<font face=\\\\\"\"Arial\\\\\"\" size=2>[IBM][CLI Driver][AS] SQL0104N  Um token inesperado &quot;&lt;&quot; foi encontrado ap&#243;s &quot;&quot;.  Os tokens esperados podem incluir:  &quot;( + - ? : DAY INF NAN NOT RID ROW RRN CASE CAST CHAR DATE DAYS&quot;.  SQLSTATE=42601\\\\r\\\\n</font>\\\\n<p>\\\\n<font face=\\\\\"\"Arial\\\\\"\" size=2>/sistemas/saces/classe/pacote_geral01.asp</font><font face=\\\\\"\"Arial\\\\\"\" size=2>, line 95</font> \"\"),(\"\"X-Request-URL\"\",\"\"POST http://www2.goiania.go.gov.br:80/sistemas/saces/asp/saces00005a1.asp\"\")] (CJ {expose = [Cookie {cookie_name = \"\"ASPSESSIONIDASQBRSTC\"\", cookie_value = \"\"FJDGMJKAJIGAICINDDHBNBOB\"\", cookie_expiry_time = 3015-01-05 00:00:00 UTC, cookie_domain = \"\"www2.goiania.go.gov.br\"\", cookie_path = \"\"/\"\", cookie_creation_time = 2015-09-04 20:34:48.13491 UTC, cookie_last_access_time = 2015-09-04 20:34:48.135013 UTC, cookie_persistent = False, cookie_host_only = True, cookie_secure_only = False, cookie_http_only = False}]})\""

testString = "9292,\"Salad, chicken (\"\"mayo\"\" dressing), with egg, chicken, breast, skin removed before cooking,  mayo type dressing, real,  regular, commercial, salt regular\",\"NAO SE APLICA\",\"Cactus pads (nopales), cooked, boiled\",\"Receita de Ambrosia digitada no NDS 0 fonte \"\"Culin\195\161ria Goiana\"\"\""
testString2 = "\\\\\"\"PROJETO DEVOLVIDO AO CBM AP\195\147S CORRE\195\135\195\131O\\\\\"\""
ptestString = (parseOnly (unIntercalateAtto (parsePrim <$> [PText,PText,PText,PText,PText]) (char ',') )) testString
ptestString2 = (parseOnly (unIntercalateAtto (parsePrim <$> [PText]) (char ',') )) testString2
ptestString3 = (parseOnly (startQuotedText )) testString3

parsePrim
  :: KPrim
       -> Parser Showable
-- parsePrim i | traceShow i False = error ""
parsePrim i =  do
   case i of
        PDynamic ->  let
              pr = SDynamic . B.decode . BSL.fromStrict . fst . B16.decode . BS.drop 1 <$>  (takeWhile (=='\\') *> plain' "\\\",)}")
                in doublequoted pr <|> pr
        PBinary ->  let
              pr = SBinary . fst . B16.decode . BS.drop 1 <$>  (takeWhile (=='\\') *> plain' "\\\",)}")
                in doublequoted pr <|> pr
        PMime  _ -> let
              pr = SBinary . fst . B16.decode . BS.drop 1 <$>  (takeWhile (=='\\') *> plain' "\\\",)}" <* takeWhile (=='\\'))
                in doublequoted  pr <|> pr
        PInt ->  SNumeric <$>  signed decimal
        PBoolean -> SBoolean <$> ((const True <$> string "t") <|> (const False <$> string "f"))
        PDouble -> SDouble <$> pg_double
        PText -> let
            dec =  startQuotedText <|> const "" <$> string"\"\""
              in    (fmap SText $ join $ either (fail. show)  (return)  . TE.decodeUtf8' <$> dec) <|> (SText   . TE.decodeLatin1 <$> dec )
        PCnpj -> parsePrim PText
        PCpf -> parsePrim PText
        PInterval ->
          let i = SPInterval <$> diffInterval
           in doublequoted i <|> i

        PTimestamp ->
             let p =  do
                    i <- fmap (STimestamp  . fst) . strptime "%Y-%m-%d %H:%M:%OS"<$> plain' "\\\",)}"
                    maybe (fail "cant parse date") return i
                 in p <|> doublequoted p
        PDayTime ->
             let p =  do
                    i <- fmap (SDayTime . localTimeOfDay .  fst) . strptime "%H:%M:%OS"<$> plain' "\\\",)}"
                    maybe (fail "cant parse date") return i
                 in p <|> doublequoted p
        PDate ->
             let p = do
                    i <- fmap (SDate . localDay . fst). strptime "%Y-%m-%d" <$> plain' "\\\",)}"
                    maybe (fail "cant parse date") return i
                 in p <|> doublequoted p
        PPosition -> do
          s <- plain' "\",)}"
          case  Sel.runGet getPosition (fst $ B16.decode s)of
              i -> case i of
                Right i -> pure $ SPosition i
                Left e -> fail e
        PLineString -> do
          s <- plain' "\",)}"
          case  Sel.runGet getLineString (fst $ B16.decode s)of
              i -> case i of
                Right i -> pure $ SLineString i
                Left e -> fail e
        PBounding -> SBounding <$> ((doublequoted box3dParser ) <|> box3dParser)


-- parseShowable (KArray (KDelayed i))
    -- = (string "t" >> return (ArrayTB1 $ [ SDelayed Nothing]))
parseShowable (KArray i)
    =  ArrayTB1  <$> (par <|> doublequoted par)
      where par = char '{'  *>  sepBy (parseShowable i) (char ',') <* char '}'
parseShowable (KOptional i)
    = LeftTB1 <$> ( (Just <$> (parseShowable i)) <|> pure (showableDef i) )
parseShowable (KDelayed i)
    = (string "t" >> return (DelayedTB1 Nothing))
parseShowable (KSerial i)
    = SerialTB1 <$> ((Just <$> parseShowable i) )
parseShowable (KInterval k)=
    let
      emptyInter = const (IntervalTB1 Interval.empty) <$> string "empty"
      inter = do
        lb <- (char '[' >> return True ) <|> (char '(' >> return False )
        i <- parseShowable k
        char ','
        j <- parseShowable k
        rb <- (char ']' >> return True) <|> (char ')' >> return False )
        return $ IntervalTB1 $ Interval.interval (ER.Finite i,lb) (ER.Finite j,rb)
    in doublequoted inter <|> inter <|> emptyInter


parseShowable (Primitive i) = TB1 <$> parsePrim i
parseShowable i  = error $  "not implemented " <> show i

pg_double :: Parser Double
pg_double
    =   (string "NaN"       *> pure ( 0 / 0))
    <|> (string "Infinity"  *> pure ( 1 / 0))
    <|> (string "-Infinity" *> pure (-1 / 0))
    <|> double



unOnly :: Only a -> a
unOnly (Only i) = i


instance Sel.Serialize a => Sel.Serialize (ER.Extended a ) where
  get = ER.Finite <$> Sel.get
  put (ER.Finite i ) = Sel.put i

instance Sel.Serialize Bounding where
  get = do
      i <- liftA2 (Interval.interval) Sel.get Sel.get
      return  $ Bounding i
  put (Bounding i ) = do
      Sel.put (Interval.upperBound i)
      Sel.put (Interval.lowerBound i)



instance Sel.Serialize Position where
  get = do
      x <- Sel.getFloat64le
      y <- Sel.getFloat64le
      z <- Sel.getFloat64le
      return  $ Position (x,y,z)
  put (Position (x,y,z)) = do
      Sel.putFloat64le x
      Sel.putFloat64le y
      Sel.putFloat64le z

instance Sel.Serialize LineString where
  get = do
      n <- Sel.getWord32host
      LineString .Vector.fromList <$> replicateM (fromIntegral n ) Sel.get
  put (LineString  v ) = do
      mapM_ (Sel.put) (F.toList v)



getLineString = do
          i <- Sel.getWord8
          if i  == 1
           then do
             typ <- Sel.getWord32host
             srid <- Sel.getWord32host
             let ty = typ .&. complement 0x20000000 .&. complement 0x80000000
             case ty  of
               2 -> Sel.get
               i -> error $ "type not implemented " <> show ty
           else
             return (error $ "BE not implemented " <> show i )


box3dParser = do
          string "BOX3D"
          let makePoint [x,y,z] = Position (x,y,z)
          res  <- char '(' *> sepBy1 (sepBy1 ( scientific) (char ' ') ) (char ',') <* char ')'
          return $ case fmap (fmap  realToFrac) res  of
            [m,s] ->  Bounding ((ER.Finite $ makePoint m ,True) `Interval.interval` (ER.Finite $ makePoint s,True))



instance F.FromField Position where
  fromField f t = case  fmap (Sel.runGet getPosition ) decoded of
    Just i -> case i of
      Right i -> pure i
      Left e -> F.returnError F.ConversionFailed  f e
    Nothing -> error "empty value"
    where
        decoded = fmap (fst . B16.decode) t

getPosition = do
          i <- Sel.getWord8
          if i  == 1
           then do
             typ <- Sel.getWord32host
             srid <- Sel.getWord32host
             let ty = typ .&. complement 0x20000000 .&. complement 0x80000000
             case ty  of
               1 -> Sel.get
               i -> error $ "type not implemented " <> show ty
           else
             return (error $ "BE not implemented " <> show i  )


safeMaybe e f i = maybe (errorWithStackTrace (e  <> ", input = " <> show i )) id (f i)

instance F.FromField DiffTime where
  fromField  f mdat = case  mdat of
    Nothing -> F.returnError F.UnexpectedNull f ""
    Just dat -> do
      case parseOnly diffInterval dat of

          Left err -> F.returnError F.ConversionFailed f err
          Right conv -> return conv

diffIntervalLayout = sepBy1 (toRealFloat <$> scientific) (string " days " <|> string " day " <|>  string ":" )

diffInterval = (do
  res  <- diffIntervalLayout
  return $ case res  of
    [s] ->  secondsToDiffTime (round s)
    [m,s] ->  secondsToDiffTime (round $  (60 ) * m + s)
    [h,m,s] ->  secondsToDiffTime (round $ h * 3600 + (60 ) * m + s)
    [d,h,m,s] -> secondsToDiffTime (round $ d *3600*24 + h * 3600 + (60  ) * m + s)
    v -> errorWithStackTrace $ show v)


plain' :: String -> Parser BS.ByteString
plain' delim = takeWhile1 (notInClass (delim ))

plain0' :: String -> Parser BS.ByteString
plain0' delim = Data.Attoparsec.ByteString.Char8.takeWhile (notInClass (delim ))

parseInter token = do
    lb <- (char '[' >> return True) <|> (char '(' >> return False)
    [i,j] <- token
    rb <- (char ']' >> return True ) <|> (char ')' >> return False )
    return [(lb,ER.Finite i),(rb,ER.Finite j)]


instance F.FromField a => F.FromField (Only a) where
  fromField = fmap (fmap (fmap Only)) F.fromField

fromShowable ty v =
   case parseOnly (parseShowable (textToPrim <$> ty )) v of
      Right i -> Just i
      Left l -> Nothing

fromRecord foldable = do
    let parser  = parseRecord foldable
    FR.fieldWith (\i j -> case traverse (parseOnly  parser )  j of
                               (Right (Just r ) ) -> return r
                               Right Nothing -> error (show j )
                               Left i -> error (show i <> "  " <> maybe "" (show .T.pack . BS.unpack) j  ) )

parseField parser = do
    FR.fieldWith (\i j -> case traverse (parseOnly  parser )  j of
                               (Right (Just r ) ) -> return r
                               Right Nothing -> error (show j )
                               Left i -> error (show i <> "  " <> maybe "" (show .T.pack . BS.unpack) j  ) )

parserFieldAtto parser = (\i j -> case traverse (parseOnly  parser )  j of
                               (Right (Just r ) ) -> return r
                               Right Nothing -> error (show j )
                               Left i -> error (show i <> "  " <> maybe "" (show .T.pack . BS.unpack) j  ) )

instance (FromField a, FromField b, FromField c, FromField d, FromField e,
          FromField f, FromField g, FromField h, FromField i, FromField j,FromField k) =>
    FromRow (a,b,c,d,e,f,g,h,i,j,k) where
    fromRow = (,,,,,,,,,,) <$> field <*> field <*> field <*> field <*> field
                          <*> field <*> field <*> field <*> field <*> field <*> field


withCount value = do
  v <- value
  c <- FR.field
  return (v,c)

fromAttr foldable = do
    let parser  = parseLabeledTable foldable
    FR.fieldWith (\i j -> case traverse (parseOnly  parser )  j of
                               (Right (Just r ) ) -> return r
                               Right Nothing -> error (show j )
                               Left i -> error (show i <> "  " <> maybe "" (show .T.pack . BS.unpack) j  ) )

withTestConn s action  = do
  conn <- liftIO $connectPostgreSQL $ "user=massudaw password=queijo host=localhost port=5433 dbname=" <> fromString (T.unpack s)
  action conn

withConn s action =  do
  conn <- liftIO $connectPostgreSQL $ "user=postgres password=queijo host=localhost port=5432 dbname=" <> fromString (T.unpack s)
  action conn
