{-# LANGUAGE DeriveDataTypeable,ConstraintKinds,TypeFamilies ,DeriveTraversable,DeriveFoldable,StandaloneDeriving,RecursiveDo,FlexibleInstances,RankNTypes,NoMonomorphismRestriction,ScopedTypeVariables,UndecidableInstances,FlexibleContexts,OverloadedStrings ,TupleSections, ExistentialQuantification #-}
module Postgresql where

import Types
import Data.Ord
import Control.Monad
import Query
import GHC.Stack
import Debug.Trace
import qualified Data.Binary as B
import Data.Functor.Identity
import Data.Scientific hiding(scientific)
import Data.Bits
import qualified  Data.Map as M

import Data.Tuple
import Data.Time.Clock
import Data.String
import Data.Attoparsec.Combinator (lookAhead)

import Control.Applicative
import Control.Monad.IO.Class
import qualified Data.Serialize as Sel
import Data.Maybe
import qualified Data.ExtendedReal as ER
import qualified Data.ByteString.Base16 as B16
import Data.Time.Parse
import           Database.PostgreSQL.Simple.Types as PGTypes
import           Data.Attoparsec.ByteString.Char8 hiding (Result)
import Data.Traversable (traverse)
import qualified Data.Traversable  as Tra
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
import qualified Database.PostgreSQL.Simple.ToField as TF
import qualified Database.PostgreSQL.Simple.FromRow as FR
import qualified Database.PostgreSQL.Simple.ToRow as TR
import Database.PostgreSQL.Simple
import Blaze.ByteString.Builder(fromByteString)
import Blaze.ByteString.Builder.Char8(fromChar)



-- Wrap new instances without quotes delimiting primitive values
newtype UnQuoted a = UnQuoted {unQuoted :: a}

instance (Show a,TF.ToField a , TF.ToField (UnQuoted (a))) => TF.ToField (FTB a) where
  toField (LeftTB1 i) = maybe (TF.Plain (fromByteString "null")) TF.toField  i
  toField (SerialTB1 i) = maybe (TF.Plain (fromByteString "null")) TF.toField  i
  toField (DelayedTB1 i) = maybe (TF.Plain (fromByteString "null")) TF.toField  i
  toField (ArrayTB1 is ) = TF.toField $ PGTypes.PGArray   is
  toField (IntervalTB1 is ) = TF.toField  $ fmap (\(TB1 i ) -> i) is
  toField (TB1 i) = TF.toField i
  -- toField i = errorWithStackTrace (show i)


instance  TF.ToField (TB Identity Key Showable)  where
  toField (Attr k  i) = case  topconversion (textToPrim <$> keyType k) of
          Just (_,b) -> TF.toField (b i)
          Nothing -> TF.toField i
  toField (IT n (LeftTB1 i)) = maybe (TF.Plain ( fromByteString "null")) (TF.toField . IT n ) i
  toField (IT n (TB1 (m,i))) = TF.toField (TBRecord2  (kvMetaFullName  m ) (L.sortBy (comparing (keyPosition . inattr ) ) $ maybe id (flip mappend) attrs $ (runIdentity.getCompose <$> F.toList (_kvvalues $ unTB i) )  ))
      where attrs = Tra.traverse (\i -> Attr i <$> showableDef (keyType i) ) $  F.toList $ (S.fromList $ _kvattrs  m ) `S.difference` (S.map _relOrigin $ S.unions $ M.keys (_kvvalues $ unTB i))
  toField (IT (n)  (ArrayTB1 is )) = TF.toField $ PGTypes.PGArray $ (TF.toField . IT n) <$> is
  toField e = errorWithStackTrace (show e)



instance TR.ToRow a => TF.ToField (TBRecord2 a) where
  toField (TBRecord2 s l) =  TF.Many   (TF.Plain (fromByteString "ROW(") : L.intercalate [TF.Plain $ fromChar ','] (fmap pure. TR.toRow  $ l) <> [TF.Plain (fromByteString $ ") :: " <>  BS.pack (T.unpack s) )] )


data TBRecord2 a = TBRecord2 Text a

instance TF.ToField (UnQuoted Showable) where
  toField (UnQuoted (STimestamp i )) = TF.Plain $ localTimestampToBuilder (Finite i)
  toField (UnQuoted (SDate i )) = TF.Plain $ dateToBuilder (Finite i)
  toField (UnQuoted (SDayTime  i )) = TF.Plain $ timeOfDayToBuilder (i)
  toField (UnQuoted (SDouble i )) =  TF.toField i
  toField (UnQuoted (SNumeric i )) =  TF.toField i
  toField (UnQuoted i) = errorWithStackTrace (show i)

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
  toField (STimestamp t) = TF.toField t
  toField (SDouble t) = TF.toField t
  toField (SPosition t) = TF.toField t
  toField (SLineString t) = TF.toField t
  toField (SBounding t) = TF.toField t
  toField (SBoolean t) = TF.toField t
  toField (SBinary t) = TF.toField (Binary t)
  toField (SDynamic t) = TF.toField (Binary (B.encode t))


defaultType t =
    case t of
      KOptional i -> Just (LeftTB1 Nothing)
      i -> Nothing


unIntercalateAtto :: (Show a1,Alternative f )=> [f a1] -> f a -> f [a1]
unIntercalateAtto l s = go l
  where
    go [e] =  fmap pure  e
    go (e:cs) =  liftA2 (:) e  (s *> go cs)
    go [] = errorWithStackTrace  "empty list"


parseAttr :: TB Identity Key () -> Parser (TB Identity Key Showable)
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
                escapes = [("n","\n"),("r","\r"),("t","\t"),("129","\129"),("137","\137"),("167","\167"),("194","\194"),("195","\195"),("224","\224"),("225","\225"),("227","\227"),("233","\233"),("237","\237"),("243","\243"),("245","\245"),("231","\231")]
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
parseShowable :: KType (Prim KPrim (Text,Text)) -> Parser (FTB Showable)
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

parseShowable p@(Primitive (AtomicPrim i)) = forw  . TB1 <$> parsePrim i
  where (forw,_) = conversion p

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

instance (FromField a, FromField b, FromField c, FromField d, FromField e,
          FromField f, FromField g, FromField h, FromField i, FromField j,FromField k) =>
    FromRow (a,b,c,d,e,f,g,h,i,j,k) where
    fromRow = (,,,,,,,,,,) <$> field <*> field <*> field <*> field <*> field
                          <*> field <*> field <*> field <*> field <*> field <*> field



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
   case parseOnly (parseShowable (mapKType ty )) v of
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
