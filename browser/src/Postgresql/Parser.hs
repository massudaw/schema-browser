{-# LANGUAGE
  UndecidableInstances,FlexibleInstances,FlexibleContexts,TupleSections #-}
module Postgresql.Parser where

import qualified Data.HashMap.Strict as HM
import Types hiding (Parser,double)
import Postgresql.Types
import Data.Dynamic
import Debug.Trace
import Control.Exception(throw,SomeException,catch)
import Text
import Types.Patch
import Postgresql.Printer
import RuntimeTypes
import Control.Monad.Trans.Class
import Control.Monad.RWS
import Data.Time.Format
import SchemaQuery.Store
import Data.Ord
import qualified Data.Aeson as A
import qualified Control.Lens as Le
import qualified Data.Aeson.Types as A
import qualified Data.Foldable as F
import Data.Either
import Utils
import qualified Data.Sequence.NonEmpty as NonS
import qualified Data.Binary as B
import Data.Scientific hiding(scientific)
import Data.Bits
import Data.Tuple
import Data.Time.Clock
import Data.String
import Control.Applicative
import qualified Data.Serialize as Sel
import Data.Maybe
import qualified Data.ExtendedReal as ER
import qualified Data.ByteString.Base16 as B16
import           Database.PostgreSQL.Simple.Types as PGTypes
import           Data.Attoparsec.ByteString.Char8 hiding (Result)
import           Data.Attoparsec.ByteString.Char8 as C hiding (Result)
import Data.Traversable (traverse)
import Data.Time.LocalTime
import qualified Data.List as L
import qualified Data.Vector as Vector
import qualified Data.Interval as Interval
import qualified Data.ByteString.Char8 as BS
import qualified Data.ByteString.Lazy.Char8 as BSL
import Prelude hiding (takeWhile)
import qualified Data.Text as T
import Data.Text (Text)
import Database.PostgreSQL.Simple.Time
import qualified Database.PostgreSQL.Simple.FromField as F
import qualified Database.PostgreSQL.Simple.ToField as TF
import qualified Database.PostgreSQL.Simple.FromRow as FR
import qualified Database.PostgreSQL.Simple.ToRow as TR
import Database.PostgreSQL.Simple
import Blaze.ByteString.Builder(fromByteString)
import Blaze.ByteString.Builder.Char8(fromChar)

type JSONParser = CodegenT A.Parser

newtype UnQuoted a = UnQuoted {unQuoted :: a}

newtype DoubleQuoted a = DoubleQuoted {unDoubleQuoted :: a}

instance TF.ToField (DoubleQuoted Showable) where
  toField (DoubleQuoted i) = TF.toField (DoubleQuoted (renderPrim i))

instance TF.ToField (DoubleQuoted (FTB Showable)) where
  toField (DoubleQuoted i) = TF.toField (DoubleQuoted (renderShowable i))

instance TF.ToField (DoubleQuoted String) where
  toField (DoubleQuoted i) = TF.Many [TF.Plain "\"", TF.Plain (fromByteString $ BS.pack i) , TF.Plain "\""]

instance (TF.ToField a, TF.ToField b) => TF.ToField (Either a b) where
  toField i = either TF.toField TF.toField i

instance TF.ToField (KType (Prim KPrim (Text,Text)),FTB Showable) where
  toField (k,i) = case liftA2 (,) (ktypeRec ktypeUnLift k) (topconversion preunconversion k) of
     Just (k,(_,b)) -> toFielPrim k (b i)
     Nothing -> toFielPrim k i
    where
      toFielPrim (Primitive l n@(AtomicPrim kp)) = toFiel l
        where
          toFiel (KOptional : k ) (LeftTB1 i) = maybe (TF.Plain "null") (toFiel  k) i
          toFiel (KSerial : k ) (LeftTB1 i) = maybe (TF.Plain "null") (toFiel  k) i
          toFiel (KSerial : k ) i = toFiel  k i
          toFiel (KArray : k ) (ArrayTB1 is ) = TF.Many $[TF.toField $ PGTypes.PGArray   (F.toList $ fmap unTB1 is)  ] ++ maybeToList ( TF.Plain .fromByteString . BS.pack . T.unpack . (" :: "<>) <$> ( renderType (Primitive (KArray :k) n )))
          toFiel (KInterval : k) (IntervalTB1 is ) = TF.Many [TF.Plain ( fromByteString $ BS.pack $ T.unpack $justError ("no array" <> show k) $ renderType (Primitive  (KInterval: k) n ) ) ,TF.Plain "(" ,TF.toField  (fmap unTB1 $ unFinite $ Interval.lowerBound is ), TF.Plain ",",TF.toField (fmap unTB1 $ unFinite $ Interval.upperBound is) ,TF.Plain ",'" ,TF.Plain (down (snd $ Interval.lowerBound' is)) , TF.Plain (up (snd $ Interval.upperBound' is)) ,TF.Plain "')"]
            where up True = "]"
                  up False = ")"
                  down True = "["
                  down False = "("
          toFiel [] (TB1 i) = TF.Many [TF.toField (kp,i) ,TF.Plain $ fromByteString $maybe ""  (" :: "<>) (BS.pack . T.unpack <$> renderType (Primitive [] n))]
          toFiel i j = error ("toFiel" ++ show (i,j))


instance  TF.ToField (TB PGKey Showable)  where
  toField  = TF.toField . firstTB (Le.over keyTypes (fmap textToPrim))

instance  TF.ToField (TB Key Showable)  where
  toField (Attr k  i) = TF.toField (keyType k ,i)
  toField (IT n (LeftTB1 i)) = maybe (TF.Plain (fromByteString "null")) (TF.toField . IT n ) i
  toField (IT n (TB1 i)) = TF.toField (TBRecord2 ((\(Primitive _ (RecordPrim j)) -> j )$  keyType n) $ L.sortOn (L.maximumBy (comparing keyPosition) . relOutputSet  . index) (unkvlist i))
  toField (IT n (ArrayTB1 is )) = TF.toField . PGTypes.PGArray $ IT n <$> F.toList is
  toField e = error (show e)


instance TR.ToRow a => TF.ToField (TBRecord2 a) where
  toField (TBRecord2 (s,t) l) =  TF.Many (TF.Plain (fromByteString "ROW(") : L.intercalate [TF.Plain $ fromChar ','] (fmap pure. TR.toRow  $ l) <> [TF.Plain (fromString . T.unpack $  ") :: " <> s <> "." <> t) ] )


data TBRecord2 a = TBRecord2 (Text,Text) a deriving (Show)

instance TF.ToField (UnQuoted Showable) where
  toField (UnQuoted (SDouble i )) =  TF.toField i
  toField (UnQuoted (SNumeric i )) =  TF.toField i
  toField (UnQuoted (SGeo (SPosition i ))) =  TF.toField i
  toField (UnQuoted (STime t)) = case t of
        STimestamp i ->  TF.Plain $ utcTimestampToBuilder (Finite i)
        SDate i  -> TF.Plain $ dateToBuilder (Finite i)
        SDayTime i -> TF.Plain $ timeOfDayToBuilder (i)
  toField (UnQuoted i) = error (show i)

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
          point (ER.Finite (Position  lat lon alt)) = TF.Many [str "ST_setsrid(ST_MakePoint(", TF.toField lat , del , TF.toField lon , del, TF.toField alt , str "),4326)"]
          point (ER.Finite (Position2D  lat lon)) = TF.Many [str "ST_setsrid(ST_MakePoint(", TF.toField lat , del , TF.toField lon ,  str "),4326)"]


instance TF.ToField (UnQuoted SGeo) where
  toField (UnQuoted (SMultiGeom i )) = TF.Many  [str "ST_SetSRID(ST_collect( array[" , TF.Many inner,   str "]),4326)"]
    where
      inner :: [TF.Action]
      inner = L.intercalate [del] (fmap (pure .TF.toField) i)
      str = TF.Plain . fromByteString
      del = TF.Plain $ fromChar ','
  toField (UnQuoted (SPolygon i j)) = TF.Many  [str "ST_SetSRID(ST_MakePolygon ( ", TF.toField i ,if L.null inner then str "" else TF.Many [str ",array[" , TF.Many inner,   str "]"] , str "),4326)"]
    where
      inner :: [TF.Action]
      inner = L.intercalate [del] (fmap (pure .TF.toField) j)
      str = TF.Plain . fromByteString
      del = TF.Plain $ fromChar ','
  toField (UnQuoted ((SLineString l))) = TF.toField (UnQuoted l)
  toField (UnQuoted (SPosition l )) = TF.toField (UnQuoted l)
  toField (UnQuoted (SBounding l )) = TF.toField (UnQuoted l)

instance TF.ToField (UnQuoted LineString) where
  toField (UnQuoted (LineString l)) = TF.Many  [str "ST_SetSRID(ST_MakeLine (array[", TF.Many points ,   str "]),4326)"]
    where del = TF.Plain $ fromChar ','
          str = TF.Plain . fromByteString
          points :: [TF.Action]
          points = L.intercalate [del] (fmap point (F.toList l))
          point :: Position -> [TF.Action]
          point (Position  lat lon alt ) = [str "ST_MakePoint(", TF.toField lat , del , TF.toField lon , del, TF.toField alt , str ")"]
          point (Position2D  lat lon ) = [str "ST_setsrid(ST_MakePoint(", TF.toField lat , del , TF.toField lon ,  str "),4326)"]


instance TF.ToField (UnQuoted Position) where
  toField (UnQuoted (Position  lat lon alt )) = TF.Many [str "ST_setsrid(st_makePoint(", TF.toField lat , del , TF.toField lon , del, TF.toField alt , str "),4326)"]
    where del = TF.Plain $ fromChar ','
          str = TF.Plain . fromByteString
  toField (UnQuoted (Position2D  lat lon )) = TF.Many [str "ST_setsrid(st_makePoint(", TF.toField lat , del , TF.toField lon , del,  str "),4326)"]
    where del = TF.Plain $ fromChar ','
          str = TF.Plain . fromByteString

instance TF.ToField (UnQuoted a) => TF.ToField (Interval.Interval a) where
  toField = intervalBuilder

instance TF.ToField (UnQuoted a) => TF.ToField (UnQuoted (Interval.Extended a )) where
  toField (UnQuoted (ER.Finite i)) = TF.toField (UnQuoted i)
  toField (UnQuoted (ER.NegInf )) = TF.Plain (fromByteString "")
  toField (UnQuoted (ER.PosInf )) = TF.Plain (fromByteString "")

intervalBuilder i =  TF.Many [TF.Plain $ fromByteString ("\'"  <> lbd (snd $ Interval.lowerBound' i)) ,  TF.toField $  (UnQuoted $ Interval.lowerBound i) , TF.Plain $ fromChar ',' , TF.toField  (UnQuoted $ Interval.upperBound i) , TF.Plain $ fromByteString (ubd (snd $ Interval.upperBound' i) <> "\'")]
    where lbd True  =  "["
          lbd False = "("
          ubd True = "]"
          ubd False =")"

instance TF.ToField SGeo where
  toField (SPosition t) = TF.toField t
  toField (SLineString t) = TF.toField t
  toField (SBounding t) = TF.toField t
  toField t = TF.toField (UnQuoted t)


instance TF.ToField (KPrim,Showable) where
  toField (PDynamic "ftb_showable", SDynamic (HDynamic t)) = TF.toField (Binary  $ B.encode (justError "wrong type " $ fromDynamic t :: FTB Showable))
  toField (PDynamic "row_index", SDynamic (HDynamic t)) = TF.toField (Binary  $ B.encode (justError "wrong type " $ fromDynamic t :: [TBIndex Showable]))
  toField (PDynamic "row_operation", SDynamic (HDynamic t)) = TF.toField (Binary  $ B.encode (justError "wrong type " $ fromDynamic t :: RowOperation Text Showable))
  toField (_,i) = TF.toField i

instance TF.ToField Showable where
  toField (SJSON t) = TF.toField t
  toField (SText t) = TF.toField t
  toField (SNumeric t) = TF.toField t
  toField (SBoolean t) = TF.toField t
  toField (SDouble t) = TF.toField t
  toField (STime ti)
    = case ti of
      SDate  t -> TF.toField t
      SDayTime t -> TF.toField t
      STimestamp t -> TF.toField t
  toField (SGeo i ) = TF.toField i
  toField (SBinary t) = TF.toField (Binary t)
  toField (SDynamic t) = TF.toField (Binary (B.encode t))


parseAttrJSON inf (Attr i _ )  v = do
  let tyun = fromMaybe (keyType i) $ ktypeRec ktypeUnLift (keyType i)
  s<- parseShowableJSON  parsePrimitiveJSON tyun  v
  return $  Attr i s
parseAttrJSON inf (Fun i rel _ )v = do
  s<- parseShowableJSON parsePrimitiveJSON (keyType  i) v
  return $  (Fun i rel s)
parseAttrJSON inf (IT na (Primitive _ j)) v = do
  mj <- parseShowableJSON  (parseRecordLoad inf j) (keyType na) v
  return $ IT  na mj
parseAttrJSON inf i v = error (show ("ParserAttrJSON",i,v))

parseRecordLoad :: InformationSchema -> KVMeta Key -> Prim KPrim (Text,Text) -> A.Value -> JSONParser (FTB (TBData Key Showable))
parseRecordLoad inf proj (RecordPrim r) v=
  fmap TB1 $ parseRecordJSON inf (tableMeta tb) proj v
  where tb = lookSTable inf r


parseRecordJSON :: InformationSchema -> KVMetadata Key -> KVMeta Key -> A.Value -> JSONParser (TBData Key Showable)
parseRecordJSON  inf me m (A.Object v) = atTable me $ do
  let try1 i v = do
        tb <- lkTB i
        return $ justError (" no attr " <> show (i,v)) $ HM.lookup tb  v
  traverseKV (\i -> parseAttrJSON  inf i =<<  try1 i v)$   m

decodeDynamic :: String -> BSL.ByteString  -> Showable
decodeDynamic "row_index" i = SDynamic . HDynamic . toDyn $ ( B.decode i :: [TBIndex Showable])
decodeDynamic "ftb_showable" i = SDynamic . HDynamic . toDyn $ (B.decode i :: FTB Showable)
decodeDynamic "showable" i = SDynamic . HDynamic . toDyn $ (B.decode i :: Showable)
decodeDynamic "row_operation" i = SDynamic . HDynamic . toDyn $ ( B.decode i :: RowOperation Text Showable)

parsePrimJSON :: KPrim -> A.Value -> A.Parser Showable
parsePrimJSON i  A.Null = fail ("cant be null" <> show i)
parsePrimJSON i  v =
  (case i of
      PDynamic t -> A.withText (show i) (return .decodeDynamic t . BSL.fromStrict . (fst . B16.decode . BS.drop 1 . BS.dropWhile (=='\\') ) . BS.pack . T.unpack)
      PBinary -> A.withText (show i) (return .SBinary . (fst . B16.decode . BS.drop 1 . BS.dropWhile (=='\\') ) . BS.pack . T.unpack)
      PMime i  -> case i of
                "text/json" -> return .SJSON
                i ->  A.withText (show i) (return .SBinary . (fst . B16.decode . BS.drop 1 . BS.dropWhile (=='\\') )  . BS.pack . T.unpack )
      PInt  _ -> A.withScientific (show i) (return .SNumeric . floor)
      PDouble  -> A.withScientific (show i) (return .SDouble . toRealFloat)
      PDimensional _ _ -> A.withText (show i) (return .SDouble .  read . T.unpack )
      PBoolean -> A.withBool (show i) (return. SBoolean)
      PAddress -> A.withText (show i) (return .SText )
      PColor -> A.withText (show i) (return .SText )
      PText -> A.withText (show i) (return .SText )
      PCnpj -> A.withText (show i) (return .SText )
      PCpf -> A.withText (show i) (return .SText )
      PTime t -> fmap STime <$> case t of
        PInterval ->  A.withText (show i) (either (error "no parse" ) (return . SPInterval )  . parseOnly diffInterval .BS.pack . T.unpack)
        PTimestamp _ ->  A.withText (show i) (\s -> either fail (return .STimestamp )  (parseUTCTime (BS.pack . T.unpack $s)  <|> parseUTCTime (BS.pack . T.unpack $s <> "Z")))
        PDayTime  -> A.withText (show i) (maybe (fail "cant parse daytime") (return .SDayTime . localTimeOfDay) . parseTimeM True defaultTimeLocale "%H:%M:%OS" . T.unpack)
        PDate  -> A.withText (show i) (maybe (fail "cant parse date") (return .SDate . localDay ) . parseTimeM True defaultTimeLocale "%Y-%m-%d" .T.unpack)
      PGeom ix a -> A.withText (show i)  (fmap SGeo . either fail pure .Sel.runGet (parseGeom ix a). fst . B16.decode .BS.pack . T.unpack)

      i -> error ("not defined " <> show i)
  ) v

executeLogged :: (ToRow q ,MonadIO m) => InformationSchema -> KVMetadata Key -> Query -> q -> m ()
executeLogged inf table sqr args = liftIO $ do
  logTable inf table . BS.unpack =<< formatQuery (conn inf) sqr args
  fromIntegral <$> execute (conn inf) sqr args `catch` (\e -> print (e :: SomeException ) >> throw e )
  return ()

queryLogged :: (FromRow o ,ToRow q ,MonadIO m) => InformationSchema -> KVMetadata Key -> Query -> q -> m [o]
queryLogged inf table sqr args = liftIO $ do
  logTable inf table . BS.unpack =<< formatQuery (conn inf) sqr args
  query (conn inf) sqr args `catch` (\e -> print (e :: SomeException ) >> throw e )


-- parseGeom a | traceShow a False = undefined
parseGeom ix a = case a of
          PPosition ->  case ix of
                3 -> fmap SPosition $ (getPosition3d get3DPosition)
                2 -> fmap SPosition $ (getPosition3d get2DPosition )

          PPolygon ->  case ix of
                3 ->  getPolygon get3DPosition
                2 ->  getPolygon get2DPosition
          MultiGeom g ->do
            i <- Sel.getWord8
            if i  == 1
             then do
               typ <- Sel.getWord32host
               srid <- Sel.getWord32host
               let ty = typ .&. complement 0x20000000 .&. complement 0x80000000
               n <- Sel.getWord32host
               case  ty  of
                 6 -> SMultiGeom <$> replicateM (fromIntegral n) (parseGeom ix g)
             else fail "no little endiang"
          PLineString -> case ix of
            3 -> fmap SLineString $ (getLineString get3DPosition)
            2->fmap SLineString $ (getLineString get2DPosition )


tryquoted parser = do
  i <- many (char '"' >> many (char '\\'))
  o <- parser
  C.take (length i)
  return o

parseShowableJSON  fun p@(Primitive l i) v = fix parseKTypePrim l v
  where
    parseKTypePrim f (KSerial :i)  v = LeftTB1 . Just <$> f i v
    parseKTypePrim f (KOptional :i ) v =
      case v of
        A.Null ->  return $ LeftTB1 Nothing
        vn -> (LeftTB1 . Just  <$>  f i vn) <|> return (LeftTB1 Nothing)
    parseKTypePrim  f (KArray :i )  (A.Array l )
      =  maybe (fail $ "parseKTypePrim empty list: "  ++ show l ) (fmap (ArrayTB1 . NonS.fromList) . mapM (f i)) (nonEmpty $ F.toList l)
    parseKTypePrim f (KInterval :l ) (A.String v)
      = do
        env <- ask
        st <- get
        let
          dec = do
            i <- many (satisfy (`L.notElem` (")],\"\\" :: String)))
            if i == ""
               then
                  return Nothing
               else
                  return . Just  . A.parseEither (runCodegenT env st . f l) . maybe (A.String $ T.pack i ) id .  A.decode . BSL.pack $ i
          inter = do
            lb <- (char '[' >> return True) <|> (char '(' >> return False )
            [i,j] <- sepBy1 (tryquoted dec) (char ',')
            rb <- (char ']' >> return True) <|> (char ')' >> return False )
            return $ IntervalTB1 $ Interval.interval (maybe ER.NegInf (either error ER.Finite)  i,lb) ( maybe ER.PosInf (either error ER.Finite)  j,rb)

        case parseOnly inter (BS.pack $ T.unpack v) of
              Right i -> return i
              Left i -> fail i
    parseKTypePrim f [] v = fun i v
    parseKTypePrim f a b = fail $ "no match " ++ show (p,a,b)

parsePrimitiveJSON :: Prim KPrim (Text,Text) -> A.Value -> JSONParser (FTB Showable)
parsePrimitiveJSON (AtomicPrim i) v= lift $ forw . TB1 <$> parsePrimJSON i v
    where (forw,_)  =conversion (Primitive [] (AtomicPrim i))


instance Sel.Serialize a => Sel.Serialize (ER.Extended a ) where
  get = ER.Finite <$> Sel.get
  put (ER.Finite i ) = Sel.put i


get2DPosition = do
      x <- Sel.getFloat64le
      y <- Sel.getFloat64le
      return  $ Position2D  x y 
put2DPosition (Position2D  x y ) = do
      Sel.putFloat64le x
      Sel.putFloat64le y

get3DPosition = do
      x <- Sel.getFloat64le
      y <- Sel.getFloat64le
      z <- Sel.getFloat64le
      return  $ Position  x y z 
put3DPosition (Position  x y z ) = do
      Sel.putFloat64le x
      Sel.putFloat64le y
      Sel.putFloat64le z

getLineStringArray get = do
      n <- Sel.getWord32host
      LineString .Vector.fromList <$> replicateM (fromIntegral n ) get
putLineStringArray (LineString  v ) = do
      mapM_ put3DPosition (F.toList v)


getPoly get = do
      n <- Sel.getWord32host
      (\(i:xs) -> SPolygon i xs)<$> replicateM (fromIntegral n) (getLineStringArray get)

getPolygon get = do
          i <- Sel.getWord8
          if i  == 1
           then do
             typ <- Sel.getWord32host
             -- srid <- Sel.getWord32host
             let ty = typ .&. complement 0x20000000 .&. complement 0x80000000
             case ty  of
               3 -> getPoly get
               i -> error ("no polygon type" <> show i)
           else
             return (error $ "BE not implemented " <> show i )


getLineString get = do
          i <- Sel.getWord8
          if i  == 1
           then do
             typ <- Sel.getWord32host
             srid <- Sel.getWord32host
             let ty = typ .&. complement 0x20000000 .&. complement 0x80000000
             case ty  of
               2 -> getLineStringArray get
               i -> error $ "type not implemented " <> show ty
           else
             return (error $ "BE not implemented " <> show i )


box3dParser = do
          string "BOX3D" <|> string "BOX2D"
          let
            makePoint [x,y,z] = Position  x y z
            makePoint [x,y] = Position2D  x y 
          res  <- char '(' *> sepBy1 (sepBy1 ( scientific) (char ' ') ) (char ',') <* char ')'
          return $ case fmap (fmap  realToFrac) res  of
            [m,s] ->  Bounding ((ER.Finite $ makePoint m ,True) `Interval.interval` (ER.Finite $ makePoint s,True))


instance F.FromField Position where
  fromField f t = case  fmap (Sel.runGet (getPosition3d get3DPosition)) decoded of
    Just i -> case i of
      Right i -> pure i
      Left e -> F.returnError F.ConversionFailed  f e
    Nothing -> error "empty value"
    where
        decoded = fmap (fst . B16.decode) t

getPosition3d get = do
          i <- Sel.getWord8
          if i  == 1
           then do
             typ <- Sel.getWord32host
             srid <- Sel.getWord32host
             let ty = typ .&. complement 0x20000000 .&. complement 0x80000000
             case ty  of
               1 -> get
               i -> error $ "type not implemented " <> show ty
           else
             return (error $ "BE not implemented " <> show i  )


instance F.FromField DiffTime where
  fromField  f mdat = case  mdat of
    Nothing -> F.returnError F.UnexpectedNull f ""
    Just dat -> do
      case parseOnly diffInterval dat of

          Left err -> F.returnError F.ConversionFailed f err
          Right conv -> return conv

diffInterval = (do
  res  <- diffIntervalLayout
  return $ case res  of
    [s] ->  secondsToDiffTime (round s)
    [m,s] ->  secondsToDiffTime (round $  60 * m + s)
    [h,m,s] ->  secondsToDiffTime (round $ h * 3600 + (60 ) * m + s)
    [d,h,m,s] -> secondsToDiffTime (round $ d *3600*24 + h * 3600 + (60  ) * m + s)
    v -> error $ show v)
    where
      diffIntervalLayout = sepBy1 (toRealFloat <$> scientific) (string " days " <|> string " day " <|>  string ":" )


fromShowable k f = case A.parseEither (fmap fst.codegent. parseShowableJSON  parsePrimitiveJSON k) f of
                 Right i -> i
                 Left i -> error (show i)

fromRecordJSON :: InformationSchema -> KVMetadata Key -> KVMeta Key -> NameMap ->  FR.RowParser (TBData Key Showable)
fromRecordJSON inf m foldable namemap = do
  let
    parser f
     = case A.parseEither (\(A.Object i) -> fmap fst $ evalRWST (parseRecordJSON inf m foldable $ justError "no top" $ HM.lookup "p0"  i) [] namemap )  f of
       Right i -> i
       Left i -> error (show i)
  parser <$> FR.field


withCount value = do
  v <- value
  c <- FR.field
  return (v,c)
