{-# LANGUAGE
  UndecidableInstances,FlexibleInstances,FlexibleContexts,TupleSections #-}
module Postgresql.Parser where

import qualified Data.HashMap.Strict as HM
import Data.Map (Map)
import Types hiding (Parser,double)
import Postgresql.Types
import Text
import Postgresql.Printer
import Control.Monad.Trans.Class
import Control.Monad.RWS
import Data.Ord
import qualified Data.Aeson as A
import qualified Data.Aeson.Types as A
import qualified Data.Vector as V
import qualified Data.Foldable as F
import Data.Either
import Utils
import Control.Monad
import qualified NonEmpty as Non
import NonEmpty (NonEmpty (..))
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

type JSONParser = CodegenT A.Parser

mapKeyType :: FKey (KType PGPrim) -> FKey (KType (Prim KPrim (Text,Text)))
mapKeyType  = fmap mapKType

mapKType :: KType PGPrim -> KType CorePrim
mapKType i = fromMaybe (fmap textToPrim i) $ ktypeRec ktypeLift (fmap textToPrim i)

textToPrim :: Prim PGType (Text,Text) -> Prim KPrim (Text,Text)
-- textToPrim i | traceShow i False =undefined
textToPrim (AtomicPrim (s,i,tymod)) = case  HM.lookup i  postgresPrim of
  Just k -> AtomicPrim k -- $ fromMaybe k (M.lookup k (M.fromList postgresLiftPrim ))
  Nothing -> case tymod of
               Just ty -> case HM.lookup i postgresPrimTyp of
                            Just i -> AtomicPrim $ i ty
                            Nothing -> error $ "no conversion for type " <> (show i)
               Nothing -> error $ "no conversion for type " <> (show i)
textToPrim (RecordPrim i) =  (RecordPrim i)


-- Wrap new instances without quotes delimiting primitive values
newtype UnQuoted a = UnQuoted {unQuoted :: a}
newtype DoubleQuoted a = DoubleQuoted {unDoubleQuoted :: a}

    -- toField i = error (show i)

instance TF.ToField (DoubleQuoted Showable ) where
  toField (DoubleQuoted i) =  TF.toField (DoubleQuoted (renderPrim i))

instance TF.ToField (DoubleQuoted (FTB Showable ) ) where
  toField (DoubleQuoted i) =  TF.toField (DoubleQuoted (renderShowable i))

instance TF.ToField (DoubleQuoted String) where
  toField (DoubleQuoted i) = TF.Many [TF.Plain "\"", TF.Plain (fromByteString $ BS.pack i) , TF.Plain "\""]

instance (Show a,TF.ToField a , TF.ToField (UnQuoted a)) => TF.ToField (FTB (Text,a)) where
  toField (LeftTB1 i) = maybe (TF.Plain (fromByteString "null")) TF.toField  i
  toField (LeftTB1 i) = maybe (TF.Plain (fromByteString "null")) TF.toField  i
  toField (ArrayTB1 is ) = TF.toField $ PGTypes.PGArray   (F.toList is)
  toField (IntervalTB1 is )
    | ty == Just "time" = TF.Many [TF.toField  tyv , TF.Plain $ fromByteString " :: " , TF.Plain $ fromByteString (BS.pack $maybe "" T.unpack $ ty), TF.Plain $ fromByteString "range"]
    | ty == Just "POINT3" = TF.Many [TF.Plain "box3d(", TF.toField  (unFinite $ Interval.lowerBound is ), TF.Plain ",",TF.toField (unFinite $ Interval.upperBound is) ,TF.Plain ")"]
    | ty == Just "LINESTRING3" = TF.Many [TF.Plain "point3range(", TF.toField  (unFinite $ Interval.lowerBound is ), TF.Plain ",",TF.toField (unFinite $ Interval.upperBound is) ,TF.Plain ")"]
    | otherwise  = TF.toField  tyv
    where tyv = fmap (\(TB1 i ) -> snd i) is
          ty = unFinite $  Interval.lowerBound $ fmap (\(TB1 i ) -> fst i) is
  toField (TB1 (t,i)) = TF.toField i
  -- toField i = error (show i)

instance (TF.ToField a , TF.ToField b ) => TF.ToField (Either a b ) where
  toField (Right i) = TF.toField i
  toField (Left i) = TF.toField i

instance TF.ToField (KType (Prim KPrim (Text,Text)),FTB Showable) where
  toField (k ,i) = case   liftA2 (,) (ktypeRec ktypeUnLift  k ) (topconversion preunconversion k) of
                     Just (k,(_,b)) -> toFielPrim k (b i)
                     Nothing -> toFielPrim k i
    where
      toFielPrim (Primitive l n) = toFiel l
        where
          toFiel (KOptional : k ) (LeftTB1 i) = maybe (TF.Plain "null") (toFiel  k) i
          toFiel (KSerial : k ) (LeftTB1 i) = maybe (TF.Plain "null") (toFiel  k) i
          toFiel (KDelayed : k ) (LeftTB1 i) = maybe (TF.Plain "null") (toFiel k) i
          toFiel (KArray : k ) (ArrayTB1 is ) = TF.Many $[TF.toField $ PGTypes.PGArray   (F.toList $ fmap unTB1 is)  ] ++ maybeToList ( TF.Plain .fromByteString . BS.pack . T.unpack . (" :: "<>) <$> ( renderType (Primitive (KArray :k) n )))
          toFiel (KInterval : k) (IntervalTB1 is ) = TF.Many [TF.Plain ( fromByteString $ BS.pack $ T.unpack $justError ("no array" <> show k) $ renderType (Primitive  (KInterval: k) n ) ) ,TF.Plain "(" ,TF.toField  (fmap unTB1 $ unFinite $ Interval.lowerBound is ), TF.Plain ",",TF.toField (fmap unTB1 $ unFinite $ Interval.upperBound is) ,TF.Plain ")"]
            -- | k == Just "time" = TF.Many [TF.toField  tyv , TF.Plain $ fromByteString " :: " , TF.Plain $ fromByteString (BS.pack $maybe "" T.unpack $ ty), TF.Plain $ fromByteString "range"]
            -- | k == Just "POINT3" = TF.Many [TF.Plain "point3range(", TF.toField  (unFinite $ Interval.lowerBound is ), TF.Plain ",",TF.toField (unFinite $ Interval.upperBound is) ,TF.Plain ")"]
            -- | ty == Just "LINESTRING3" = TF.Many [TF.Plain "point3range(", TF.toField  (unFinite $ Interval.lowerBound is ), TF.Plain ",",TF.toField (unFinite $ Interval.upperBound is) ,TF.Plain ")"]
            -- | otherwise  = TF.toField  tyv
          toFiel [] (TB1 i) = TF.Many [TF.toField i ,TF.Plain $ fromByteString $maybe ""  (" :: "<>) (BS.pack . T.unpack <$> renderType (Primitive [] n))]
          toFiel i j = error ("toFiel" ++ show (i,j))



instance  TF.ToField (TB Key Showable)  where
  toField (Attr k  i) = TF.toField (keyType k ,i)
  toField (IT n (LeftTB1 i)) = maybe (TF.Plain ( fromByteString "null")) (TF.toField . IT n ) i
  toField (IT n (TB1 (m,i))) = TF.toField (TBRecord2  (kvMetaFullName  m ) (L.sortBy (comparing (fmap (keyPosition ._relOrigin). keyattri ) ) $ maybe id (flip mappend) attrs $ (F.toList (_kvvalues $ i) )  ))
      where attrs = Tra.traverse (\i -> Attr i <$> showableDef (keyType i) ) $  F.toList $ (S.fromList $ _kvattrs  m ) `S.difference` (S.map _relOrigin $ S.unions $ M.keys (_kvvalues $ i))
  toField (IT (n)  (ArrayTB1 is )) = TF.toField $ PGTypes.PGArray $ F.toList $ (TF.toField . IT n) <$> is
  toField e = error (show e)



instance  TF.ToField (TB PGKey Showable)  where
  toField (Attr k  i) = case  topconversion preconversion (textToPrim <$> keyType k) of
          Just (_,b) -> TF.toField (fmap ( (\(AtomicPrim (_,i,_) ) -> i)$head $ F.toList $ keyType k,) $ b i)
          Nothing -> TF.toField (fmap ((\(AtomicPrim (_,i,_) ) -> i) $ head $ F.toList $ keyType k,) i)
  toField (IT n (LeftTB1 i)) = maybe (TF.Plain ( fromByteString "null")) (TF.toField . IT n ) i
  toField (IT n (TB1 (m,i))) = TF.toField (TBRecord2  (kvMetaFullName  m ) (L.sortBy (comparing (fmap (keyPosition ._relOrigin). keyattri ) ) $ maybe id (flip mappend) attrs $ (F.toList (_kvvalues $ i) )  ))
      where attrs = Tra.traverse (\i -> Attr i <$> showableDef (keyType i) ) $  F.toList $ (S.fromList $ _kvattrs  m ) `S.difference` (S.map _relOrigin $ S.unions $ M.keys (_kvvalues $ i))
  toField (IT n  (ArrayTB1 is)) = TF.toField $ PGTypes.PGArray $ F.toList $ (TF.toField . IT n) <$> is
  toField e = error (show e)



instance TR.ToRow a => TF.ToField (TBRecord2 a) where
  toField (TBRecord2 s l) =  TF.Many   (TF.Plain (fromByteString "ROW(") : L.intercalate [TF.Plain $ fromChar ','] (fmap pure. TR.toRow  $ l) <> [TF.Plain (fromByteString $ ") :: " <>  BS.pack (T.unpack s) )] )


data TBRecord2 a = TBRecord2 Text a

instance TF.ToField (UnQuoted Showable) where
  toField (UnQuoted (SDouble i )) =  TF.toField i
  toField (UnQuoted (SNumeric i )) =  TF.toField i
  toField (UnQuoted (SGeo (SPosition i ))) =  TF.toField i
  toField (UnQuoted (STime t)) = case t of
        STimestamp i ->  TF.Plain $ localTimestampToBuilder (Finite i)
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
          point (ER.Finite (Position (lat,lon,alt))) = TF.Many [str "ST_setsrid(ST_MakePoint(", TF.toField lat , del , TF.toField lon , del, TF.toField alt , str "),4326)"]
          point (ER.Finite (Position2D (lat,lon))) = TF.Many [str "ST_setsrid(ST_MakePoint(", TF.toField lat , del , TF.toField lon ,  str "),4326)"]


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
          point (Position (lat,lon,alt)) = [str "ST_MakePoint(", TF.toField lat , del , TF.toField lon , del, TF.toField alt , str ")"]
          point (Position2D (lat,lon)) = [str "ST_setsrid(ST_MakePoint(", TF.toField lat , del , TF.toField lon ,  str "),4326)"]


instance TF.ToField (UnQuoted Position) where
  toField (UnQuoted (Position (lat,lon,alt))) = TF.Many [str "ST_setsrid(st_makePoint(", TF.toField lat , del , TF.toField lon , del, TF.toField alt , str "),4326)"]
    where del = TF.Plain $ fromChar ','
          str = TF.Plain . fromByteString
  toField (UnQuoted (Position2D (lat,lon))) = TF.Many [str "ST_setsrid(st_makePoint(", TF.toField lat , del , TF.toField lon , del,  str "),4326)"]
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

instance TF.ToField Showable where
  toField (SText t) = TF.toField t
  toField (SNumeric t) = TF.toField t
  toField (SBoolean t) = TF.toField t
  toField (SDouble t) = TF.toField t
  toField (STime ti) = case ti of
                        SDate  t -> TF.toField t
                        (SDayTime t) -> TF.toField t
                        (STimestamp t) -> TF.toField t
  toField (SGeo i ) = TF.toField i
  toField (SBinary t) = TF.toField (Binary t)
  toField (SDynamic t) = TF.toField (Binary (B.encode t))


defaultType t =
  case _keyFunc t of
      KOptional : i -> Just (LeftTB1 Nothing)
      i -> Nothing


unIntercalateAtto :: (Show a1,Alternative f )=> [f a1] -> f a -> f [a1]
unIntercalateAtto l s = go l
  where
    go [e] =  fmap pure  e
    go (e:cs) =  liftA2 (:) e  (s *> go cs)
    go [] = error  "unIntercalateAtto empty list"

-- parseAttrJSON i v | traceShow (i,v) False = undefined
parseAttrJSON (Attr i _ ) v = do
  let tyun = fromMaybe (keyType i) $ ktypeRec ktypeUnLift (keyType i)
  s<- lift $ parseShowableJSON   tyun  v
  return $  Attr i s
parseAttrJSON (Fun i rel _ )v = do
  s<- lift $ parseShowableJSON (keyType  i) v
  return $  (Fun i rel s)
parseAttrJSON (IT na j) v = do
  mj <- parseLabeledTableJSON j v
  return $ IT  na mj
parseAttrJSON i v = error (show (i,v))

-- Note Because the list has a mempty operation when parsing
-- we have overlap between maybe and list so we allow only nonempty lists

parseLabeledTableJSON (ArrayTB1 (l :| _)) (A.Array a)=
  ArrayTB1 <$> traverse (parseLabeledTableJSON l ) (Non.fromList . F.toList $a)
-- parseLabeledTableJSON (ArrayTB1 (l :| _)) (A.Null) = fail "no array"
parseLabeledTableJSON (LeftTB1 (Just l)) A.Null = return $ LeftTB1 Nothing
parseLabeledTableJSON (LeftTB1 (Just l)) v = fmap LeftTB1 $ fmap Just (parseLabeledTableJSON l v) <|> return (Nothing)
parseLabeledTableJSON (TB1 l) v = fmap TB1 $ parseRecordJSON  l v
parseLabeledTableJSON i v= error (show (i,v))


parseRecordJSON :: TBData Key () -> A.Value -> JSONParser (TBData Key Showable)
parseRecordJSON  (me,m) (A.Object v) = atTable me $ do
  let try1 i v = do
        tb <- lkTB i
        return $ justError (" no attr " <> show (i,v)) $ HM.lookup tb  v

  im <- traverse ((\ i -> parseAttrJSON  i =<<  try1 i v))$   _kvvalues m
  return (me, KV im )


parsePrimJSON :: KPrim -> A.Value -> A.Parser Showable
parsePrimJSON i  A.Null = fail ("cant be null" <> show i)
parsePrimJSON i  v =
  (case i of
      PDynamic  -> A.withText (show i) (return .SDynamic . B.decode . BSL.fromStrict . (fst . B16.decode . BS.drop 1 . BS.dropWhile (=='\\') ).  BS.pack . T.unpack)
      PBinary -> A.withText (show i) (return .SBinary . (fst . B16.decode . BS.drop 1 . BS.dropWhile (=='\\') ) . BS.pack . T.unpack)
      PMime _ -> A.withText (show i) (return .SBinary . (fst . B16.decode . BS.drop 1 . BS.dropWhile (=='\\') )  . BS.pack . T.unpack )
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
        PTimestamp _ -> (\v -> A.withText (show i) (\s -> maybe (fail ("cant parse timestamp: " <> show (i,v))) (return .STimestamp  . fst)  (strptime "%Y-%m-%dT%H:%M:%OS"   s <|> strptime "%Y-%m-%d %H:%M:%OS" s )) v )
        PDayTime  -> A.withText (show i) (maybe (fail "cant parse daytime") (return .SDayTime . localTimeOfDay . fst) . strptime "%H:%M:%OS")
        PDate  -> A.withText (show i) (maybe (fail "cant parse date") (return .SDate . localDay . fst) . strptime "%Y-%m-%d")
      PGeom ix a -> A.withText (show i)  (fmap SGeo . either fail pure .Sel.runGet (parseGeom ix a). fst . B16.decode .BS.pack . T.unpack)

      i -> error ("not defined " <> show i)
  ) v

-- parseGeom a | traceShow a False = undefined
parseGeom ix a = case a of
          PPosition ->  case ix of
                3 -> fmap SPosition $(getPosition3d get3DPosition)
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



parseShowableJSON  p@(Primitive l (AtomicPrim i)) v = parseKTypePrim l v
  where
    parseKTypePrim (KDelayed :i) (A.Bool b)
      = if b then return (LeftTB1 Nothing)  else fail "no error"
    parseKTypePrim (KSerial :i)  v = LeftTB1 . Just <$> parseKTypePrim i v
    parseKTypePrim (KOptional :i ) v =
      case v of
        A.Null ->  return $ LeftTB1 Nothing
        vn -> LeftTB1 . Just  <$>  parseKTypePrim i vn
    parseKTypePrim  (KArray :i )  (A.Array l )
      =  maybe (fail "parseKTypePrim empty list" ) (fmap (ArrayTB1 . Non.fromList) . mapM (parseKTypePrim i)) (nonEmpty $ F.toList l)

    parseKTypePrim (KInterval :l ) (A.String v)
      = case parseOnly inter (BS.pack $ T.unpack v) of
            Right i -> return i
            Left i -> fail i
      where
        dec  =  maybe (Left "can't decode interval number " ) (A.parseEither (parseKTypePrim l)) . A.decode . BSL.fromStrict
        inter = do
            lb <- (char '[' >> return True ) <|> (char '(' >> return False )
            i <- dec <$> takeWhile (/=',')
            char ','
            j <- dec <$> takeWhile (\i -> i /=']' && i /= ')' )
            rb <- (char ']' >> return True) <|> (char ')' >> return False )
            return $ IntervalTB1 $ Interval.interval (either (const ER.NegInf) ER.Finite i,lb) (either (const ER.PosInf ) ER.Finite j,rb)

    parseKTypePrim [] v = forw . TB1 <$> ( parsePrimJSON i v)
        where (forw,_)  =conversion (Primitive [] (AtomicPrim i))
    parseKTypePrim a b = error $ "no match " ++ show (p,a,b)


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


get2DPosition = do
      x <- Sel.getFloat64le
      y <- Sel.getFloat64le
      return  $ Position2D (x,y)
put2DPosition (Position2D (x,y)) = do
      Sel.putFloat64le x
      Sel.putFloat64le y



get3DPosition = do
      x <- Sel.getFloat64le
      y <- Sel.getFloat64le
      z <- Sel.getFloat64le
      return  $ Position (x,y,z)
put3DPosition (Position (x,y,z)) = do
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
            makePoint [x,y,z] = Position (x,y,z)
            makePoint [x,y] = Position2D (x,y)
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

safeMaybe e f i = maybe (error (e  <> ", input = " <> show i )) id (f i)

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





instance F.FromField a => F.FromField (Only a) where
  fromField = fmap (fmap (fmap Only)) F.fromField

fromShowable k f = case A.parseEither (parseShowableJSON  k) f of
                 Right i -> i
                 Left i -> error (show i)

fromRecordJSON :: TBData Key () -> NameMap ->  FR.RowParser (TBData Key Showable)
fromRecordJSON foldable namemap = do
  let parser   f = case A.parseEither (\(A.Object i) -> fmap fst $ evalRWST (parseRecordJSON foldable $ justError "no top" $ HM.lookup "p0"  i) [] namemap )  f of
                  Right i -> i
                  Left i -> error (show i)
  parser <$> FR.field



withCount value = do
  v <- value
  c <- FR.field
  return (v,c)
