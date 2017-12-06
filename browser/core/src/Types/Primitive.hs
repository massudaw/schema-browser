{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}

module Types.Primitive  where

import Types.Common
import Data.Ord
import Text.Show.Deriving
import Data.Vector (Vector)
import Data.Functor.Classes
import Data.Dynamic
import Control.DeepSeq
import qualified NonEmpty as Non

import NonEmpty (NonEmpty(..))
import Control.Lens.TH
import qualified Control.Lens as Le
import Data.Functor.Apply
import Utils
import Data.Bifunctor
import Safe
import Prelude hiding(head)
import Data.Maybe
import GHC.Generics
import Data.Binary (Binary)
import Data.Vector.Binary
import qualified Data.Binary as B
import Data.Text.Binary
import System.IO.Unsafe
import Data.Functor.Identity
import Data.Typeable
import Data.Vector(Vector)
import Data.Functor.Classes
import Data.Foldable (Foldable)
import qualified Data.Foldable as F
import qualified Data.Interval as Interval
import Data.Interval (Extended,Interval(..))
import qualified Data.ExtendedReal as ER
import Data.Monoid hiding (Product)
import qualified Data.Text as T
import qualified Data.ByteString as BS
import GHC.Stack
import Data.Traversable(Traversable,traverse)
import Data.Time
import Data.Time.Clock.POSIX
import Control.Monad
import GHC.Exts
import Control.Applicative
import qualified Data.List as L
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Set as  S
import Control.Monad.State
import Data.Text (Text)

import Debug.Trace
import Data.Unique


makeLenses ''KV
makeLenses ''TB

data KTypePrim
  = KSerial
  | KArray
  | KInterval
  | KOptional
  | KDelayed
  deriving(Eq,Ord,Show,Generic)

data KType a
  = Primitive { _keyFunc :: [KTypePrim]
              , _keyAtom :: a}
  deriving(Eq,Ord,Functor,Generic,Foldable,Show)

makeLenses ''KType

isSerial (Primitive (KSerial: _) _) = True
isSerial _ = False

isPrim (Primitive [] i) = True
isPrim i = False

isOptional (Primitive (KOptional:_) _) = True
isOptional _ = False


isArray :: KType i -> Bool
isArray (Primitive (KOptional:KArray :_) _) = True
isArray (Primitive (KArray :_) _) = True
isArray _ = False

newtype TBIndex  a
  = Idex [FTB a]
  deriving(Eq,Show,Ord,Functor,Generic)


type CorePrim = Prim KPrim (Text,Text)
type CoreKey = FKey (KType CorePrim)


showableDef (Primitive (KOptional:xs) i) = Just $ LeftTB1 (showableDef (Primitive xs i))
showableDef (Primitive (KSerial:xs) i) = Just $ LeftTB1 (showableDef (Primitive xs i))
showableDef (Primitive (KArray:xs) i) = Nothing -- Just (SComposite Vector.empty)
showableDef i = Nothing

isFunction :: SqlOperationK k -> Bool
isFunction (FunctionField _ _ _) = True
isFunction i = False

isRecRel (RecJoin _ _ ) =  True
isRecRel i = False

pathRelOri :: Ord k => SqlOperationK k -> Set k
pathRelOri = S.map _relOrigin . pathRelRel

pathRelRel :: Ord k => SqlOperationK k -> Set (Rel k)
pathRelRel (FKJoinTable  rel   _  ) = Set.fromList rel
pathRelRel (FKInlineTable  r _  ) = Set.singleton $ Inline r
pathRelRel (RecJoin l rel ) =  pathRelRel rel
pathRelRel (FunctionField r _ a ) =  S.singleton $ RelFun r (relAccesGen <$> a)


pathRelRel' :: Ord k => SqlOperationK k -> MutRec [Set (Rel k )]
pathRelRel' (RecJoin l rel )
  | L.null (unMutRec l) =  MutRec [[pathRelRel rel ]]
  | otherwise = fmap ((pathRelRel rel  :) . fmap (Set.fromList)) l


type Column k a = TB k a
type TBData k a = (KVMetadata k,KV k a )
type TB3Data   k a = (KVMetadata k,KV k a )


type Key = CoreKey

data FKey a
    = Key
    { keyValue :: Text
    , keyTranslation ::  (Maybe Text)
    , keyModifier :: [FieldModifier]
    , keyPosition :: Int
    , keyStatic :: Maybe (FTB Showable)
    , keyFastUnique ::  KeyUnique
    , _keyTypes ::  a
    }deriving(Functor,Generic)

type KeyUnique = Unique

instance NFData a => NFData (FKey a)

keyType = _keyTypes

instance Binary KTypePrim
instance Binary a => Binary (KType a)
instance Binary Position
instance NFData Position
instance Binary Bounding
instance NFData Bounding
instance Binary LineString
instance NFData LineString
instance Binary Showable
instance NFData Showable
instance Binary SGeo
instance NFData SGeo
instance Binary STime
instance NFData STime

data GeomType
  = MultiGeom GeomType
  | PPolygon
  | PLineString
  | PPosition
  | PBounding
  deriving(Eq,Show,Ord,Generic)

data TimeType
  =  PTimestamp (Maybe TimeZone)
  |  PDate
  |  PDayTime
  |  PInterval
  deriving(Show,Eq,Ord,Generic)

data KPrim
   = PText
   | PBoolean
   | PAddress
   | PInt Int
   | PDouble
   | PDimensional Int (Int,Int,Int,Int,Int,Int,Int)
   | PGeom Int GeomType
   | PTime TimeType
   | PMime Text
   | PCnpj
   | PCpf
   | PBinary
   | PColor
   | PDynamic
   | PAny
   | PTypeable TypeRep
   deriving(Show,Eq,Ord,Generic)

instance NFData KPrim
instance NFData GeomType
instance NFData TimeType

data Prim a b
  = AtomicPrim a
  | RecordPrim b
  deriving(Eq,Ord,Show,Generic)

instance (NFData a , NFData b) => NFData (Prim a b)

instance NFData KTypePrim
instance NFData a => NFData (KType a)

showTy f (Primitive l i ) = f i ++ showT l
  where
  showT  (KArray :i) = "{" <>  showT  i <> "}"
  showT  (KOptional :i) = showT  i <> "*"
  showT  (KInterval: i) = "(" <>  showT  i <> ")"
  showT  (KSerial: i) = showT  i <> "?"
  showT  (KDelayed :i) = showT  i <> "-"


instance Eq (FKey a) where
   k == l = keyFastUnique k == keyFastUnique l

instance Ord (FKey a) where
   compare i j = compare (keyFastUnique i) (keyFastUnique j)

instance Show a => Show (FKey a)where
  -- show = T.unpack . showKey
  show k = (T.unpack $ maybe (keyValue k) id (keyTranslation  k))

showKey k  =   maybe (keyValue k)  (\t -> keyValue k <> "-" <> t ) (keyTranslation k) <> "::" <> T.pack ( show $ hashUnique $ keyFastUnique k )<> "::" <> T.pack (show $ keyStatic k) <>  "::" <> T.pack (show (keyType k) <> "::" <> show (keyModifier k) <> "::" <> show (keyPosition k )  )

data Position
    = Position (Double,Double,Double)
    | Position2D (Double,Double)
    deriving(Eq,Typeable,Show,Read,Generic)

instance Ord Position where
  (Position (x,y,z) ) <= (Position (a,b,c)) =  x <= a && y <= b && z <= c
  (Position2D (x,y) ) <= (Position2D (a,b)) =  x <= a && y <= b
  (Position (x,y,z) ) >= (Position (a,b,c)) =  x >= a && y >= b && z >= c
  (Position2D (x,y) ) >= (Position2D (a,b)) =  x >= a && y >= b


newtype Bounding = Bounding (Interval.Interval Position) deriving(Eq,Ord,Typeable,Show,Generic)

newtype LineString = LineString (Vector Position) deriving(Eq,Ord,Typeable,Show,Read,Generic)

--- Geo Data Runtime Representations
data SGeo
  = SPosition !Position
  | SLineString !LineString
  | SPolygon !LineString ![LineString]
  | SMultiGeom ![SGeo]
  | SBounding !Bounding
  deriving(Ord,Eq,Show,Generic)

--- Time Data Runtime Representations
data STime
  = STimestamp ! UTCTime
  | SDate ! Day
  | SDayTime ! TimeOfDay
  | SPInterval ! DiffTime
  deriving(Ord,Eq,Show,Generic)


newtype HDynamic = HDynamic Dynamic

instance Eq HDynamic where
  i == j = True
instance Ord HDynamic where
  compare i j = EQ

instance NFData HDynamic where
  rnf (HDynamic i) =  ()

instance Binary HDynamic where
  put (HDynamic i) = return ()
  get = undefined

instance Show HDynamic where
  show i = "HDynamic"


data Showable
  = SText  Text
  | SNumeric  Int
  | SBoolean  Bool
  | SDouble Double
  | SGeo  SGeo
  | STime STime
  | SBinary BS.ByteString
  | SDynamic (FTB Showable)
  | SHDynamic  HDynamic
  deriving(Ord,Eq,Show,Generic)



type SqlOperation = SqlOperationK Key
data SqlOperationK k
  = FKJoinTable [Rel k] (Text,Text)
  | RecJoin (MutRec [[Rel k ]])  (SqlOperationK k)
  | FKInlineTable k (Text,Text)
  | FunctionField k Expr [Access k]
  deriving(Eq,Ord,Show,Functor)

fkTargetTable (FKJoinTable  r tn) = snd tn
fkTargetTable (FKInlineTable _ tn ) = snd tn
fkTargetTable (RecJoin t tn) = fkTargetTable tn

data FieldModifier
   = FRead
   | FWrite
   | FPatch
   deriving(Eq,Ord,Show,Generic)

instance NFData FieldModifier

data TableType
   = ReadOnly
   | WriteOnly
   | ReadWrite
   deriving(Eq,Ord,Show)

type Table = TableK Key


mapTableK f (Raw  uni s tt tr de is rn  un idx rsc rp rd rf rat ) = Raw uni s tt tr (S.map f de) is rn (fmap (fmap f) un) (fmap (fmap f) idx) (map f rsc ) (map f rp) (fmap f rd) (S.map (mapPath f )  rf ) (S.map f rat)
  where mapPath f j  = (fmap f j)
mapTableK f (Project t tr) = Project (mapTableK f t) (mapTransform f tr)

mapTransform f (Union l ) = Union (fmap (mapTableK f) l)

instance Show Unique where
    show i = show (hashUnique i)
instance Eq (TableK k) where
  i == j = tableUnique i == tableUnique j
instance Ord (TableK k) where
  compare i j = compare (tableUnique i) (tableUnique j)

rawIsSum (Project i  _ ) = __rawIsSum i
rawIsSum i = __rawIsSum i


data TableK k
  =  Raw   { tableUniqueR :: Int
           ,_rawSchemaL :: Text
           , rawTableType :: TableType
           , rawTranslation :: Maybe Text
           , rawDelayed :: (Set k)
           , __rawIsSum :: Bool
           , _rawNameL :: Text
           , uniqueConstraint :: [[k]]
           , _rawIndexes ::  [[k]]
           , _rawScope :: [k]
           , _rawPKL :: [k]
           , _rawDescriptionL :: [k]
           , _rawFKSL ::  (Set (SqlOperationK k ))
           , _rawAttrsR :: (Set k)
           }
     | Project  (TableK k)  (TableTransform  k)
     deriving(Show)


data TableTransform  k
  = Union [TableK k]
  | From (TableK k)
  | Join (TableTransform k) (TableK k)  [Rel k]
  | Filter (TableTransform k) (BoolCollection (Access k,AccessOp Showable))
  deriving(Show)


unRecRel (RecJoin _ l) = l
unRecRel l = l

data BoolCollection a
 = AndColl [BoolCollection a]
 | OrColl [BoolCollection a]
 | PrimColl a
 deriving(Show,Eq,Ord,Functor,Foldable,Generic)

instance NFData a => NFData (BoolCollection a)
instance Binary a => Binary (BoolCollection a)


tableUnique (Project i _ ) = tableUniqueR i
tableUnique i =  tableUniqueR i
rawFKS (Project i _ ) =  _rawFKSL i
rawFKS i =  _rawFKSL i
rawUnion (Project i (Union l)) = l
rawUnion _= []
rawPK  (Project i _ ) = _rawPKL i
rawPK  i  = _rawPKL i
rawDescription (Project i _ ) = _rawDescriptionL i
rawDescription  i  = _rawDescriptionL i
rawName (Project i _) = _rawNameL i
rawName i  = _rawNameL i
rawSchema (Project i _) = _rawSchemaL i
rawSchema i  = _rawSchemaL i
rawAttrs (Project i _ ) = _rawAttrsR i
rawAttrs i = _rawAttrsR i
tableName = rawName
translatedName tb =  maybe (rawName tb) id (rawTranslation tb )


type TableModification p = TableModificationK Table p
data TableModificationK k p
  = TableModification
  { tableId :: Maybe Int
  , tableTime :: UTCTime
  , tableUser :: Text
  , tableObj :: k
  , tableDiff ::  p
  }
  deriving(Eq,Show,Functor,Generic)


type QueryRef = State ((Int,Map Int Table ),(Int,Map Int Key))

-- Literals Instances
instance IsString Showable where
    fromString i = SText (T.pack i)


instance Enum Showable where
    toEnum = SNumeric . toEnum
    fromEnum (SNumeric i ) = fromEnum i


instance Real Showable where
  toRational (SNumeric i )=  toRational i
  toRational (SDouble i )=  toRational i

instance RealFrac Showable where
  properFraction (SDouble i) = second SDouble $ properFraction i --toRational (SDouble i )=  toRational i
  properFraction (SNumeric j ) = (fromIntegral j,SNumeric 0)


instance Integral Showable where
  toInteger (SNumeric i) = toInteger i
  quotRem (SNumeric i ) (SNumeric j ) = (\(l,m) -> (SNumeric l , SNumeric m)) $ quotRem i j


instance Num Showable where
    SNumeric i +  SNumeric j = SNumeric (i + j)
    SDouble i +  SDouble j = SDouble (i + j)
    SDouble i + SNumeric j = SDouble $ i +  fromIntegral j
    SNumeric j  + SDouble i = SDouble $ i +  fromIntegral j
    v + k = errorWithStackTrace (show (v,k))
    STime(STimestamp i) - STime(STimestamp j) =  STime $ SPInterval $ realToFrac $ diffUTCTime i j
    SNumeric i -  SNumeric j = SNumeric (i - j)
    SDouble i -  SDouble j = SDouble (i - j)
    SDouble i - SNumeric j = SDouble $ i -  fromIntegral j
    SNumeric j  - SDouble i = SDouble $ i -  fromIntegral j
    v - k = errorWithStackTrace (show (v,k))
    SNumeric i *  SNumeric j = SNumeric (i * j)
    SNumeric i *  SDouble j = SDouble (fromIntegral i * j)
    SDouble i *  SNumeric j = SDouble (i * fromIntegral j)
    SDouble i *  SDouble j = SDouble (i * j)
    SDouble i *  (STime (SPInterval j)) = SDouble (i * realToFrac j)
    (STime (SPInterval i ))*  SDouble j = SDouble (j * realToFrac i)
    STime(SPInterval i) *  STime (SPInterval j) = STime $ SPInterval (i * j)
    i * j = errorWithStackTrace (show (i,j))
    fromInteger i = SDouble $ fromIntegral i
    negate (SNumeric i) = SNumeric $ negate i
    negate (SDouble i) = SDouble $ negate i
    negate i = errorWithStackTrace (show i)
    abs (SNumeric i) = SNumeric $ abs i
    abs (SDouble i) = SDouble $ abs i
    signum (SNumeric i) = SNumeric $ signum i
    signum (SDouble i) = SDouble $ signum i

instance Fractional Showable where
  fromRational i = SDouble (fromRational i)
  recip (SDouble i) = SDouble (recip i)
  recip (STime (SPInterval i)) = STime $ SPInterval (recip i)
  recip (SNumeric i) = SDouble (recip $ fromIntegral i)
  recip i = errorWithStackTrace (show i)

-- type HashQuery =  HashSchema (Set Key) (SqlOperation Table)
type PathQuery = SqlOperation




tableAttr (m , KV n) =   concat  $ F.toList (nonRef <$> n)
  where
    nonRef i@(Fun _ _ _ ) =[i]
    nonRef i@(Attr _ _ ) =[i]
    nonRef (FKT i  _ _ ) = concat (nonRef <$> unkvlist i)
    nonRef j@(IT k v ) = [j]

-- nonRef i = errorWithStackTrace (show i)

-- joinNonRef :: Ord k => TB2 k a -> TB2 k a
-- joinNonRef = fmap joinNonRef'

-- joinNonRef' :: Ord k => TB3Data f k a -> TB3Data f k a

tableNonRef2 :: Ord k => TBData k a -> TBData  k a
tableNonRef2 (m,n)  = (m, (KV . rebuildTable . _kvvalues) n)
  where
    rebuildTable n =    Map.unions (nonRef <$> F.toList n)
    nonRef :: Ord k => Column k a -> Map (Set (Rel k )) (TB  k a)
    nonRef ((Fun i _ _ )) =Map.empty
    nonRef ((FKT i _ _ )) = _kvvalues i
    nonRef ((IT j k )) = Map.singleton (S.singleton $ Inline j) (IT  j (tableNonRef2 <$> k ))
    nonRef i@((Attr j _)) = Map.singleton (S.singleton $ Inline j) (i)




nonRefTB :: Ord k => TB k a -> [(TB ) k a]
nonRefTB (FKT i _ _ ) = concat (nonRefTB <$> unkvlist i)
nonRefTB (IT j k ) = [IT  j (tableNonRef k ) ]
nonRefTB i  = [i]


addDefault
  :: TB  d a
     -> TB  d b
addDefault = def
  where
    def ((Attr k i)) = (Attr k (LeftTB1 Nothing))
    def ((Fun k i _)) = (Fun k i (LeftTB1 Nothing))
    def ((IT  rel j )) = (IT  rel (LeftTB1 Nothing)  )
    def ((FKT at rel j )) = (FKT (KV $ addDefault <$> _kvvalues at) rel (LeftTB1 Nothing)  )




tableMeta :: Ord k => TableK k -> KVMetadata k
tableMeta (Project s _ ) =  tableMeta s
tableMeta t = KVMetadata (rawName t) (rawSchema t) (_rawScope t) (rawPK t) (rawDescription t) (fmap F.toList $ uniqueConstraint t) [] (F.toList $ rawAttrs t)[]  (F.toList $ rawDelayed t) (paths' <> paths)
  where
    rec = filter isRecRel  (Set.toList $ rawFKS t)
    same = filter ((tableName t ==). fkTargetTable ) rec
    notsame = filter (not . (tableName t ==). fkTargetTable  ) rec
    paths = fmap (fmap (fmap F.toList). pathRelRel' ) notsame
    paths' = (\i -> if L.null i then [] else [MutRec i]) $ fmap ((head .unMutRec). fmap (fmap F.toList). pathRelRel' ) same

tblist' :: Ord k => TableK k -> [TB  k a] -> TBData k a
tblist' t  = tblistM (tableMeta t)


isInline (Primitive _ (RecordPrim _ ) ) = True
isInline _ = False


-- Intersections and relations

makeLenses ''Rel
makeLenses ''FKey
makeLenses ''TableK

--
--- Attr Cons/Uncons
--
unIndexItens :: (Show (KType k),Show a) =>  Int -> Int -> TB (FKey (KType k))  a  -> (Maybe (TB (FKey (KType k))  a ))
unIndexItens ix o =  unIndex (ix+ o)

unIndex :: (Show (KType k),Show a) => Int -> TB (FKey (KType k)) a -> Maybe (TB (FKey (KType k)) a )
unIndex o (Attr k (ArrayTB1 v)) = Attr (unKArray k) <$> Non.atMay v o
unIndex o (IT na (ArrayTB1 j))
  =  IT  na <$>  Non.atMay j o
unIndex o (FKT els rel (ArrayTB1 m)  ) = (\li mi ->  FKT  (kvlist $ nonl <> fmap ((firstTB unKArray) )li) (Le.over relOri (\i -> if isArray (keyType i) then unKArray i else i ) <$> rel) mi ) <$> (maybe (Just []) (Just .pure ) (join ((traFAttr (indexArray o))  <$> l))) <*> (Non.atMay m o)
  where
    l = L.find (all (isArray.keyType) . fmap _relOrigin . keyattr)  (unkvlist els)
    nonl = L.filter (not .all (isArray.keyType) . fmap _relOrigin . keyattr) (unkvlist els)
    indexArray ix s =  Non.atMay (unArray s) ix
unIndex o i = errorWithStackTrace (show (o,i))

unLeftKey :: (Show k,Ord b,Show b) => TB (FKey (KType k)) b -> TB (FKey (KType k)) b
unLeftKey (Attr k v ) = (Attr (unKOptional k) v)
unLeftKey (IT na (LeftTB1 (Just tb1))) = IT na tb1
unLeftKey i@(IT na (TB1  _ )) = i
unLeftKey (FKT ilk rel  (LeftTB1 (Just tb1))) = (FKT (kvlist $ (firstTB unKOptional) <$> unkvlist ilk) (Le.over relOri unKOptional <$> rel) tb1)
unLeftKey i@(FKT ilk rel  (TB1  _ )) = i
unLeftKey i = errorWithStackTrace (show i)

unLeftItens  :: (Show k , Show a) => TB (FKey (KType k)) a -> Maybe (TB (FKey (KType k)) a )
unLeftItens = unLeftTB
  where
    unLeftTB (Attr k v)
      = Attr (unKOptional k) <$> unSOptional v
    unLeftTB (Fun k rel v)
      = Fun (unKOptional k) rel <$> unSOptional v
    unLeftTB (IT na (LeftTB1 l))
      = IT (unKOptional na) <$>  l
    unLeftTB i@(IT na (TB1 (_,l)))
      = Just i
    unLeftTB (FKT ifk rel  (LeftTB1 tb))
      = (\ik -> FKT (kvlist ik  ) (Le.over relOri unKOptional <$> rel))
          <$> traverse ( (traFAttr unSOptional) . (firstTB unKOptional )  ) (unkvlist ifk)
          <*>  tb
    unLeftTB i@(FKT ifk rel  (TB1  _ )) = Just i
    unLeftTB i = errorWithStackTrace (show i)



attrOptional :: TB (FKey (KType k))  Showable ->  (TB (FKey (KType k))  Showable)
attrOptional (Attr k v) =  Attr (kOptional k) (LeftTB1 . Just $ v)
attrOptional (Fun k rel v) =  Fun (kOptional k) rel (LeftTB1 . Just $ v)
attrOptional (FKT ifk rel  tb)  = FKT (mapKV tbOptional ifk) (Le.over relOri kOptional <$> rel) (LeftTB1 (Just tb))
  where tbOptional = (firstTB kOptional) . (mapFAttr (LeftTB1 . Just))
attrOptional (IT na j) = IT  na (LeftTB1 (Just j))

leftItens :: TB (FKey (KType k)) a -> Maybe (TB (FKey (KType k)) Showable) -> Maybe (TB (FKey (KType k)) Showable)
leftItens tb@(Fun k  rel _ ) =  maybe emptyAttr (Just .attrOptional)
  where emptyAttr = Fun k rel <$> (showableDef (keyType k))
leftItens tb@(Attr k _ ) =  maybe emptyAttr (Just .attrOptional)
  where emptyAttr = Attr k <$> (showableDef (keyType k))
leftItens tb@(IT na _ ) =   Just . maybe  emptyIT attrOptional
  where emptyIT = IT  na  (LeftTB1 Nothing)
leftItens tb@(FKT ilk rel _) = Just . maybe  emptyFKT attrOptional
  where
      emptyFKT = FKT (mapKV ((mapFAttr (const (LeftTB1 Nothing)))) ilk) rel (LeftTB1 Nothing)



attrArray :: TB Key b -> NonEmpty (TB Key Showable) -> TB Key Showable
attrArray back@(Attr  k _) oldItems  = (\tb -> Attr k (ArrayTB1 tb)) $ (\(Attr _ v) -> v) <$> oldItems
attrArray back@(FKT _ _ _) oldItems  = (\(lc,tb) ->  FKT (kvlist [Attr (kArray $ _relOrigin $  head $ keyattr (Non.head lc )) (ArrayTB1 $ head .  kattr  <$> lc)]) (_fkrelation back) (ArrayTB1 tb  ) )  $ Non.unzip $ (\(FKT lc rel tb ) -> (head $ F.toList $ _kvvalues lc , tb)) <$> oldItems
attrArray back@(IT _ _) oldItems  = (\tb ->  IT  (_tbattrkey back) (ArrayTB1 tb  ) )  $ (\(IT _ tb ) -> tb) <$> oldItems


unFin (Interval.Finite i) = Just i
unFin i = Nothing



kOptional = Le.over (keyTypes .keyFunc ) ( KOptional:)
kArray = Le.over (keyTypes .keyFunc ) (KArray:)
kDelayed = Le.over (keyTypes.keyFunc)  (KDelayed:)

unKOptional (Key a  v c m n d (Primitive (KOptional :cs ) e )) = Key a  v c m n d (Primitive cs e)
unKOptional (Key a  v c m n d (Primitive (KSerial :cs) e)) = Key a  v c m n d (Primitive cs e)
unKOptional (Key a  v c m n d (Primitive [] e)) = Key a  v c m n d (Primitive [] e)
unKOptional i = i -- errorWithStackTrace ("unKOptional" <> show i)

unKTDelayed (KDelayed : e ) = e
unKTDelayed (KSerial : e ) = e
unKTDelayed (KOptional : e ) = KOptional : unKTDelayed e
unKTDelayed (KArray : e ) = KArray : unKTDelayed e
unKTDelayed i = i

unKDelayed (Key v a  c m n d e) = (Key v a  c m n d (Le.over keyFunc unKTDelayed e) )
unKDelayed i = errorWithStackTrace ("unKDelayed" <> show i)

unKArray (Key a v c d m n (Primitive (KArray :xs ) e)) = Key a v  c d  m n (Primitive xs e)
unKArray (Key a v c d m n e) = Key a  v c d  m n e

tableKeys (TB1  (_,k) ) = concat $ fmap (fmap _relOrigin.keyattr) (F.toList $ _kvvalues $   k)
tableKeys (LeftTB1 (Just i)) = tableKeys i
tableKeys (ArrayTB1 (i :| _) ) = tableKeys i

recOverAttr :: Ord k => [Set(Rel k)] -> TB k a -> (Map (Set (Rel k )) (TB  k a ) -> Map (Set (Rel k )) (TB  k a ))
recOverAttr (k:[]) attr = Map.insert k (attr )
recOverAttr (k:xs) attr = Map.alter (fmap ((Le.over ifkttable (fmap (fmap ((KV . recOverAttr xs attr . _kvvalues )))))))  k

recOverMAttr' :: [Set (Rel Key)] -> [[Set (Rel Key)]] -> Map (Set (Rel Key)) (TB Key b ) ->Map (Set (Rel Key)) (TB  Key b )
recOverMAttr' tag tar  m =   foldr go m tar
  where
    go (k:[]) = Map.alter (fmap ((Le.over ifkttable (fmap (fmap ((KV . recOverAttr tag  recv . _kvvalues ))))) )) k
      where recv = gt tag m
    go (k:xs) = Map.alter (fmap ((Le.over ifkttable (fmap (fmap ((KV . go xs . _kvvalues )))) ))) k
    gt (k:[]) = justError "no key" . Map.lookup k
    gt (k:xs) = gt xs . _kvvalues . snd . head .F.toList. _fkttable . justError "no key" . Map.lookup k

replaceRecRel :: Map (Set (Rel Key)) (TB  Key b ) -> [MutRec [Set (Rel Key) ]] -> Map (Set (Rel Key)) (TB  Key b )
replaceRecRel = foldr (\(MutRec l) v  -> foldr (\a -> recOverMAttr' a l )   v l)

unKOptionalAttr (Attr k i ) = Attr (unKOptional k) i
unKOptionalAttr (Fun k rel i ) = Fun (unKOptional k) rel i
unKOptionalAttr (IT  r (LeftTB1 (Just j))  ) = (\j-> IT   r j )    j
unKOptionalAttr (FKT i  l (LeftTB1 (Just j))  ) = FKT (fmap ((first unKOptional) ) i)  l j

unOptionalAttr (Attr k i ) = Attr (unKOptional k) <$> unSOptional i
unOptionalAttr (Fun k rel i ) = Fun (unKOptional k) rel <$> unSOptional i
unOptionalAttr (IT r (LeftTB1 j)  ) = (\j-> IT   r j ) <$>     j
unOptionalAttr (FKT i  l (LeftTB1 j)  ) = liftA2 (\i j -> FKT i  l j) (traverseKV ( (traFAttr unSOptional) . ((firstTB unKOptional)) ) i)  j



tbUn :: Ord k =>   Set k -> TB3  k a ->   KV  k a
tbUn un (TB1 (kv,item)) =  (\kv ->  (\(KV item)->  KV $ Map.filterWithKey (\k _ -> pred kv k ) $ item) item ) un
  where pred kv k = (S.isSubsetOf (S.map _relOrigin k) kv )


getPK (TB1 i) = getPKM i

getPKM (m, k) = Map.fromList $  getPKL (m,k)

getPKL (m, k) = concat $ F.toList (fmap aattr $ F.toList $ (Map.filterWithKey (\k v -> Set.isSubsetOf  (Set.map _relOrigin k)(Set.fromList $ _kvpk m)) (  _kvvalues (k))))

getAttr'  (m, k) =  L.sortBy (comparing fst) (concat (fmap aattr $ F.toList $  (  _kvvalues k)))

getPKAttr (m, k) = (concat . F.toList . (Map.filterWithKey (\k v -> Set.isSubsetOf  (Set.map _relOrigin k)(Set.fromList $ _kvpk m))   )) k

getAttr (m, k) = concat . F.toList  $ k


getUn un (m, k) =   concat (fmap aattr $ F.toList $ (Map.filterWithKey (\k v -> Set.isSubsetOf  (Set.map _relOrigin k) un ) (  _kvvalues (k))))


inlineName (Primitive _ (RecordPrim (s, i)) ) = (s,i)

inlineFullName (Primitive _ (RecordPrim (s, i)) ) = s <> "." <> i

attrT :: (a,FTB b) -> TB  a b
attrT (i,j) = Attr i j

-- mergeFKRef  $ keyType . _relOrigin <$>rel
mergeFKRel :: [Rel CoreKey] -> KType [(Rel CoreKey,KType CorePrim)]
mergeFKRel ls = Primitive (F.foldr mergeRel [] ((\i -> _keyFunc $ keyType (_relOrigin i)) <$> ls)) ((\i -> (i, keyType (_relTarget i) ))  <$> ls)
  where
    mergeRel (KOptional : o)  (KOptional : kl) = KOptional : mergeRel o kl
    mergeRel (KArray : o)  (KArray : kl) = KArray : mergeRel o kl
    mergeRel []   []  = []
    mergeRel (KOptional : o) kt  = KOptional : mergeRel o kt
    mergeRel o (KOptional :kt)  = KOptional : mergeRel o kt
    mergeRel (KArray : o)  kl = KArray : mergeRel o kl
    mergeRel o  (KArray : kl) = KArray : mergeRel o kl

mergeFKRef :: [KType a] -> KType [a]
mergeFKRef ls = Primitive (foldl1 mergeOpt (_keyFunc <$> ls)) (_keyAtom <$> ls)
  where
    mergeOpt (KOptional : i) (KOptional : j) = KOptional : (mergeOpt i j)
    mergeOpt (KOptional : i) j = KOptional : mergeOpt i j
    mergeOpt i (KOptional : j) = KOptional : mergeOpt i j
    mergeOpt (KArray : i) (KArray : j ) = KArray :  mergeOpt i j
    mergeOpt (KArray : i) j = KArray : mergeOpt i j
    mergeOpt i (KArray : j) = KArray : mergeOpt i j
    mergeOpt [] []  = []

srange l m = IntervalTB1 $ Interval.interval (Interval.Finite l,True) (Interval.Finite m ,True)

txt = TB1 . SText
int = TB1 . SNumeric
pos = TB1 . SGeo . SPosition
double = TB1 . SDouble
timestamp = TB1 .STime . STimestamp
date = TB1 . STime . SDate

array f = ArrayTB1 . fmap f
opt i = LeftTB1 .  fmap i

class ConstantGen v where
  generate ::  Constant -> v

instance ConstantGen (FTB Showable) where
  generate = generateConstant


generateConstant CurrentDate = unsafePerformIO $ do
        i<- getCurrentTime
        return  (TB1 $ STime $ SDate (utctDay i))
generateConstant CurrentTime = unsafePerformIO $ do
        i<- getCurrentTime
        return (TB1 $ STime  $STimestamp  i)

replaceRel rel (Attr k v) = (justError "no rel" $ L.find ((==k) ._relOrigin) rel,v)
