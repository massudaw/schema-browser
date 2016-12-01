{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor #-}
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
{-# LANGUAGE UndecidableInstances #-}

module Types.Primitive  where

import Types.Common
import Data.Ord
import Data.Vector (Vector)
import Control.DeepSeq
import qualified NonEmpty as Non
import NonEmpty (NonEmpty(..))
import Control.Lens.TH
import qualified Control.Lens as Le
import Data.Functor.Apply
import Utils
import qualified Network.Wreq.Session as Sess
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
makeLenses ''Rel

isSerial (KSerial _) = True
isSerial _ = False

isPrim (Primitive i) = True
isPrim i = False

isOptional (KOptional _) = True
isOptional _ = False


isArray :: KType i -> Bool
isArray (KArray _) = True
isArray (KOptional i) = isArray i
isArray _ = False

newtype TBIndex  a
  -- = Idex (Map k (FTB a))
  = Idex [FTB a]
  deriving(Eq,Show,Ord,Functor,Generic)


type PGType = (Text,Text)
type PGKey = FKey (KType PGPrim )
type PGRecord = (Text,Text)
type PGPrim =  Prim PGType PGRecord
type CorePrim = Prim KPrim (Text,Text)
type CoreKey = FKey (KType CorePrim)


showableDef (KOptional i) = Just $ LeftTB1 (showableDef i)
showableDef (KSerial i) = Just $ SerialTB1 (showableDef i)
showableDef (KArray i ) = Nothing -- Just (SComposite Vector.empty)
showableDef i = Nothing

isFunction :: SqlOperationK k -> Bool
isFunction (FunctionField _ _ _) = True
isFunction i = False

isRecRel (RecJoin _ _ ) =  True
isRecRel i = False

pathRel (Path _ rel  ) = rel
pathRelRef (Path ifk _  ) = ifk

pathRelRel :: Ord k => Path (Set k ) (SqlOperationK k) -> Set (Rel k)
pathRelRel (Path _ (FKJoinTable  rel   _ )  ) = Set.fromList rel
pathRelRel (Path r (FKInlineTable  _  )   ) = Set.map Inline r
pathRelRel (Path r (RecJoin l rel )   ) =  pathRelRel (Path r rel )
pathRelRel (Path _ (FunctionField r _ a ) ) =  S.singleton $ RelFun r (relAccesGen <$> a)


pathRelRel' :: Ord k => Path (Set k ) (SqlOperationK k) -> MutRec [Set (Rel k )]
pathRelRel' (Path r (RecJoin l rel )   )
  | L.null (unMutRec l) =  MutRec [[pathRelRel (Path r rel )]]
  | otherwise = fmap ((pathRelRel (Path r rel ) :) . fmap (Set.fromList)) l




data Path a b
  = Path  a  b
  deriving(Eq,Ord,Show ,Functor)





type Column k a = TB Identity k a
type TBData k a = (KVMetadata k,Compose Identity (KV (Compose Identity (TB Identity))) k a )
type TB3Data  f k a = (KVMetadata k,Compose f (KV (Compose f (TB f ))) k a )


-- Reference labeling
-- exchange label reference for values when labeled
-- inline values reference when unlabeled

data Labeled l v
  = Labeled
  { label :: l
  , labelValue :: v
  }
  | Unlabeled
  { labelValue :: v
  } deriving(Eq,Show,Ord,Foldable,Functor,Traversable)

instance (Show f) =>  Show1 (Labeled f  ) where
  showsPrec1 = showsPrec

type Key = CoreKey -- FKey (KType  (Prim (Text,Text) (Text,Text)))

data FKey a
    = Key
    { keyValue :: Text
    , keyTranslation ::  (Maybe Text)
    , keyModifier :: [FieldModifier]
    , keyPosition :: Int
    , keyStatic :: Maybe (FTB Showable)
    , keyFastUnique ::  Unique
    , _keyTypes ::  a
    }deriving(Functor,Generic)

instance NFData a => NFData (FKey a)

keyType = _keyTypes



instance Binary Sess.Session where
  put i = return ()
  get = error ""
instance NFData Sess.Session where
  rnf _ = ()

instance Binary a => Binary (KType a)



instance Binary Position
instance NFData Position
instance Binary Bounding
instance NFData Bounding
instance Binary LineString
instance NFData LineString
instance Binary Showable
instance NFData Showable




type FTB1 f k a = FTB (KVMetadata k, Compose f (KV (Compose f (TB f))) k a)

data GeomType
  = MultiGeom GeomType
  | PPolygon Int
  | PLineString Int
  | PPosition Int
  | PBounding  Int
  deriving(Eq,Show,Ord,Generic)

data KPrim
   = PText
   | PBoolean
   | PAddress
   | PInt Int
   | PDouble
   | PDate
   | PDayTime
   | PTimestamp (Maybe TimeZone)
   | PInterval
   | PGeom GeomType
   | PCnpj
   | PMime Text
   | PCpf
   | PBinary
   | PSession
   | PColor
   | PDynamic
   deriving(Show,Eq,Ord,Generic)

instance NFData KPrim
instance NFData GeomType

data Prim a b
  = AtomicPrim a
  | RecordPrim b
  deriving(Eq,Ord,Show,Generic)

instance (NFData a , NFData b) => NFData (Prim a b)
data KType a
   = Primitive a
   | KSerial (KType a)
   | KArray (KType a)
   | KInterval (KType a)
   | KOptional (KType a)
   | KDelayed (KType a)
   | KTable [KType a]
   deriving(Eq,Ord,Functor,Generic,Foldable,Show)

instance NFData a => NFData (KType a)

showTy f (Primitive i ) = f i
showTy f (KArray i) = "{" <>  showTy f i <> "}"
showTy f (KOptional i) = showTy f i <> "*"
showTy f (KInterval i) = "(" <>  showTy f i <> ")"
showTy f (KSerial i) = showTy f i <> "?"
showTy f (KDelayed i) = showTy f i <> "-"
showTy f (KTable i) = "t"
showTy f i = errorWithStackTrace ("no ty for " <> show   i)


instance Eq (FKey a) where
   k == l = keyFastUnique k == keyFastUnique l

instance Ord (FKey a) where
   compare i j = compare (keyFastUnique i) (keyFastUnique j)

instance Show a => Show (FKey a)where
  show k = (T.unpack $ maybe (keyValue k) id (keyTranslation  k))

showKey k  =   maybe (keyValue k)  (\t -> keyValue k <> "-" <> t ) (keyTranslation k) <> "::" <> T.pack ( show $ hashUnique $ keyFastUnique k )<> "::" <> T.pack (show $ keyStatic k) <>  "::" <> T.pack (show (keyType k) <> "::" <> show (keyModifier k) <> "::" <> show (keyPosition k )  )

data Position
    = Position (Double,Double,Double)
    | Position2D (Double,Double) deriving(Eq,Typeable,Show,Read,Generic)

instance Ord Position where
  (Position (x,y,z) ) <= (Position (a,b,c)) =  x <= a && y <= b && z <= c
  (Position2D (x,y) ) <= (Position2D (a,b)) =  x <= a && y <= b
  (Position (x,y,z) ) >= (Position (a,b,c)) =  x >= a && y >= b && z >= c
  (Position2D (x,y) ) >= (Position2D (a,b)) =  x >= a && y >= b


newtype Bounding = Bounding (Interval.Interval Position) deriving(Eq,Ord,Typeable,Show,Generic)

newtype LineString = LineString (Vector Position) deriving(Eq,Ord,Typeable,Show,Read,Generic)


data Showable
  = SText Text
  | SNumeric Int
  | SBoolean Bool
  | SDouble Double
  | STimestamp LocalTime
  | SPInterval DiffTime
  | SPosition Position
  | SBounding Bounding
  | SLineString LineString
  | SPolygon LineString [LineString]
  | SMultiGeom [Showable]
  | SDate Day
  | SDayTime TimeOfDay
  | SBinary BS.ByteString
  | SDynamic  (FTB Showable)
  | SSession Sess.Session
  deriving(Ord,Eq,Show,Generic)

instance Eq Sess.Session where
   i==  j = True

instance Ord Sess.Session where
  compare i j = compare 1 2


type SqlOperation = SqlOperationK Key
data SqlOperationK k
  = FKJoinTable [Rel k] (Text,Text)
  | RecJoin (MutRec [[Rel k ]])  (SqlOperationK k)
  | FKInlineTable (Text,Text)
  | FunctionField k Expr [Access k]
  deriving(Eq,Ord,Show,Functor)

fkTargetTable (FKJoinTable  r tn) = snd tn
fkTargetTable (FKInlineTable tn) = snd tn
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

mapTableK f (Raw  uni s tt tr de is rn  un ra rsc rp rd rf inv rat u ) = Raw uni s tt tr (S.map f de) is rn (fmap (S.map f) un) ra (map f rsc ) (map f rp) (fmap f rd) (S.map (mapPath f )  rf )(S.map (mapPath f )  inv) (S.map f rat) (mapTableK f <$> u)
  where mapPath f (Path i j ) = Path (S.map f i) (fmap f j)

instance Show Unique where
    show i = show (hashUnique i)
instance Eq (TableK k) where
  i == j = _tableUnique i == _tableUnique j
instance Ord (TableK k) where
  compare i j = compare (_tableUnique i) (_tableUnique j)

data TableK k
  =  Raw   { _tableUnique :: Int
           ,_rawSchemaL :: Text
           , rawTableType :: TableType
           , rawTranslation :: Maybe Text
           , rawDelayed :: (Set k)
           , rawIsSum :: Bool
           , _rawNameL :: Text
           , uniqueConstraint :: [Set k]
           , rawAuthorization :: [Text]
           , _rawScope :: [k]
           , _rawPKL :: [k]
           , _rawDescriptionL :: [k]
           , _rawFKSL ::  (Set (Path (Set k) (SqlOperationK k )))
           , _rawInvFKS ::  (Set (Path (Set k) (SqlOperationK k)))
           , rawAttrs :: (Set k)
           , rawUnion :: [TableK k ]
           }
     | Union
          { origin :: TableK k
          , unionList :: [(TableK k)]
          }
     deriving(Show)

rawFKS = _rawFKSL

unRecRel (RecJoin _ l) = l
unRecRel l = l




rawPK  (Union i _ ) = _rawPKL i
rawPK  i  = _rawPKL i
rawDescription (Union i _ ) = _rawDescriptionL i
rawDescription  i  = _rawDescriptionL i
rawName (Union i _) = _rawNameL i
rawName i  = _rawNameL i
rawSchema (Union i _) = _rawSchemaL i
rawSchema i  = _rawSchemaL i

tableName = rawName
translatedName tb =  maybe (rawName tb) id (rawTranslation tb )


data TableModification p
  = TableModification
  { tableId :: (Maybe Int)
  , tableObj :: Table
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
    STimestamp i - STimestamp j =  SPInterval $ realToFrac $ diffUTCTime (localTimeToUTC utc i) (localTimeToUTC utc  j)
    SNumeric i -  SNumeric j = SNumeric (i - j)
    SDouble i -  SDouble j = SDouble (i - j)
    SDouble i - SNumeric j = SDouble $ i -  fromIntegral j
    SNumeric j  - SDouble i = SDouble $ i -  fromIntegral j
    v - k = errorWithStackTrace (show (v,k))
    SNumeric i *  SNumeric j = SNumeric (i * j)
    SNumeric i *  SDouble j = SDouble (fromIntegral i * j)
    SDouble i *  SNumeric j = SDouble (i * fromIntegral j)
    SDouble i *  SDouble j = SDouble (i * j)
    SDouble i *  SPInterval j = SDouble (i * realToFrac j)
    SPInterval i *  SDouble j = SDouble (j * realToFrac i)
    SPInterval i *  SPInterval j = SPInterval (i * j)
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
  recip (SPInterval i) = SPInterval (recip i)
  recip (SNumeric i) = SDouble (recip $ fromIntegral i)
  recip i = errorWithStackTrace (show i)

-- type HashQuery =  HashSchema (Set Key) (SqlOperation Table)
type PathQuery = Path (Set Key) (SqlOperation )

type TBLabel =  Compose (Labeled Text) (TB (Labeled Text) ) Key
type TBIdent =  Compose Identity  (TB Identity ) Key


instance Applicative (Labeled Text) where
  pure =Unlabeled
  Labeled t l <*> Labeled j k = Labeled t (l  k)
  Unlabeled  l <*> Labeled t k = Labeled t (l  k)
  Labeled t l <*> Unlabeled  k = Labeled t (l  k)
  Unlabeled l <*> Unlabeled  k = Unlabeled  (l  k)

instance Monad (Labeled Text) where
  return = Unlabeled
  Unlabeled i >>= j = j i
  Labeled t i >>= j = case j i of
                    Unlabeled i -> Labeled t i
                    Labeled t0 i -> Labeled t  i





-- tableAttr :: (Traversable f ,Ord k) => TB3 f k () -> [Compose f (TB f) k ()]
-- tableAttr (ArrayTB1 i) = tableAttr <$> i
-- tableAttr (LeftTB1 i ) = tableAttr<$> i
tableAttr (DelayedTB1 (Just tb)) = tableAttr tb
tableAttr (TB1 (m ,(Compose (Labeled _ (KV  n)))) ) =   concat  $ F.toList (nonRef <$> n)
tableAttr (TB1 (m ,(Compose (Unlabeled (KV  n)))) ) =   concat  $ F.toList (nonRef <$> n)

nonRef :: (Ord f,Show k ,Show f,Ord k) => Compose (Labeled f ) (TB (Labeled f) ) k () -> [Compose (Labeled f ) (TB (Labeled f) ) k ()]
nonRef i@(Compose (Labeled _ (Fun _ _ _ ))) =[i]
nonRef i@(Compose (Unlabeled  (Fun _ _ _ ))) =[i]
nonRef i@(Compose (Labeled _ (Attr _ _ ))) =[i]
nonRef i@(Compose (Unlabeled  (Attr _ _ ))) =[i]
nonRef (Compose (Unlabeled  ((FKT i  _ _ )))) = concat (nonRef <$> unkvlist i)
nonRef (Compose (Labeled _ ((FKT i  _ _ )))) = concat (nonRef <$> unkvlist i)
nonRef j@(Compose (Unlabeled (IT k v ))) = [Compose (Labeled (label $ getCompose $ snd $ head $ F.toList v) (Attr k (TB1 ()))) ]
nonRef j@(Compose (Labeled l (IT k v ))) = [Compose (Labeled l (Attr k (TB1 ()))) ]

-- nonRef i = errorWithStackTrace (show i)

-- joinNonRef :: Ord k => TB2 k a -> TB2 k a
-- joinNonRef = fmap joinNonRef'

-- joinNonRef' :: Ord k => TB3Data f k a -> TB3Data f k a

flattenMap ::  Ord k => TB3Data (Labeled Text) k a -> [Compose (Labeled Text) (TB (Labeled Text) )  k a]
flattenMap (m,n)  = (concat . fmap nonRef . F.toList . _kvvalues) (head . F.toList $  getCompose n)
  where
    -- compJoin :: Monad f => Compose f (Compose f g ) k  a -> Compose f g k a
    nonRef :: (Ord k) => Compose (Labeled Text) (TB (Labeled Text)) k a ->  [Compose (Labeled Text) (TB (Labeled Text) )  k a]
    nonRef (Compose (Labeled l (Attr k v ))) = [Compose (Labeled l ( Attr k v))]
    -- nonRef (FKT i _ _ ) = tra
        -- where tra = concat ( fmap compJoin   . traComp  nonRef <$> i)
    nonRef (Compose (Labeled l it@(IT j k ))) =   concat $ flattenMap <$> (F.toList k  )
    nonRef (Compose (Unlabeled it@(IT j k ))) =   concat $ flattenMap <$> (F.toList k  )

flattenNonRec ::  Ord k => [MutRec [[Rel k]]] -> TB3Data (Labeled Text) k a -> [Compose (Labeled Text) (TB (Labeled Text) )  k a]
flattenNonRec rels (m,n)  = (concat . fmap (\r -> if pred rels r then nonRef (fmap (L.drop 1) <$>   (L.filter (\(MutRec rel) -> L.any (\rel -> keyattr r == head rel )rel) rels )) r  else []  ) . F.toList . _kvvalues) (head . F.toList $  getCompose n)
  where
    -- compJoin :: Monad f => Compose f (Compose f g ) k  a -> Compose f g k a
    pred rs v = not $ L.any (\(MutRec r) ->  L.any (\r -> L.length r == 1 && last r == keyattr  v ) r ) rs
    nonRef :: (Ord k) => [MutRec [[Rel k]]] -> Compose (Labeled Text) (TB (Labeled Text)) k a ->  [Compose (Labeled Text) (TB (Labeled Text) )  k a]
    nonRef r (Compose (Labeled l (Attr k v ))) = [Compose (Labeled l ( Attr k v))]
    nonRef r (Compose (Labeled l (FKT i _ k ))) = tra
        where tra = unkvlist i <> concat  (flattenNonRec r <$> (F.toList k))
    nonRef r (Compose (Unlabeled (FKT i _ k ))) = tra
        where tra = unkvlist i <> concat  (flattenNonRec r <$> (F.toList k))
    nonRef r (Compose (Labeled l it@(IT j k ))) =   concat $ flattenNonRec r <$> (F.toList k  )
    nonRef r (Compose (Unlabeled it@(IT j k ))) =   concat $ flattenNonRec r <$> (F.toList k  )

flattenRec ::  (Show a, Show k ,Ord k) => [MutRec [Set (Rel k)]] -> TB3Data (Labeled Text) k a -> [Compose (Labeled Text) (TB (Labeled Text) )  k a]
flattenRec rels (m,n)  = (concat . fmap (\r -> if pred rels r then nonRef (fmap (L.drop 1)   <$> (L.filter (\(MutRec rel) -> L.any (\rel -> Set.fromList (keyattr r ) == head rel ) rel ) rels )) r  else []  ) . F.toList . _kvvalues) (head . F.toList $  getCompose n)
  where
    -- compJoin :: Monad f => Compose f (Compose f g ) k  a -> Compose f g k a
    pred rs v = L.any (\(MutRec r) ->   L.any (\r -> head r == Set.fromList (keyattr  v )) r  ) rs
    nonRef :: (Show a, Show k,Ord k) => [MutRec [Set (Rel k)]] -> Compose (Labeled Text) (TB (Labeled Text)) k a ->  [Compose (Labeled Text) (TB (Labeled Text) )  k a]
    nonRef r  v | concat (fmap Set.toList $ concat (concat (fmap unMutRec r))) == []  = [v]
    nonRef r (Compose (Labeled l (Attr k v ))) = [Compose (Labeled l ( Attr k v))]
    nonRef r (Compose (Labeled l (FKT i _ k ))) = tra
        where tra = unkvlist i <> concat  (flattenRec r <$> (F.toList k))
    nonRef r (Compose (Unlabeled (FKT i _ k ))) = tra
        where tra = unkvlist i <> concat  (flattenRec r <$> (F.toList k))
    nonRef r (Compose (Labeled l it@(IT j k ))) =   concat $ flattenRec r <$> (F.toList k  )
    nonRef r (Compose (Unlabeled it@(IT j k ))) =   concat $ flattenRec r <$> (F.toList k  )



-- unlabelIT ::  (Functor f,Show a, Show k ,Ord k) => [[[Rel k]]] -> TB3Data f k a -> TB3Data f k a
unlabelIT (m,n)  = (m, mapComp (KV . fmap (Compose . nonRef  .getCompose) . _kvvalues )  n  )
  where
    nonRef  (Labeled l (IT j k )) =   Unlabeled (IT j (unlabelIT  <$> k ))
    nonRef  i = i




tableNonRef2 :: Ord k => TB3Data (Labeled Text) k a -> TB3Data (Labeled Text) k a
tableNonRef2 (m,n)  = (m, mapComp (KV . rebuildTable . _kvvalues) n)
  where
    rebuildTable n =    Map.unions (nonRef . getCompose <$> F.toList n)
    -- nonRef :: Ord k => TB (Labeled Text) k a -> M.Map (Rel k) (TB (Labeled Text) k  a)
    nonRef :: Ord k => Labeled Text (TB (Labeled Text) k a) -> Map (Set (Rel k )) (Compose (Labeled Text ) (TB (Labeled Text)) k a)
    nonRef (Labeled _ (Fun i _ _ )) =Map.empty
    nonRef (Unlabeled (Fun i _ _ )) = Map.empty
    nonRef (Labeled _ (FKT i _ _ )) = _kvvalues i
    nonRef (Unlabeled (FKT i _ _ )) = _kvvalues i
    nonRef (Labeled t it@(IT j k )) = Map.singleton (S.singleton $ Inline j) (Compose $ Labeled t $ IT  j (tableNonRef2 <$> k ))
    nonRef (Unlabeled it@(IT j k )) = Map.singleton (S.singleton $ Inline j) (Compose $ Unlabeled $ IT  j (tableNonRef2 <$> k ))
    nonRef i@(Labeled t (Attr j _)) = Map.singleton (S.singleton $ Inline j) (Compose i)
    nonRef i@(Unlabeled (Attr j _)) = Map.singleton (S.singleton $ Inline j) (Compose i)




nonRefTB :: Ord k => TB Identity k a -> [(TB Identity ) k a]
nonRefTB (FKT i _ _ ) = concat (overComp nonRefTB <$> unkvlist i)
nonRefTB it@(IT j k ) = [(IT  j (tableNonRef k )) ]
nonRefTB i  = [i]


addDefault
  :: Functor g => Compose g (TB g) d a
     -> Compose g (TB g) d b
addDefault = mapComp def
  where
    def ((Attr k i)) = (Attr k (LeftTB1 Nothing))
    def ((Fun k i _)) = (Fun k i (LeftTB1 Nothing))
    def ((IT  rel j )) = (IT  rel (LeftTB1 Nothing)  )
    def ((FKT at rel j )) = (FKT (KV $ addDefault <$> _kvvalues at) rel (LeftTB1 Nothing)  )







tableMeta :: Ord k => TableK k -> KVMetadata k
tableMeta (Union s l ) =  tableMeta s
tableMeta t = KVMetadata (rawName t) (rawSchema t) (_rawScope t) (rawPK t) (rawDescription t) (fmap F.toList $ uniqueConstraint t) [] (F.toList $ rawAttrs t) (F.toList $ rawDelayed t) (paths' <> paths)
  where rec = filter (isRecRel.pathRel)  (Set.toList $ rawFKS t)
        same = filter ((tableName t ==). fkTargetTable . pathRel) rec
        notsame = filter (not . (tableName t ==). fkTargetTable . pathRel) rec
        paths = fmap (fmap (fmap F.toList). pathRelRel' ) notsame
        paths' = (\i -> if L.null i then [] else [MutRec i]) $ fmap ((head .unMutRec). fmap (fmap F.toList). pathRelRel' ) same




tblist' :: Ord k => TableK k -> [Compose Identity  (TB Identity) k a] -> TBData k a
tblist' t  = tblistM (tableMeta t)





isInline (KOptional i ) = isInline i
isInline (KArray i ) = isInline i
isInline (Primitive (RecordPrim _ ) ) = True
isInline _ = False


-- Intersections and relations


srange l m = IntervalTB1 $ Interval.interval (Interval.Finite l,True) (Interval.Finite m ,True)




makeLenses ''FKey
makeLenses ''TableK

--
--- Attr Cons/Uncons
--
unIndexItens :: (Show (KType k),Show a) =>  Int -> Int -> Maybe (TB Identity  (FKey (KType k))  a ) -> Maybe (TB Identity  (FKey (KType k))  a )
unIndexItens ix o =  join . fmap (unIndex (ix+ o) )

unIndex :: (Show (KType k),Show a) => Int -> TB Identity (FKey (KType k)) a -> Maybe (TB Identity (FKey (KType k)) a )
unIndex o (Attr k (ArrayTB1 v)) = Attr (unKArray k) <$> Non.atMay v o
unIndex o (IT na (ArrayTB1 j))
  =  IT  na <$>  Non.atMay j o
unIndex o (FKT els rel (ArrayTB1 m)  ) = (\li mi ->  FKT  (kvlist $ nonl <> fmap (mapComp (firstTB unKArray) )li) (Le.over relOri (\i -> if isArray (keyType i) then unKArray i else i ) <$> rel) mi ) <$> (maybe (Just []) (Just .pure ) (join (traComp (traFAttr (indexArray o))  <$> l))) <*> (Non.atMay m o)
  where
    l = L.find (all (isArray.keyType) . fmap _relOrigin . keyattr)  (unkvlist els)
    nonl = L.filter (not .all (isArray.keyType) . fmap _relOrigin . keyattr) (unkvlist els)
    indexArray ix s =  Non.atMay (unArray s) ix
unIndex o i = errorWithStackTrace (show (o,i))

unLeftKey :: (Show k,Ord b,Show b) => TB Identity (FKey (KType k)) b -> TB Identity (FKey (KType k)) b
unLeftKey (Attr k v ) = (Attr (unKOptional k) v)
unLeftKey (IT na (LeftTB1 (Just tb1))) = IT na tb1
unLeftKey i@(IT na (TB1  _ )) = i
unLeftKey (FKT ilk rel  (LeftTB1 (Just tb1))) = (FKT (kvlist $ mapComp (firstTB unKOptional) <$> unkvlist ilk) (Le.over relOri unKOptional <$> rel) tb1)
unLeftKey i@(FKT ilk rel  (TB1  _ )) = i
unLeftKey i = errorWithStackTrace (show i)

unLeftItens  :: (Show k , Show a) => TB Identity  (FKey (KType k)) a -> Maybe (TB Identity  (FKey (KType k)) a )
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
          <$> traverse ( traComp (traFAttr unSOptional) . mapComp (firstTB unKOptional )  ) (unkvlist ifk)
          <*>  tb
    unLeftTB i@(FKT ifk rel  (TB1  _ )) = Just i
    unLeftTB i = errorWithStackTrace (show i)



attrOptional :: TB Identity (FKey (KType k))  Showable ->  (TB Identity  (FKey (KType k))  Showable)
attrOptional (Attr k v) =  Attr (kOptional k) (LeftTB1 . Just $ v)
attrOptional (Fun k rel v) =  Fun (kOptional k) rel (LeftTB1 . Just $ v)
attrOptional (FKT ifk rel  tb)  = FKT (mapKV tbOptional ifk) (Le.over relOri kOptional <$> rel) (LeftTB1 (Just tb))
  where tbOptional = mapComp (firstTB kOptional) . mapComp (mapFAttr (LeftTB1 . Just))
attrOptional (IT na j) = IT  na (LeftTB1 (Just j))

leftItens :: TB Identity (FKey (KType k)) a -> Maybe (TB Identity  (FKey (KType k)) Showable) -> Maybe (TB Identity  (FKey (KType k)) Showable)
leftItens tb@(Fun k  rel _ ) =  maybe emptyAttr (Just .attrOptional)
  where emptyAttr = Fun k rel <$> (showableDef (keyType k))
leftItens tb@(Attr k _ ) =  maybe emptyAttr (Just .attrOptional)
  where emptyAttr = Attr k <$> (showableDef (keyType k))
leftItens tb@(IT na _ ) =   Just . maybe  emptyIT attrOptional
  where emptyIT = IT  na  (LeftTB1 Nothing)
leftItens tb@(FKT ilk rel _) = Just . maybe  emptyFKT attrOptional
  where
      emptyFKT = FKT (mapKV (mapComp (mapFAttr (const (LeftTB1 Nothing)))) ilk) rel (LeftTB1 Nothing)

-- mapkvlist f =  kvlist . f . unkvlist


attrArray :: TB Identity Key b -> NonEmpty (TB Identity Key Showable) -> TB Identity Key Showable
attrArray back@(Attr  k _) oldItems  = (\tb -> Attr k (ArrayTB1 tb)) $ (\(Attr _ v) -> v) <$> oldItems
attrArray back@(FKT _ _ _) oldItems  = (\(lc,tb) ->  FKT (kvlist [Compose $ Identity $ Attr (kArray $ _relOrigin $  head $ keyattr (Non.head lc )) (ArrayTB1 $ head .  kattr  <$> lc)]) (_fkrelation back) (ArrayTB1 tb  ) )  $ Non.unzip $ (\(FKT lc rel tb ) -> (head $ F.toList $ _kvvalues lc , tb)) <$> oldItems
attrArray back@(IT _ _) oldItems  = (\tb ->  IT  (_tbattrkey back) (ArrayTB1 tb  ) )  $ (\(IT _ tb ) -> tb) <$> oldItems


keyOptional (k,v) = (kOptional k ,LeftTB1 $ Just v)

unKeyOptional (k  ,(LeftTB1 v) ) = fmap (unKOptional k,) v

kOptional = Le.over keyTypes KOptional
kArray = Le.over keyTypes KArray
kDelayed = Le.over keyTypes KDelayed

unKOptional (Key a  v c m n d (KOptional e)) = (Key a  v c m n d e )
unKOptional (Key a  v c m n d (KSerial e)) = (Key a  v c m n d e )
unKOptional (Key a  v c m n d (e@(Primitive _))) = (Key a  v c m n d e )
unKOptional i = errorWithStackTrace ("unKOptional" <> show i)

unKDelayed (Key v a  c m n d (KDelayed e)) = (Key v a  c m n d e )
unKDelayed i = errorWithStackTrace ("unKDelayed" <> show i)

unKArray (Key a v c d m n (KArray e)) = Key a v  c d  m n e
unKArray (Key a v c d m n e) = Key a  v c d  m n e

tableKeys (TB1  (_,k) ) = concat $ fmap (fmap _relOrigin.keyattr) (F.toList $ _kvvalues $  runIdentity $ getCompose $ k)
tableKeys (LeftTB1 (Just i)) = tableKeys i
tableKeys (ArrayTB1 (i :| _) ) = tableKeys i

recOverAttr :: Ord k => [Set(Rel k)] -> TB Identity k a -> (Map (Set (Rel k )) (Compose Identity (TB Identity) k a ) -> Map (Set (Rel k )) (Compose Identity (TB Identity) k a ))
recOverAttr (k:[]) attr = Map.insert k (_tb attr )
recOverAttr (k:xs) attr = Map.alter (fmap (mapComp (Le.over fkttable (fmap (fmap (mapComp (KV . recOverAttr xs attr . _kvvalues )))))))  k

recOverMAttr' :: [Set (Rel Key)] -> [[Set (Rel Key)]] -> Map (Set (Rel Key)) (Compose Identity (TB Identity ) Key b ) ->Map (Set (Rel Key)) (Compose Identity (TB Identity ) Key b )
recOverMAttr' tag tar  m =   foldr go m tar
  where
    go (k:[]) = Map.alter (fmap (mapComp (Le.over fkttable (fmap (fmap (mapComp (KV . recOverAttr tag  recv . _kvvalues ))))) )) k
      where recv = gt tag m
    go (k:xs) = Map.alter (fmap (mapComp (Le.over fkttable (fmap (fmap (mapComp (KV . go xs . _kvvalues )))) ))) k

    gt (k:[]) = unTB . justError "no key" . Map.lookup k
    gt (k:xs) = gt xs . _kvvalues . unTB . snd . head .F.toList. _fkttable . unTB  . justError "no key" . Map.lookup k

replaceRecRel :: Map (Set (Rel Key)) (Compose Identity (TB Identity ) Key b ) -> [MutRec [Set (Rel Key) ]] -> Map (Set (Rel Key)) (Compose Identity (TB Identity ) Key b )
replaceRecRel = foldr (\(MutRec l) v  -> foldr (\a -> recOverMAttr' a l )   v l)

unKOptionalAttr (Attr k i ) = Attr (unKOptional k) i
unKOptionalAttr (Fun k rel i ) = Fun (unKOptional k) rel i
unKOptionalAttr (IT  r (LeftTB1 (Just j))  ) = (\j-> IT   r j )    j
unKOptionalAttr (FKT i  l (LeftTB1 (Just j))  ) = FKT (fmap (mapComp (first unKOptional) ) i)  l j

unOptionalAttr (Attr k i ) = Attr (unKOptional k) <$> unSOptional i
unOptionalAttr (Fun k rel i ) = Fun (unKOptional k) rel <$> unSOptional i
unOptionalAttr (IT r (LeftTB1 j)  ) = (\j-> IT   r j ) <$>     j
unOptionalAttr (FKT i  l (LeftTB1 j)  ) = liftA2 (\i j -> FKT i  l j) (traverseKV ( traComp (traFAttr unSOptional) . (mapComp (firstTB unKOptional)) ) i)  j



tbUn :: (Functor f,Ord k) =>   Set k -> TB3 f k a ->  Compose f (KV  (Compose f (TB f ))) k a
tbUn un (TB1 (kv,item)) =  (\kv ->  mapComp (\(KV item)->  KV $ Map.filterWithKey (\k _ -> pred kv k ) $ item) item ) un
  where pred kv k = (S.isSubsetOf (S.map _relOrigin k) kv )


getPK (TB1 i) = getPKM i
getPKM (m, k) = Map.fromList $  concat $ F.toList (fmap aattr $ F.toList $ (Map.filterWithKey (\k v -> Set.isSubsetOf  (Set.map _relOrigin k)(Set.fromList $ _kvpk m)) (  _kvvalues (unTB k))))

getAttr'  (m, k) =  L.sortBy (comparing fst) (concat (fmap aattr $ F.toList $  (  _kvvalues (runIdentity $ getCompose k))))

getPKAttr (m, k) = traComp (concat . F.toList . (Map.filterWithKey (\k v -> Set.isSubsetOf  (Set.map _relOrigin k)(Set.fromList $ _kvpk m))   )) k
getAttr (m, k) = traComp (concat . F.toList) k


getUn un (m, k) =   concat (fmap aattr $ F.toList $ (Map.filterWithKey (\k v -> Set.isSubsetOf  (Set.map _relOrigin k) un ) (  _kvvalues (unTB k))))


inlineName (KOptional i) = inlineName i
inlineName (KArray a ) = inlineName a
inlineName (Primitive (RecordPrim (s, i)) ) = (s,i)

inlineFullName (KOptional i) = inlineFullName i
inlineFullName (KArray a ) = inlineFullName a
inlineFullName (Primitive (RecordPrim (s, i)) ) = s <> "." <> i

attrT :: (a,FTB b) -> Compose Identity (TB Identity) a b
attrT (i,j) = Compose . Identity $ Attr i j


-- notOptional :: k a -> G.TBIndex k a
notOptionalPK m =  justError "cant be empty " . traverse unSOptional'  $ m

txt = TB1 . SText
int = TB1 . SNumeric

generateConstant CurrentDate = unsafePerformIO $ do
        i<- getCurrentTime
        return  (TB1 $ SDate (utctDay i))
generateConstant CurrentTime = unsafePerformIO $ do
        i<- getCurrentTime
        return (TB1 $ STimestamp ( utcToLocalTime utc i))

