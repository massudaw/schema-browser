{-# LANGUAGE Arrows #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module TP.View where

import qualified Data.Aeson as A
import Control.Arrow
import Control.Monad (join)
import Utils
import SchemaQuery.Arrow 
import qualified Data.Sequence.NonEmpty as NonS
import qualified Data.Aeson.Diff as AP
import qualified Data.Aeson.Pointer as AP
import Safe
import qualified NonEmpty as Non
import Data.Functor.Identity
import Debug.Trace
import Data.Maybe
import qualified Graphics.UI.Threepenny as UI
import Graphics.UI.Threepenny.Core hiding (get,delete,apply)
import Data.Semigroup
import Control.Arrow (first)
import Control.Applicative
import qualified Data.Map as M
import GHC.Stack
import NonEmpty (NonEmpty)
import qualified Data.Foldable as F
import Types
import Types.Patch
import Environment
import qualified Types.Index as G
import qualified Data.Vector as V
import qualified Data.List as L
import Data.Ord
import Text
import RuntimeTypes
import Step.Common
import Step.Host
import Data.Time
import Query
import Data.Interval as Interval
import qualified Data.Text as T

newtype TRow = TRow (TBData Key Showable)

instance ToJS (KV T.Text Showable)

instance A.ToJSON TRow  where
  toJSON (TRow kv)  = A.toJSON $ M.mapKeys (T.intercalate "," . L.map (keyValue ._relOrigin) . relUnComp) (unKV kv)

instance A.ToJSON (Column Key Showable)  where
  toJSON (Attr k v ) =
    case keyType k of
      Primitive [] (AtomicPrim PColor )-> A.toJSON $  "#" <> renderShowable v
      i ->  A.toJSON v
  toJSON (IT k v) = A.toJSON (fmap TRow v)


instance A.ToJSON a => A.ToJSON (PathFTB a) where
  toJSON  = toPatch
    where 
      toPatch (PAtom i) = A.toJSON i
      toPatch (PIdx ix i ) = A.toJSON $  case i of 
                        Just i ->  AP.Add (AP.Pointer [AP.AKey ix] ) (A.toJSON $ toPatch i)
                        Nothing ->  AP.Rem (AP.Pointer [AP.AKey ix] )


instance A.ToJSON a => A.ToJSON (FTB a) where
    toJSON (TB1 i) = A.toJSON i
    toJSON (LeftTB1 i) = fromMaybe (A.toJSON ("" :: String)) (A.toJSON <$> i)
    toJSON (ArrayTB1 i) = A.toJSON $ F.toList i

instance A.ToJSON LineString where
    toJSON (LineString l ) = A.toJSON l

instance A.ToJSON Position where
    toJSON (Position  y x z ) =
        A.Array $
        V.fromList
            [ A.Number (realToFrac x)
            , A.Number (realToFrac y)
            , A.Number (realToFrac z)]
    toJSON (Position2D  y x ) =
        A.Array $
        V.fromList
            [ A.Number (realToFrac x)
            , A.Number (realToFrac y)
            , A.Number 0]

instance A.ToJSON SGeo where
    toJSON (SMultiGeom l) = A.toJSON l
    toJSON (SPolygon h t) = A.toJSON (h:t)
    toJSON (SLineString i) = A.toJSON i
    toJSON (SPosition i ) = A.toJSON i
instance A.ToJSON Showable where
    toJSON (SText i) = A.toJSON i
    toJSON (SGeo o) = A.toJSON o
    toJSON i = A.toJSON (renderPrim i)

geoPred inf tname geofields (ne,sw) = geo
  where
    geo = OrColl $ geoField <$> F.toList geofields
    geoField f =
      PrimColl .
        fixrel . (, Left (makeInterval (_keyAtom nty)  (sw,ne) ,op nty))
            $ index
      where
        nty= relType index
        index =  liftRel inf (tableName tname)  $  indexerRel f

    op (Primitive f a) =  go f
      where
        go [] = Flip Contains
        go (f:i) = case f of
          KInterval -> IntersectOp
          KOptional  -> go i
          KSerial  -> go i
          KArray -> AnyOp $ go i

timePred inf tname evfields (incrementT,resolution) = time
  where
    time = OrColl $ timeField <$> F.toList evfields
    timeField f =
      PrimColl . fixrel . (, Left ( IntervalTB1 $ fmap (ref ty) i,op ty)) $ index
      where
        index =  liftRel inf (tableName tname) $  indexerRel f
        ty = relType index
    op (Primitive f a) = go f
      where
        go [] = Flip Contains
        go (f:i) = case f of
             KInterval -> IntersectOp
             KOptional -> go i
             KSerial  -> go i
             i -> error ("type not supported : " ++ show i)
    ref (Primitive f a) =  case a of
            (AtomicPrim (PTime PDate)) ->
              TB1 . STime . SDate . utctDay
            (AtomicPrim (PTime (PTimestamp _))) ->
              TB1 . STime . STimestamp
            v -> error ("Wrong type: " ++ show (evfields,tname,v))
    i =
        (\r d ->
              Interval.interval
                  (Interval.Finite $ resRange True r d, True)
                  (Interval.Finite $ resRange False r d, True))
            resolution
            incrementT

predicate
  :: InformationSchema
    -> Table
    -> Maybe (NonEmpty T.Text)
    -> Maybe (NonEmpty T.Text)
    -> (Maybe ([Double], [Double]), Maybe (UTCTime, String))
    -> BoolCollection (Rel Key,[(Rel Key,AccessOp Showable)])
predicate inf tname evfields geofields (i,j) =
    AndColl $
      catMaybes [liftA2 (geoPred inf tname ) geofields i, liftA2 (timePred inf tname) evfields j]

resRange b "year" d =
    d
    { utctDay = addGregorianMonthsClip
          (if b
               then -6
               else 6)
          (utctDay d),
      utctDayTime = if b then 0 else  86399
    }
resRange b "month" d =
    d
    { utctDay = addGregorianMonthsClip
          (if b
               then -1
               else 1)
          (utctDay d),
      utctDayTime = if b then 0 else  86399
    }
resRange b "day" d =
    d
    { utctDay = addDays
          (if b
               then -1
               else 1)
          (utctDay d),
      utctDayTime = if b then 0 else  86399
    }
resRange b "week" d =
    d
    { utctDay = addDays
          (if b
               then -7
               else 7)
          (utctDay d),
      utctDayTime = if b then 0 else  86399
    }
resRange b "hour" d =
   addUTCTime (if b
               then -3600
               else 3600) d

makeInterval :: Prim KPrim (T.Text,T.Text) ->  ([Double] , [Double]) -> FTB Showable
makeInterval nty (sw,ne) = IntervalTB1 $ Interval.interval (makePos nty sw) (makePos nty ne)

makePos :: Prim KPrim (T.Text,T.Text) -> [Double] -> (Extended (FTB Showable),Bool)
makePos (AtomicPrim (PGeom 3 _ )) [b,a,z] =
    (Interval.Finite $ pos (Position  a  b z ), True)
makePos (AtomicPrim (PGeom 2 _ )) [b,a,z] =
    (Interval.Finite $ pos (Position2D  a  b ), True)
makePos a i = error (show (a,i))

writePK' :: T.Text -> [(Rel Key ,FTB Showable )]-> FTB Showable -> T.Text
writePK'  m r efield =
    (\i ->
          m <> "->" <> i <> "->" <>
          T.pack (renderShowable efield)) $
    T.intercalate ",," $
    fmap
        (\(i,j) ->
          T.pack $ renderRel i <> "=" <>  renderShowable j)  r



writePK :: KVMetadata Key -> TBData Key Showable -> FTB Showable -> T.Text
writePK m r efield = writePK' (_kvname m)  (M.toList (getPKM m r))  efield


readPK :: InformationSchema -> T.Text -> (Table, TBIndex Showable, Key)
readPK inf s = (tb, Idex $ snd <$> L.sortBy (comparing ((`L.elemIndex` rawPK tb).fst)) pk, editField)
  where
    [t,pks,f] = T.splitOn "->" s
    pk =
        (\(k,v) ->
          (k, justError ("cant read" <> show (k,v)) $ readType (relType k) (T.unpack $ T.drop 1 v))) .
        first
            (\k ->
              justError ("cant find " <> show (k,pksk, _relOrigin <$> pksk,pks)) $ F.find ((k ==) . keyValue. _relOrigin) pksk) .
        T.break ('=' ==) <$>
        T.splitOn ",," pks
    tb = lookTable inf t
    editField = lookKey inf t f
    pksk = rawPK tb
makePatch
    :: TimeZone
    -> ( Key, Either (Interval UTCTime) UTCTime)
    -> TBIdx Key Showable
makePatch zone (k,a) =
  kvlistp $ PAttr k <$> (typ (keyType k) a)
  where
    typ (Primitive l a ) =  ty l
      where
        ty (KOptional : k) i = fmap (POpt . Just) . ty k $ i
        ty (KSerial : k) i = fmap (POpt. Just) . ty k $ i
        ty (KInterval : k) (Left i) =
          [ PatchSet $ Non.fromList $
            (fmap (PInter True . (, True)) . traverse (ty k . Right) $
               Interval.lowerBound i) <>
                 (fmap (PInter False . (, True)) . traverse (ty k . Right ) $
               Interval.upperBound i)]
        ty []  (Right r) = pure . PAtom . cast a $ r
    cast (AtomicPrim (PTime PDate)) = STime . SDate . utctDay
    cast (AtomicPrim (PTime (PTimestamp l))) =
      STime . STimestamp .
        localTimeToUTC zone . utcToLocalTime utc

readPosition:: EventData -> Maybe ([Double],[Double])
readPosition v = (,) <$>  readP ni na nz <*>readP si sa sz
  where
     [ni,na,nz,si,sa,sz] = unsafeFromJSON v
     readP i a z = (\i j z-> [i,j, z]) <$> readMay i<*> readMay a <*> readMay z

currentPosition :: Element -> Event ([Double],[Double])
currentPosition el = filterJust $ readPosition<$>  domEvent "currentPosition" el


convertInter i =    liftA2 (,) (fmap convertPoint $ G.unFin $ fst $upperBound' i) (fmap convertPoint $ G.unFin $ fst $lowerBound' i)
  where
     convertPoint (SGeo (SPosition (Position  y x z ) )) = [x,y,z]
     convertPoint (SGeo (SPosition (Position2D  y x ) )) = [x,y,0]

execTable project =  runIdentity .evalEnv project . (,[]) . Atom .  mapKey' keyValue

columnName name = ivalue $ irecord $ iforeign [ Rel name Equals "ordinal_position"] (ivalue $ irecord (ifield  "column_name" (ivalue $  readV PText)))


tableDef inf = 
  innerJoinS
    (fixLeftJoinS
      (fromS "tables")
      (fromS "table_description") [Rel "schema_name" Equals "table_schema", Rel "table_name" Equals "table_name"]  indexDescription  )
    (fromS "pks") [Rel "schema_name"  Equals "schema_name", Rel "table_name" Equals "table_name"]
    where 
      indexDescription = liftRel (meta inf) "table_description" $ RelAccess (Rel "description" Equals "column_name")
                            (RelAccess (Inline "col_type")
                                (RelAccess (Inline "composite")
                                    (RelComposite [Rel "schema_name" Equals "schema_name", Rel "data_name" Equals "table_name"])))  


tableProj inf =  fields
  where
      pkjoin = [Rel "schema_name" Equals "schema_name", Rel "table_name" Equals "table_name"]
      descjoin= [Rel "schema_name" Equals "table_schema", Rel "table_name" Equals "table_name"]
      compdescjoin = [Rel "schema_name" Equals "schema_name", Rel "data_name" Equals "table_name"]
      eitherDescription = isum [nestedDescription, directDescription] 
      directDescription = fmap (fmap Leaf) $ iforeign descjoin (iopt . ivalue $ irecord (ifield "description" (imap . ivalue $  readV PText)))
      nestedDescription = fmap (fmap (\(i,j) -> Tree $ NonS.zipWith (,) i j)) . iforeign descjoin  . iopt . ivalue $ irecord 
              (liftA2 (,) 
                (ifield "description" (imap . ivalue $  readV PText))
                (iforeign (relUnComp $ fmap keyValue $ liftRel (meta inf ) "table_description" $ relComp $ [Rel "description" Equals "column_name"] )
                (imap . ivalue . irecord $ (iinline "col_type" 
                  (ivalue . irecord . iinline "composite" . fmap join . iopt . ivalue $ irecord 
                    (iforeign compdescjoin 
                       . ivalue . irecord $ eitherDescription 
                        ))))))
      fields =  proc t -> do
          SText tname <-
              ifield "table_name" (ivalue (readV PText))  -< ()
          desc <-  eitherDescription -< ()
          dir <- directDescription -< ()
          pks <- iforeign pkjoin (ivalue $ irecord (iforeign [ Rel "pks" Equals "column_name"] (imap $ ivalue $ irecord (ifield  "column_name" (ivalue $  readV PText))))) -< ()
          returnA -< (tname,desc,dir,pks)
 

toListTree (Tree i ) = fst <$> i 
toListTree (Leaf i ) = i

data Tree f a 
  = Leaf { unLeaf :: f a}
  | Tree (f (a,Maybe (Tree f a)))

instance (Show a) => Show (Tree NonS.NonEmptySeq a ) where
  show (Leaf i) = show i 
  show (Tree i) = L.intercalate "\n" . F.toList $ fmap (\(i,j) -> show i <> maybe "" (\ j ->" - \n" <> (show j) ) j )  i

explodeTree (Tree f) = concat $ fmap ((\(SText i,  j) -> maybe [ Inline i]  (fmap (RelAccess (Inline i)) ) j). fmap (fmap explodeTree)) (F.toList f)
explodeTree (Leaf i) = (\(SText t) -> Inline t) <$> F.toList i



