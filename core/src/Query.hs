{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}

module Query
  (
  TableMap
  ,joinRel2
  ,isPrimReflexive
  ,alterKeyType
  ,searchGist
  ,rawFullName
  ,isTableRec'
  ,isKOptional
  ,checkGist
  ,backFKRef
  ,reflectFK
  ,backPathRef
  ,transformKey
  ,transformKeyList
  ,filterReflexive
  ,isReflexive
  ,isInlineRel
  ,mAny
  ,allRec'
  ,inf'
  ,sup'
  ,eitherDescPK
  ,tbPK
  )
  where

import Data.Tuple(swap)
import Control.Arrow (first)
import qualified Control.Lens as Le
import Debug.Trace
import qualified NonEmpty as Non
import qualified Data.Sequence.NonEmpty as NonS
import Data.Ord
import qualified Data.Poset as P
import qualified Data.Foldable as F
import qualified Data.Traversable as Tra
import Data.Maybe
import qualified Data.Interval as Interval
import Data.Monoid hiding (Product)
import Utils
import Control.Monad
import Control.Applicative
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.HashMap.Strict as HM
import qualified Data.Set as S
import Data.Set (Set)
import Data.Text (Text)
import Types
import qualified Types.Index as G



transformKeyList
  :: (Eq b, Show a, Show b) =>
     KType [Prim KPrim b] -> KType [Prim KPrim b] -> FTB a -> FTB a
transformKeyList (Primitive l p) (Primitive l1 p1) v
  | l == l1 = v
  | all id $ zipWith isPrimReflexive p p1 = transformKPrim l l1 v
  | otherwise = error ("cant match prim type" ++ show (p,p1))


transformKey
  :: (Eq b, Show a, Show b) =>
     KType (Prim KPrim b) -> KType (Prim KPrim b) -> FTB a -> FTB a
transformKey (Primitive l p) (Primitive l1 p1) v
  | l == l1 = v
  | isPrimReflexive p p1 = transformKPrim l l1 v
  | otherwise = error ("cant match prim type" ++ show (p,p1))

transformKPrim
  :: Show a =>
    [KTypePrim] -> [KTypePrim]  -> FTB a -> FTB a
transformKPrim (KSerial :i)  (KOptional :j) (LeftTB1 v)  = LeftTB1 $ transformKPrim i j <$> v
transformKPrim (KOptional :i)  (KSerial :j) (LeftTB1 v)  = LeftTB1 $ transformKPrim i j <$> v
transformKPrim (KOptional :j) l (LeftTB1 v)
  | isJust v = transformKPrim j l (justError " no prim" v)
  | otherwise = error "no transform optional nothing"
transformKPrim (KSerial :j)  l (LeftTB1 v)
  | isJust v = transformKPrim j l (justError " no prim" v)
  | otherwise =  LeftTB1 Nothing
transformKPrim i (KOptional :j ) v  | i == j = LeftTB1 . Just $ (transformKPrim i j v)
transformKPrim i (KSerial :j ) v  | i == j = LeftTB1 . Just $ (transformKPrim i j v)
transformKPrim i (KArray :j ) v  | i == j  = ArrayTB1 . pure $ transformKPrim i j v
transformKPrim ki kr v
    | ki == kr =  v
    | otherwise = error ("No key transform defined for : " <> show ki <> " " <> show kr <> " " <> show v )


isKOptional (Primitive (KOptional :_ ) i) = True
isKOptional _ = False


--
-- Patch CRUD Postgresql Operations
--



labelTable :: Table ->  TBData Key ()
labelTable i = kvlist $ kname <$> rawAttrs i

isTableRec' tb = not $ L.null $ _kvrecrels (fst  tb )


isPrimReflexive :: Eq b => Prim KPrim b -> Prim KPrim b -> Bool
isPrimReflexive i j | i == j = True
isPrimReflexive (AtomicPrim (PInt i)) (AtomicPrim (PInt j)) = True
isPrimReflexive (AtomicPrim (PDimensional _ i)) (AtomicPrim (PDouble )) = True
isPrimReflexive (AtomicPrim PDouble ) (AtomicPrim (PDimensional _ _ )) = True
isPrimReflexive (AtomicPrim (PDimensional _ _ )) (AtomicPrim (PDimensional  _ _ )) = True
isPrimReflexive a b = False

isPairReflexive :: (Show b , Eq b) => KType (Prim KPrim b ) -> BinaryOperator -> KType (Prim KPrim b) -> Bool
isPairReflexive (Primitive l a) op (Primitive l1 a1) =  isPairPrimReflexive l op l1 &&  isPrimReflexive a a1


isPairPrimReflexive :: [KTypePrim]  -> BinaryOperator -> [KTypePrim]  -> Bool
isPairPrimReflexive i   IntersectOp j = False
isPairPrimReflexive [] op (KInterval :[])  = False
isPairPrimReflexive [] op  (KArray :[])   = False
isPairPrimReflexive (KInterval : i) op (KInterval :j)
  | i == j && op == Contains = False
  | op == Equals = isPairPrimReflexive i op j
isPairPrimReflexive [] op [] = True
isPairPrimReflexive (KOptional : i) op  j = isPairPrimReflexive i op j
isPairPrimReflexive i  op (KOptional :j) = isPairPrimReflexive i op j
isPairPrimReflexive (KSerial:i) op j = isPairPrimReflexive i op j
isPairPrimReflexive i op (KSerial:j) = isPairPrimReflexive i op j
isPairPrimReflexive (KArray :i )  op  (KArray : j)
  | i == j  && op == Contains = False
  | op == Equals = isPairPrimReflexive i op j
isPairPrimReflexive (KArray : i )  (AnyOp op ) j = isPairPrimReflexive i op j
isPairPrimReflexive i   (Flip IntersectOp) j = False
isPairPrimReflexive j op (KArray :i )  = False
isPairPrimReflexive i op  j = error $ "isPairPrimReflexive " <> show i <> " - " <> show op <> " - " <> show  j

filterReflexive ks = L.filter (reflexiveRel ks) ks

reflexiveRel ks
  | any (isArray . keyType . _relOrigin) ks =  (isArray . keyType . _relOrigin)
  | all (isJust . keyStatic . _relOrigin) ks = ( isJust . keyStatic. _relOrigin)
  | any (isJust . keyStatic . _relOrigin) ks = ( isNothing . keyStatic. _relOrigin)
  | any (\j -> not $ isPairReflexive (keyType (_relOrigin  j) ) (_relOperator j ) ( relType (_relTarget j) )) ks =  const False
  | otherwise = (\j-> isPairReflexive (keyType (_relOrigin  j) ) (_relOperator j ) (relType (_relTarget j) ))

isInlineRel (Inline _ ) =  True
isInlineRel i = False

isReflexive r@(FKJoinTable  ks  _ )
  -- |  not (t `S.isSubsetOf` (S.fromList $ fmap _relTarget ks ))  = False
  |  otherwise = isPathReflexive  r
isReflexive l  = isPathReflexive l

isPathReflexive (FKJoinTable  ks _)
  | otherwise   = all id $ fmap (\j-> isPairReflexive (keyType (_relOrigin  j) ) (_relOperator j ) (relType (_relTarget j) )) ks
isPathReflexive (FKInlineTable _ _)= True
isPathReflexive (FunctionField _ _ _)= False
isPathReflexive (RecJoin _ i ) = isPathReflexive i


type TableMap = HM.HashMap Text (HM.HashMap Text Table)

allRec'
  :: TableMap
  -> Table
  -> TBData Key ()
allRec' invSchema r = recurseTB invSchema [] r


pathToRel (FKInlineTable i _ )  = [Inline i]
pathToRel (FunctionField i _ _ )  = [Inline i]
pathToRel (FKJoinTable ks _  ) = ks


findRefFK ::  [Key] -> KV Key ()  -> KV Key ()
findRefFK fks ksbn = kvlist $ fmap (\i -> findRefIT i ksbn ) fks
  where
    findRefIT ::  Key -> KV Key () -> TB Key ()
    findRefIT ifk = justError ("cant find ref" <> show ifk) . findAttr  ifk

recursePath
  :: RecState Key
  -> [(Set (Rel Key), TB Key ())]
  -> KV Key ()
  -> TableMap
  -> SqlOperation
  -> TB Key ()
recursePath  isRec vacc ksbn invSchema p@(FKInlineTable ifk reft)
  =  IT ifk (recBuild p tb)
  where
    tb = fun nextT
    ks = pathToRel p
    nextT = lkSTable  invSchema reft
    fun =  recurseTB invSchema  isRec
recursePath  isRec vacc ksbn invSchema jo@(FKJoinTable  ks reft)
  =  FKT (findRefs  ksbn) ks (recBuild jo tb)
  where
    tb = fun nextT
    nextT = lkSTable invSchema reft
    oldRef = S.unions $ fmap (S.map _relOrigin . fst) vacc
    noldRef = filter (\i -> not $ S.member (_relOrigin i) oldRef ) (filterReflexive ks)
    findRefs = findRefFK  (_relOrigin <$> noldRef)
    e = S.fromList $ rawPK nextT
    fun =   recurseTB invSchema  isRec
recursePath  isRec vacc ksbn invSchema (RecJoin l f)
  = recursePath  (fmap (\(b,c) -> if mAny (\c -> L.null c) c  then (b,b) else (b,c)) $  isRec  ) vacc ksbn invSchema f
recursePath  isRec vacc ksbn invSchema (FunctionField k l f)
  = (Fun k  (l,f) (TB1 () ))


recBuild :: SqlOperation -> (a -> FTB a)
recBuild p =
  case mergeFKRef (keyType . _relOrigin<$> ks) of
    Primitive l _ ->  F.foldl' (.) id (effect <$> l) . TB1
  where
    ks = pathToRel p
    effect :: KTypePrim  -> FTB a -> FTB a
    effect KOptional = LeftTB1 . pure
    effect KArray = ArrayTB1 .pure

lkSTable invSchema (s,t) = justError ("recursepath lookIT: "  <> show (s,t) <> " " <> show (HM.keys invSchema, HM.lookup s invSchema)) (HM.lookup t =<< HM.lookup s invSchema)

recurseTB :: TableMap -> RecState Key  -> Table ->  TBData Key ()
recurseTB invSchema isRec table =
  let
    m = tableMeta table
    fks' = rawFKS table
    kv = labelTable table
    items = kv
    fkSet:: S.Set Key
    fkSet =   S.unions . fmap (S.fromList . fmap _relOrigin . (\i -> if all isInlineRel i then i else filterReflexive i ) . S.toList . pathRelRel ) $ filter isReflexive  $ fks'
    funSet = S.unions $ fmap (S.map _relOrigin.pathRelRel) $ functionRefs table
    nonFKAttrs =  kvFilter (\i -> not $ S.isSubsetOf (relOutputSet i) (fkSet <> funSet)) items
    fklist = P.sortBy (P.comparing (S.map _relOrigin <$> pathRelRel )) fks' <> functionRefs table
    pt  = F.foldl' (\acc  fk ->
          let relFk =pathRelRel fk
              lastItem =   L.filter cond isRec
              cond (_,l) = mAny (\l-> L.length l == 1  && ((== relFk ). S.fromList. last $ l)) l
              i = (relFk,) .  recursePath  (fmap (fmap (L.drop 1 ))  <$> L.filter (\(_,i) -> mAny (\i -> (S.fromList .concat . maybeToList . safeHead $ i) == relFk ) i ) (isRec <> fmap (\i -> (i,i) ) (_kvrecrels m))) acc kv invSchema $ fk
          in if L.length lastItem < 2
                then i:acc
                else acc) [] fklist
  in (nonFKAttrs <> kvlist (snd <$> pt))

mAny f (MutRec i) = L.any f i

type RecState k = [(MutRec [[Rel k]],MutRec [[Rel k]])]



eitherDescPK :: Show a => KVMetadata Key -> TBData Key a -> KV  Key a
eitherDescPK kv i
  | not (null (_kvdesc kv)) = fromMaybe pk desc
  | otherwise = pk
    where desc =   (\i -> if L.null i then Nothing else Just (kvlist i)). fmap (justError "") . filter isJust  $  fmap unLeftItens $  (unkvlist $ tbDesc kv i)
          pk = tbPK kv i

tbDesc, tbPK :: Ord k => KVMetadata k -> TBData  k a ->  TBData  k a
tbDesc  kv =  kvFilter  (\k -> S.isSubsetOf (relOutputSet k) (S.unions $ relOutputSet <$> _kvdesc kv))
tbPK kv = kvFilter (\k -> S.isSubsetOf (relOutputSet k) (S.unions $ relOutputSet <$> _kvpk kv ))

-- Combinators

kname :: Key -> TB Key ()
kname i = Attr i (TB1 ())


alterKeyType f  = Le.over keyTypes f


inf' = unFinite . Interval.lowerBound
sup' = unFinite . Interval.upperBound


backPathRef ::  SqlOperation -> TBData Key Showable ->  [Column Key Showable]
backPathRef (FKJoinTable rel t) = justError ("no back path ref "  ++ show rel ). backFKRef (M.fromList $ fmap (\i -> (_relOrigin $ _relTarget i ,_relOrigin i)) rel) (_relOrigin<$> rel)

backFKRefType
  :: Show a =>
     M.Map Key Key
     -> M.Map Key (KType CorePrim)
     -> [Key]
     -> TBData  Key a
     -> Maybe [ TB Key a]
backFKRefType relTable relType ifk = fmap (fmap (uncurry Attr)) . nonEmpty . catMaybes . reorderPK . concat . fmap aattr . unkvlist
  where
    reorderPK  = fmap lookFKsel
    lookFKsel (ko,v)=  join $ transformType <$> knm <*> tknm
        where
          transformType kn tkn
            | isSerial (keyType ko) =  (kn ,)  <$> unSOptional  (transformKey (keyType ko) tkn v)
            | otherwise =  Just (kn , transformKey (keyType ko) tkn v)
          knm = M.lookup ko relTable
          tknm =  M.lookup ko relType

reflectFK
  :: Show a => [Rel Key] -> TBData Key a -> Maybe (TBData Key a)
reflectFK [] i = pure mempty
reflectFK rel table =
  kvlist <$> backFKRefType relTable relType (_relOrigin <$> rel) table
      where
        Primitive _ c = mergeFKRel rel
        relTable = M.fromList $ (\i -> (_relOrigin $ _relTarget i, _relOrigin i)) <$> rel
        unKSerial (Primitive l c ) = Primitive (filter  (/= KSerial) l) c
        relType = M.fromList $ zip (_relOrigin . _relTarget <$> rel ) (unKSerial .snd <$> c)


backFKRef
  :: Show a =>
     M.Map Key Key
     -> [Key]
     -> TBData  Key a
     -> Maybe [ TB Key a]
backFKRef relTable ifk = fmap (fmap (uncurry Attr)) . nonEmpty . catMaybes . reorderPK .  concat . fmap aattr . unkvlist
  where
    reorderPK l = fmap (\i  -> L.find ((== i).fst) (catMaybes (fmap lookFKsel l) ) )  ifk
    lookFKsel (ko,v)=  (\kn -> (kn ,transformKey (keyType ko ) (keyType kn) v)) <$> knm
          where knm =  M.lookup ko relTable


tbpred m un  = G.notOptional . G.getUnique  un

tbpredFK
  ::  ( Show k,Ord k)
  => M.Map (Rel k) (Rel k)
  -> [Rel k]
  -> [Rel k]
  -> KV k a1 ->  Maybe (TBIndex a1)
tbpredFK rel un  pk2 v  = tbjust . Tra.traverse (Tra.traverse unSOptional) . fmap (first projectRel).  filter ((`S.member` S.fromList un). fst )  $ M.toList (kvToMap v)
  where
    projectRel k = justError (show k) $ M.lookup k (flipTable  rel )
    flipTable = M.fromList . fmap swap .M.toList
    tbjust = fmap (Idex . fmap snd.L.sortBy (comparing ((`L.elemIndex` (simplifyRel <$> pk2)). simplifyRel.fst)))

{-searchGist ::
  (Functor t,  Ord a1,Ord (G.Tangent a1),G.Predicates a1,Show a ,Show a1,Ord k,  Show k,
   Foldable t, G.Predicates (FTB a1) ,G.Predicates (TBIndex  a1)) =>
  M.Map k k
  -> KVMetadata k
  -> G.GiST (TBIndex  a1) a
  -> [([k],G.GiST (TBIndex  a1) (TBIndex a1))]
  -> t (TB Identity k a1)
  -> Maybe a-}
searchGist rel m gist sgist i =  join $ foldl (<|>) ((\pkg -> lookGist relTable pkg i gist) <$> (  allMaybes$ fmap (\k->  M.lookup k relTable) (rawPK m) ))  (((\(un,g) -> lookSIdx  un i g) <$> M.toList sgist) )
  where
    relTable = M.fromList $ fmap (\(Rel i _ j ) -> (j,i)) rel
    lookGist rel un pk  v =  join res
      where res = flip G.lookup v <$> tbpredFK rel un (rawPK m) pk

    lookSGist sidsx rel un pk  v =  join res
      where res = fmap M.keys .flip G.lookup v <$> tbpredFK rel un sidsx pk

    lookSIdx un pk sg = join . fmap (\i -> G.lookup i gist ) . join . fmap safeHead . (\i -> lookSGist  un relTable i  pk sg) <$> (allMaybes $  fmap (\k -> M.lookup k relTable ) un  )

joinRel2
  :: (Show k , Ord k,Ord a ,Show a,G.Predicates (TBIndex a)) 
   => KVMetadata k
   -> [(Rel k ,FTB a)]
   -> G.GiST (TBIndex a) (TBData k a) 
   -> Maybe (FTB (TBData k a))
joinRel2 tb ref table = recurse ref
  where
    recurse ref 
      | L.any (isLeft.snd) ref -- || L.any (isKOptional .keyType ._relOrigin .fst )  ref
        = Just $ LeftTB1  $ join $ fmap recurse  (Tra.traverse (traverse unSOptional) ref )
      | L.any (isArray.snd) ref
        = let
            arr = justError ("no array"<> show ref )$ L.find (isArray .snd) ref
            arrayTB1 =  fmap (ArrayTB1 .  NonS.fromList ).nonEmpty
         in  join . fmap arrayTB1 . Tra.sequenceA   $ fmap (recurse . (:L.filter (not .isArray .snd) ref)) 
              (fmap (\i -> (fst arr,) . justError ("cant index  " <> show (i,ref)). (flip NonS.atMay i) $ unArray $ snd arr ) 
              [0..(NonS.length (unArray $ snd arr)   - 1)])
      | otherwise
        =  TB1 <$> G.lookup idx table
        where
          debug = (_kvname tb ,renderRel .simplifyRel <$> _kvpk tb ,  _relTarget .fst <$> ref, (flip L.elemIndex (simplifyRel <$> _kvpk tb). _relTarget .fst ) <$> ref ,idx)
          idx = Idex $ fmap snd $ L.sortBy (comparing (justError (show debug).flip  L.elemIndex (simplifyRel <$> _kvpk tb). _relTarget .fst )) ref

    isLeft (LeftTB1 i) = True
    isLeft i = False
    isArray (ArrayTB1 i) = True
    isArray i = False



checkGist un pk  m = maybe False (\i -> not $ L.null $ G.search i m ) (tbpredM un pk)

tbpredM un  = G.notOptionalM . G.getUnique  un
