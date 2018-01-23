{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}

module Query
  (
   tbPK
  ,tableAttrs
  ,RelSort(..)
  ,TableMap
  ,joinRel2
  ,isPrimReflexive
  ,alterKeyType
  ,searchGist
  ,rawFullName
  ,isTableRec'
  ,isKDelayed
  ,isKOptional
  ,checkGist
  ,backFKRef
  ,backFKRefType
  ,backPathRef
  ,filterReflexive
  ,isReflexive
  ,isInlineRel
  ,attrValueName
  ,mAny
  ,allRec'
  ,eitherDescPK
  ,inf'
  ,sup'
  )
  where

import Data.Tuple(swap)
import Control.Arrow (first)
import qualified Control.Lens as Le
import NonEmpty (NonEmpty(..))
import qualified Data.Vector as V
import qualified NonEmpty as Non
import Data.Time.LocalTime
import Data.Unique
import Data.Ord
import qualified Data.Poset as P
import qualified Data.Foldable as F
import qualified Data.Traversable as Tra
import Data.Maybe
import qualified Data.Interval as Interval
import Data.Monoid hiding (Product)
import qualified Data.Text as T
import qualified Data.ExtendedReal as ER
import Utils
import Control.Monad
import System.IO.Unsafe
import Control.Applicative
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.HashMap.Strict as HM
import qualified Data.Set as S
import Data.Set (Set)
import Data.Map (Map)
import Control.Monad.State
import Data.Text (Text)
import GHC.Stack
import Types
import Debug.Trace
import qualified Types.Index as G




transformKey
  :: (Eq b, Show a, Show b) =>
     KType (Prim KPrim b) -> KType (Prim KPrim b) -> FTB a -> FTB a
transformKey (Primitive l p) (Primitive l1 p1) v
  | isPrimReflexive p p1 = transformKPrim l l1 v
  | otherwise = error ("cant match prim type" ++ show (p,p1))

-- transformKey ki ko v | traceShow (ki,ko,v) False = undefined
transformKPrim
  :: Show a =>
    [KTypePrim] -> [KTypePrim]  -> FTB a -> FTB a
transformKPrim (KSerial :i)  (KOptional :j) (LeftTB1 v)  = LeftTB1 $ transformKPrim i j <$> v
transformKPrim (KOptional :i)  (KSerial :j) (LeftTB1 v)  = LeftTB1 $ transformKPrim i j <$> v
transformKPrim (KOptional :j) l (LeftTB1 v)
    | isJust v = transformKPrim j l (fromJust v)
    | otherwise = errorWithStackTrace "no transform optional nothing"
transformKPrim (KSerial :j)  l (LeftTB1 v)
    | isJust v = transformKPrim j l (fromJust v)
    | otherwise =  LeftTB1 Nothing
transformKPrim []   (KOptional :j ) v  = LeftTB1 . Just $ (transformKPrim [] j v)
transformKPrim []  (KSerial :j ) v   = LeftTB1 . Just $ (transformKPrim [] j v)
transformKPrim [] (KArray :j ) v    = ArrayTB1 . pure $ transformKPrim [] j v
transformKPrim ki kr v
    | ki == kr =  v
    | otherwise = errorWithStackTrace  ("No key transform defined for : " <> show ki <> " " <> show kr <> " " <> show v )


isKDelayed (Primitive l _)  = isJust  $ L.find (==KDelayed) l
isKOptional (Primitive (KOptional :_ ) i) = True
isKOptional _ = False


attrValueName ::  TB (FKey k) a -> Text
attrValueName (Attr i _ )= keyValue i
attrValueName (IT i  _) = keyValue i


--
-- Patch CRUD Postgresql Operations
--


rawFullName t  = rawSchema t <> "." <> rawName t


tableAttrs :: Table -> [Key]
tableAttrs r =
  L.nub $ (rawPK r <> rawDescription r  <>rawAttrs r)



labelTable :: Table ->  TBData Key ()
labelTable i = tblist $ kname <$> tableAttrs i


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
isPairPrimReflexive i op  j = errorWithStackTrace $ "isPairPrimReflexive " <> show i <> " - " <> show op <> " - " <> show  j

filterReflexive ks = L.filter (reflexiveRel ks) ks

reflexiveRel ks
--  | any (isArray . keyType . _relOrigin) ks =  (isArray . keyType . _relOrigin)
  | all (isJust . keyStatic . _relOrigin) ks = ( isJust . keyStatic. _relOrigin)
  | any (isJust . keyStatic . _relOrigin) ks = ( isNothing . keyStatic. _relOrigin)
  | any (\j -> not $ isPairReflexive (keyType (_relOrigin  j) ) (_relOperator j ) ( keyType (_relTarget j) )) ks =  const False
  | otherwise = (\j-> isPairReflexive (keyType (_relOrigin  j) ) (_relOperator j ) (keyType (_relTarget j) ))

isInlineRel (Inline _ ) =  True
isInlineRel i = False

isReflexive r@(FKJoinTable  ks  _ )
  -- |  not (t `S.isSubsetOf` (S.fromList $ fmap _relTarget ks ))  = False
  |  otherwise = isPathReflexive  r
isReflexive l  = isPathReflexive l

isPathReflexive (FKJoinTable  ks _)
  | otherwise   = all id $ fmap (\j-> isPairReflexive (keyType (_relOrigin  j) ) (_relOperator j ) (keyType (_relTarget j) )) ks
isPathReflexive (FKInlineTable _ _)= True
isPathReflexive (FunctionField _ _ _)= False
isPathReflexive (RecJoin _ i ) = isPathReflexive i


type TableMap = HM.HashMap Text (HM.HashMap Text Table)

allRec'
  :: TableMap
  -> Table
  -> TBData Key ()
allRec' invSchema r = recurseTB invSchema (tableMeta r) (rawFKS r) [] (labelTable r)


pathToRel (FKInlineTable i _ )  = [Inline i]
pathToRel (FunctionField i _ _ )  = [Inline i]
pathToRel (FKJoinTable ks _  ) = ks

findRefIT ::  Key -> KV Key () -> TB Key ()
findRefIT ifk = justError ("cant find ref" <> show ifk) . M.lookup (S.singleton $ Inline ifk ) . _kvvalues

findRefFK ::  [Key] -> KV Key ()  -> KV Key ()
findRefFK fks ksbn = kvlist $ fmap (\i -> findRefIT i ksbn ) fks

recursePath
  :: KVMetadata Key
  ->  RecState Key
  -> [(Set (Rel Key), TB Key ())]
  -> KV Key ()
  -> TableMap
  -> SqlOperation
  -> TB Key ()
-- recursePath _ _ _ _ _ _ o | traceShow o False = undefined
recursePath m isRec vacc ksbn invSchema p@(FKInlineTable ifk reft)
  =  IT ifk (recBuild p $ tb )
  where
    tb = fun (labelTable nextT)
    ks = pathToRel p
    nextT = lkSTable  invSchema reft
    fun =  recurseTB invSchema (tableMeta nextT) (rawFKS nextT) isRec
recursePath m isRec vacc ksbn invSchema jo@(FKJoinTable  ks reft)
  =  FKT (findRefs  ksbn) ks (recBuild jo $ tb)
  where
    tb = fun (labelTable nextT)
    nextT = lkSTable invSchema reft
    findRefs = findRefFK  (_relOrigin <$> filter (\i -> not $ S.member (_relOrigin i) (S.map _relOrigin $ S.unions $ fmap fst vacc)) (filterReflexive ks))
    e = S.fromList $ rawPK nextT
    fun =   recurseTB invSchema (tableMeta nextT) (rawFKS nextT) isRec
recursePath m isRec vacc ksbn invSchema jo@(RecJoin l f)
  = recursePath m (fmap (\(b,c) -> if mAny (\c -> L.null c) c  then (b,b) else (b,c)) $  isRec  ) vacc ksbn invSchema f
recursePath m isRec vacc ksbn invSchema jo@(FunctionField k l f)
  = (Fun k  (l,f) (TB1 () ))


recBuild :: SqlOperation -> (a -> FTB a)
recBuild p =
  case mergeFKRel ks of
    Primitive l o ->  F.foldl' (.) id (effect <$> l) . TB1
  where
    ks = pathToRel p
    effect :: KTypePrim  -> FTB a -> FTB a
    effect KOptional = LeftTB1 . pure
    effect KArray = ArrayTB1 .pure

lkSTable invSchema (s,t) = justError ("recursepath lookIT "  <> show t <> " " <> show invSchema) (HM.lookup t =<< HM.lookup s invSchema)

recurseTB :: TableMap -> KVMetadata Key -> [SqlOperation] -> RecState Key  -> TBData Key () ->  TBData Key ()
recurseTB invSchema m fks' isRec  kv =
  let
    items = _kvvalues kv
    fkSet:: S.Set Key
    fkSet =   S.unions . fmap (S.fromList . fmap _relOrigin . (\i -> if all isInlineRel i then i else filterReflexive i ) . S.toList . pathRelRel ) $ filter isReflexive  $ filter(not.isFunction) $ fks'
    funSet = S.unions $ fmap (S.map _relOrigin.pathRelRel) $ filter isFunction fks'
    nonFKAttrs =  M.toList $  M.filterWithKey (\i a -> not $ S.isSubsetOf (S.map _relOrigin i) (fkSet <> funSet)) items
    fklist = P.sortBy (P.comparing (RelSort . F.toList . pathRelRel)) fks'
    pt  = F.foldl (\acc  fk ->
          let relFk =pathRelRel fk
              lastItem =   L.filter cond isRec
              cond (_,l) = mAny (\l-> L.length l == 1  && ((== relFk ). S.fromList. last $ l)) l
              i = (relFk,) . recursePath m (fmap (fmap (L.drop 1 ))  <$> L.filter (\(_,i) -> mAny (\i -> (S.fromList .concat . maybeToList . safeHead $ i) == relFk ) i ) (isRec <> fmap (\i -> (i,i) ) (_kvrecrels m))) acc kv invSchema $ fk
          in if L.length lastItem < 2
                then i:acc
                else acc) [] fklist
  in (KV . M.fromList $ nonFKAttrs <> pt)

mAny f (MutRec i) = L.any f i

type RecState k = [(MutRec [[Rel k]],MutRec [[Rel k]])]




eitherDescPK :: Show a => KVMetadata Key -> TB3Data Key a -> M.Map (S.Set (Rel Key )) (Column Key a)
eitherDescPK kv i
  | not (null ( _kvdesc kv) ) =  if L.null (F.toList desc) then  pk else fromMaybe pk desc
  | otherwise = pk
    where desc = (\i -> if F.null i then Nothing else Just i). fmap (justError "") . M.filter isJust  $  fmap unLeftItens $  (_kvvalues $ tbDesc kv i)
          pk = _kvvalues $ tbPK kv i

tbDesc,tbPK :: Ord k => KVMetadata k -> TB3Data  k a ->  TB3Data  k a
tbDesc  kv =  kvFilter  (\k -> S.isSubsetOf (S.map _relOrigin k) (S.fromList $ _kvdesc kv ) )
tbPK kv = kvFilter (\k -> S.isSubsetOf (S.map _relOrigin k) (S.fromList $ _kvpk kv ) )

kvFilter :: Ord k =>  (Set (Rel k) -> Bool) -> TB3Data  k a ->  TB3Data  k a
kvFilter pred (KV item) = KV $ M.filterWithKey (\k _ -> pred k ) item

-- Combinators

kname :: Key -> TB Key ()
kname i = Attr i (TB1 ())


alterKeyType f  = Le.over keyTypes f


inf' = unFinite . Interval.lowerBound
sup' = unFinite . Interval.upperBound


data RelSort k = RelSort [Rel k] deriving (Eq,Ord)

-- To Topologically sort the elements we compare  both inputs and outputs for intersection if one matches we flip the
instance  (Ord k,Show k,P.Poset k) => P.Poset (RelSort k ) where
  compare (RelSort i ) (RelSort j)
    = case (comp (out i) (inp j) , (comp (out j) (inp i)) ,P.compare (inp i) (inp j),P.compare (out i ) (out j) ) of
            -- Reverse order
            (_ , P.LT,_,_) -> if S.size (out j) == L.length j then P.GT else P.EQ
            -- Right order
            (P.LT , _ ,_,_) -> P.LT
            -- No intersection  between elements sort by inputset
            (_,_ ,P.EQ,o) -> o
            (_,_ ,i,_) -> i

    where
      inp j= norm $ _relInputs <$> j
      out j = norm $ _relOutputs <$> j
      norm  = S.fromList . concat . catMaybes
      comp i j  | S.null (S.intersection i j ) = P.EQ
      comp i j  | S.empty == i = P.EQ
      comp i j  | S.empty == j  = P.EQ
      comp i j = P.compare i j
  compare (RelSort [i] ) (RelSort [j]) = P.compare i j
  compare (RelSort [i] ) (RelSort j) = P.compare (S.singleton i ) (S.fromList j) <> if L.any (==P.EQ) (P.compare i <$> j) then P.LT else foldl1 mappend  (P.compare i <$> j)
  compare (RelSort i ) (RelSort [j]) = P.compare (S.fromList i) (S.singleton j ) <> if L.any (==P.EQ) (flip P.compare j <$> i) then P.GT else foldl1 mappend (flip P.compare j <$> i)
  compare (RelSort i ) (RelSort j ) = P.compare (S.fromList i) (S.fromList j)

instance (Show i,P.Poset i )=> P.Poset (Rel i)where
  compare  (Inline i ) (Inline j) = P.compare i j
  compare  (Rel i _ a ) (Inline j ) = case i == j of
                                        True -> P.GT
                                        False -> P.compare i j
  compare  (Inline j )(Rel i _ a )  = case i == j of
                                        True -> P.LT
                                        False -> P.compare j i
  compare  (Rel i _ a ) (Rel j _ b) = P.compare i j <> P.compare a b
  compare  n@(RelFun i  ex a ) o@(RelFun j ex2 k)  = case  (L.any (== Inline j) a,L.any (==Inline i) k)  of
                                          (True ,_)-> P.GT
                                          (_,True)-> P.LT
                                          (False,False)-> P.compare (Inline i) (Inline j)
  compare  (RelFun i e a ) j  = case L.any (== j) a  of
                                          True -> P.GT
                                          False -> P.compare (Inline i) j
  compare   j (RelFun i e a )= case L.any (== j) a  of
                                          True -> P.LT
                                          False -> P.compare j (Inline i)

  compare i j = errorWithStackTrace (show (i,j))


instance P.Poset (FKey i)where
  compare  i j = case compare (keyPosition i) (keyPosition j) of
                      EQ -> P.EQ
                      LT -> P.LT
                      GT -> P.GT



backPathRef ::  SqlOperation -> TBData Key Showable ->  [Column Key Showable]
backPathRef (FKJoinTable rel t) = justError ("no back path ref "  ++ show rel ). backFKRef (M.fromList $ fmap (\i -> (_relTarget i ,_relOrigin i)) rel) (_relOrigin<$> rel)

backFKRefType
  :: (Show a) =>
     M.Map Key Key
     -> M.Map Key CorePrim
     -> [Key]
     -> TBData  Key a
     -> Maybe [ TB Key a]
backFKRefType i j  k  | traceShow (i ,j,k) False =  undefined
backFKRefType relTable relType ifk = fmap (fmap (uncurry Attr)) . nonEmpty . catMaybes . traceShowId . reorderPK .  concat . fmap aattr . F.toList .  _kvvalues
  where
    reorderPK l = fmap (\i  -> L.find ((== i).fst) (catMaybes (fmap lookFKsel l) ) )  ifk
    lookFKsel (ko,v)=  (\kn tkn -> (kn ,transformKey (keyType ko ) (Primitive [] tkn) v)) <$> knm <*> tknm
        where
          knm =  M.lookup ko relTable
          tknm =  M.lookup ko relType


backFKRef
  :: (Show a) =>
     M.Map Key Key
     -> [ Key]
     -> TBData  Key a
     -> Maybe [ TB Key a]
-- backFKRef i j  | traceShow (i ,j) False =  undefined
backFKRef relTable ifk = fmap (fmap (uncurry Attr)) . nonEmpty . catMaybes . reorderPK .  concat . fmap aattr . F.toList .  _kvvalues
  where
    reorderPK l = fmap (\i  -> L.find ((== i).fst) (catMaybes (fmap lookFKsel l) ) )  ifk
    lookFKsel (ko,v)=  (\kn -> (kn ,transformKey (keyType ko ) (keyType kn) v)) <$> knm
          where knm =  M.lookup ko relTable


tbpred un  = G.notOptional . G.getUnique un

tbpredFK
  ::  ( Show k,Ord k)
  => M.Map k k
  -> [k]
  -> [k]
  -> [(k,FTB a1)] ->  Maybe (G.TBIndex a1)
tbpredFK rel un  pk2 v = tbjust  .  Tra.traverse (Tra.traverse unSOptional') . fmap (first (\k -> justError (show k) $ M.lookup k (flipTable  rel ))).  filter ((`S.member` S.fromList un). fst )  $ v
        where
          flipTable = M.fromList . fmap swap .M.toList
          tbjust = fmap (G.Idex . fmap snd.L.sortBy (comparing ((`L.elemIndex` pk2).fst)))

{-searchGist ::
  (Functor t,  Ord a1,Ord (G.Tangent a1),G.Predicates a1,Show a ,Show a1,Ord k,  Show k,
   Foldable t, G.Predicates (FTB a1) ,G.Predicates (G.TBIndex  a1)) =>
  M.Map k k
  -> KVMetadata k
  -> G.GiST (G.TBIndex  a1) a
  -> [([k],G.GiST (G.TBIndex  a1) (G.TBIndex a1))]
  -> t (TB Identity k a1)
  -> Maybe a-}
-- searchGist  i j k l m  | traceShow (i, fmap fst l,m) False = undefined
searchGist relTable m gist sgist i =  join $ foldl (<|>) ((\pkg -> lookGist relTable pkg i gist) <$> (  allMaybes$ fmap (\k->  M.lookup k relTable) (rawPK m) ))  (((\(un,g) -> lookSIdx  un i g) <$> sgist) )
  where
    lookGist rel un pk  v =  join res
      where res = flip G.lookup v <$> tbpredFK rel un (rawPK m) pk

    lookSGist sidsx rel un pk  v =  join res
      where res = fmap fst .flip G.lookup v <$> tbpredFK rel un sidsx pk

    lookSIdx un pk sg = join . fmap (\i -> G.lookup i gist ) . (\i -> lookSGist  un relTable i  pk sg) <$> (allMaybes $  fmap (\k -> M.lookup k relTable ) un  )

joinRel2 :: (Show k , Ord k,Ord a ,Show a,G.Predicates (G.TBIndex a)) => KVMetadata k->  [(Rel k ,FTB a)] -> G.GiST (G.TBIndex a) (TBData k a) -> Maybe (FTB (TBData k a))
joinRel2 tb ref table
  | L.any (isLeft.snd) ref
  = Just $ LeftTB1  $ join $ fmap (flip (joinRel2 tb ) table) (Tra.traverse (traverse unSOptional) ref )
  | L.any (isArray.snd) ref
  = let
      !arr = justError ("no array"<> show ref )$ L.find (isArray .snd) ref
   in join .fmap ( fmap (ArrayTB1 .  Non.fromList ).nonEmpty) $Tra.sequenceA   $ fmap (flip (joinRel2 tb ) table . (:L.filter (not .isArray .snd) ref)) (fmap (\i -> (fst arr,) . justError ("cant index  " <> show (i,ref)). (flip Non.atMay i) $ unArray $ snd arr ) [0..(Non.length (unArray $ snd arr)   - 1)])
  | otherwise
    =  TB1 <$> tbel
      where
            isLeft (LeftTB1 i) = True
            isLeft i = False
            isArray (ArrayTB1 i) = True
            isArray i = False
            idx = G.Idex $ fmap snd $ L.sortBy (comparing (flip L.elemIndex (_kvpk tb). _relTarget .fst )) ref
            tbel = G.lookup idx table


checkGist un pk  m = maybe False (\i -> not $ L.null $ G.search i m ) (tbpredM un pk)

tbpredM un  = G.notOptionalM . G.getUnique un
