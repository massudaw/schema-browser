{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}

module Query
  (
  tbPK
  ,joinRel
  ,alterKeyType
  ,forceDAttr
  ,rawFullName
  ,unComp
  ,isTableRec
  ,tbFilterE
  ,intersectionOp
  ,isKDelayed
  ,isKOptional
  ,tlabel
  ,tableView
  ,unTlabel'
  ,interPointPost
  ,PGRecord
  ,PGType
  ,PGKey
  ,CoreKey
  ,CorePrim
  ,backFKRef
  ,filterReflexive
  ,isReflexive
  ,isInlineRel
  ,attrValueName
  ,diffUpdateAttr
  ,relabelT
  ,showTable
  ,tbPK'
  ,relabelT'
  ,mAny
  ,allKVRec
  ,allRec'
  ,tableViewNR
  ,inf'
  ,sup'
  ,tbAttr
  )
  where

import qualified Control.Lens as Le
import NonEmpty (NonEmpty(..))
import qualified NonEmpty as Non
import Data.Functor.Apply
import Data.Time.LocalTime
import Data.Unique
import Data.Functor.Identity
import Data.Ord
import qualified Data.Poset as P
import qualified Data.Foldable as F
-- import Data.Traversable (mapAccumL)
import qualified Data.Traversable as Tra
import Data.Maybe
import qualified Data.Interval as Interval
import Data.Monoid hiding (Product)

import qualified Data.Text as T
import qualified Data.ExtendedReal as ER

import Utils


import Prelude hiding (head)
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



transformKey (KSerial i)  (KOptional j) (SerialTB1 v)  | i == j = LeftTB1  v
transformKey (KOptional i)  (KSerial j) (LeftTB1 v)  | i == j = SerialTB1 v
transformKey (KOptional j) l (LeftTB1  v)
    | isJust v = transformKey j l (fromJust v)
    | otherwise = errorWithStackTrace "no transform optional nothing"
transformKey (KSerial j)  l (SerialTB1 v)
    | isJust v = transformKey j l (fromJust v)
    | otherwise =  DelayedTB1 Nothing
transformKey l@(Primitive _)  (KOptional j ) v  = LeftTB1 $ Just (transformKey l j v)
transformKey l@(Primitive _)  (KSerial j ) v   = SerialTB1 $ Just (transformKey l j v)
transformKey l@(Primitive _)  (KArray j ) v | j == l  = ArrayTB1 $ pure v
transformKey ki kr v | ki == kr = v
transformKey ki kr  v = errorWithStackTrace  ("No key transform defined for : " <> show ki <> " " <> show kr <> " " <> show v )





isKDelayed (KDelayed i) = True
isKDelayed (KSerial i) = isKDelayed i
isKDelayed (KOptional i) = isKDelayed i
isKDelayed (KInterval i) = isKDelayed i
isKDelayed (KArray i)  = isKDelayed i
isKDelayed _ = False


isKOptional (KOptional i) = True
isKOptional (KSerial i) = isKOptional i
isKOptional (KInterval i) = isKOptional i
isKOptional (Primitive _) = False
isKOptional (KArray i)  = isKOptional i
-- isKOptional i = errorWithStackTrace (show ("isKOptional",i))



getPrim i@(Primitive _ ) = i
getPrim (KOptional j) =  getPrim j
getPrim (KDelayed j) =  getPrim j
getPrim (KSerial j) =  getPrim j
getPrim (KArray j) =  getPrim j
getPrim (KInterval j) =  getPrim j

inner b l m = l <> b <> m

-- Operators

intersectionOp :: (Eq b,Show (KType (Prim KPrim b ))) => KType (Prim KPrim b)-> Text -> KType (Prim KPrim b)-> (Text -> Text -> Text)
intersectionOp (KOptional i) op (KOptional j) = intersectionOp i op j
intersectionOp i op (KOptional j) = intersectionOp i op j
intersectionOp (KOptional i) op j = intersectionOp i op j
intersectionOp (KInterval i) op (KInterval j )  = inner op
intersectionOp (KArray i) op  (KArray j )  = inner op
intersectionOp (KInterval i) op j
    | getPrim i == getPrim j =  inner op
    | otherwise = errorWithStackTrace $ "wrong type intersectionOp " <> show i <> " /= " <> show j
intersectionOp i op (KInterval j)
    | getPrim i == getPrim j = inner "<@"
    | otherwise = errorWithStackTrace $ "wrong type intersectionOp " <> show i <> " /= " <> show j
intersectionOp (KArray i ) op  j
    | i == getPrim j = (\j i -> i <> " IN (select * from unnest("<> j <> ") ) ")
    | otherwise = errorWithStackTrace $ "wrong type intersectionOp {*} - * " <> show i <> " /= " <> show j
intersectionOp j op (KArray i )
    | getPrim i == getPrim j = (\i j  -> i <> " IN (select * from unnest("<> j <> ") ) ")
    | otherwise = errorWithStackTrace $ "wrong type intersectionOp * - {*} " <> show j <> " /= " <> show i
intersectionOp i op j = inner op

showTable t  = rawSchema t <> "." <> rawName t




diffUpdateAttr :: (Ord k , Ord a) => TBData k a -> TBData k a -> Maybe (TBData k a )
diffUpdateAttr  kv kold@(t,_ )  =  fmap ((t,) . _tb . KV ) .  allMaybesMap  $ liftF2 (\i j -> if i == j then Nothing else Just i) (unKV . snd . tableNonRef'  $ kv ) (unKV . snd . tableNonRef' $ kold )


attrValueName :: (Ord a,Ord k, Show k ,Show a) => TB Identity (FKey k) a -> Text
attrValueName (Attr i _ )= keyValue i
attrValueName (IT i  _) = overComp attrValueName i
attrValueName i = errorWithStackTrace $ " no attr value instance " <> show i


--
-- Patch CRUD Postgresql Operations
--




rawFullName = showTable


allKVRec :: Ord f => TB2 f Showable -> [FTB Showable]
allKVRec = concat . F.toList . fmap allKVRec'

allKVRec' :: Ord k => TBData k  Showable -> [FTB Showable]
allKVRec'  t@(m, e)=  concat $ fmap snd $ L.sortBy (comparing (\i -> maximum $ (`L.elemIndex` _kvdesc m)  <$> (fmap _relOrigin $ F.toList $fst i) ))  $ M.toList (go . unTB <$> (_kvvalues $ unTB $ eitherDescPK t))
  where
        go  (FKT _  _ tb) =  allKVRec  tb
        go  (IT  _ tb) = allKVRec tb
        go  (Attr _ a) = [a]


tableToKV r =   do
   ((rawPK r)) <> (rawDescription r)  <>(S.toList (rawAttrs r))

labelTable :: Table -> State ((Int, Map Int Table), (Int, Map Int Key)) (Labeled Text Table,TB3Data (Labeled Text)  Key  () )
labelTable i = do
   t <- tname i
   name <- Tra.traverse (\k-> (S.singleton (Inline k),) <$> kname t k ) (tableToKV i)
   return (t, (tableMeta i,) $ Compose $ Labeled (label t) $ KV $ M.fromList $ fmap Compose <$> name)

unComp :: (Show (g k a) ,F.Foldable f ) => Compose f g k a -> g k a
unComp = head . F.toList . getCompose

isTableRec tb = isTableRec'  (unTB1 tb )
isTableRec' tb = not $ L.null $ _kvrecrels (fst  tb )


isPairReflexive (Primitive i ) op (KInterval (Primitive j)) | i == j = False
isPairReflexive (Primitive j) op  (KArray (Primitive i) )  | i == j = False
isPairReflexive (KInterval i) op (KInterval j)
  | i == j && op == "<@" = False
  | i == j && op == "=" = True
isPairReflexive (Primitive i ) op (Primitive j) | i == j = True
isPairReflexive (KOptional i ) op  j = isPairReflexive i op j
isPairReflexive i  op (KOptional j) = isPairReflexive i op j
isPairReflexive (KSerial i) op j = isPairReflexive i op j
isPairReflexive i op (KSerial j) = isPairReflexive i op j
isPairReflexive (KArray i )  op  (KArray j)
  | i == j  && op == "<@" = False
  | i == j  && op == "=" = True
isPairReflexive (KArray i )  op  j = True
isPairReflexive i op  j = errorWithStackTrace $ "isPairReflexive " <> show i <> " - "<> show  j

filterReflexive ks = L.filter (reflexiveRel ks) ks

reflexiveRel ks
  | any (isArray . keyType . _relOrigin) ks =  (isArray . keyType . _relOrigin)
  | all (isJust . keyStatic . _relOrigin) ks = ( isJust . keyStatic. _relOrigin)
  | any (isJust . keyStatic . _relOrigin) ks = ( isNothing . keyStatic. _relOrigin)
  | any (\j -> not $ isPairReflexive (keyType (_relOrigin  j) ) (_relOperator j ) ( keyType (_relTarget j) )) ks =  const False
  | otherwise = (\j-> isPairReflexive (keyType (_relOrigin  j) ) (_relOperator j ) (keyType (_relTarget j) ))

isInlineRel (Inline _ ) =  True
isInlineRel i = False

isReflexive (Path i r@(FKJoinTable _ ks _ )  t)
  |  not (t `S.isSubsetOf` (S.fromList $ fmap _relTarget ks ))  = False
  |  otherwise = isPathReflexive  r
isReflexive (Path _ l _ ) = isPathReflexive l

isPathReflexive (FKJoinTable _ ks _)
  | otherwise   = all id $ fmap (\j-> isPairReflexive (keyType (_relOrigin  j) ) (_relOperator j ) (keyType (_relTarget j) )) ks
isPathReflexive (FKInlineTable _)= True
isPathReflexive (RecJoin _ i ) = isPathReflexive i



allRec'
  :: Map Text Table
     -> Table
     -> TBData Key ()
allRec' i t = unTlabel' $ tableView  i t

tableView  invSchema r = fst $ flip runState ((0,M.empty),(0,M.empty)) $ do
  when (L.null $ rawPK r) (fail $ "cant generate ast for table " <> T.unpack (tableName r ) <> " the pk is null")
  (t,ks) <- labelTable r
  tb <- recurseTB invSchema (rawFKS r) False [] ks
  return  $ tb

tableViewNR invSchema r = fst $ flip runState ((0,M.empty),(0,M.empty)) $ do
  when (L.null $ rawPK r) (fail $ "cant generate ast for table " <> T.unpack (tableName r )<> " the pk is null")
  (t,ks) <- labelTable r
  tb <- recurseTB invSchema (S.filter (all isInlineRel. F.toList .pathRelRel)$ rawFKS r) False [] ks
  return  $ TB1 tb




--- Note [InlinableRec]
-- when some base table has a recursive inlinable field we need to
-- open the table reach the recursive attr, perform a with recursive query
-- with field and index tagging , then recover the base table
-- for example :
--  def :
--  rec_root ( id serial , rec_test :: rec_test)
--  rec_test ( tag tag , rec_test:: rec_test)
--  procedure :
--   open(id,iter,tag,rec_test) (expand rec_root with iter 0 and open the recursive field) (iter over the recursive field)
--   close(id,iter,tag,rec_test) (get max iter) (iterate until last item)
--   final(id,rec_test) join rec_root where iter = 0 and replace rec_field with (row (tag,rec_test))
--



tlabel t = (label $ getCompose $ snd (unTB1 t))


dumbKey n = Key n  Nothing [] 0 Nothing (unsafePerformIO newUnique) (Primitive (AtomicPrim PInt ))

recursePath
  :: Bool->  RecState Key
     -> [(Set (Rel Key), Labeled Text (TB (Labeled Text) Key ()))]
     -> [(Set (Rel Key), Labeled Text (TB (Labeled Text) Key ()))]
     -> Map Text Table
     -> Path (Set Key) SqlOperation
     -> State
          ((Int, Map Int Table), (Int, Map Int Key))
          (Compose (Labeled Text) (TB (Labeled Text)) Key ())
recursePath isLeft isRec vacc ksbn invSchema (Path ifk jo@(FKInlineTable t ) e)
    | isArrayRel ifk  {-&& not (isArrayRel e )-}=   do
          tas <- tname nextT
          let knas = dumbKey (rawName nextT)
          kas <- kname tas  knas
          let
          (_,ksn) <-  labelTable  nextT
          tb <- fun ksn
          let
              ref = (\i -> Compose . justError ("cant find " ). fmap snd . L.find ((== S.singleton (Inline i)) . fst )$ ksbn ) $ head (S.toList ifk )
          return $  Compose $ Labeled (label $ kas) $ IT ref   (mapOpt $ mapArray $ TB1 tb )
    | otherwise = do
          (_,ksn) <-  labelTable nextT
          tb <-fun ksn
          lab <- if isTableRec' tb
            then do
              tas <- tname nextT
              let knas = dumbKey (rawName nextT)
              kas <- kname tas  knas
              return $ Labeled (label kas)
            else return  Unlabeled
          let
            ref = (\i -> Compose . justError ("cant find " ). fmap snd . L.find ((== S.singleton (Inline i)) . fst )$ ksbn ) $ head (S.toList ifk )
          return $ ( Compose $ lab $ IT  ref  (mapOpt $ TB1 tb)   )
    where
        nextLeft =  isLeft || isLeftRel ifk
        mapArray i =  if isArrayRel ifk then ArrayTB1 $ pure i else i
        mapOpt i = if isLeftRel ifk then  LeftTB1 $ Just  i else i
        nextT = justError ("recursepath lookIT "  <> show t <> " " <> show invSchema) (M.lookup t invSchema)
        fun =  recurseTB invSchema (rawFKS nextT) nextLeft isRec

recursePath isLeft isRec vacc ksbn invSchema (Path ifk jo@(FKJoinTable w ks tn) e)
    | S.size ifk   < S.size e =   do
          (t,ksn) <- labelTable nextT
          tb <-fun ksn
          tas <- tname nextT
          let knas = dumbKey(rawName nextT)
          kas <- kname tas  knas
          return $ Compose $ Labeled (label $ kas) (FKT [] ks  (mapOpt $ ArrayTB1 (pure  $ TB1 tb)  ))
    | isArrayRel ifk && not (isArrayRel e) =   do
          (t,ksn) <- labelTable nextT
          tb <-fun ksn
          tas <- tname nextT
          let knas = dumbKey (rawName nextT)
          kas <- kname tas  knas
          return $ Compose $ Labeled (label $ kas) (FKT (fmap (\i -> Compose . justError ("cant find " ). fmap snd . L.find ((== S.singleton (Inline i)) . fst )$ ksbn ) (_relOrigin <$> (filter (\i -> not $ S.member i (S.unions $ fmap fst vacc)) $  filterReflexive ks) ))  ks  (mapOpt $ mapArray $ TB1 tb  ))
    | otherwise = do
          (t,ksn) <- labelTable nextT
          tb@(m,Compose r)  <-fun ksn
          lab <- if not  . L.null $ isRec
            then do
              tas <- tname nextT
              let knas = dumbKey (rawName nextT)
              kas <- kname tas  knas
              return $ Labeled (label kas)
            else return  Unlabeled
          return $ Compose $ lab $ FKT (fmap (\i -> Compose . justError ("cant find " ). fmap snd . L.find ((== S.singleton (Inline i)) . fst )$ ksbn ) (_relOrigin <$> filter (\i -> not $ S.member (_relOrigin i) (S.map _relOrigin $ S.unions $ fmap fst vacc)) (filterReflexive ks)))  ks (mapOpt $ TB1 tb)
  where
        nextT = (\(Just i)-> i) (M.lookup tn (invSchema))
        nextLeft = any (isKOptional.keyType) (S.toList ifk) || isLeft
        mapArray i =  if isArrayRel ifk then ArrayTB1 (pure i) else i
        mapOpt i = if isLeftRel  ifk then  LeftTB1 $ Just  i else i
        fun =   recurseTB invSchema (rawFKS nextT) nextLeft isRec

recursePath isLeft isRec vacc ksbn invSchema jo@(Path ifk (RecJoin l f) e)
    = recursePath isLeft (fmap (\(b,c) -> if mAny (\c -> L.null c) c  then (b,b) else (b,c)) $  isRec  ) vacc ksbn invSchema (Path ifk f e)

recurseTB :: Map Text Table -> Set (Path (Set Key ) SqlOperation ) -> Bool -> RecState Key  -> TB3Data (Labeled Text) Key () -> StateT ((Int, Map Int Table), (Int, Map Int Key)) Identity (TB3Data (Labeled Text) Key ())
recurseTB invSchema  fks' nextLeft isRec (m, kv) =  (if L.null isRec then m else m  ,) <$>
    (\kv -> case kv of
      (Compose (Labeled l kv )) -> do
         i <- fun kv
         return (Compose (Labeled l i));
      (Compose (Unlabeled kv)) -> do
         i<- fun kv
         return (Compose (Unlabeled i))) kv
    where
      fun =  (\kv -> do
          let
              items = _kvvalues kv
              fkSet:: S.Set Key
              fkSet =   S.unions . fmap (S.fromList . fmap _relOrigin . (\i -> if all isInlineRel i then i else filterReflexive i ) . S.toList . pathRelRel ) $ filter isReflexive  $ S.toList fks'
              nonFKAttrs :: [(S.Set (Rel Key) ,TBLabel  ())]
              nonFKAttrs =  M.toList $  M.filterWithKey (\i a -> not $ S.isSubsetOf (S.map _relOrigin i) fkSet) items
          pt <- foldl (\acc  fk ->  do
                  vacc <- acc
                  let relFk =pathRelRel fk
                      lastItem =   L.filter cond isRec
                      cond (_,l) = mAny (\l-> L.length l == 1  && ((== relFk ). S.fromList. last $ l)) l
                  if L.length lastItem < 2
                  then   do
                    i <- fmap (relFk,) . recursePath nextLeft ( fmap (fmap (L.drop 1 ))  <$> L.filter (\(_,i) -> mAny (\i -> (S.fromList .concat . maybeToList . safeHead $ i) == relFk ) i ) (isRec <> fmap (\i -> (i,i) ) (_kvrecrels m))) vacc ( (M.toList $  fmap getCompose items )) invSchema $ fk
                    return (fmap getCompose i:vacc)
                  else return vacc
                  ) (return []) $ P.sortBy (P.comparing pathRelRel) (F.toList $ fks' )
          return (   KV $ M.fromList $ nonFKAttrs <> (fmap (fmap Compose ) pt)))

mAny f (MutRec i) = L.any f i


type RecState k = [(MutRec [[Rel k]],MutRec [[Rel k]])]

isLeftRel ifk = any (isKOptional.keyType) (S.toList ifk)
isArrayRel ifk = any (isArray.keyType) (S.toList ifk)


eitherDescPK :: (Functor f,F.Foldable f,Ord k) =>TB3Data f k a -> Compose f (KV  (Compose f (TB f ))) k a
eitherDescPK i@(kv, _)
  | not ( null ( _kvdesc kv) ) =  if L.null (F.toList desc) then tbPK' i else desc
  | otherwise = tbPK' i
    where desc = tbDesc i


tbDesc :: (Functor f,Ord k)=>TB3Data f k a -> Compose f (KV  (Compose f (TB f ))) k a
tbDesc  =  tbFilter'  (\kv k -> (S.isSubsetOf (S.map _relOrigin k) (S.fromList $ _kvdesc kv ) ))

tbPK :: (Functor f,Ord k)=>TB3 f k a -> Compose f (KV  (Compose f (TB f ))) k a
tbPK = tbFilter  (\kv k -> (S.isSubsetOf (S.map _relOrigin k) (S.fromList $ _kvpk kv ) ))


tbPK' :: (Functor f,Ord k)=>TB3Data f k a -> Compose f (KV  (Compose f (TB f ))) k a
tbPK' = tbFilter'  (\kv k -> (S.isSubsetOf (S.map _relOrigin k) (S.fromList $ _kvpk kv ) ))

tbAttr :: (Functor f,Ord k) =>  TB3 f k a ->  Compose f (KV  (Compose f (TB f ))) k a
tbAttr  =  tbFilter  (\kv k -> not (S.isSubsetOf (S.map _relOrigin k) (S.fromList (_kvpk kv) <> (S.fromList (_kvdesc kv ))) ))

tbFilter' :: (Functor f,Ord k) =>  ( KVMetadata k -> Set (Rel k) -> Bool) -> TB3Data f k a ->  Compose f (KV  (Compose f (TB f ))) k a
tbFilter' pred (kv,item) =  mapComp (\(KV item)->  KV $ M.filterWithKey (\k _ -> pred kv k ) $ item) item
tbFilterE  pred (kv,item) =  (kv,mapComp (\(KV item)->  KV $ M.filterWithKey (\k _ -> pred kv k ) $ item) item)

tbFilter :: (Functor f,Ord k) =>  ( KVMetadata k -> Set (Rel k) -> Bool) -> TB3 f k a ->  Compose f (KV  (Compose f (TB f ))) k a
tbFilter pred (TB1 i) = tbFilter' pred i
tbFilter pred (LeftTB1 (Just i)) = tbFilter pred i
tbFilter pred (ArrayTB1 (i :| _ )) = tbFilter pred i
tbFilter pred (DelayedTB1 (Just i)) = tbFilter pred i





mkKey i = do
  (c,m) <- snd <$> get
  let next = (c+1,M.insert (c+1) i m)
  modify (\(j,_) -> (j,next))
  return (c+1,i)

mkTable i = do
  (c,m) <- fst <$> get
  let next = (c+1,M.insert (c+1) i m)
  modify (\(_,j) -> (next,j))
  return (c+1)

kname :: Labeled Text Table -> Key -> QueryRef (Labeled Text (TB (Labeled Text) Key () ))
kname t i = do
  n <- mkKey i
  return $ (Labeled ("k" <> (T.pack $  show $ fst n)) (Attr i (TB1 ())) )




tname :: Table -> QueryRef (Labeled Text Table)
tname i = do
  n <- mkTable i
  return $ Labeled ("t" <> (T.pack $  show n)) i




forceDAttr v = go v
  where
    go v = case v of
      (KOptional i) -> KOptional $ go i
      (KArray i ) -> KArray $ go i
      (KDelayed i ) -> i
      i -> i


alterKeyType f  = Le.over keyTypes f





unTlabel' ((m,kv) )  = (m,) $ overLabel (\(KV kv) -> KV $ fmap (Compose . Identity .unlabel.getCompose ) $   kv) kv
unTlabel  = fmap unTlabel'

unlabel (Labeled l (IT tn t) ) = (IT (relabel tn) (unTlabel t ))
unlabel (Unlabeled (IT tn t) ) = (IT (relabel tn) (unTlabel t ))
unlabel (Labeled l (FKT i fkrel t) ) = (FKT (fmap relabel i) fkrel (unTlabel  t ))
unlabel (Unlabeled (FKT i fkrel t) ) = (FKT (fmap relabel i) fkrel (unTlabel t))
unlabel (Labeled l (Attr k i )) = Attr k i

relabel = Compose . Identity . unlabel.getCompose

-- alterComp :: (f k a -> g d b ) -> Compose (Labeled Text) f  k a -> Compose (f Identityg d b
overLabel f = Compose .  Identity . f . labelValue  .getCompose




-- interval' i j = Interval.interval (ER.Finite i ,True) (ER.Finite j , True)
unFinite (ER.Finite i) = i
unFinite ER.PosInf = errorWithStackTrace ("posinf")
unFinite ER.NegInf = errorWithStackTrace ("neginf")
inf' = unFinite . Interval.lowerBound
sup' = unFinite . Interval.upperBound


instance P.Poset (FKey (KType Text))where
  compare  = (\i j -> case compare (i) (j) of
                      EQ -> P.EQ
                      LT -> P.LT
                      GT -> P.GT )

relabeling :: (forall a . f a -> a ) -> (forall a . a -> p a ) -> TB f k a -> TB p k a
relabeling p l (Attr k i ) = (Attr k i)
relabeling p l (IT i tb ) = IT ((Compose.  l . relabeling p l . p . getCompose ) i) (relabelT p l tb)

relabelT :: (forall a . f a -> a ) -> (forall a . a -> p a ) -> TB3 f k a -> TB3 p k a
relabelT p l =  fmap (relabelT' p l)

relabelT' :: (forall a . f a -> a ) -> (forall a . a -> p a ) -> TB3Data f k a -> TB3Data p k a
relabelT' p l (m ,Compose j) =  (m,Compose $ l (KV $ fmap (Compose.  l . relabeling p l . p . getCompose ) (_kvvalues $ p j)))

backFKRef
  :: (Show (f Key ),Show a, Functor f) =>
     M.Map Key Key
     -> f Key
     -> TBData  Key a
     -> f (TB f1 Key a)
backFKRef relTable ifk = fmap (uncurry Attr). reorderPK .  concat . fmap aattr . F.toList .  _kvvalues . unTB . snd
  where
        reorderPK l = fmap (\i -> justError (show ("reorder wrong" :: String, ifk ,relTable , l,i))  $ L.find ((== i).fst) (catMaybes (fmap lookFKsel l) ) )  ifk
        lookFKsel (ko,v)=  (\kn -> (kn ,transformKey (keyType ko ) (keyType kn) v)) <$> knm
          where knm =  M.lookup ko relTable


joinRel :: (Ord a ,Show a) => KVMetadata Key ->  [Rel Key] -> [Column Key a] -> [TBData Key a] -> FTB (TBData Key a)
joinRel tb rel ref table
  | L.all (isOptional .keyType) origin = LeftTB1 $ fmap (flip (joinRel tb (Le.over relOrigin unKOptional <$> rel ) ) table) (Tra.traverse unLeftItens ref )
  | L.any (isArray.keyType) origin = ArrayTB1 $ Non.fromList $  fmap (flip (joinRel tb (Le.over relOrigin unKArray <$> rel ) ) table . pure ) (fmap (\i -> justError ("cant index  " <> show (i,head ref)). unIndex i $ (head ref)) [0..(Non.length (unArray $ unAttr $ head ref) - 1)])
  | otherwise = maybe (TB1 $ tblistM tb (_tb . firstTB (\k -> justError "no rel key" $ M.lookup k relMap ) <$> ref )) TB1 tbel
      where origin = fmap _relOrigin rel
            relMap = M.fromList $ (\r ->  (_relOrigin r,_relTarget r) )<$>  rel
            tbel = L.find (\(_,i)-> interPointPost rel ref (nonRefAttr  $ F.toList $ _kvvalues $ unTB  i) ) table



interPointPost rel ref tar = interPoint ( rel) ( ref) (tar)
