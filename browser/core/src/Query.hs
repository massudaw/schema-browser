{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}

module Query
  (
   tbPK
  ,tableAttrs
  ,joinRel
  ,liftASch
  ,joinRel2
  ,isPrimReflexive
  ,alterKeyType
  ,searchGist
  ,rawFullName
  ,unComp
  ,isTableRec
  ,isKDelayed
  ,isKOptional
  ,lookGist
  ,tlabel
  ,tableView
  ,unTlabel'
  ,backFKRef
  ,backPathRef
  ,filterReflexive
  ,isReflexive
  ,isInlineRel
  ,attrValueName
  ,relabelT
  ,showTable
  ,isAccessRel
  ,isArrayRel
  ,isLeftRel
  ,relabelT'
  ,mAny
  ,allKVRec'
  ,allRec'
  ,tableViewNR
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
import Data.Functor.Identity
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
import Debug.Trace
import qualified Types.Index as G




transformKey
  :: (Eq b, Show a, Show b) =>
     KType (Prim KPrim b) -> KType (Prim KPrim b) -> FTB a -> FTB a
-- transformKey ki ko v | traceShow (ki,ko,v) False = undefined
transformKey (KSerial i)  (KOptional j) (SerialTB1 v)  | i == j = LeftTB1  v
transformKey (KOptional i)  (KSerial j) (LeftTB1 v)  | i == j = SerialTB1 v
transformKey (KOptional j) l (LeftTB1  v)
    | isJust v = transformKey j l (fromJust v)
    | otherwise = errorWithStackTrace "no transform optional nothing"
transformKey (KSerial j)  l v@(TB1 _) = transformKey j l v
transformKey (KSerial j)  l (SerialTB1 v)
    | isJust v = transformKey j l (fromJust v)
    | otherwise =  SerialTB1 Nothing
transformKey l@(Primitive _)  (KOptional j ) v  = LeftTB1 $ Just (transformKey l j v)
transformKey l@(Primitive _)  (KSerial j ) v   = SerialTB1 $ Just (transformKey l j v)
transformKey l@(Primitive _)  (KArray j ) v | j == l  = ArrayTB1 $ pure v
transformKey ki kr v | ki == kr = v
transformKey (Primitive ki) (Primitive kr) v
  | isPrimReflexive ki kr = v
transformKey ki kr  v = errorWithStackTrace  ("No key transform defined for : " <> show ki <> " " <> show kr <> " " <> show v )





isKDelayed (KDelayed i) = True
isKDelayed (KSerial i) = isKDelayed i
isKDelayed (KOptional i) = isKDelayed i
isKDelayed (KInterval i) = isKDelayed i
isKDelayed (KArray i)  = isKDelayed i
isKDelayed _ = False


isKOptional (KOptional i) = True
isKOptional _ = False
-- isKOptional i = errorWithStackTrace (show ("isKOptional",i))

-- Operators

showTable t  = rawSchema t <> "." <> rawName t






attrValueName :: (Ord a,Ord k, Show k ,Show a) => TB Identity (FKey k) a -> Text
attrValueName (Attr i _ )= keyValue i
attrValueName (IT i  _) = keyValue i
attrValueName i = errorWithStackTrace $ " no attr value instance " <> show i


--
-- Patch CRUD Postgresql Operations
--




rawFullName = showTable


allKVRec :: TB2 Key Showable -> [FTB Showable]
allKVRec = concat . F.toList . fmap allKVRec'

allKVRec' :: TBData Key  Showable -> [FTB Showable]
allKVRec'  t@(m, e)=  concat $ fmap snd $ L.sortBy (comparing (\i -> maximum $ (`L.elemIndex` _kvdesc m)  <$> (fmap _relOrigin $ F.toList $fst i) ))  $ M.toList (go  <$> eitherDescPK t)
  where
        go  (FKT _  _ tb) =  allKVRec  tb
        go  (IT  _ tb) = allKVRec tb
        go  (Attr _ a) = [a]


tableAttrs r =   do
   ((rawPK r)) <> (rawDescription r)  <>(S.toList (rawAttrs r))



labelTable :: Table -> State ((Int, Map Int Table), (Int, Map Int Key)) (TB3Data (Labeled Text)  Key  () )
labelTable i = do
   t <- tname i
   name <- Tra.traverse (\k-> (S.singleton (Inline k),) <$> kname t k ) (tableAttrs i)
   return ( (tableMeta i,) $ Compose $ Labeled (label t) $ KV $ M.fromList $ fmap Compose <$> name)

unComp :: (Show (g k a) ,F.Foldable f ) => Compose f g k a -> g k a
unComp = head . F.toList . getCompose

isTableRec tb = isTableRec'  (unTB1 tb )
isTableRec' tb = not $ L.null $ _kvrecrels (fst  tb )


isPrimReflexive :: Eq b => Prim KPrim b -> Prim KPrim b -> Bool
isPrimReflexive i j | i == j = True
isPrimReflexive (AtomicPrim (PInt i)) (AtomicPrim (PInt j)) = True
isPrimReflexive a b = False

isPairReflexive :: (Show b , Eq b) => KType (Prim KPrim b ) -> BinaryOperator -> KType (Prim KPrim b) -> Bool
isPairReflexive (Primitive i ) op (KInterval (Primitive j)) | i == j = False
isPairReflexive (Primitive j) op  (KArray (Primitive i) )  | i == j = False
isPairReflexive (KInterval i) op (KInterval j)
  | i == j && op == Contains = False
  | op == Equals = isPairReflexive i op j
isPairReflexive (Primitive i ) op (Primitive j) = isPrimReflexive i  j
isPairReflexive (KOptional i ) op  j = isPairReflexive i op j
isPairReflexive i  op (KOptional j) = isPairReflexive i op j
isPairReflexive (KSerial i) op j = isPairReflexive i op j
isPairReflexive i op (KSerial j) = isPairReflexive i op j
isPairReflexive (KArray i )  op  (KArray j)
  | i == j  && op == Contains = False
  | op == Equals = isPairReflexive i op j
isPairReflexive (KArray i )  op  j = True
isPairReflexive j op (KArray i )  = False
isPairReflexive i op  j = errorWithStackTrace $ "isPairReflexive " <> show i <> " - " <> show op <> " - " <> show  j

filterReflexive ks = L.filter (reflexiveRel ks) ks

reflexiveRel ks
  | any (isArray . keyType . _relOrigin) ks =  (isArray . keyType . _relOrigin)
  | all (isJust . keyStatic . _relOrigin) ks = ( isJust . keyStatic. _relOrigin)
  | any (isJust . keyStatic . _relOrigin) ks = ( isNothing . keyStatic. _relOrigin)
  | any (\j -> not $ isPairReflexive (keyType (_relOrigin  j) ) (_relOperator j ) ( keyType (_relTarget j) )) ks =  const False
  | otherwise = (\j-> isPairReflexive (keyType (_relOrigin  j) ) (_relOperator j ) (keyType (_relTarget j) ))

isInlineRel (Inline _ ) =  True
isInlineRel i = False

isReflexive (Path i r@(FKJoinTable  ks  _ )  )
  -- |  not (t `S.isSubsetOf` (S.fromList $ fmap _relTarget ks ))  = False
  |  otherwise = isPathReflexive  r
isReflexive (Path _ l  ) = isPathReflexive l

isPathReflexive (FKJoinTable  ks _)
  | otherwise   = all id $ fmap (\j-> isPairReflexive (keyType (_relOrigin  j) ) (_relOperator j ) (keyType (_relTarget j) )) ks
isPathReflexive (FKInlineTable _)= True
isPathReflexive (FunctionField _ _ _)= False
isPathReflexive (RecJoin _ i ) = isPathReflexive i


type TableMap = HM.HashMap Text (HM.HashMap Text Table)

allRec'
  :: TableMap
     -> Table
     -> TBData Key ()
allRec' i t = unTlabel' $ tableView  i t

tableView  invSchema r = fst $ flip runState ((0,M.empty),(0,M.empty)) $ do
  when (L.null $ rawPK r) (fail $ "cant generate ast for table " <> T.unpack (tableName r ) <> " the pk is null")
  ks <- labelTable r
  tb <- recurseTB invSchema (rawFKS r) False [] ks
  return  $ tb

tableViewNR invSchema r = fst $ flip runState ((0,M.empty),(0,M.empty)) $ do
  when (L.null $ rawPK r) (fail $ "cant generate ast for table " <> T.unpack (tableName r )<> " the pk is null")
  ks <- labelTable r
  tb <- recurseTB invSchema (S.filter (all isInlineRel. F.toList .pathRelRel)$ rawFKS r) False [] ks
  return  $ TB1 tb






tlabel t = (label $ getCompose $ snd (unTB1 t))

pathToRel (Path ifk (FKInlineTable _ ) ) = fmap Inline $ F.toList ifk
pathToRel (Path ifk (FunctionField _ _ _ ) ) = fmap Inline $ F.toList ifk
pathToRel (Path ifk (FKJoinTable ks _ ) ) = ks

dumbKey n = Key n  Nothing [] 0 Nothing (unsafePerformIO newUnique) (Primitive (AtomicPrim (PInt 0) ))

findRefIT ifk = justError ("cant find ref" <> show ifk). M.lookup (S.map Inline ifk )
findRefFK fks ksbn = kvlist $ fmap (\i -> Compose . justError ("cant find " ). M.lookup (S.singleton (Inline i)) $ ksbn ) fks

recursePath
  :: KVMetadata Key
  -> Bool
  ->  RecState Key
     -> [(Set (Rel Key), Labeled Text (TB (Labeled Text) Key ()))]
     -> M.Map (Set (Rel Key)) (Labeled Text (TB (Labeled Text) Key ()))
     -> TableMap
     -> Path (Set Key) SqlOperation
     -> State
          ((Int, Map Int Table), (Int, Map Int Key))
          (Compose (Labeled Text) (TB (Labeled Text)) Key ())
recursePath m isLeft isRec vacc ksbn invSchema p@(Path ifk jo@(FKInlineTable (s,t) ) )
    | anyArrayRel ks  =   do
          let
              ref = findRefIT ifk ksbn
          ksn <-  labelTable  nextT
          tb <- fun ksn
          tas <- tname nextT
          return $  Compose $ Labeled ((label $ ref)) $ IT (head (S.toList ifk))   (mapOpt $ mapArray $ TB1 tb )
    | otherwise = do
          let
            ref = findRefIT ifk  ksbn
          ksn <-  labelTable  nextT
          tb <- fun ksn
          lab <- if isTableRec' tb
            then do
              tas <- tname nextT
              let knas = dumbKey (rawName nextT)
              kas <- kname tas  knas
              return $ Labeled (label kas)
            else return  (Labeled (label ref) )
          return $ ( Compose $ lab $ IT  (head (S.toList ifk)) (mapOpt $ TB1 tb)   )
    where
        ks = pathToRel p
        nextLeft =  isLeft || anyLeftRel ks
        mapArray i =  if anyArrayRel ks then ArrayTB1 $ pure i else i
        mapOpt i = if anyLeftRel ks then  LeftTB1 $ Just  i else i
        nextT = justError ("recursepath lookIT "  <> show t <> " " <> show invSchema) (join $ HM.lookup t <$> HM.lookup s invSchema)
        fun =  recurseTB invSchema (rawFKS nextT) nextLeft isRec

recursePath m isLeft isRec vacc ksbn invSchema (Path ifk jo@(FKJoinTable  ks (sn,tn)) )
    | anyArrayRel ks =   do
          ksn <- labelTable nextT
          tb <-fun ksn
          tas <- tname nextT
          let knas = dumbKey (rawName nextT)
          kas <- kname tas  knas
          return $ Compose $ Labeled (label $ kas) (FKT (findRefFK (_relRoot <$> (filter (\i -> not $ S.member i (S.unions $ fmap fst vacc)) $  filterReflexive ks) ) ksbn  )  ks  (mapOpt $ mapArray $ TB1 tb  ))
    | otherwise = do
          ksn <- labelTable nextT
          tb@(m,Compose r)  <-fun ksn
          lab <- if not  . L.null $ isRec
            then do
              tas <- tname nextT
              let knas = dumbKey (rawName nextT)
              kas <- kname tas  knas
              return $ Labeled (label kas)
            else return  Unlabeled
          return $ Compose $ lab $ FKT (findRefFK  (_relOrigin <$> filter (\i -> not $ S.member (_relOrigin i) (S.map _relOrigin $ S.unions $ fmap fst vacc)) (filterReflexive ks)) ksbn )  ks (mapOpt $ TB1 tb)
  where
        nextT = (\(Just i)-> i) (join $ HM.lookup tn <$> (HM.lookup sn invSchema))
        e = S.fromList $ rawPK nextT
        nextLeft = any (isKOptional.keyType) (S.toList ifk) || isLeft
        mapArray i =  if anyArrayRel ks then ArrayTB1 (pure i) else i
        mapOpt i = if anyLeftRel ks then  LeftTB1 $ Just  i else i
        fun =   recurseTB invSchema (rawFKS nextT) nextLeft isRec

recursePath m isLeft isRec vacc ksbn invSchema jo@(Path ifk (RecJoin l f) )
  = recursePath m isLeft (fmap (\(b,c) -> if mAny (\c -> L.null c) c  then (b,b) else (b,c)) $  isRec  ) vacc ksbn invSchema (Path ifk f )
recursePath m isLeft isRec vacc ksbn invSchema jo@(Path ifk (FunctionField k l f) )
  = return $ Compose $ Labeled (label ref) (Fun k  (l,a) (TB1 () ))
    where
      a = f
      ref = (\i -> justError ("cant find " ).  M.lookup (S.singleton (Inline i)) $ ksbn ) $ head (S.toList ifk )

recurseTB :: TableMap -> Set (Path (Set Key ) SqlOperation ) -> Bool -> RecState Key  -> TB3Data (Labeled Text) Key () -> StateT ((Int, Map Int Table), (Int, Map Int Key)) Identity (TB3Data (Labeled Text) Key ())
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
              fkSet =   S.unions . fmap (S.fromList . fmap _relOrigin . (\i -> if all isInlineRel i then i else filterReflexive i ) . S.toList . pathRelRel ) $ filter isReflexive  $ filter(not.isFunction .pathRel) $ S.toList fks'
              funSet = S.unions $ fmap (\(Path i _ )-> i) $ filter (isFunction.pathRel) (S.toList fks')
              nonFKAttrs :: [(S.Set (Rel Key) ,TBLabel  ())]
              nonFKAttrs =  M.toList $  M.filterWithKey (\i a -> not $ S.isSubsetOf (S.map _relOrigin i) (fkSet <> funSet)) items
          pt <- foldl (\acc  fk ->  do
                  vacc <- acc
                  let relFk =pathRelRel fk
                      lastItem =   L.filter cond isRec
                      cond (_,l) = mAny (\l-> L.length l == 1  && ((== relFk ). S.fromList. last $ l)) l
                  if L.length lastItem < 2
                  then   do
                    i <- fmap (relFk,) . recursePath m nextLeft ( fmap (fmap (L.drop 1 ))  <$> L.filter (\(_,i) -> mAny (\i -> (S.fromList .concat . maybeToList . safeHead $ i) == relFk ) i ) (isRec <> fmap (\i -> (i,i) ) (_kvrecrels m))) vacc ( (fmap getCompose items )) invSchema $ fk
                    return (fmap getCompose i:vacc)
                  else return vacc
                  ) (return []) $ P.sortBy (P.comparing pathRelRel) (F.toList $ fks' )
          return (   KV $ M.fromList $ nonFKAttrs <> (fmap (fmap Compose ) pt)))

mAny f (MutRec i) = L.any f i


type RecState k = [(MutRec [[Rel k]],MutRec [[Rel k]])]

isAccessRel (RelAccess i _ ) = True
isAccessRel i  = False

anyArrayRel = L.any isArrayRel

isArrayRel (Rel i _ j ) = isArray (keyType i ) && not (isArray (keyType j))
isArrayRel (Inline i  ) = isArray (keyType i )
isArrayRel (RelAccess i  j ) = isArray (keyType i) || isArrayRel j

anyLeftRel = L.any isLeftRel

isLeftRel (Rel i _ _ ) =  isKOptional (keyType i)
isLeftRel (Inline i ) =  isKOptional (keyType i)
isLeftRel (RelAccess i j ) =  isKOptional (keyType i) || isLeftRel j


liftASch :: TableMap  -> Text -> Text -> Access Text  -> Access Key
liftASch inf s tname (ISum i) =  ISum $ fmap (liftASch inf s tname)  i
liftASch inf s tname (Many i) =  Many $ fmap (liftASch inf s tname)  i
liftASch inf s tname (IProd b l) = IProd b $ fmap lookKey  l
  where
    tb = lookup tname $  lookup s inf
    lookup i m = justError ("no look" <> show i) $ HM.lookup i m
    lookKey c = i
      where
        i = justError "no attr" $ L.find ((==c).keyValue ) (tableAttrs tb)
liftASch inf s tname (Nested i c) = Nested ref (liftASch inf (fst l ) (snd l) c)
  where
    ref@(IProd _ refk) = liftASch inf s tname i
    lookup i m = justError ("no look" <> show i) $ HM.lookup i m
    tb = lookup tname $  lookup s inf
    n = justError "no fk" $ L.find (\i -> S.fromList refk == (S.map _relOrigin $ pathRelRel i) ) (rawFKS tb)
    l = case n of
          (Path _ rel@(FKJoinTable  _ l  ) ) ->  l
          (Path _ rel@(FKInlineTable  l  ) ) ->  l
liftASch _ _ _ i = errorWithStackTrace (show i)



eitherDescPK :: Show a => TB3Data Identity Key a -> M.Map (S.Set (Rel Key )) (Column Key a)
eitherDescPK i@(kv, _)
  | not ( null ( _kvdesc kv) ) =  if L.null (F.toList desc) then  pk else fromMaybe pk desc
  | otherwise = pk
  where desc = (\i -> if F.null i then Nothing else Just i). fmap (justError "") . M.filter (\i -> isJust i) $  fmap unLeftItens $  unTB <$> (_kvvalues $ unTB $ snd $ tbDesc i)
        pk = unTB <$> (_kvvalues $ unTB $ snd $tbPK i)


tbDesc :: (Functor f,Ord k)=>TB3Data f k a ->  TB3Data f k a
tbDesc  =  tbFilter'  (\kv k -> (S.isSubsetOf (S.map _relOrigin k) (S.fromList $ _kvdesc kv ) ))

tbPK :: (Functor f,Ord k)=>TB3Data f k a -> TB3Data f k a
tbPK = tbFilter'  (\kv k -> (S.isSubsetOf (S.map _relOrigin k) (S.fromList $ _kvpk kv ) ))

tbFilter' :: (Functor f,Ord k) =>  ( KVMetadata k -> Set (Rel k) -> Bool) -> TB3Data f k a ->  TB3Data f k a
tbFilter' pred (kv,item) =  (kv,mapComp (\(KV item)->  KV $ M.filterWithKey (\k _ -> pred kv k ) $ item) item)
-- Combinators




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



alterKeyType f  = Le.over keyTypes f


unTlabel' ((m,kv) )  = (m,) $ overLabel (\(KV kv) -> KV $ fmap (Compose . Identity .unlabel.getCompose ) $   kv) kv
unTlabel  = fmap unTlabel'

unlabel (Labeled l (IT tn t) ) = (IT tn (unTlabel t ))
unlabel (Unlabeled (IT tn t) ) = (IT tn (unTlabel t ))
unlabel (Labeled l (FKT i fkrel t) ) = (FKT (mapKV relabel i) fkrel (unTlabel  t ))
unlabel (Unlabeled (FKT i fkrel t) ) = (FKT (mapKV relabel i) fkrel (unTlabel t))
unlabel (Labeled l (Attr k i )) = Attr k i
unlabel (Labeled l (Fun k i m )) = Fun k i m

relabel = Compose . Identity . unlabel.getCompose

-- alterComp :: (f k a -> g d b ) -> Compose (Labeled Text) f  k a -> Compose (f Identityg d b
overLabel f = Compose .  Identity . f . labelValue  .getCompose




-- interval' i j = Interval.interval (ER.Finite i ,True) (ER.Finite j , True)

inf' = unFinite . Interval.lowerBound
sup' = unFinite . Interval.upperBound


instance (Show i,P.Poset i )=> P.Poset (Rel i)where
  compare  (Inline i ) (Inline j) = P.compare i j
  compare  (Rel i _ a ) (Inline j ) = case i == j of
                                        True -> P.GT
                                        False -> P.compare i j
  compare  (Inline j )(Rel i _ a )  = case i == j of
                                        True -> P.LT
                                        False -> P.compare j i
  compare  (Rel i _ a ) (Rel j _ b) = P.compare i j <> P.compare a b
  compare  (RelFun i  a ) j  = case L.any (== j) a  of
                                          True -> P.GT
                                          False -> P.compare (Inline i) j
  compare   j (RelFun i  a )= case L.any (== j) a  of
                                          True -> P.LT
                                          False -> P.compare j (Inline i)

  compare i j = errorWithStackTrace (show (i,j))




instance P.Poset (FKey i)where
  compare  = (\i j -> case compare (i) (j) of
                      EQ -> P.EQ
                      LT -> P.LT
                      GT -> P.GT )

relabeling :: (forall a . f a -> a ) -> (forall a . a -> p a ) -> TB f k a -> TB p k a
relabeling p l (Attr k i ) = (Attr k i)
relabeling p l (IT i tb ) = IT i (relabelT p l tb)

relabelT :: (forall a . f a -> a ) -> (forall a . a -> p a ) -> TB3 f k a -> TB3 p k a
relabelT p l =  fmap (relabelT' p l)

relabelT' :: (forall a . f a -> a ) -> (forall a . a -> p a ) -> TB3Data f k a -> TB3Data p k a
relabelT' p l (m ,Compose j) =  (m,Compose $ l (KV $ fmap (Compose.  l . relabeling p l . p . getCompose ) (_kvvalues $ p j)))

backPathRef :: Path (Set Key) SqlOperation -> TBData Key Showable ->  [Column Key Showable]
backPathRef (Path k (FKJoinTable rel t)) = backFKRef (M.fromList $ fmap (\i -> (_relTarget i ,_relOrigin i)) rel) (F.toList k)

backFKRef
  :: (Show (f Key ),Show a, Functor f) =>
     M.Map Key Key
     -> f Key
     -> TBData  Key a
     -> f (TB f1 Key a)
backFKRef relTable ifk = fmap (uncurry Attr). reorderPK .  concat . fmap aattr . F.toList .  _kvvalues . unTB . snd
  where
        reorderPK l = fmap (\i -> justError (show ("reorder wrong" :: String, ifk ,relTable , l,i))  $ L.find ((== i).fst) (catMaybes (fmap lookFKsel l) ) )  ifk
        lookFKsel (ko,v)=  (\kn -> (kn ,transformKey (keyType ko ) (keyType kn) (  v))) <$> knm
          where knm =  M.lookup ko relTable


tbpred un  = G.notOptional . G.getUnique un

searchGist ::
  (Functor t,  Show a ,Show a1,Ord k,  Show k,
   Foldable t, G.Predicates (G.TBIndex  a1)) =>
  M.Map k k
  -> KVMetadata k
  -> G.GiST (G.TBIndex  a1) a
  -> Maybe (t (TB Data.Functor.Identity.Identity k a1))
  -> Maybe a
searchGist relTable m gist =  join . fmap (\k -> lookGist (S.fromList $fmap (\k-> justError (" no pk " <> show (k,relTable)) $ M.lookup k relTable) (_kvpk m) ) k  gist)
  where
    lookGist un pk  v =  join $ safeHead <$> res
      where res =  flip G.search  v <$> tbpred un pk

    tbpred un  = tbjust  .  Tra.traverse (Tra.traverse unSOptional') . fmap (first (\k -> justError (show k) $ M.lookup k (flipTable  relTable ))).  filter ((`S.member` un). fst ) . concat .fmap aattri
        where
          flipTable = M.fromList . fmap swap .M.toList
          tbjust = fmap (G.Idex . fmap snd.L.sortBy (comparing ((`L.elemIndex` _kvpk m).fst)))

joinRel :: (Show k ,Ord k ,Ord a ,Show a,G.Predicates (G.TBIndex a)) => KVMetadata k ->  [(Rel k ,FTB a)] -> G.GiST (G.TBIndex a) (TBData k a) -> FTB (TBData k a)
joinRel tb ref table
  | L.any (isLeft.snd)  ref
  = LeftTB1 $ fmap (flip (joinRel tb ) table) (Tra.traverse (Tra.traverse unSOptional) ref )
  | L.any (isArray.snd) ref
  = let
      !arr = justError ("no array"<> show ref )$ L.find (isArray. snd ) ref
   in ArrayTB1 $ Non.fromList $  fmap (\i -> joinRel tb ((fst arr,i): L.filter (not . isArray . snd)  ref) table ) (fmap (\i -> justError ("cant index  " <> show (i,ref)). (`Non.atMay` i) . unArray . snd $ arr ) [0..(Non.length (unArray  $ snd arr )- 1)])
  | otherwise
  = maybe (TB1 $ tblistM tb (fmap _tb $  fmap (\(i,j) -> Attr  (_relTarget i) j )  ref )) TB1 tbel
      where
            isLeft (LeftTB1 i) = True
            isLeft i = False
            isArray (ArrayTB1 i) = True
            isArray i = False
            tbel = G.lookup (G.Idex $ fmap snd $ L.sortBy (comparing (flip L.elemIndex (_kvpk tb). _relTarget .fst )) ref) table

joinRel2 :: (Show k , Ord k,Ord a ,Show a,G.Predicates (G.TBIndex a)) => KVMetadata k->  [(Rel k ,FTB a)] -> G.GiST (G.TBIndex a) (TBData k a) -> Maybe (FTB (TBData k a))
joinRel2 tb ref table
  | L.any (isLeft.snd) ref
  = Just $ LeftTB1  $ join $ fmap (flip (joinRel2 tb ) table) (Tra.traverse (traverse unSOptional) ref )
  | L.any (isArray.snd) ref
  = let
      !arr = justError ("no array"<> show ref )$ L.find (isArray .snd) ref
   in fmap (ArrayTB1 .  Non.fromList ) $Tra.sequenceA   $ fmap (flip (joinRel2 tb ) table . (:L.filter (not .isArray .snd) ref)) (fmap (\i -> (fst arr,) . justError ("cant index  " <> show (i,head ref)). (flip Non.atMay i) $ unArray $ snd arr ) [0..(Non.length (unArray $ snd arr)   - 1)])
  | otherwise
    =  TB1 <$> tbel
      where
            isLeft (LeftTB1 i) = True
            isLeft i = False
            isArray (ArrayTB1 i) = True
            isArray i = False
            tbel = G.lookup (G.Idex $ fmap snd $ L.sortBy (comparing (flip L.elemIndex (_kvpk tb). _relTarget .fst )) ref) table


lookGist un pk  = G.search (tbpred un pk)







