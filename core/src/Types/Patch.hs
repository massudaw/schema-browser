{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}

module Types.Patch
  -- Class Patch Interface
  ( Compact(..)
  , foldCompact
  , foldUndo
  , Patch(..)
  -- Patch Data Types and to be moved methods
  , patchSet
  , groupSplit2
  --,recoverEdit
  , Editor(..)
  , Atom(..)
  , filterDiff
  , isDiff
  , isKeep
  , isDelete
  , Address(..)
  , patchEditor
  , joinEditor
  , checkPatch
  , indexFilterP
  , indexFilterR
  , indexFilterPatch
  , G.tbpred
  , PTBRef(..)
  --
  , nonRefPatch
  , patchfkt
  , patchvalue
  , unAtom
  , unLeftItensP
  --
  , recoverPFK
  , liftPFK
  , PathFTB(..)
  , PathTID(..)
  , upperPatch
  , lowerPatch
  , PathAttr(..)
  , TBIdx
  , firstPatch
  , firstPatchAttr
  , PatchConstr
  , firstPatchRow
  , RowOperation(..)
  , RowPatch(..)
  ) where
import Control.DeepSeq
import qualified Control.Lens as Le
import Control.Monad.Reader
import Data.Bifunctor
import Data.Binary (Binary(..))
import Data.Either
import Data.Foldable (Foldable)
import qualified Data.Foldable as F
import Data.Functor.Compose
import qualified Data.Interval as Interval
import Data.Interval (Extended(..))
import Data.Interval (interval, lowerBound', upperBound')
import Data.Maybe
import Data.Monoid hiding (Product, (<>))
import Data.Ord
import Data.Semigroup hiding (diff)
import Data.Traversable (sequenceA, traverse)
import Data.Tuple
import GHC.Generics
import qualified NonEmpty as Non
import qualified Data.Sequence.NonEmpty as NonS
import NonEmpty (NonEmpty)
import Types.Common
import Types.Primitive
import Step.Common
import Patch
import qualified Types.Index as G
import Utils
import Debug.Trace
import Control.Applicative
import qualified Data.List as L
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import GHC.Exts

newtype Atom a = Atom { unAtom' :: a } deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

instance (Compact (Index a ),Patch a) => Patch (Atom a) where
  type Index (Atom a) = [Index a]
  createIfChange l =  do
    n <- safeHead (compact l)
    Atom <$> createIfChange n
  applyUndo (Atom i) j = first Atom <$> foldUndo  i j



instance Applicative PathFTB where
  pure = PAtom
  POpt i <*> POpt j = POpt $ liftA2 (<*>) i j
  PIdx ixi i <*> PIdx ix j
    | ixi == ix = PIdx ix $ liftA2 (<*>) i j
  PatchSet i <*> PatchSet j = PatchSet $ Non.zipWith (<*>) i j
  PAtom i <*> PAtom j = PAtom $ i j
  PIdx ix i <*> j = PIdx ix $ (<*> j) <$> i
  i <*> PIdx ix j = PIdx ix $ (i <*>) <$> j
  i <*> POpt j = POpt $ fmap (i <*>) j
  POpt i <*> j = POpt $ fmap (<*> j) i
  PatchSet i <*> j = PatchSet $ fmap (<*> j) i
  i <*> PatchSet j = PatchSet $ fmap (i <*>) j



data Editor a
  = Diff a
  | Delete
  | Keep
  deriving (Eq, Ord, Functor, Show)

data EitherDiff a b
  = LeftDelta a
  | RightDelta b
  deriving (Eq, Ord, Functor, Show)

filterDiff = fmap (\(Diff i) -> i) . filter isDiff

instance (Compact (Index a),Compact (Index b),Patch a , Patch b) => Patch (a,b) where
  type Index (a,b) = (Index (Atom a) , Index (Atom b))
  createIfChange (i,j) = liftA2 (,) (unAtom' <$> createIfChange i ) (unAtom' <$>createIfChange j)
  applyUndo  (i,j) (a,b)  = do
    (i',ua) <- applyUndo (Atom i) a
    (j',ub) <- applyUndo (Atom j) b
    return ((unAtom'  i',unAtom'  j'),(ua,ub))

  diff (i,j) (a,b) = all (diff (Atom i) (Atom a)) (diff (Atom j) (Atom b))
    where
      all Nothing Nothing = Nothing
      all (Just []) (Just []) = Nothing
      all i j = Just (fromMaybe [] i,fromMaybe [] j)


instance (Patch a ,Patch b) => Patch (Either a b) where
  type Index (Either a b) = EitherDiff (Index a) (Index b)
  createIfChange (RightDelta i) = Right <$> createIfChange i
  createIfChange (LeftDelta i) = Left <$> createIfChange i
  patch (Right i)  = RightDelta (patch i)
  patch (Left i)  = LeftDelta (patch i)

instance Patch b => Patch (Maybe b) where
  type Index (Maybe b) = Editor (Index b)
  diff i = Just . editor i
  createIfChange (Diff i) = Just <$> createIfChange i
  createIfChange Delete = Nothing
  createIfChange Keep = Nothing
  patch i = maybe Delete (Diff . patch) i
  applyUndo i = recoverEditChange i

-- Investigate adding a new field for target Edit
data PTBRef k s = PTBRef { sourcePRef :: TBIdx k s , targetPRef :: TBIdx k s , targetPRefEdit :: TBIdx k s }  deriving(Show,Eq,Ord,Functor,Generic)

nonRefPatch (PFK rel i j) = i
nonRefPatch i = [i]

data PathFTB a
  = PAtom a
  | POpt (Maybe (PathFTB a))
  | PIdx Int
         (Maybe (PathFTB a))
  | PInter Bool
           (Extended (PathFTB a), Bool)
  | PatchSet (Non.NonEmpty (PathFTB a))
  deriving (Show, Eq, Ord, Functor, Generic, Foldable, Traversable)

data PatchFTBC  a 
 = PAtomicC a
 | POptC (Maybe (PathFTB a))
 | PInterC (Extended (PathFTB a),Bool)
 | PatchSetC (Non.NonEmpty (PatchFTBC a))

isDiff (Diff _) = True
isDiff i = False

isKeep Keep = True
isKeep i = False

isDelete Delete = True
isDelete i = False

joinEditor (Diff i) = i
joinEditor Keep = Keep
joinEditor Delete = Delete

foldUndo
  :: (Foldable t, Patch a) =>
     a -> t (Index a) -> Either String (a, [Index a])
foldUndo vi =  fmap (fmap reverse) . F.foldl' (\i j -> edit j =<< i) (Right (vi, []))
  where
    edit l (i, tr) = fmap (:tr) <$> applyUndo i l


foldCompact :: (a -> a -> Maybe a) -> [a] -> [a]
foldCompact f [] = []
foldCompact f (x:xs) =
  let (l,i) = F.foldl' fun ([],x)  xs
      fun (o,c) j = case f c j  of
          Just n -> (o,n)
          Nothing -> (c:o,j)
  in reverse (i:l)

instance Compact i => Compact (Editor i) where
  compact l = [F.foldl' pred Keep l]
    where
      pred (Diff i) (Diff j) = maybe Keep Diff $ safeHead $ compact [i, j]
      pred _ (Diff i) = (maybe Keep Diff $ safeHead $ compact [i])
      pred _ Delete = Delete
      pred i Keep = i

firstPatchRow ::
     (Ord a, Ord k, Ord (Index a), Ord j)
  => (k -> j)
  -> RowPatch k a
  -> RowPatch j a
firstPatchRow f (RowPatch (ix, i))  = RowPatch (ix,firstRowOperation f i)
firstPatchRow f (BatchPatch rows  i)  = BatchPatch rows (firstRowOperation f i)

firstRowOperation f (CreateRow i) = CreateRow $ mapKey' f i
firstRowOperation f DropRow = DropRow
firstRowOperation f (PatchRow i) = PatchRow $ firstPatch f i

data RowPatch k a
  = RowPatch   { unRowPatch :: (TBIndex a, RowOperation k a) }
  | BatchPatch { targetRows :: [TBIndex a]
               , operation  :: RowOperation k a }
  | PredicatePatch { targetPredicate :: TBPredicate k a
               , operation  :: RowOperation k a }
  deriving (Show, Eq, Functor, Generic)

data RowOperation k a
  = CreateRow (TBData k a)
  | PatchRow (TBIdx k a)
  | DropRow
  deriving (Show, Eq,Ord, Functor, Generic)

instance (NFData k, NFData a) => NFData (RowPatch k a)
instance (Ord a,Ord k, Binary k, Binary a) => Binary (RowPatch k a)

instance (NFData k, NFData a) => NFData (RowOperation k a)
instance (Ord a,Ord k, Binary k, Binary a) => Binary (RowOperation k a)

instance (Ord k, Compact v, Show v, Show k, Patch v, Ord v, v ~ Index v) =>
         Compact (RowOperation k v) where
  compact l =
    if L.null l
      then l
      else [F.foldl' ops DropRow l]
    where
      ops (CreateRow i) (PatchRow j) = CreateRow $ apply i j
      ops (PatchRow i) (PatchRow j) = PatchRow $ (compact $ i ++ j)
      ops i (CreateRow j) = CreateRow j
      ops i DropRow = DropRow
      ops DropRow j = j

instance (Ord k, Patch v, Compact v, Show v, Show k, v ~ Index v, Ord v) =>
         Compact (RowPatch k v) where
  compact = flipop . op
    where
      op, flipop :: [RowPatch k v] -> [RowPatch k v]
      flipop i =
        (\(i, j) -> rebuild (concat j) i) <$> groupSplit2 content index i
      op i =
        (uncurry rebuild) . fmap (head . compact) <$>
        groupSplit2 index content i

instance Address (RowPatch k v) where
  type Idx (RowPatch k v) = [TBIndex v]
  type Content (RowPatch k v) = RowOperation k v
  index (RowPatch (i,_)) = [i]
  index (BatchPatch i _ ) = i
  content (RowPatch (_,i) ) = i
  content (BatchPatch _ i ) = i
  rebuild i j = if L.length i > 1 then BatchPatch  i j else RowPatch (head i, j)

-- type TBIdx k a = Map (Set k) [PValue k a]
type TBIdx k a = [PathAttr k a]

data PathAttr k a
  = PAttr k
        (PathFTB a)
  | PFun k
        (Expr, [Rel k])
        (PathFTB a)
  | PInline k
        (PathFTB (TBIdx k a))
  | PFK [Rel k]
        [PathAttr k a]
        (PathFTB (TBIdx k a))
  deriving (Eq, Ord, Show, Functor, Generic)


patchEditor i
  | L.length i == 0 = Keep
  | L.length i == 1 = maybe Keep Diff $ safeHead i
  | otherwise = Diff $ PatchSet (Non.fromList $ concat $ normalize <$> i)
  where
    normalize (PatchSet i) = concat $ fmap normalize i
    normalize i = [i]

splitMatch (b, pk) p =
  L.any (\i -> G.match
    (mapPredicate
       (\i -> justError ("no index" ++ show (i, pk)) $ L.elemIndex i pk)
       b)
    (Right i)) (index p)

checkPatch fixed@(WherePredicate b, pk) d =
  case (notPK, isPK) of
    (Just i, Just l) -> indexFilterR pk i d && splitMatch (l, pk) d
    (Just i, Nothing) -> indexFilterR pk i d
    (Nothing, Just l) -> splitMatch (l, pk) d
    (Nothing, Nothing) -> True
  where
    notPK = fmap WherePredicate $ splitIndexPKB b pk
    isPK = fmap WherePredicate $ splitIndexPK b pk

indexFilterR ::
     (Patch a,a ~Index a,G.IndexConstr k a ,Show k, Ord k) => [k] -> TBPredicate k a -> RowPatch k a -> Bool
indexFilterR table j (BatchPatch i l) =  F.any (\ix -> indexFilterR table j (RowPatch (ix ,l) )) i

indexFilterR table j (RowPatch (ix, i)) = case  i of
  DropRow -> G.checkPred (makePK table ix) j
  CreateRow i -> G.checkPred i j
  PatchRow i -> indexFilterP j i
  where
    makePK table (Idex l) = kvlist $ zipWith Attr table l
indexFilterP (WherePredicate p) v = go p
  where
    go (AndColl l) = F.all go l
    go (OrColl l) = F.any go l
    go (PrimColl l) = indexFilterPatch l v

indexFilterPatch ::
     (Patch a ,a ~ Index a,G.IndexConstr k a ,Show k, Ord k)
  => (Rel k, [(k, AccessOp a)])
  -> TBIdx k a
  -> Bool
indexFilterPatch (Inline l, ops) lo =
  case L.find ((Inline l ==) . index) lo
  -- case Map.lookup (Set.singleton (Inline l)) lo of
        of
    Just i ->
      case i
        --  PPrim f -> G.match op (Right $ (create f :: FTB Showable))
            of
        PAttr k f -> matching f
        i -> True
    Nothing -> True
  where
    create' :: (Index a ~ a,Patch a ,Show a,Ord a) => PathFTB (Index a) -> FTB a
    create'  = create
    matching f = G.match (G.getOp l ops) (Right (create' f))

indexFilterPatch (RelAccess l n, op) lo =
  case L.find ((l ==) . index) lo of
    Just i ->
      case i of
        PInline k f -> L.any (indexFilterPatchU (n, op)) f
        PFK _ _ f -> L.any (indexFilterPatchU (n, op)) f
        -- PRef  f -> L.any (indexFilterPatchU (n,op)) f
        -- PRel _   f -> L.any (indexFilterPatchU (n,op)) f
        i -> True
    Nothing -> True
indexFilterPatch i o = error (show (i, o))

indexFilterPatchU ::
     ( Patch a,a ~ Index a,G.IndexConstr k a,Show k, Ord k)
  => (Rel k, [(k, AccessOp a )])
  -> TBIdx k a
  -> Bool
indexFilterPatchU (n, op) o = indexFilterPatch (n, op) o

unSOptionalP (PatchSet l) =
  PatchSet <$> Non.nonEmpty (catMaybes (unSOptionalP <$> F.toList l))
unSOptionalP (POpt i) = i
unSOptionalP i = Just i

unLeftItensP ::
     (Show k, Show a)
  => PathAttr (FKey (KType k)) a
  -> Maybe (PathAttr (FKey (KType k)) a)
unLeftItensP = unLeftTB
  where
    unLeftTB (PAttr k (PatchSet l)) =
      PAttr (unKOptional k) . PatchSet <$>
      Non.nonEmpty (catMaybes (unSOptionalP <$> F.toList l))
    unLeftTB (PAttr k v) = PAttr (unKOptional k) <$> unSOptionalP v
    unLeftTB (PFun k rel v) = PFun (unKOptional k) rel <$> unSOptionalP v
    unLeftTB (PInline na l) = PInline (unKOptional na) <$> unSOptionalP l
    unLeftTB (PFK rel ifk tb) =
      (\ik -> PFK (Le.over relOri unKOptional <$> rel) ik) <$>
      traverse unLeftTB ifk <*>
      unSOptionalP tb
    unLeftTB i = error (show i)

-- recoverEditChange  i j | traceShow (i,j) False = undefined
recoverEditChange (Just i) Keep = Right (Just i, Keep)
recoverEditChange (Just i) Delete = Right (Nothing, Diff (patch i))
recoverEditChange (Just i) (Diff j) = bimap Just Diff <$> applyUndo i j
recoverEditChange Nothing (Diff j) =
  (, Delete) . Just <$> maybe (Left $ "cant create: Nothing, Diff") Right (createIfChange j)
recoverEditChange Nothing Keep = Right (Nothing, Keep)
recoverEditChange Nothing Delete = Right (Nothing,Keep)
recoverEditChange _ _ = error "no edit"

-- editor  i j | traceShow (i,j) False = undefined
editor (Just i) Nothing = Delete
editor (Just i) (Just j) = maybe Keep Diff df
  where
    df = diff i j
editor Nothing (Just j) = Diff (patch j)
editor Nothing Nothing = Keep

upperPatch = PInter False

lowerPatch = PInter True

data PatchIndex a =
  PatchIndex Int
             (Maybe a)
  deriving (Show)

instance Patch a => Patch (NonEmpty a) where
  type Index (NonEmpty a) = PatchIndex (Index a)
  applyIfChange j (PatchIndex i (Just a)) =
    Just $
    Non.imap
      (\ix ->
         if ix == i
           then flip apply a
           else id)
      j
  applyIfChange j (PatchIndex i Nothing) =
    Non.nonEmpty $ Non.take i j <> Non.drop (i + 1) j
  createIfChange (PatchIndex i a) = join $ fmap (fmap pure . createIfChange) a

instance (Show a, Show k, Compact a, Ord k) => Compact (PathAttr k a) where
  compact = compactAttr

instance Address (PathFTB a) where
  type Idx (PathFTB a) = PathTID
  type Content (PathFTB a) = PatchFTBC a 

  index (PIdx i _) = PIdIdx i
  index (PAtom i) = PIdAtom
  index (POpt i) = PIdOpt
  index (PInter i _) = PIdInter i

  content (PIdx i v) =  POptC v
  content (POpt v ) =  POptC v
  content (PInter _ v) =  PInterC v
  content (PAtom i) = PAtomicC i

  rebuild (PIdIdx i) (POptC j)  = PIdx i j 
  rebuild PIdAtom (PAtomicC j)  = PAtom j 
  rebuild PIdOpt (POptC j)  = POpt j 
  rebuild (PIdInter i) (PInterC j)  = PInter i j 

instance (Show a, Compact a) => Compact (PathFTB a) where
  compact = maybeToList . compactPatches

instance (Show k, Show a, Compact a, Ord k) => Compact (TBIdx k a) where
  compact i = L.transpose $ compact . snd <$> groupSplit2 index id (join i)

instance Compact Showable where
  compact = id

instance PatchConstr k a => Patch (AValue k a) where
  type Index (AValue k a) = PValue k (Index a)
  diff (APrim i) (APrim j) = PPrim <$> diff i j  
  diff (ARef i) (ARef j)  = PRef <$> diff i j  
  diff (ARel i l) (ARel j m) = PRel <$> (diff i j <|> pure [] ) <*>   diff l m
  applyUndo (APrim i) (PPrim j) = bimap APrim PPrim <$> applyUndo  i j 
  applyUndo (ARef i) (PRef j) = bimap ARef PRef <$> applyUndo  i j 
  applyUndo (ARel i j) (PRel l m) = (\(a,b) (c,d) -> (ARel a c , PRel b d)) <$> applyUndo  i l  <*> applyUndo j m 
  createIfChange (PPrim i )= APrim <$> createIfChange i 
  createIfChange (PRel i j )= ARel <$> createIfChange i  <*> createIfChange j 
  createIfChange (PRef i )=  ARef <$> createIfChange i 
  patch (APrim i)= PPrim (patch i)
  patch (ARel i j)= PRel (patch i) (patch j)
  patch (ARef i)= PRef (patch i) 


instance PatchConstr k a => Patch (TB k a) where
  type Index (TB k a) = PathAttr k (Index a)
  diff = diffAttr
  applyUndo = applyUndoAttrChange
  createIfChange = createAttrChange
  patch = patchAttr


instance (Ord k) => Address (PathAttr k a) where
  type Idx (PathAttr k a) = Rel k
  type Content (PathAttr k a ) = PValue k a
  index = pattrKey
  content (PAttr _ i ) =  PPrim i 
  content (PFun _ _ i ) =  PPrim i 
  content (PFK  _ i   j) = PRel i j 
  content (PInline _ i ) = PRef i
  rebuild (RelFun (Inline i) j l ) (PPrim k ) =  PFun i (j,l) k
  rebuild (Inline i) (PPrim k ) =  PAttr i k
  rebuild (Inline i) (PRef k ) =  PInline i k
  rebuild (RelComposite l) (PRel i k ) =  PFK l i k
  rebuild r@(Rel _ _ _ ) (PRel i k ) =  PFK [r] i k

instance (Ord k) => Address (TB k a) where
  type Idx (TB k a) = Rel k
  index = keyattr

instance PatchConstr k a => Patch (TBData k a) where
  type Index (TBData k a) = TBIdx k (Index a)
  diff = difftable
  applyUndo = applyRecordChange
  createIfChange = createTB1
  patch = patchTB1

instance (Ord a, Show a, Patch a) => Patch (FTB a) where
  type Index (FTB a) = PathFTB (Index a)
  diff = diffFTB patch diff
  applyUndo = applyUndoFTBM
  createIfChange = either (\e -> Nothing) Just . createUndoFTBM
  patch = patchFTB patch

instance Semigroup Showable where
  i <> j = j

instance Patch () where
  type Index () = ()
  patch = id
  diff _ _ = Nothing
  createIfChange  = Just
  applyUndo _ _ = Left "no difference"

diffPrim i j
  | i == j = Nothing
  | otherwise = Just j


instance Patch Showable where
  type Index Showable = Showable
  diff = diffPrim

  applyUndo (SNumeric s) (SDelta (DSInt i))  = Right (SNumeric (s + i),SDelta (DSInt $ negate i))
  applyUndo (SDouble s) (SDelta (DSDouble i))  = Right (SDouble (s + i),SDelta (DSDouble $ negate i))
  applyUndo j i = Right (i, j)
  createIfChange = Just
  patch = id

instance (Monoid a, Monoid b,Compact a , Compact b) => Compact (a,b) where
  compact i = fromMaybe [] $ liftA2 (zipWith (,)) f s <|> (fmap (,mempty ) <$> f)  <|> (fmap (mempty ,) <$> s)
    where
      f = nonEmpty (compact (fst <$> i))
      s = nonEmpty (compact (snd <$> i))


instance (Ord a,Show a,Show b,Compact b) => Compact (PTBRef a b) where
  compact i =  zipWith3 PTBRef f (defEmpty s)  (defEmpty t)
    where
      defEmpty = maybe (pure []) id . nonEmpty
      f = compact (sourcePRef <$> i)
      s = compact (targetPRef <$> i)
      t = compact (targetPRefEdit <$> i)

instance Patch (TBRef Key Showable) where
  type Index (TBRef Key Showable) = PTBRef Key Showable
  diff (TBRef (i, j)) (TBRef (k, l) )=
    (PTBRef <$> dref <*> dtb <*> pure []) <|> (PTBRef <$> dref <*> pure [] <*> pure []) <|>
    (PTBRef <$> pure [] <*> pure [] <*> dtb )
    where
      dref = diff i k
      dtb = diff j l
  patch (TBRef (i, j)) = PTBRef (patch i) (patch j) []
  applyUndo (TBRef (i, j)) (PTBRef k l e) = do
    (s,su) <- applyUndo i k <|> Right (i,[])
    (t,tu) <- applyUndo j l <|> Right (j,[])
    (t',tu') <- applyUndo t e <|> Right (t,tu)
    return (TBRef (s,t'),PTBRef su tu tu')
  createIfChange (PTBRef i j k ) = do
    (s,t) <-
      ((,) <$> createIfChange i <*> createIfChange j) <|>
      -- create non reflective
      (( kvlist [],) <$> createIfChange j) <|>
      -- TODO: check if we need to create no ref ptbref
      ((, kvlist []) <$> createIfChange i)
    t' <- applyIfChange t k
    return (TBRef (s,t'))

type PatchConstr k a
   = ( Show (Index a)
     , Compact (Index a)
     , Eq (Index a)
     , Patch a
     , Ord a
     , Show a
     , Show k
     , Ord k)

type PAttr k a = (Rel k, PValue k a)



data PValue k a
  = PPrim { pprim :: PathFTB a }
  | PRel { prel :: TBIdx k a
         , pref :: PathFTB (TBIdx k a) }
  | PRef { pref :: PathFTB (TBIdx k a) }
  deriving (Eq, Ord, Show, Functor, Generic)

patchvalue (PAttr _ v) = v
patchvalue (PFun _ _ v) = v

patchfkt (PFK _ _ k) = k
patchfkt (PInline _ k) = k
patchfkt i = error ("not patch atom" ++ show i)

unAtom (PatchSet (PAtom l Non.:| _)) = l
unAtom (PAtom i) = i
unAtom i = error ("not atom" ++ show i)

instance (Binary k, Binary a) => Binary (PathAttr k a)

instance (NFData k, NFData a) => NFData (PathAttr k a)

instance (NFData k) => NFData (PathFTB k)

instance (Binary k) => Binary (PathFTB k)

firstPatch ::
     (Ord a, Ord k, Ord (Index a), Ord j) => (k -> j) -> TBIdx k a -> TBIdx j a
firstPatch f k = fmap (firstPatchAttr f) k

firstPatchAttr ::
     (Ord k, Ord j, Ord a, Ord (Index a))
  => (k -> j)
  -> PathAttr k a
  -> PathAttr j a
firstPatchAttr f (PAttr k a) = PAttr (f k) a
firstPatchAttr f (PFun k rel a) = PFun (f k) (fmap (fmap f) <$> rel) a
firstPatchAttr f (PInline k a) = PInline (f k) (fmap (firstPatch f) a)
firstPatchAttr f (PFK rel k b) =
  PFK (fmap (fmap f) rel) (fmap (firstPatchAttr f) k) (fmap (firstPatch f) $ b)

instance (Ord k ,Compact v,Show k ,Show v) => Compact (PValue k v) where
  compact  l = [F.foldl' merge  (head l) (tail l)]
    where 
      merge (PPrim i) (PPrim j) = head $ PPrim <$> compact [i ,j]
      merge (PRef i) (PRef j) = head $ PRef <$> compact [i ,j]
      merge (PRel i k) (PRel j l) = head $ PRel (concat $ compact [i ,j] ) <$> (compact [k ,l])

compactAttr ::
     (Show a, Show b, Compact b, Ord a) => [PathAttr a b] -> [PathAttr a b]
compactAttr i = (uncurry rebuild . fmap (head . compact)) <$>  groupSplit2 index content  i

unPAtom (PAtom i) = i

instance (Compact a ,Show a) => Compact (PatchFTBC a ) where
  associate (POptC i) (POptC j) = POptC $ (associate <$> i <*> j ) <|>  j 
  associate (PInterC (i,l)) (PInterC (j,m)) = PInterC $ (associate <$> i <*> j ,m)
  associate (PAtomicC l) (PAtomicC m) = PAtomicC  (associate l m )
  associate (PatchSetC i ) l = justError "cant be empty" $ patchSetC $ compact (F.toList $ i <>pure l)
  associate i (PatchSetC l) = justError "cant be empty" $ patchSetC $ compact (F.toList $ pure i <> l)
  associate (PatchSetC i) (PatchSetC l) = justError "cant be empty" $patchSetC $  compact (F.toList $ i <> l) 


compactPatches :: (Show a, Compact a) => [PathFTB a] -> Maybe (PathFTB a)
compactPatches [] = Nothing
compactPatches i =
  patchSet .
  catMaybes . fmap (fmap (uncurry rebuild). traverse (patchSetC . compact)). groupSplit2 index content . concat . fmap expandPSet $
  i
  where
    expandPSet (PatchSet l) = F.toList l
    expandPSet p = [p]

groupSplit2 :: Ord b => (a -> b) -> (a -> c) -> [a] -> [(b, [c])]
groupSplit2 f g =
  fmap (\i -> (f $ justError "cant group" $ safeHead i, g <$> i)) . groupWith f


patchTB1 :: PatchConstr k a => TBData k a -> TBIdx k (Index a)
patchTB1 k = patchAttr <$> unkvlist k

difftable ::
     (PatchConstr k a, Show a, Show k)
  => TBData k a
  -> TBData k a
  -> Maybe (Index (TBData k a))
difftable v o =
  if L.null attrs
    then Nothing
    else Just attrs
  where
    attrs = uncurry rebuild <$> (catMaybes $ sequenceA <$> (mergeKVWith diff (Just . patch) v o))

createTB1 :: PatchConstr d a => (TBIdx d (Index a)) -> Maybe (TBData d a)
createTB1 k =
  kvlist <$>
  nonEmpty
    (catMaybes $
     fmap
       createAttrChange
       (concat $
        maybe [] id . fmap compactAttr . nonEmpty . snd <$>
        groupSplit2 index id k))

pattrKey :: Ord k => PathAttr k t -> Rel k
pattrKey (PAttr s _) = Inline s
pattrKey (PFun s l _) = RelFun (Inline s) (fst l) (snd l)
pattrKey (PInline s _) =  Inline s
pattrKey (PFK s _ _) = relComp s

applyRecordChange ::
  forall  d a . PatchConstr d a
  => KV d a
  -> TBIdx d (Index a)
  -> Either String (KV d a, TBIdx d (Index a))
applyRecordChange i [] = Right (i, [])
applyRecordChange v k =
  add . swap <$> getCompose (traverseKVWith editAValue v)
  where
    editAValue key vi =
        let edits = filter ((key ==). index) k
        in Compose . fmap (swap . fmap (fmap (rebuild key))) $ foldUndo vi (content <$> edits)
    add (v, p) =
      (foldr (\p v -> maybe v (\i -> addAttr  i v) ({-traceShow (index p , createIfChange p :: Maybe (TB d a)) $-} createIfChange p) ) v $
        filter (isNothing . flip kvLookup v . index) k
      , p)

patchSetE i
  | L.length i == 0 = Left "empty array"
  | L.length i == 1 = Right (head i)
  | otherwise = Right $ PatchSet (Non.fromList $ concat $ normalize <$> i)
  where
    normalize (PatchSet i) = concat $ fmap normalize i
    normalize i = [i]

patchSetC i
  | L.length i == 0 = Nothing
  | L.length i == 1 = safeHead i
  | otherwise = Just $ PatchSetC (Non.fromList $ concat $ normalize <$> i)
  where
    normalize (PatchSetC i) = concat $ fmap normalize i
    normalize i = [i]


patchSet i
  | L.length i == 0 = Nothing
  | L.length i == 1 = safeHead i
  | otherwise = Just $ PatchSet (Non.fromList $ concat $ normalize <$> i)
  where
    normalize (PatchSet i) = concat $ fmap normalize i
    normalize i = [i]

applyUndoAttrChange (Attr k i) (PAttr _ p) =
  bimap (Attr k) (PAttr k) <$> applyUndo i p
applyUndoAttrChange (Fun k rel i) (PFun _ _ p) =
  bimap (Fun k rel) (PFun k rel) <$> applyUndo i p
applyUndoAttrChange (IT k i) (PInline _ p) =
  bimap (IT k) (PInline k) <$> applyUndo i p
--applyUndoAttrChange i j | traceShow (i,j) False = undefined
applyUndoAttrChange (FKT k rel i) (PFK _ p b) = do
  (tv, tp) <- applyUndo i b
  (refv, refp) <-  applyRecordChange k p
  return (FKT refv rel tv, PFK rel refp tp)

-- diffAValue :: PatchConstr k a  => AValue k a -> AValue k a -> Maybe (PValue k  (Index a))
-- diffAValue  (ARef i) (ARef j) = PRef $ diff i j
diffAttr :: PatchConstr k a => TB k a -> TB k a -> Maybe (PathAttr k (Index a))
diffAttr (Attr k i) (Attr l m) = fmap (PAttr k) (diffShowable i m)
diffAttr (Fun k rel i) (Fun l rel2 m) = fmap (PFun k rel) (diffShowable i m)
diffAttr (IT k i) (IT _ l) = fmap (PInline k) (diff i l)
diffAttr (FKT k _ i) (FKT m rel b) =
  PFK rel <$>
  (Just $
   catMaybes $
   F.toList $
     Map.intersectionWith (\i j -> diffAttr (i) (j)) (unKV k) (unKV m)) <*>
  diff i b

patchAttr :: PatchConstr k a => TB k a -> PathAttr k (Index a)
patchAttr a@(Attr k v) = PAttr k (patchFTB patch v)
patchAttr a@(Fun k rel v) = PFun k rel (patchFTB patch v)
patchAttr a@(IT k v) = PInline k (patchFTB patchTB1 v)
patchAttr a@(FKT k rel v) = PFK rel (patchAttr <$> unkvlist k) (patch v)

createAttrChange :: PatchConstr k a => PathAttr k (Index a) -> Maybe (TB k a)
createAttrChange (PAttr k s) = Attr k <$> createIfChange s
createAttrChange (PFun k rel s) = Fun k rel <$> createIfChange s
createAttrChange (PInline k s) = IT k <$> createIfChange s
createAttrChange (PFK rel k b) =
  flip FKT rel <$> (kvlist <$> traverse createAttrChange k) <*> createIfChange b

diffShowable ::
     (Show a, Ord a, Patch a) => FTB a -> FTB a -> Maybe (PathFTB (Index a))
diffShowable = diffFTB patch diff

applyShowable :: (Show a, Ord a, Patch a) => FTB a -> PathFTB (Index a) -> FTB a
applyShowable = apply

createShowable :: (Show a, Ord a, Patch a) => PathFTB (Index a) -> FTB a
createShowable = create

-- FTB
patchFTB :: Show a => (a -> Index a) -> FTB a -> PathFTB (Index a)
patchFTB p (LeftTB1 j) = POpt (patchFTB p <$> j)
patchFTB p (ArrayTB1 j) =
  justError ("empty array in arraytb1 patchftb" <> show j) $
  patchSet $
  zipWith (\i m -> PIdx i (Just m)) [0 ..] (F.toList $ patchFTB p <$> j)
patchFTB p (IntervalTB1 j) =
  justError ("no patch for" <> show j) $
  patchSet
    [ PInter True $ (first (fmap (patchFTB p)) $ Interval.lowerBound' j)
    , PInter False $ (first (fmap (patchFTB p)) $ Interval.upperBound' j)
    ]
patchFTB p (TB1 j) = PAtom $ p j

diffOpt ::
     (Ord a, Show a)
  => (a -> Index a)
  -> (a -> a -> Maybe (Index a))
  -> Maybe (FTB a)
  -> Maybe (FTB a)
  -> Maybe (Maybe (PathFTB (Index a)))
diffOpt p d i j
  | isJust i && isJust j = sequenceA $ liftA2 (diffFTB p d) i j
  | isJust i && isNothing j = Just Nothing
  | isNothing i && isJust j = Just (patchFTB p <$> j)
  | isNothing i && isNothing j = Nothing

diffFTB ::
     (Ord a, Show a)
  => (a -> Index a)
  -> (a -> a -> Maybe (Index a))
  -> FTB a
  -> FTB a
  -> Maybe (PathFTB (Index a))
diffFTB p d (LeftTB1 i) (LeftTB1 j) = POpt <$> diffOpt p d i j
diffFTB p d (ArrayTB1 i) (ArrayTB1 j) =
  patchSet $
  catMaybes $
  zipWith
    (\i -> fmap (PIdx i))
    [0 ..]
    (F.toList $ (NonS.toSequence $ NonS.zipWith (\i j -> fmap Just $ diffFTB p d i j) i j) <>
     (const (Just Nothing) <$> NonS.drop (NonS.length j) i) <>
     (Just . Just . patchFTB p <$> NonS.drop (NonS.length i) j))
diffFTB p d (IntervalTB1 i) (IntervalTB1 j)
  | i == j = Nothing
  | otherwise =
    patchSet $
    catMaybes
      [ match True (lowerBound' i) (lowerBound' j)
      , match False (upperBound' i) (upperBound' j)
      ]
  where
    match f = diffExtended
      where
        diffExtended (Finite i, bi) (Finite j, bj) =
          fmap (PInter f . (, bj) . Finite) $ diffFTB p d i j
        diffExtended _ (Finite i, bi) =
          Just $ PInter f (Finite $ patchFTB p i, bi)
        diffExtended _ (PosInf, bi) =
          if not f
            then Just (PInter f (PosInf, bi))
            else Nothing
        diffExtended _ (NegInf, bi) =
          if f
            then Just (PInter f (NegInf, bi))
            else Nothing
diffFTB p d (TB1 i) (TB1 j) = fmap PAtom $ d i j
diffFTB p d i j = error ("diffError" <> show (i, j))

applyUndoFTBM ::
     (Patch a, Ord a, Show a)
  => FTB a
  -> PathFTB (Index a)
  -> Either String (FTB a, PathFTB (Index a))
applyUndoFTBM (LeftTB1 i) op@(POpt o) =
  case (i, o) of
    (Just i, Just o) ->
      Right $
      either
        (\_ -> (LeftTB1 Nothing, POpt (Just $patch i)))
        (bimap (LeftTB1 . Just) (POpt . Just)) $
      applyUndoFTBM i o
    (Just i, Nothing) -> Right (LeftTB1 Nothing, POpt $ Just $ patch i)
    (Nothing, Just i) ->
      Right $
      either
        (\_ -> (LeftTB1 Nothing, POpt Nothing))
        ((, POpt Nothing) . LeftTB1 . Just) $
      createUndoFTBM i
    (Nothing, Nothing) -> Right (LeftTB1 Nothing, POpt Nothing)
applyUndoFTBM (ArrayTB1 i) (PIdx ix o) =
  case o of
    Nothing ->
      maybe
        (Left "empty array")
        (Right . ((, PIdx ix $ patch <$> NonS.atMay i ix) . ArrayTB1)) .
      NonS.nonEmptySeq $  (NonS.take ix i) <> (NonS.drop (ix + 1) i)
    Just p ->
      if ix <= NonS.length i - 1
        then do
          let c = i NonS.!! ix
          (v, p) <- applyUndoFTBM c p
          el <-
            maybe (Left "empty arraytb1 list ") Right $
            NonS.nonEmptySeq $ NonS.take ix i <> pure v <> NonS.drop (ix + 1) i
          return (ArrayTB1 el, PIdx ix (Just p))
        else if ix == NonS.length i
               then (\p -> (ArrayTB1 $ i <> pure p, PIdx ix Nothing)) <$>
                    createUndoFTBM p
               else Left
                      ("ix bigger than next elem " ++
                       show ix ++ "-" ++ show (L.length i) ++ "-")
applyUndoFTBM (IntervalTB1 i) (PInter b (p, l)) =
  (first IntervalTB1 <$>
   (checkNull =<<
    (if b
       then first ((flip interval) (upperBound' i)) <$>
            mapExtended p (lowerBound' i)
       else first (interval (lowerBound' i)) <$> mapExtended p (upperBound' i)))) <|>
  createNew
  where
    checkNull i
      | fst i == Interval.empty = Left "empty"
    checkNull j = Right j
    createNew = (, patch (IntervalTB1 i)) <$> createUndoFTBM (PInter b (p, l))
    mapExtended (Interval.Finite n) (Interval.Finite i, co) = do
      (newv, newp) <- applyUndoFTBM i n
      return ((Interval.Finite newv, l), PInter b (Interval.Finite newp, co))
    mapExtended (Interval.Finite p) (f, co) =
      (, PInter b (fmap patch f, co)) . (, l) . Interval.Finite <$>
      createUndoFTBM p
    mapExtended PosInf (f, co) =
      return ((Interval.PosInf, l), PInter b (fmap patch f, co))
    mapExtended NegInf (f, co) =
      return ((Interval.NegInf, l), PInter b (fmap patch f, co))
applyUndoFTBM (TB1 i) (PAtom p) = bimap TB1 PAtom <$> applyUndo i p
applyUndoFTBM b (PatchSet l) =
  join . patchSet $ foldUndo b l
  where
    patchSet =
      fmap
        (\(i, l) ->
           maybe (Left "empty patchset") Right $
           (i, ) . PatchSet <$> Non.nonEmpty l)
applyUndoFTBM a b = error ("applyFTB: " ++ show a ++ "\n ============= \n" ++show (let v = createUndoFTBM b  in (v == Right a ,v)))

checkInterM ::
     (Show a, Ord a)
  => PathFTB (Index a)
  -> Interval.Interval (FTB a)
  -> Either String (Interval.Interval (FTB a))
checkInterM (PInter b o) inter =
  if fst (lowerBound' inter) == Interval.PosInf ||
     fst (upperBound' inter) == Interval.NegInf
    then (Left "ilegal interval bounds")
    else Right inter

createUndoFTBM ::
     (Patch a, Show a, Ord a) => PathFTB (Index a) -> Either String (FTB a)
createUndoFTBM (POpt i) = if isJust i then (fmap LeftTB1 $ traverse createUndoFTBM i ) else Right (LeftTB1 Nothing)
createUndoFTBM (PIdx ix o) =
  maybe (Left "Cant delete") (fmap (ArrayTB1 . pure) . createUndoFTBM) o
createUndoFTBM (PInter b o) =
  IntervalTB1 <$> join (checkInterM (PInter b o) <$> inter)
  where
    inter =
      if b
        then flip interval (Interval.PosInf, False) <$>
             firstT (traverse createUndoFTBM) o
        else interval (Interval.NegInf, False) <$>
             (firstT (traverse createUndoFTBM) o)
createUndoFTBM (PAtom i) =
  maybe (Left  "cant create: ") (Right . TB1) $ createIfChange i
createUndoFTBM (PatchSet (i Non.:| l)) =
  F.foldl'
    (\i j -> flip (\i -> fmap fst . applyUndoFTBM i) j =<< i)
    (createUndoFTBM i)
    l

firstT f (i, j) = (, j) <$> f i

instance Ord a => Semigroup (FTB a) where
  LeftTB1 i <> LeftTB1 j = LeftTB1 j
  IntervalTB1 i <> IntervalTB1 j = IntervalTB1 (i `Interval.intersection` j)
  ArrayTB1 i <> ArrayTB1 j = ArrayTB1 (i <> j)
  TB1 i <> TB1 j = TB1 j

instance Applicative Editor where
  pure = Diff
  Diff f <*> Diff v = Diff $ f v
  _ <*> Delete = Delete
  Delete <*> _ = Delete
  Keep <*> _ = Keep
  _ <*> Keep = Keep

instance Monad Editor where
  return = pure
  Diff i >>= j = j i
  Keep >>= j = Keep
  Delete >>= j = Delete

instance Monad PathFTB where
  PAtom i >>= j = j i
  PIdx ix i >>= j = PIdx ix $ (j =<<) <$> i
  POpt i >>= j = POpt $ (j =<<) <$> i
  PatchSet i >>= j = PatchSet $ (j =<<) <$> i

liftPFK :: (Show k, Show b, Ord k) => PathAttr k b -> PathFTB (PTBRef k b)
liftPFK (PFK rel l i) = liftPRel l rel i

liftPRel ::
     (Show b, Show k, Ord k)
  => [PathAttr k b]
  -> [Rel k]
  -> PathFTB (TBIdx k b)
  -> PathFTB (PTBRef k b)
liftPRel l rel f = liftA3 PTBRef (F.foldl' (flip mergePFK) (PAtom []) rels) f (pure  [])
  where
    rels = catMaybes $ findPRel l <$> rel

filterPFK f (PatchSet l )  = PatchSet . Non.fromList <$> nonEmpty (Non.filter (isJust . filterPFK f) l)
filterPFK f (POpt l) = Just . POpt. join $ filterPFK f <$> l
filterPFK f (PIdx ix l) = fmap (PIdx  ix) . sequenceA $ filterPFK f <$> l
filterPFK f (PAtom p )= if f p then Just (PAtom p) else Nothing


recoverRel ::
     Eq k => PathFTB ([b], TBIdx k b) -> ([PathFTB b], PathFTB (TBIdx k b))
recoverRel i = (getZipList $ sequenceA $ ZipList . fst <$> i, snd <$> i)

mergePFK :: Show a => PathFTB a -> PathFTB [a] -> PathFTB [a]
mergePFK (POpt i) (POpt j) = POpt $ mergePFK <$> i <*> j
mergePFK (PatchSet i) (PatchSet j) = PatchSet $ Non.zipWith mergePFK i j
mergePFK (PIdx ixi i) (PIdx ixj j)
  | ixi == ixj = PIdx ixi $ mergePFK <$> i <*> j
  | otherwise = error ("wrong idx: " ++ show (ixi, ixj))
mergePFK (PAtom i) (PAtom l) = PAtom (i : l)
mergePFK (POpt i) j = POpt $ flip mergePFK j <$> i
mergePFK j (POpt i) = POpt $ mergePFK j <$> i
mergePFK (PatchSet j) i = PatchSet $ flip mergePFK i <$> j
mergePFK i (PatchSet j) = PatchSet $ mergePFK i <$> j
mergePFK (PIdx ix i) (PAtom l) = PIdx ix (flip mergePFK (PAtom l) <$> i)
mergePFK i j = error (show (i, j))

findPRel l (Rel k op j) = do
  PAttr k v <- L.find (\(PAttr i v) -> i == _relOrigin k) l
  return $ fmap (PAttr k . PAtom) v

recoverPFK ::
     [Key]
  -> [Rel Key]
  -> PathFTB (PTBRef Key Showable)
  -> Maybe (PathAttr Key Showable)
recoverPFK ori rel i =
  PFK rel
    (catMaybes $
     (\k ->
        PAttr k <$>
        (fmap join .
         traverse
           (fmap patchvalue .
            L.find ((== Inline k) . index) . sourcePRef) $
              i)) <$> ori) <$>
      (fmap (\v -> targetPRef  v <> targetPRefEdit v) <$>  (filterPFK  ( \i -> not $ L.null $ targetPRef i <> targetPRefEdit i  ) i))
