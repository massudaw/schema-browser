{-# LANGUAGE Arrows,FlexibleInstances,FlexibleContexts,DeriveAnyClass,DeriveGeneric,StandaloneDeriving,TypeFamilies,OverloadedStrings,DeriveTraversable,DeriveFoldable,GADTs,DeriveFunctor,RankNTypes,UndecidableInstances,ExistentialQuantification #-}
module Environment where

import RuntimeTypes
import Step.Host
import Step.Client
import Types
import Data.Maybe
import Types.Index as G
import Control.Monad.RWS
import Types.Patch
import qualified NonEmpty as Non
import Utils

import qualified Data.List as L
import Control.Arrow
import Data.Text (Text)
import Control.Applicative

import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Foldable as F

type DatabaseM ix i a = Parser (Kleisli TransactionM) ix i  a

type PluginM ix s m  i a = Parser (Kleisli (RWST (s,Index s) (Index s) ()  m )) ([ix],[ix]) i  a

instance (Show u ,Patch a) => Patch (M.Map u a ) where
  type Index  (M.Map u a) = [(u,Index a)]

data RowModifier
  = RowCreate
  | RowDrop
  | RowUpdate
  deriving(Show)


type MutationTy = Mutation (Prim KPrim (Text,Text))

data Row pk k
  = Row pk (Union (AttributePath k MutationTy))
  deriving(Show)

data JoinType
  = LeftJoin
  | InnerJoin
  deriving(Eq,Show,Ord)

data View i k
  = FromV i
  | JoinV (View i k ) (View i k) JoinType [Rel k] k
  | WhereV (View i k) [(Rel k,AccessOp Showable)]
  | ProjectV (View i k) (Union (AttributePath k MutationTy))
  deriving(Eq,Show,Ord)

tablesV (FromV i) = [(i,[])]
tablesV (JoinV i j  _ _ _ ) = tablesV i <> tablesV j
tablesV (WhereV i r ) = fmap (\(i,j)-> (i,j++ r)) $ tablesV i
tablesV (ProjectV i _ ) = tablesV i

data Module t pk k
  = Module t [Row pk k]
  deriving(Show)

data Namespace n t pk k
  = Namespace n [Module t pk k ]
  deriving(Show)

data Universe u n t pk k
  = Universe u [Namespace n t pk k]
  deriving(Show)

runEnv  r  e  =  (\(_,_,i) -> i) <$> runRWST   ( (runKleisli $ dynP r ) ()) e ()
evalEnv  r  e  =  (\(i,_,_) -> i) <$> runRWST   ( (runKleisli $ dynP r ) ()) e ()

indexTID (PIdIdx  ix )  (ArrayTB1 l) = l Non.!! ix
indexTID PIdOpt  (LeftTB1 l) = justError "no opt value" l

-- indexTIDM (PIdIdx  ix )  (ArrayTB1 l) = l `Non.atMay` ix
indexTIDM PIdOpt  (LeftTB1 l) = l
indexTIDM i j = error $ show (i,j)

liftTID (PIdIdx ix) l = PIdx ix (Just l)
liftTID PIdOpt  l = POpt $ Just l

unliftTID (PIdIdx ix)  (PIdx ix1 l)
  | ix == ix1 = l
  | otherwise = Nothing
unliftTID PIdOpt  (POpt l) = l

data Mutation  a = Mutation Bool Bool a deriving(Show,Eq,Ord)

readV :: (Patch a, Monad m) => KPrim ->  PluginM MutationTy  (Atom a) m i a
readV v = P ( [(Mutation True True (AtomicPrim v))],[]) (Kleisli (\_ ->  (\(Atom i,j) -> foldl apply i j )  <$> ask ))

readR :: (Compact (Index a),Ord (Index a),Ord a,Show a,Show (Index a),Show k,Ord k,Patch a, Monad m) => (Text,Text) ->  PluginM MutationTy (Atom (TBData k a)) m i (TBData k a)
readR v = P ( [(Mutation True True (RecordPrim v))],[]) (Kleisli (\_ ->  (\(Atom i,j) -> foldl apply i j )  <$> ask ))

deltaV  v = P ( [(Mutation False True (AtomicPrim v))],[]) (Kleisli (\_ ->  (\(Atom i,j) -> j )  <$> ask ))
changeV  v = P ( [(Mutation True True (AtomicPrim v))],[]) (Kleisli (\_ ->  (\(Atom i,j) -> (i,foldl apply i j) )  <$> ask ))
oldV  v = P ( [(Mutation True False (AtomicPrim v))],[]) (Kleisli (\_ ->  (\(Atom i,j) -> i)  <$> ask ))
writeV v = P ( [],[(Mutation False True (AtomicPrim v))]) (Kleisli (\i ->   tell  [i] ))

withReaderT4
  :: Functor n
    => (t2 -> t3)
    -> (t3 -> t2)
    -> (t1 -> t) -> RWST (t, t2) t2 s n b -> RWST (t1, t3) t3 s n b
withReaderT4 g h f = mapRWST (fmap (\(r,s,w) -> (r,s,g w ))) . withRWST  (\(i,p) j -> ((f i,h p) ,j))

withReaderT g f = mapRWST (fmap (\(r,s,w) -> (r,s,g w ))) . withRWST  (\i j -> (f i ,j))

withReaderMap
  :: (Show w,Show t1,Show t,Monad m, Monoid w) =>
    (Int -> t3 -> w)
     -> (Int -> t2 -> t1)
     -> (t -> Non.NonEmpty t)
     -> RWST (t, t1) t3 s m a
     -> RWST (t, t2) w s m (Non.NonEmpty a)
withReaderMap f h g  a= do
  (env ,_) <- ask
  mapM (\ix  -> withRWST (\(i,p) j -> ((g i Non.!! ix,h ix p) ,j)) .  mapRWST (fmap (\(r,s,w) -> (r,s, f ix w )))  $ a)  (Non.fromList [0..Non.length (g env) - 1])


withReaderT3
  :: (Monad m, Monoid w) =>
     (t3 -> w)
     -> (t2 -> t1)
     -> (t -> Maybe a1)
     -> RWST (a1, t1) t3 s m a
     -> RWST (t, t2) w s m (Maybe a)
withReaderT3 f h g  a= do
  (env ,_) <- ask
  maybe (return Nothing) (\_ -> withRWST (\(i,p) j -> ((justError "no opt" $ g  i,h p) ,j)) .  mapRWST (fmap (\(r,s,w) -> (Just r,s, f w )))  $ a)  (g env)

type Operation k p = Either (Union (AttributePath k p)) MutationTy
-- Primitive Value
irecord :: (Show k,Monad m ,Show s,Show (Index s)) =>
   PluginM (AttributePath k p)  (Atom (TBData k s))  m i a
  -> PluginM ((Union (AttributePath k p)))  (Atom ((TBData k s)))  m  i a
irecord = irecordU Many

irecordU :: (Show k,Monad m ,Show s,Show (Index s)) =>
  (forall a. [a ]-> Union a)
  -> PluginM (AttributePath k p)  (Atom (TBData k s))  m i a
  -> PluginM (Union (AttributePath k p))  (Atom ((TBData k s)))  m  i a
irecordU f (P (tidxi ,tidxo) (Kleisli op) )  = P (mapUnion f $ tidxi,mapUnion f $ tidxo) (Kleisli op )


ivalue :: (Monad m ,Show s,Show (Index s)) =>
  PluginM v  (Atom s) m i a
  -> PluginM (PathIndex PathTID v)  (Atom (FTB s) ) m i a
ivalue (P (tidxi ,tidxo) (Kleisli op) )  = P (TipPath <$> tidxi,TipPath  <$> tidxo) (Kleisli (withReaderT4 (fmap PAtom  )  (fmap unPAtom) (fmap unTB1) . op ))

unPAtom (PAtom i) = i
unPAtom i = error (show i)


iftb :: Monad m =>
       PathTID
       -> PluginM (PathIndex PathTID v)  (Atom (FTB b))  m i a
       -> PluginM (PathIndex PathTID v)  (Atom (FTB b))  m i a
iftb s   (P (tidxi ,tidxo) (Kleisli op) )  = P (NestedPath s <$> tidxi,NestedPath s <$> tidxo) (Kleisli (withReaderT4 (fmap (liftTID s)) (catMaybes . fmap (unliftTID s)) (fmap (indexTID s) ) . op  ))


imap :: (Show (Index b),Show b,Monad m) =>
       PluginM (PathIndex PathTID v)  (Atom (FTB b))  m i a
       -> PluginM (PathIndex PathTID v)  (Atom (FTB b))  m i (Non.NonEmpty a)
imap (P (tidxi ,tidxo) (Kleisli op) )  = P (NestedPath PIdTraverse <$> tidxi, NestedPath PIdTraverse <$> tidxo) (Kleisli (\i -> withReaderMap (\ix -> fmap (PIdx ix . Just))  (\ix -> catMaybes . fmap (unliftTID (PIdIdx ix))) (traverse  unArray) (op i) ))


iopt :: (Show b,Monad m )=>
       PluginM (PathIndex PathTID v)  (Atom (FTB b))  m i a
       -> PluginM (PathIndex PathTID v)  (Atom (FTB b))  m i (Maybe a)
iopt (P (tidxi ,tidxo) (Kleisli op) )  = P (NestedPath PIdOpt <$> tidxi, NestedPath PIdOpt <$> tidxo) (Kleisli (withReaderT3 (fmap (liftTID PIdOpt))  (catMaybes . fmap (unliftTID PIdOpt)) (traverse (indexTIDM PIdOpt) ) . op  ))


-- Attribute indexing
ifield ::
       (Monad m ,Show k ,Ord k) => k
       -> PluginM (PathIndex PathTID p)  (Atom (FTB Showable )) m i a
       -> PluginM (AttributePath k p)  (Atom (TBData k Showable ))  m i a
ifield s (P (tidxi ,tidxo) (Kleisli op) )  = P (PathAttr s <$> tidxi,PathAttr s <$> tidxo) (Kleisli (withReaderT4 (\ v -> [PAttr s <$> v]) (concat . fmap (catMaybes .fmap pvalue) ) (fmap (_tbattr .justError ("no field " ++ show s ).indexField (IProd Nothing s))) . op ))
  where pvalue (PAttr k v) | k == s = Just v
        pvalue i = Nothing

iinlineR ::
       (Monad m ,Patch s ,Show s ,Show k ,Ord k) => k
       -> PluginM (PathIndex PathTID p)  (Atom (FTB (TBData k s))) m i a
       -> PluginM (AttributePath k p)  (Atom (TBData k s))  m i a
iinlineR s (P (tidxi ,tidxo) (Kleisli op) )  = P (PathAttr s <$> tidxi,PathAttr s <$> tidxo) (Kleisli (withReaderT4 (\v -> [PInline s   <$> v]) (concat . fmap (fmap pvalue )) (fmap (\ v -> _fkttable .justError ( "no inline " ++ show (s,v)). indexField (IProd Nothing s) $v   )) . op ))
  where pvalue (PInline _ v) = v

iinline ::
       (Monad m ,Patch s ,Show s ,Show k ,Ord k) => k
       -> PluginM (PathIndex PathTID (Union (AttributePath k p)))  (Atom (FTB (TBData k s)))  m  i a
       -> PluginM (AttributePath k p)  (Atom (TBData k s))  m i a
iinline s (P (tidxi ,tidxo) (Kleisli op) )  = P (PathInline s <$> tidxi,PathInline s <$> tidxo) (Kleisli (withReaderT4 (\v -> [PInline s   <$> v]) (concat . fmap (fmap pvalue )) (fmap (\v -> _fkttable .justError ( "no inline " ++ show (s,v)). indexField (IProd Nothing s)  $v )) . op ))
  where pvalue (PInline _ v) = v


iforeign ::
       (Monad m ,Patch s ,Show s ,Show (Index s) ,Show k ,Ord k) => [Rel k]
       -> PluginM (PathIndex PathTID (Union (AttributePath k p)))  (Atom (FTB (TBData k s)))  m  i a
       -> PluginM (AttributePath k p)  (Atom (TBData k s))  m i a
iforeign s (P (tidxi ,tidxo) (Kleisli op) )  = P (mapNonEmpty (PathForeign s) tidxi,mapNonEmpty (PathForeign s) tidxo) (Kleisli (withReaderT4 (\v -> pure .PFK s [] <$> v ) (concat . fmap (catMaybes . fmap pvalue ))(fmap ( _fkttable . justError ("no foreign " ++ show s). indexField (Nested(Non.fromList s) (Many []))   ) ). op ))
  where pvalue (PFK  rel _ v) | rel == s = Just v
        pvalue i = Nothing

mapNonEmpty f i = join . maybeToList $ fmap f <$>  nonEmpty i

-- Row

isum :: ((Show k,Monad m ,Show s,Show (Index s)))
  => [PluginM (AttributePath k p) (Atom ((TBData k s))) m i (Maybe a)]

  -> PluginM (Union (AttributePath k p))  (Atom ((TBData k s)))  m  i a
-- -> PluginM (Union(AttributePath k p)) o m i a
isum  lsp = irecordU ISum $ P ( concat $ fmap (fst .staticP) ls, concat $ fmap (snd.staticP)  ls ) (Kleisli (\i -> fmap (justError "no value ") $ foldr (liftA2 (<|>)) (return Nothing) $ (\ j -> (unKleisli . dynP $ j) i ) <$> ls))
  where unKleisli (Kleisli op) = op
        ls =  lsp

arow :: (Show (Index s),Show s,Show k ,Monad m) =>
  RowModifier
  -> PluginM (AttributePath k MutationTy) (Atom (TBData k s)) m i a
  -> PluginM (Row RowModifier k ) (Atom (TBData k s)) m i a
arow  m  p = P (fmap (Row m) tidxi ,fmap (Row m) tidxo) op
  where P (tidxi ,tidxo) op  = irecord p


mapUnion f i = maybeToList $ f <$> nonEmpty i

mapUnionU f i = manyU . maybeToList $ f <$> nonEmptyU i
nonEmptyU (Many i) = Many <$> nonEmpty i


-- Table

itable :: Monad m
       => (Show t ,Ord t)
       => t
       -> PluginM (Row pk k)  (TableIndex k Showable )  m  i a
       -> PluginM (Module t pk k )  (M.Map t (TableIndex k Showable) )  m i a
itable s (P (tidxi ,tidxo) (Kleisli op) )  = P (mapUnion (Module s) tidxi,mapUnion (Module s) tidxo) (Kleisli (withReaderT4 (pure . (s,)) (last . fmap snd) (justError ("no table "++ show s). M.lookup  s ) . op ))

atable ::( Show t ,Monad m)
       => Ord t
       => t
       -> PluginM (Row pk k)  o  m  i a
       -> PluginM (Module t pk k )  o  m i a
atable s (P (tidxi ,tidxo) (Kleisli op) )  = P (mapUnion (Module s) tidxi,mapUnion (Module s) tidxo) (Kleisli (withReaderT id id  . op ))


-- Schema
ischema :: (Monad m ,Show s ,Ord s)
       => s
       -> PluginM (Module t pk k)  (M.Map t (TableIndex k Showable ))  m  i a
       -> PluginM (Namespace s t pk k )  (M.Map s (M.Map t (TableIndex k Showable)))  m i a
ischema s (P (tidxi ,tidxo) (Kleisli op) )  = P (mapUnion (Namespace s) tidxi,mapUnion (Namespace s) tidxo) (Kleisli (withReaderT4 (pure . (s,)) (concat .  fmap snd) (justError ("no schema" ++ show s). M.lookup  s ) . op ))

aschema :: (Monad m ,Ord s)
       => s
       -> PluginM (Module t pk k)  o  m  i a
       -> PluginM (Namespace s t pk k )  o  m i a
aschema s (P (tidxi ,tidxo) (Kleisli op) )  = P (mapUnion (Namespace s) tidxi,mapUnion (Namespace s) tidxo) (Kleisli (withReaderT id id . op ))

from :: (Eq (Namespace s t pk k),Ord s, Ord t,Show t,Monad m ,Show s)=> s -> t -> PluginM (Namespace s t pk k )  (M.Map s (M.Map t (TableIndex k Showable)))  m i (TableIndex k Showable)
from s t = P ([Namespace s ([Module t ([])])] ,[]) (Kleisli (\_ -> justError ("table not found: " ++ show (s,t)). (\i -> M.lookup t  =<<  M.lookup s i ) . fst <$>ask))


-- Database
iuniverse   :: (Monad m ,Show u ,Ord u)
       => u
       -> PluginM (Namespace s t pk  k)  (M.Map s (M.Map t (TableIndex k Showable )))  m  i a
       -> PluginM (Universe u s t pk  k )  (M.Map u (M.Map s (M.Map t (TableIndex k Showable)))) m i a
iuniverse s (P (tidxi ,tidxo) (Kleisli op) )  = P (mapUnion (Universe s) tidxi,mapUnion (Universe s) tidxo) (Kleisli (withReaderT4 (pure . (s,)) (concat . fmap snd) (justError ("no database " ++ show s). M.lookup  s ) . op ))

type PluginMethod  a b = PluginM (Namespace Text Text RowModifier Text) (Atom (TBData Text Showable)) TransactionM a b

patternMatch  :: (Show a,Show k,Ord k) => Union (AttributePath k MutationTy) -> TBData k a -> Bool
patternMatch (Many i)  v =  F.all (flip attrMatch v) i
patternMatch (ISum i)  v =  F.any (flip attrMatch v) i

matchPrim (Mutation _ _ (AtomicPrim PText)) _   = True
matchPrim i j = True

attrMatch :: (Show k,Show a,Ord k) => AttributePath k MutationTy ->  TBData k a -> Bool
attrMatch (PathAttr i p) v =  maybe False (matchFTB matchPrim p .  _tbattr) $ kvLookup (S.singleton $ Inline i)  v
attrMatch (PathInline i p) v = maybe False (matchFTB patternMatch p .  _fkttable) $ kvLookup (S.singleton $ Inline i)  v
attrMatch (PathForeign i p)  v = maybe False (matchFTB patternMatch p .  _fkttable) $ kvLookup (S.fromList i)  v

-- matchFTB f i j | traceShow (i,j) False = undefined
matchFTB f (TipPath i ) (TB1 v ) =  f i v
matchFTB f (NestedPath PIdOpt  l ) (LeftTB1 v ) =  maybe False (matchFTB f l) v
matchFTB f i j = error$  show (i,j)


translate
  :: (Show k,Ord k)
  => PluginM (Namespace Text Text RowModifier k) (Atom (TBData Text Showable)) TransactionM () t1
  -> ((Text, Text), [(TBData k Showable -> Bool ,OverloadedRule)])
translate  r
   = case staticP r  of
       ([Namespace i [Module m [(Row RowDrop s )]]],_) ->
         let
           lift j i = do
             inf <- askInf
             ((dropRow' (lookMeta inf m)  . F.foldl' apply i ) . fmap (liftPatch inf  m)) <$> j (Atom $ mapKey' keyValue i,[])
         in ((i,m),[(patternMatch s ,DropRule (lift (runEnv r)))])
       ([Namespace i [Module m [Row RowCreate s ]]],_) ->
         let
           lift j i = do
             inf <- askInf
             ((createRow' (lookMeta inf m) . F.foldl' apply i ) . fmap (liftPatch inf  m)) <$> j (Atom $ mapKey' keyValue i,[])
         in ((i,m),[(patternMatch s ,CreateRule (lift (runEnv r)))])
       ([Namespace i [Module m [Row RowUpdate s ]]],_)  ->
         let
           lift j i p = do
             inf <- askInf
             ((\a-> RowPatch . fmap PatchRow . (G.getIndex (lookMeta inf m) i,) . L.head . compact $ (p:a)) . fmap (liftPatch inf  m)) <$> j (Atom $ mapKey' keyValue i, [firstPatch keyValue p])
         in ((i,m),[(patternMatch s ,UpdateRule (lift (runEnv r)))])
