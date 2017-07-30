{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Types.Inference
  (inferOperatorType
  ,runInfer
  ,Scheme(..)
  ,TVar(..)
  ,infer
  ,Type(..)
  ,typeInt
  ,extend
  ,inferExpr
  ,emptyTyenv
  ) where

import Control.Monad.State
import Control.Monad.Except
import Data.Maybe
import Data.Monoid
import Data.List (nub)
import Data.Foldable (foldr)
import qualified Data.Map as Map
import qualified Data.Set as Set

import Data.Text(Text)

import Types
import Debug.Trace
import GHC.Stack

inferOperatorType ::
                     BinaryOperator -> KType a -> KType a

inferOperatorType op  (Primitive l o) = Primitive (inferOp op l ) o
inferOp (Flip (Flip e))  i = inferOp e i
inferOp e (KOptional : i) = inferOp e i
inferOp e (KDelayed : i) = inferOp e i
inferOp e (KSerial : i) = inferOp e i
inferOp Contains  (KInterval : i) = i
inferOp Contains  (KArray : i) = KArray : i
inferOp (Flip Contains) i = KInterval : i
inferOp (AnyOp e ) (KArray : i) = inferOp e i
inferOp (Flip (AnyOp e)) (KArray : i) =  KArray : inferOp (Flip e) i
inferOp (Flip (AnyOp e)) i =  KArray : inferOp (Flip e) i
inferOp Equals i = i
inferOp (GreaterThan _) i = i
inferOp (Flip (GreaterThan _)) i = i
inferOp (LowerThan _) i = i
inferOp (Flip (LowerThan _)) i = i
inferOp (Flip Equals) i = i
inferOp IntersectOp i = i
inferOp (Flip IntersectOp ) i = i
inferOp o k = errorWithStackTrace ("infererror" ++ show (o,k))



newtype TVar = TV String
  deriving (Show, Eq, Ord)

type Var = Integer

data Type
  = TVar TVar
  | TCon (Prim  KPrim (Text,Text))
  | TCon1 [KTypePrim] Type
  | TArr Type Type
  | TOp Op Type Type
  deriving (Show, Eq, Ord)

data Op
  = Mult
  | Div
  | Equal
  deriving(Show,Eq,Ord)

infixr `TArr`

data Scheme = Forall [TVar] Type
  deriving (Show, Eq, Ord)


typeInt :: Type
typeInt  = TCon (AtomicPrim (PInt 8))

typeFloat :: Type
typeFloat = TCon ( AtomicPrim PDouble)

typeBool :: Type
typeBool = TCon ( AtomicPrim PBoolean)

newtype TypeEnv = TypeEnv (Map.Map Var Scheme)
  deriving Monoid

data Unique = Unique { count :: Integer }

type Infer = ExceptT TypeError (State Unique)

type Subst = Map.Map TVar Type

data TypeError
  = UnificationFail Type Type
  | InfiniteType TVar Type
  | UnboundVariable String
  deriving(Show)



runInfer :: Infer (Subst, Type) -> Either TypeError Scheme
runInfer m = case evalState (runExceptT m) initUnique of
  Left err  -> Left err
  Right res  -> Right $ closeOver res

closeOver :: (Map.Map TVar Type, Type) -> Scheme
closeOver (sub, ty) = normalize sc
  where sc = generalize emptyTyenv (apply sub ty)

initUnique :: Unique
initUnique = Unique { count = 0 }

extend :: TypeEnv -> (Var, Scheme) -> TypeEnv
extend (TypeEnv env) (x, s) = TypeEnv $ Map.insert x s env

emptyTyenv :: TypeEnv
emptyTyenv = TypeEnv Map.empty

typeof :: TypeEnv -> Var -> Maybe Scheme
typeof (TypeEnv env) name = Map.lookup name env

class Substitutable a where
  apply :: Subst -> a -> a
  ftv   :: a -> Set.Set TVar

instance Substitutable Type where
  apply s (TCon1 l f)    = TCon1 l (apply s f)
  apply _ (TCon a)       = TCon a
  apply s t@(TVar a)     = Map.findWithDefault t a s
  apply s (t1 `TArr` t2) = apply s t1 `TArr` apply s t2
  apply s (TOp op t1 t2) = TOp op (apply s t1 ) (apply s t2)

  ftv TCon{}         = Set.empty
  ftv (TCon1 l v)    =  ftv v
  ftv (TVar a)       = Set.singleton a
  ftv (t1 `TArr` t2) = ftv t1 `Set.union` ftv t2
  ftv (TOp op t1 t2) = ftv t1 `Set.union` ftv t2



instance Substitutable Scheme where
  apply s (Forall as t)   = Forall as $ apply s' t
                            where s' = foldr Map.delete s as
  ftv (Forall as t) = ftv t `Set.difference` Set.fromList as

instance Substitutable a => Substitutable [a] where
  apply = fmap . apply
  ftv   = foldr (Set.union . ftv) Set.empty

instance Substitutable TypeEnv where
  apply s (TypeEnv env) =  TypeEnv $ Map.map (apply s) env
  ftv (TypeEnv env) = ftv $ Map.elems env


nullSubst :: Subst
nullSubst = Map.empty


compose :: Subst -> Subst -> Subst
s1 `compose` s2 = Map.map (apply s1) s2 `Map.union` s1

unify ::  Type -> Type -> Infer Subst
unify (l `TArr` r) (l' `TArr` r')  = do
  s1 <- unify l l'
  s2 <- unify (apply s1 r) (apply s1 r')
  return (s2 `compose` s1)

unify (l  `TArr` r) (TOp op l' r')  = do
  s1 <- fmap traceShowId $ unify l l'
  s2 <- unify (apply s1 r) (apply s1 r')
  return (s2 `compose` s1)



unify (TVar a) t = bind a t
unify t (TVar a) = bind a t
unify (TCon1 l  a) (TCon1 j b)
  | l == j = unify a b
unify (TCon a) (TCon b)
  | a == b = return nullSubst
unify (TCon (AtomicPrim(PDimensional _ _))) (TCon (AtomicPrim (PDimensional _ _ ))) = return nullSubst
unify t1 t2 = throwError $ UnificationFail t1 t2

bind ::  TVar -> Type -> Infer Subst
bind a t
  | t == TVar a     = return nullSubst
  | occursCheck a t = throwError $ InfiniteType a t
  | otherwise       = return $ Map.singleton a t

occursCheck ::  Substitutable a => TVar -> a -> Bool
occursCheck a t = a `Set.member` ftv t

letters :: [String]
letters = [1..] >>= flip replicateM ['a'..'z']

fresh :: Infer Type
fresh = do
  s <- get
  put s{count = count s + 1}
  return $ TVar $ TV (letters !! fromIntegral (count s))

instantiate ::  Scheme -> Infer Type
instantiate (Forall as t) = do
  as' <- mapM (const fresh) as
  let s = Map.fromList $ zip as as'
  return $ apply s t

generalize :: TypeEnv -> Type -> Scheme
generalize env t  = Forall as t
  where as = Set.toList $ ftv t `Set.difference` ftv env


lookupEnv :: TypeEnv -> Var -> Infer (Subst, Type)
lookupEnv (TypeEnv env) x =
  case Map.lookup x env of
    Nothing -> throwError $ UnboundVariable (show x)
    Just s  -> do t <- instantiate s
                  return (nullSubst, t)


infer :: OpsEnv -> TypeEnv -> Expr -> Infer (Subst, Type)
infer ops env ex = case ex of

  Value x -> lookupEnv env (fromIntegral x)

  Function op l -> do
    inferPrim ops env l  (fromJust (Map.lookup op ops ))



inferPrim :: OpsEnv -> TypeEnv -> [Expr] -> Scheme -> Infer (Subst, Type)
inferPrim ops env l t = do
  tv <- fresh
  (s1, tf) <- foldM inferStep (nullSubst, id) l
  st <- instantiate t
  s2 <- unify (apply s1 (tf tv)) st
  return (s2 `compose` s1, apply s2 tv)
  where
  inferStep (s, tf) exp = do
    (s', t) <- infer ops (apply s env) exp
    return (s' `compose` s, tf . (TArr t))

type OpsEnv = Map.Map Text Scheme


inferExpr :: OpsEnv ->  TypeEnv -> Expr -> Either TypeError Scheme
inferExpr ops env = runInfer . infer ops env

inferTop :: OpsEnv -> TypeEnv -> [(Var, Expr)] -> Either TypeError TypeEnv
inferTop ops env [] = Right env
inferTop ops env ((name, ex):xs) = case inferExpr ops env ex of
  Left err -> Left err
  Right ty -> inferTop ops (extend env (name, ty)) xs

normalize :: Scheme -> Scheme
normalize (Forall ts body) = Forall (fmap snd ord) (normtype body)
  where
    ord = zip (nub $ fv body) (fmap TV letters)

    fv (TVar a)   = [a]
    fv (TArr a b) = fv a ++ fv b
    fv (TOp op  a b) = fv a ++ fv b
    fv (TCon _)   = []
    fv (TCon1 l i )   = fv i

    normtype (TArr a b) = TArr (normtype a) (normtype b)
    normtype (TOp op  a b) = TOp op (normtype a) (normtype b)
    normtype (TCon1 [] f)   = normtype f
    normtype (TCon1 a f)   = TCon1 a (normtype f)
    normtype (TCon a)   = TCon a
    normtype (TVar a)   =
      case lookup a ord of
        Just x -> TVar x
        Nothing -> error "type variable not in signature"


