{-# LANGUAGE
 Arrows,
 FlexibleContexts,
 TypeFamilies,
 NoMonomorphismRestriction,
 OverloadedStrings,
 TupleSections #-}
module Default where

import Types
import qualified Data.Poset as P
import Utils
import qualified NonEmpty as Non
import RuntimeTypes
import Debug.Trace
import Query
import Types.Patch
import qualified  Data.Map as M
import qualified  Data.HashMap.Strict as HM
import Control.Applicative
import Data.Monoid
import Data.Maybe
import qualified Data.List as L
import qualified Data.Foldable as F
import qualified Data.Text as T
import qualified Data.Set as S


foldTopologicaly iniset fun fks = snd (F.foldl' (filterDuplicated fun) (iniset,[]) $ P.sortBy (P.comparing (RelSort . F.toList . pathRelRel))fks)

filterDuplicated  fun (i,l)  j = (i <> S.map _relOrigin (pathRelRel j) ,fun i j : l)

evaluateKeyStatic (ConstantExpr i) = Just i
evaluateKeyStatic (Function _ _ ) = Nothing -- evaluateKeyStatic

defaultAttrs k = PAttr k <$> (go (_keyFunc $keyType k) <|> fmap patch (evaluateKeyStatic  =<< keyStatic k))
  where
    go ty  =
      case  ty of
        KOptional :i -> Just (POpt (go i))
        KSerial :i -> Just (POpt (go i))
        i -> Nothing

defaultFKS inf prev (FKJoinTable i j )
  | L.all isRel i &&  L.any (isKOptional . keyType . _relOrigin) i = Just $ PFK i  (catMaybes (defaultAttrs .  _relOrigin  <$> filter (not. (`S.member` prev) ._relOrigin) i)) (POpt Nothing)
  | otherwise  = Nothing
  where isRel Rel{} = True
        isRel _ = False
defaultFKS inf prev (FKInlineTable k i) =
  case _keyFunc $ keyType k of
    KOptional :_ -> Just (PInline k (POpt Nothing))
    KSerial :_ -> Just (PInline k (POpt Nothing))
    [] -> PInline k . PAtom  <$> nonEmpty (defaultTableType rinf (lookTable rinf (snd i)))
    _ ->  Nothing
  where rinf = fromMaybe inf $ HM.lookup (fst i) (depschema inf)
defaultFKS _ prev (FunctionField  k _ _ ) = defaultAttrs k
defaultFKS inf prev (RecJoin     _ i ) =  defaultFKS inf prev i

defaultTB inf prev (RecJoin     _ i ) v =  defaultTB inf prev i v
defaultTB _ _ (FunctionField  k _ _ ) _ = defaultAttrs k
defaultTB inf prev (FKInlineTable k i) (IT _ l) = PInline k <$>  go (_keyFunc $ keyType k) l
  where
    go   (KArray :xs) (ArrayTB1 l) = Just . PatchSet . Non.fromList $ zipWith (\i j -> (PIdx i ) $ go xs j ) [0..] (F.toList l)
    go  (KSerial :xs) (LeftTB1 i) =
        case i of
          Just i -> POpt . Just <$> go xs i
          Nothing -> Just (POpt Nothing)
    go  (KOptional :xs) (LeftTB1 i) =
        case i of
          Just i -> POpt . Just <$> go xs i
          Nothing -> Just (POpt Nothing)
    go  [] (TB1  v) = PAtom  <$> nonEmpty (defaultTableData rinf (lookTable rinf (snd i)) v)
    go  _  _ = Nothing
    rinf = fromMaybe inf $ HM.lookup (fst i) (depschema inf)
defaultTB inf prev j@FKJoinTable {} _ = defaultFKS inf prev j

defaultTableData
  :: InformationSchemaKV Key Showable
     -> TableK (FKey (KType (Prim KPrim (T.Text, T.Text))))
     -> TBData Key Showable
     -> [PathAttr (FKey (KType CorePrim)) Showable]
defaultTableData inf table v =
  let
    nonFKAttrs = nonFKS table
 in catMaybes $ fmap defaultAttrs  nonFKAttrs <> foldTopologicaly (S.fromList  nonFKAttrs) (\pred ix -> maybe (defaultFKS inf pred ix) (defaultTB inf pred ix) (M.lookup (pathRelRel ix) (unKV v))) (rawFKS table)

defaultTableType
  :: InformationSchemaKV Key Showable
     -> TableK (FKey (KType (Prim KPrim (T.Text, T.Text))))
     -> [PathAttr (FKey (KType CorePrim)) Showable]
defaultTableType inf table =
  let
    nonFKAttrs = nonFKS table
  in catMaybes $ fmap defaultAttrs  nonFKAttrs <> foldTopologicaly (S.fromList nonFKAttrs) (defaultFKS inf)  (rawFKS table)

nonFKS :: Table -> [Key]
nonFKS table =  nonFKAttrs
    where
    fks' =  rawFKS table
    items = rawAttrs table
    fkSet,funSet:: S.Set Key
    fkSet =   S.unions . fmap (S.fromList . fmap _relOrigin . (\i -> if all isInlineRel i then i else filterReflexive i ) . S.toList . pathRelRel ) $ filter isReflexive  $ filter(not.isFunction ) fks'
    funSet = S.unions $ pathRelOri <$> filter isFunction fks'
    nonFKAttrs :: [Key]
    nonFKAttrs =   filter (\i -> not $ S.member i (fkSet <> funSet)) items
