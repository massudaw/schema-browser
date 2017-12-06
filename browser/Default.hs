{-# LANGUAGE Arrows,FlexibleContexts,TypeFamilies ,NoMonomorphismRestriction,OverloadedStrings ,TupleSections #-}
module Default  where

import Types
import qualified Types.Index as G
import Environment
import Step.Common
import qualified Data.Poset as P
import Step.Host
import Data.Functor.Apply
import System.Environment
import Safe
import Control.Monad
import Utils
import Text
import Control.Monad.Reader
import GHC.Stack
import RuntimeTypes
import Query
import Control.Monad.Writer hiding (pass)
import System.Time.Extra
import Types.Patch
import Data.Ord
import Data.Functor.Identity
import qualified  Data.Map as M
import qualified  Data.HashMap.Strict as HM

import Data.Tuple
import Data.String

import Control.Applicative
import Data.Maybe
import qualified Data.List as L

import Prelude hiding (takeWhile,head)

import qualified Data.Foldable as F
import qualified Data.Text as T
import Data.Text (Text)
import qualified Data.Set as S


--- Generate default values  patches
--
deftable
  :: InformationSchemaKV Key Showable
     -> TableK (FKey (KType (Prim KPrim (T.Text, T.Text))))
     -> [PathAttr (FKey (KType CorePrim)) Showable]
deftable inf table =
  let
    fks' = S.toList $ rawFKS table
    items = tableAttrs table
    fkSet,funSet:: S.Set Key
    fkSet =   S.unions . fmap (S.fromList . fmap _relOrigin . (\i -> if all isInlineRel i then i else filterReflexive i ) . S.toList . pathRelRel ) $ filter isReflexive  $ filter(not.isFunction ) $ fks'
    funSet = S.unions $ fmap pathRelOri  $ filter (isFunction) (fks')
    nonFKAttrs :: [Key]
    nonFKAttrs =   filter (\i -> not $ S.member i (fkSet <> funSet)) items
    fks = fks'

  in catMaybes $ fmap defaultAttrs  nonFKAttrs <> fmap (defaultFKS  inf) fks


defaultAttrs  k  = PAttr k <$> (go (_keyFunc $keyType k) <|> fmap patch (keyStatic k))
  where
    go ty  =
      case  ty of
        KOptional :i -> Just (POpt (go i))
        i -> Nothing

defaultFKS inf (FKJoinTable i j )
  | L.all isRel i &&  L.any (isKOptional . keyType . _relOrigin ) i = flip (PFK i) (POpt Nothing) <$>  (traverse (defaultAttrs .  _relOrigin ) i)
  | otherwise  = Nothing
  where isRel (Rel _  _ _ ) = True
        isRel _ = False
defaultFKS inf (FKInlineTable k i) =
  case _keyFunc $ keyType k of
    KOptional :_ -> Just (PInline k (POpt Nothing))
    [] -> PInline k . PAtom .(tableMeta (lookTable rinf (snd i)) , G.Idex [],) <$> nonEmpty ( deftable rinf (lookTable rinf (snd i)))
    _ ->  Nothing
  where rinf = fromMaybe inf $ HM.lookup (fst i) (depschema inf)
defaultFKS _ (FunctionField  k _ _ ) = defaultAttrs k
defaultFKS inf (RecJoin     _ i ) =  defaultFKS inf i



