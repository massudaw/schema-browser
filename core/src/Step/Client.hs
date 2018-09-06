{-# LANGUAGE Arrows, OverloadedStrings, FlexibleContexts,
  NoMonomorphismRestriction #-}

module Step.Client
  ( module Step.Common
  , notNull
  , idxR
  , idxK
  , idxKIn
  , act
  , odx
  , odxR
  , nameO
  , nameI
  , callI
  , atAny
  , atAnyM
  , idxA
  , atMA
  , callO
  , odxM
  , idxM
  , atR
  , atK
  , atRA
  , attrT
  , tb
  , indexTable
  , atMR
  , anyP
  , manyU
  ) where

import Control.Applicative
import Control.Arrow
import Control.Category (Category(..))
import Control.Monad.Reader
import qualified NonEmpty as Non
import Control.Monad.Trans.Maybe
import qualified Data.Bifunctor as BF
import Data.Foldable (toList)
import qualified Data.Map as M
import Data.Maybe
import Data.Monoid
import qualified Data.Set as S
import Data.String
import qualified Data.Text as T
import Data.Text (Text)
import Prelude hiding ((.), id)
import Step.Common
import Types
import Utils

act :: (Monoid s, Monad m) => (a -> m b) -> Parser (Kleisli m) s a b
act a = P mempty (Kleisli a)

atAny k = atP k . anyP
atAnyM k  =  fmap join . atMR k . anyPM

allP = id

anyPM ps =
  P
    (ISum (concat $ fmap unMany fsum), ISum (concat $ fmap unMany ssum))
    (Kleisli
       (\i ->
          runMaybeT $
          foldr1 ((<|>)) (fmap ($i) asum)))
  where
    unMany (Many i)=  i
    unMany (ISum l) = error (show ("ISum" ,l))
    asum = fmap (\(P s (Kleisli j)) -> fmap MaybeT j) ps
    fsum = fmap (\(P s _) -> fst s) ps
    ssum = fmap (\(P s _) -> snd s) ps


anyP ps =
  P
    (ISum (concat $ fmap unMany fsum), ISum (concat $ fmap unMany ssum))
    (Kleisli
       (\i ->
          fmap (justError "no instance found") . runMaybeT $
          foldr1 ((<|>)) (fmap ($i) asum)))
  where
    unMany (Many i)=  i
    unMany (ISum l) = error (show ("ISum" ,l))
    asum = fmap (\(P s (Kleisli j)) -> fmap MaybeT j) ps
    fsum = fmap (\(P s _) -> fst s) ps
    ssum = fmap (\(P s _) -> snd s) ps

atMR k (P (fsum, ssum) (Kleisli a)) =
  P (nest fsum, nest ssum) (Kleisli ((\v -> do
      i <- ask
      let o = unSOptional  =<<  indexTB1M ind  i
      traverse (\i -> local (unTB1 . fromJust .unSOptional . indexTB1 ind) (a v)) o)))
  where
    unTB1 (TB1 i) = i
    unTB1 j = error (show j)
    nest (Many []) = Many []
    nest (ISum []) = Many []
    nest ls = Many [Nested (Non.fromList (Inline .iprodRef <$> ind)) ls]
    ind = splitIndex Nothing k


atP k (P (fsum, ssum) (Kleisli a)) =
  P (nest fsum, nest ssum) (Kleisli (fmap (local (unTB1 . fromJust . unSOptional. indexTB1 ind)) a))
  where
    unTB1 (TB1 i) = i
    unTB1 j = error (show j)
    nest (Many []) = Many []
    nest (ISum []) = Many []
    nest ls = Many [Nested (Non.fromList (Inline .iprodRef <$> ind)) ls]
    ind = splitIndex (Just $ Not IsNull) k

nest :: [Rel Text] -> Union (Access Text) -> Union (Access Text)
nest ind (Many []) = Many []
nest ind (Many [(Rec ix i)]) = Many [Nested (Non.fromList ind) $ Many [Rec ix i]]
nest ind j = Many [Nested (Non.fromList ind) j]

atMA ::
     (KeyString t2, Show t2, MonadReader (TBData t2 Showable) m, Ord t2)
  => String
  -> Parser (Kleisli m) (Union (Access Text), Union (Access Text)) t t1
  -> Parser (Kleisli m) (Union (Access Text), Union (Access Text)) t [t1]
atMA i (P s (Kleisli j)) =
  P
    (BF.second (nest (Inline . iprodRef <$> ind)) . BF.first (nest (Inline . iprodRef <$> ind)) $
     s)
    (Kleisli
       (\i ->
          mapM (\env -> local (const env) (j i)) =<<
          (return .
           maybe [] (\(ArrayTB1 l) -> unTB1 <$> toList l) .
            join . fmap unSOptional . indexTB1M ind) =<<
          ask))
  where
    ind = splitIndex Nothing i

atRA ::
     (KeyString t2, Show t2, MonadReader ((TBData t2 Showable)) m, Ord t2)
  => String
  -> Parser (Kleisli m) (Union (Access Text), Union (Access Text)) t t1
  -> Parser (Kleisli m) (Union (Access Text), Union (Access Text)) t [t1]
atRA i (P s (Kleisli j)) =
  P
    (BF.second (nest (Inline . iprodRef <$> ind)) . BF.first (nest (Inline . iprodRef <$> ind)) $
     s)
    (Kleisli
       (\i ->
          mapM (\env -> local (const env) (j i)) =<<
          (return .
           maybe [] (\(ArrayTB1 l) -> unTB1 <$> toList l) .
           unSOptional . indexTB1 ind) =<<
          ask))
  where
    ind = splitIndex Nothing i

unLeftTB1 v =
  case v of
    (LeftTB1 i) -> i
    i@(TB1 _) -> Just i

at b i (P s (Kleisli j)) =
  P
    (BF.second (nest (Inline . iprodRef <$> ind b)) .
      BF.first (nest (Inline . iprodRef <$> ind b)) $
     s)
    (Kleisli (\i -> onlyLocal (fmap unTB1 . unLeftTB1 . indexTB1 (ind b)) (j i)))
  where
    ind b = splitIndex b i

onlyLocal g f = do
  v <- ask
  maybe (return (error "failed")) (\i -> local (const i) g) (g v)

maybeLocal g f = do
  v <- ask
  maybe (return Nothing) (\i -> local (const i) g) (g v)

atR ::
     (Show k,Ord k, KeyString k, MonadReader (TBData k Showable) m)
  => String
  -> Parser (Kleisli m) (Union (Access Text), Union (Access Text)) a b
  -> Parser (Kleisli m) (Union (Access Text), Union (Access Text)) a b
atR k = atP k



atK = at Nothing

nameI i (P (l, v) d) = P (Many [Rec i l], v) d

callI i ~(P _ d) = P (Many [Point i], one) d

nameO i (P (l, v) d) = P (l, Many [Rec i v]) d

callO i ~(P _ d) = P (one, Many [Point i]) d

splitIndex b l = fmap (IProd b . T.pack) . unIntercalate (',' ==) $ l

manyU = Many
  -- Obrigatory value with maybe wrapping

odx p l =
  let ll = splitIndex p l
  in P (one, manyU ll) (Kleisli $ const $ ask >>= (return . indexTableAttr ll))

odxR l =
  let ll = splitIndex notNull l
  in P (one, manyU ll) (Kleisli $ const $ ask >>= (return . indexTableAttr ll))

odxM l =
  let ll = splitIndex Nothing l
  in P
       (one, manyU ll)
       (Kleisli $ const $ ask >>= (return . (indexTableAttr ll)))

-- Optional value with maybe wrapping
idxM l =
  let ll = splitIndex Nothing l
  in P
       (manyU ll, one)
       (Kleisli $ const $ ask >>= (return . unSOptional . indexTableAttr ll))

-- Obrigatory value without maybe wrapping
tb ::
     MonadReader a m
  => Parser (Kleisli m) (Union (Access Text), Union (Access Text)) t a
tb = P (one, one) (Kleisli (const ask))

idxKIn l =
  let ll = splitIndex notNull l
  in P
       (manyU ll, one)
       (Kleisli $
        const $
        ask >>=
        (\v ->
           return .
           justError ("no value found " <> show (ll, v)) .
           unSOptional . indexTB1 ll $
           v))

idxK l =
  let ll = splitIndex notNull l
  in P
       (manyU ll, one)
       (Kleisli $
        const $
        ask >>=
        (\v ->
           return .
           justError ("no value found " <> show (ll, v)) .
           unSOptional . indexTableAttr ll $
           v))

idxA l =
  let ll = splitIndex notNull l
  in P
       (manyU ll, one)
       (Kleisli $
        const $
        ask >>=
        (\v ->
           return .  indexAttr ll $
           v))

idxR = idxK


indexAttrM l =
   kvFind (\i -> S.map (keyString . _relOrigin) i == S.fromList (iprodRef <$> l))

indexAttr l = justError (show ("cant indexAttr ", l)) . indexAttrM l

indexTB1M l v = do
  i <- indexAttrM l v
  case i of
    Attr _ l -> Nothing
    FKT l i j -> Just j
    IT l j -> Just j


indexTB1 l v =
  let i = indexAttr l v
  in case i of
       Attr _ l -> error "no element"
       FKT l i j -> j
       IT l j -> j

indexTableAttr l v =
  let i = indexAttr l v
  in case i of
       Attr k l -> l
       i -> error (show i)

indexTable l v = do
  let i = indexAttr l v
  case i of
    Attr k l -> return (k, l)
    FKT v _ _ -> safeHead $ aattr (justError "nohead3" $ safeHead $ unkvlist v)
    i -> error (show i)
