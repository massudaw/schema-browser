{-# LANGUAGE Arrows,OverloadedStrings,FlexibleContexts,NoMonomorphismRestriction #-}
module Step.Client (module Step.Common,notNull,idxR,idxK,act,odx,odxR,nameO,nameI,callI,atAny,idxA,atMA,callO,odxM,idxM,atR,atK,atRA,attrT,tb,indexTable,atMR,allP,anyP) where

import Types
import Step.Common
import Control.Monad.Reader
import Control.Monad.Trans.Maybe
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Maybe
import Data.Foldable (toList)
import Control.Applicative
import qualified Data.Text as T
import Data.Text (Text)
import Data.Functor.Identity
import Data.String
import qualified Data.List as L


import GHC.Stack
import Control.Arrow
import Control.Category (Category(..))
import Prelude hiding((.),id,head)
import Data.Monoid
import qualified Data.Bifunctor as BF
import Utils


act :: (Monoid s,Monad m) => (a -> m b) ->  Parser (Kleisli m) s a b
act a = P mempty (Kleisli a )


atAny k ps = atP k (anyP ps)
-- -atAny k ps = P (nest fsum,nest ssum ) (Kleisli (\i -> local (fmap unTB1 . indexTB1 ind)$foldr (liftA2 just)  (return Nothing)(fmap ($i) asum)))

atAny k ps = P (nest fsum,nest ssum ) (Kleisli (\i -> local (fmap unTB1 . indexTB1 ind)$foldr (liftA2 (<|>))  (return Nothing)(fmap ($i) asum)))
    where
     nest [] = []
     nest ls = [Nested ind $ ISum (concat ls)]
     ind = splitIndex (Just $ Not IsNull) k
     fsum =  fmap (\(P s _ )-> fst s ) ps
     ssum =  fmap (\(P s _ )-> snd s ) ps
     asum = fmap (\(P s (Kleisli j) ) -> j ) ps

allP (P (ps,ks) a) = P (Many ps ,Many ks) a

anyP ps = P (ISum fsum ,ISum ssum) (Kleisli (\i -> runMaybeT $ foldr1 ((<|>) )  (fmap ($i) asum)))
  where
    asum = fmap (\(P s (Kleisli j) ) -> fmap MaybeT j ) ps
    fsum = concat $  fmap (\(P s _ )-> fst s ) ps
    ssum = concat $  fmap (\(P s _ )-> snd s ) ps

atP k (P (fsum,ssum) (Kleisli a))= P (nest fsum,nest ssum ) (Kleisli (fmap (local (fmap unTB1 . indexTB1 ind))  a))
  where
    nest (Many []) = []
    nest (ISum []) = []
    nest ls = [Nested ind ls]
    ind = splitIndex (Just $ Not IsNull) k


nest ind [Rec ix i]  = pure . Nested ind $ Many [Rec ix i]
nest ind [] = []
nest ind  j = pure . Nested ind $ Many j

atMA
  :: (KeyString t2, Show t2,
      MonadReader (Maybe (TBData t2 Showable)) m, Ord t2) =>
     String
     -> Parser (Kleisli m) [Access Text] t t1
     -> Parser (Kleisli m) [Access Text] t [t1]
atMA i (P s (Kleisli j) )  =  P (BF.second (nest ind) . BF.first (nest ind) $ s) (Kleisli (\i -> maybe (return []) (mapM (\env -> local (const (Just env))  (j i ))) =<<  (return . Just . maybe [] (\(ArrayTB1 l) -> unTB1 <$> toList l) . join . fmap (\(LeftTB1 i )-> i) . indexTB1 ind)  =<< ask ))
  where ind = splitIndex Nothing i


atRA
  :: (KeyString t2, Show t2,
      MonadReader (Maybe (TBData t2 Showable)) m, Ord t2) =>
     String
     -> Parser (Kleisli m) [Access Text] t t1
     -> Parser (Kleisli m) [Access Text] t [t1]
atRA i (P s (Kleisli j) )  =  P (BF.second (nest ind) . BF.first (nest ind) $ s) (Kleisli (\i -> maybe (return []) (mapM (\env -> local (const (Just env))  (j i ))) =<<  (return . Just . maybe [] (\(ArrayTB1 l) -> unTB1 <$> toList l) . join . fmap (\(LeftTB1 i )-> i) . indexTB1 ind)  =<< ask ))
  where ind = splitIndex (Just $ Not IsNull) i

unLeftTB1 = join . fmap (\v -> case v of
               (LeftTB1 i ) -> i
               i@(TB1 _ ) -> Just i)


at b i (P s (Kleisli j) )  =  P (BF.second (nest (ind b)) . BF.first (nest (ind b)) $ s) (Kleisli (\i -> local (fmap unTB1 . unLeftTB1 . indexTB1 (ind b)) (j i )  ))
  where ind b = splitIndex b i


atR k = atP k . allP

atK = at Nothing
atMR = at notNull
  where
    at b i (P s (Kleisli j) )  =  P (BF.second (nest (ind Nothing)) . BF.first (nest (ind b)) $ s) (Kleisli (\i -> local (fmap unTB1 . unLeftTB1 . indexTB1 (ind b)) (j i )  ))
      where ind b = splitIndex b i





nameI  i (P (l,v) d)=  P ([Rec i (Many l)] ,  v )  d
callI  i ~(P _ d) = P ([Point i],[] ) d

nameO  i (P (l,v) d)=  P (l ,  [Rec i (Many v)] )  d
callO  i ~(P _ d) = P ([],[Point i] ) d



splitIndex b l = fmap (IProd b . T.pack) . unIntercalate (','==) $ l

  -- Obrigatory value with maybe wrapping
odx p l =
  let ll = splitIndex p l
   in  P ([],ll ) (Kleisli $ const $  ask >>= (return . fmap snd . join . fmap (indexTableAttr ll)))

odxR  l =
  let ll = splitIndex notNull l
   in  P ([],ll ) (Kleisli $ const $  ask >>= (return . fmap snd . join . fmap (indexTableAttr ll)))
odxM  l =
  let ll = splitIndex Nothing l
   in  P ([],ll ) (Kleisli $ const $  ask >>= (return . fmap snd . join . fmap (indexTableAttr ll)))


-- Optional value with maybe wrapping
idxM  l =
  let ll = splitIndex Nothing l
   in  P (ll,[] ) (Kleisli $ const $  ask >>= (return . join . fmap (unSOptional' . snd) . join  . fmap (indexTableAttr ll)))

-- Obrigatory value without maybe wrapping


tb :: MonadReader  a m => Parser (Kleisli m) [Access Text] t a
tb = P ([] , []) (Kleisli (const ask ))

idxK  l =
  let ll = splitIndex notNull l
   in  P (ll,[] ) (Kleisli $ const $  ask >>= (\ v -> return . justError ("no value found "  <> show (ll,v)). join . fmap (unSOptional' . snd) . join . fmap (indexTableAttr ll)$ v) )

idxA  l =
  let ll = splitIndex notNull l
   in  P (ll,[] ) (Kleisli $ const $  ask >>= (\ v -> return . justError ("no value found "  <> show (ll,v)). indexAttr ll$ v) )




idxR  l =
  let ll = splitIndex notNull l
   in  P (ll,[] ) (Kleisli $ const $  ask >>= (return . fmap snd . join . fmap (indexTableAttr ll)))


indexAttr l t
  = do
    (m,v) <- t
    i <-   M.lookup (S.fromList (iprodRef <$> l)) $ M.mapKeys (S.map (keyString. _relOrigin))$ _kvvalues $ unTB v
    return $ unTB i


indexTB1 l t
  = do
    (m,v) <- t
    i <-   M.lookup (S.fromList (iprodRef <$> l)) $ M.mapKeys (S.map (keyString. _relOrigin))$ _kvvalues $ unTB v
    case runIdentity $ getCompose $i  of
         Attr _ l -> Nothing
         FKT l  _ j -> return j
         IT l  j -> return j


firstCI f = mapComp (firstTB f)


indexTableAttr l t@(m,v)
  = do
    let finder = fmap (firstCI keyString ) . M.lookup (S.fromList $ fmap (Inline .iprodRef) l) . M.mapKeys (S.map (fmap keyString))
    i <- finder (_kvvalues $ unTB v )
    case runIdentity $ getCompose $ i  of
         Attr k l -> return (k,l)
         i ->  errorWithStackTrace (show i)


indexTable l t@(m,v)
  = do
    let finder = L.find (L.any (==fmap iprodRef l). L.permutations .fmap _relOrigin. keyattr. firstCI keyString )
    i <- finder (toList $ _kvvalues $ unTB v )
    case runIdentity $ getCompose $ i  of
         Attr k l -> return (k,l)
         FKT v _ _  -> safeHead $ aattr (head $ unkvlist v)
         i ->  errorWithStackTrace (show i)

