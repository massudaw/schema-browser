{-# LANGUAGE Arrows,OverloadedStrings,FlexibleContexts,NoMonomorphismRestriction #-}
module Step.Client (module Step.Common,idxR,idxK,act,odxR,nameO,nameI,callI,atAny,atMA,callO,odxM,idxM,atR,atK,atRA,attrT,tb,indexTable,atMR) where

import Types
import Step.Common
import Control.Monad.Reader
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




just (Just i ) (Just j) = Nothing
just i Nothing = i
just  Nothing i  = i


atAny k ps = P (nest fsum,nest ssum ) (Kleisli (\i -> local (fmap unTB1 . indexTB1 ind)$foldr1 (liftA2 just)  (fmap ($i) asum)))
  where
    nest [] = Many []
    nest ls = Many [Nested ind $ ISum ls]
    ind = splitIndex True k
    fsum = filter (/= Many [])$ fmap (\(P s _ )-> fst s ) ps
    ssum = filter (/= Many [])$ fmap (\(P s _ )-> snd s ) ps
    asum = fmap (\(P s (Kleisli j) ) -> j ) ps

nest _ (Many []) = Many []
nest _ (ISum [] ) = ISum []
nest ind (Many [Rec ix i])  = Many . pure . Nested ind $ Rec ix i
nest ind  (Many j) = Many . pure . Nested ind $ Many j
nest ind (ISum i) = Many . pure . Nested ind $ ISum i
nest ind (Rec ix i) = Many . pure . Nested ind $(Rec ix i)

atMA
  :: (KeyString t2, Show t2,
      MonadReader (Maybe (TBData t2 Showable)) m, Ord t2) =>
     String
     -> Parser (Kleisli m) (Access Text) t t1
     -> Parser (Kleisli m) (Access Text) t [t1]
atMA i (P s (Kleisli j) )  =  P (BF.second (nest ind) . BF.first (nest ind) $ s) (Kleisli (\i -> maybe (return []) (mapM (\env -> local (const (Just env))  (j i ))) =<<  (return . Just . maybe [] (\(ArrayTB1 l) -> unTB1 <$> toList l) . join . fmap (\(LeftTB1 i )-> i) . indexTB1 ind)  =<< ask ))
  where ind = splitIndex False i


atRA
  :: (KeyString t2, Show t2,
      MonadReader (Maybe (TBData t2 Showable)) m, Ord t2) =>
     String
     -> Parser (Kleisli m) (Access Text) t t1
     -> Parser (Kleisli m) (Access Text) t [t1]
atRA i (P s (Kleisli j) )  =  P (BF.second (nest ind) . BF.first (nest ind) $ s) (Kleisli (\i -> maybe (return []) (mapM (\env -> local (const (Just env))  (j i ))) =<<  (return . Just . maybe [] (\(ArrayTB1 l) -> unTB1 <$> toList l) . join . fmap (\(LeftTB1 i )-> i) . indexTB1 ind)  =<< ask ))
  where ind = splitIndex True i

unLeftTB1 = join . fmap (\v -> case v of
               (LeftTB1 i ) -> i
               i@(TB1 _ ) -> Just i)

at b i (P s (Kleisli j) )  =  P (BF.second (nest (ind b)) . BF.first (nest (ind b)) $ s) (Kleisli (\i -> local (fmap unTB1 . unLeftTB1 . indexTB1 (ind b)) (j i )  ))
  where ind b = splitIndex b i


atK = at False
atR = at True
atMR = at True
  where
    at b i (P s (Kleisli j) )  =  P (BF.second (nest (ind False)) . BF.first (nest (ind b)) $ s) (Kleisli (\i -> local (fmap unTB1 . unLeftTB1 . indexTB1 (ind b)) (j i )  ))
      where ind b = splitIndex b i





nameI  i (P (Many l,Many v) d)=  P (Rec i (Many l) ,  (Many v) )  d
callI  i ~(P _ d) = P (Many[Point i],Many [] ) d

nameO  i (P (Many l,Many v) d)=  P (Many l ,  Rec i (Many v) )  d
callO  i ~(P _ d) = P (Many[],Many [Point i] ) d



splitIndex b l = (fmap T.pack . IProd b . unIntercalate (','==) $ l)

  -- Obrigatory value with maybe wrapping
odxR  l =
  let ll = splitIndex True l
   in  P (Many [],Many [ll] ) (Kleisli $ const $  ask >>= (return . fmap snd . join . fmap (indexTableAttr ll)))
odxM  l =
  let ll = splitIndex False l
   in  P (Many [],Many [ll] ) (Kleisli $ const $  ask >>= (return . fmap snd . join . fmap (indexTableAttr ll)))


-- Optional value with maybe wrapping
idxM  l =
  let ll = splitIndex False l
   in  P (Many [ll],Many [] ) (Kleisli $ const $  ask >>= (return . join . fmap (unRSOptional' . snd) . join  . fmap (indexTableAttr ll)))

-- Obrigatory value without maybe wrapping


tb :: MonadReader  a m => Parser (Kleisli m) (Access Text) t a
tb = P (Many [] , Many []) (Kleisli (const ask ))

idxK  l =
  let ll = splitIndex True l
   in  P (Many [ll],Many [] ) (Kleisli $ const $  ask >>= (\ v -> return . justError ("no value found "  <> show (ll,v)). join . fmap (unRSOptional' . snd) . join . fmap (indexTableAttr ll)$ v) )


idxR  l =
  let ll = splitIndex True l
   in  P (Many [ll],Many [] ) (Kleisli $ const $  ask >>= (return . fmap snd . join . fmap (indexTableAttr ll)))




indexTB1 (IProd _ l) t
  = do
    (m,v) <- t
    i <-   M.lookup (S.fromList l) $ M.mapKeys (S.map (keyString. _relOrigin))$ _kvvalues $ unTB v
    case runIdentity $ getCompose $i  of
         Attr _ l -> Nothing
         FKT l  _ j -> return j
         IT l  j -> return j


firstCI f = mapComp (firstTB f)


indexTableAttr (IProd _ l) t@(m,v)
  = do
    let finder = fmap (firstCI keyString ) . M.lookup (S.fromList $ fmap Inline l) . M.mapKeys (S.map (fmap keyString))
    i <- finder (_kvvalues $ unTB v )
    case runIdentity $ getCompose $ i  of
         Attr k l -> return (k,l)
         i ->  errorWithStackTrace (show i)


indexTable (IProd _ l) t@(m,v)
  = do
    let finder = L.find (L.any (==l). L.permutations .fmap _relOrigin. keyattr. firstCI keyString )
    i <- finder (toList $ _kvvalues $ unTB v )
    case runIdentity $ getCompose $ i  of
         Attr k l -> return (k,l)
         FKT v _ _  -> safeHead $ aattr (head $ unkvlist v)
         i ->  errorWithStackTrace (show i)

