{-# LANGUAGE Arrows,OverloadedStrings,FlexibleContexts,NoMonomorphismRestriction #-}
module Step.Client (module Step.Common,notNull,idxR,idxK,idxKIn,act,odx,odxR,nameO,nameI,callI,atAny,idxA,atMA,callO,odxM,idxM,atR,atK,atRA,attrT,tb,indexTable,atMR,anyP,manyU) where

import Types
import Step.Common
import Control.Monad.Reader
import Control.Monad.Trans.Maybe
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Control.Lens as Le
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
import Prelude hiding((.),id)
import Data.Monoid
import qualified Data.Bifunctor as BF
import Utils


act :: (Monoid s,Monad m) => (a -> m b) ->  Parser (Kleisli m) s a b
act a = P mempty (Kleisli a )


atAny k = atP k . anyP

allP = id

anyP ps = P (ISum fsum ,ISum ssum) (Kleisli (\i -> fmap (justError "no instance found")  . runMaybeT $ foldr1 ((<|>) )  (fmap ($i) asum)))
  where
    asum = fmap (\(P s (Kleisli j) ) -> fmap MaybeT j ) ps
    fsum =   fmap (\(P s _ )-> fst s ) ps
    ssum =   fmap (\(P s _ )-> snd s ) ps

atP k (P (fsum,ssum) (Kleisli a))= P (nest fsum,nest ssum ) (Kleisli (fmap (local (unTB1 . indexTB1 ind))  a))
  where
    nest (Many []) = Many []
    nest (ISum []) = Many []
    nest ls = Many [One $ Nested ind ls]
    ind = splitIndex (Just $ Not IsNull) k

nest ind (Many []) = Many []
nest ind (Many [One (Rec ix i)])  = One . Nested ind $ Many [One $ Rec ix i]
nest ind  j = One $ Nested ind  j

atMA
  :: ( KeyString t2
     , Show t2
     , MonadReader (TBData t2 Showable) m
     , Ord t2)
     => String
     -> Parser (Kleisli m) (Union (Access Text)) t t1
     -> Parser (Kleisli m) (Union (Access Text)) t [t1]
atMA i (P s (Kleisli j) )  =  P (BF.second (nest ind) . BF.first (nest ind) $ s) (Kleisli (\i -> mapM (\env -> local (const env)  (j i )) =<<  (return . maybe [] (\(ArrayTB1 l) -> unTB1 <$> toList l) . unSOptional' .  indexTB1 ind)  =<< ask ))
  where ind = splitIndex Nothing i


atRA
  :: (KeyString t2, Show t2,
      MonadReader ((TBData t2 Showable)) m, Ord t2) =>
     String
     -> Parser (Kleisli m) (Union (Access Text)) t t1
     -> Parser (Kleisli m) (Union (Access Text)) t [t1]
atRA i (P s (Kleisli j) )  =  P (BF.second (nest ind) . BF.first (nest ind) $ s) (Kleisli (\i ->  mapM (\env -> local (const env)  (j i )) =<<  (return . maybe [] (\(ArrayTB1 l) -> unTB1 <$> toList l) . unSOptional' . indexTB1 ind)  =<< ask ))
  where ind = splitIndex (Just $ Not IsNull) i

unLeftTB1 v = case v of
               (LeftTB1 i ) -> i
               i@(TB1 _ ) -> Just i


at b i (P s (Kleisli j) )  =  P (BF.second (nest (ind b)) . BF.first (nest (ind b)) $ s) (Kleisli (\i -> onlyLocal ( fmap unTB1 . unLeftTB1 . indexTB1 (ind b)) (j i )  ))
  where ind b = splitIndex b i

onlyLocal g f = do
  v <- ask
  maybe (return (error "failed")) (\i -> local (const i) g ) (g v)

maybeLocal g f = do
  v <- ask
  maybe (return Nothing) (\i -> local (const i) g ) (g v)

atR
  :: (KeyString k,
      MonadReader
        (TBData k Showable)
        m) =>
     String
     -> Parser (Kleisli m) (Union (Access Text)) a b
     -> Parser (Kleisli m) (Union (Access Text)) a b
atR k = atP k

atK = at Nothing
atMR = at notNull
  where
    at b i (P s (Kleisli j) )  =  P (BF.second (nest (ind Nothing)) . BF.first (nest (ind b)) $ s) (Kleisli (\i -> maybeLocal (fmap unTB1 . unLeftTB1 . (indexTB1 (ind b))) (j i )  ))
      where ind b = splitIndex b i



nameI  i (P (l,v) d)=  P (Many [One $ Rec i l] ,  v )  d
callI  i ~(P _ d) = P (Many [One $ Point i],one ) d

nameO  i (P (l,v) d)=  P (l ,  Many [One $ Rec i v] )  d
callO  i ~(P _ d) = P (one ,Many [One $ Point i] ) d



splitIndex b l = fmap (IProd b . T.pack) . unIntercalate (','==) $ l

manyU = Many . fmap One
  -- Obrigatory value with maybe wrapping
odx p l =
  let ll = splitIndex p l
   in  P (one ,manyU ll ) (Kleisli $ const $  ask >>= (return . snd . indexTableAttr ll))

odxR  l =
  let ll = splitIndex notNull l
   in  P (one ,manyU ll ) (Kleisli $ const $  ask >>= (return . snd . indexTableAttr ll))
odxM  l =
  let ll = splitIndex Nothing l
   in  P (one,manyU ll ) (Kleisli $ const $  ask >>= (return . snd . (indexTableAttr ll)))


-- Optional value with maybe wrapping
idxM  l =
  let ll = splitIndex Nothing l
   in  P (manyU ll,one  ) (Kleisli $ const $  ask >>= (return . (unSOptional' . snd) . (indexTableAttr ll)))

-- Obrigatory value without maybe wrapping


tb :: MonadReader  a m => Parser (Kleisli m) (Union (Access Text)) t a
tb = P (one , one ) (Kleisli (const ask ))

idxKIn  l =
  let ll = splitIndex notNull l
   in  P (manyU ll,one ) (Kleisli $ const $  ask >>= (\ v -> return . justError ("no value found "  <> show (ll,v)). unSOptional' . snd . indexTableInline ll$ v) )


idxK  l =
  let ll = splitIndex notNull l
   in  P (manyU ll,one ) (Kleisli $ const $  ask >>= (\ v -> return . justError ("no value found "  <> show (ll,v)). (unSOptional' . snd) . indexTableAttr ll $ v) )

idxA  l =
  let ll = splitIndex notNull l
   in  P (manyU ll,one ) (Kleisli $ const $  ask >>= (\ v -> return . justError ("no value found "  <> show (ll,v)). indexAttr ll$ v) )


idxR = idxK



indexAttr l v
  = do
    i <-   M.lookup (S.fromList (iprodRef <$> l)) . M.mapKeys (S.map (keyString. _relOrigin)). _kvvalues $ v
    return  i

finder l v = justError "no element" . M.lookup (S.fromList (iprodRef <$> l)) . M.mapKeys (S.map (keyString. _relOrigin)) . _kvvalues $ v


indexTB1 l v =
    let i = finder l v
    in case i  of
      Attr _ l -> error "no element"
      FKT l i j -> j
      IT l j -> j




firstCI f = (firstTB f)

indexTableInline l v
  =
    let i = finder l v
    in case i  of
      IT k l -> (k,l)
      i ->  errorWithStackTrace (show i)

indexTableAttr l v =
  let i = finder l v
  in case i of
       Attr k l -> (k,l)
       i ->  errorWithStackTrace (show i)


indexTable l t@(v)
  = do
    let finder = L.find (L.any (==fmap iprodRef l). L.permutations .fmap _relOrigin. keyattr. firstCI keyString )
    i <- finder (toList $ _kvvalues $ v )
    case i  of
         Attr k l -> return (k,l)
         FKT v _ _  -> safeHead $ aattr (justError "nohead3" $ safeHead $ unkvlist v)
         i ->  errorWithStackTrace (show i)

