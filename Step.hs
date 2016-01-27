{-# LANGUAGE TypeFamilies,Arrows,OverloadedStrings,DeriveFoldable,DeriveTraversable,StandaloneDeriving,FlexibleContexts,NoMonomorphismRestriction,Arrows,FlexibleInstances, DeriveFunctor  #-}
module Step (idxR,idxK,act,odxR,nameO,nameI,callI,atAny,atMA,callO,odxM,idxM,atR,atRA,attrT,findPK,isNested,findProd,replace,uNest,checkTable,hasProd,checkTable',indexTable) where

import Types
import RuntimeTypes
import Control.Applicative.Lift
import Control.Monad.Reader
import Query
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
import Control.Category (Category(..),id)
import Prelude hiding((.),id,head)
import Data.Monoid
import qualified Data.Bifunctor as BF
import Utils

import qualified Data.Traversable as T
import Data.Traversable (traverse)
import Debug.Trace

deriving instance Functor m => Functor (Kleisli m i )


instance (Monoid s ,Arrow m)  => Arrow (Parser m s) where
  arr f = (P mempty (arr f ))
  first (P s d )  = P s (first d )

instance (Monoid s,Arrow m) => Category (Parser m s) where
   id = P mempty id
   P (i) (j) . P (l ) (m) = P (i <> l) (j . m  )

instance Applicative m => Applicative (Kleisli m a) where
  pure i = Kleisli (const (pure i ))
  Kleisli f <*> Kleisli j  =  Kleisli  $ (\i -> f i <*> j i )



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


atR i (P s (Kleisli j) )  =  P (BF.second (nest ind) . BF.first (nest ind) $ s) (Kleisli (\i -> local (fmap unTB1 . unLeftTB1 . indexTB1 ind) (j i )  ))
  where ind = splitIndex True i




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

findFK  l v =  M.lookup (S.fromList l) $ M.mapKeys (S.map (keyString. _relOrigin)) $ _kvvalues $ unTB v
findAttr l v =  M.lookup (S.fromList $ fmap Inline l) $ M.mapKeys (S.map (fmap keyString)) $ _kvvalues $ unTB v

replace ix i (Nested k nt) = Nested k (replace ix i nt)
replace ix i (Many nt) = Many (fmap (replace ix i) nt )
replace ix i (Point p)
  | ix == p = Rec ix i
  | otherwise = (Point p)
replace ix i v = v
-- replace ix i v= errorWithStackTrace (show (ix,i,v))
indexField :: Access Text -> TBData Key Showable -> Maybe (Column Key Showable)
indexField p@(IProd b l) v = unTB <$> findAttr  l  (snd v)
indexField n@(Nested ix@(IProd b l) nt ) v = unTB <$> findFK l (snd v)

checkField' :: Access Text -> Column Key Showable -> Errors [Access Text] (Column Key Showable)
checkField' p@(Point ix) _ = failure [p]
checkField' n@(Nested ix@(IProd b l) nt ) t
  = case t of
         IT l i -> IT l  <$> checkFTB  nt i
         FKT a  c d -> FKT a  c <$>  checkFTB nt d
         Attr k v -> failure [n]
checkField'  p@(IProd b l) i
  = case i  of
      Attr k v -> maybe (failure [p]) (pure) $ fmap (Attr k ) . (\i -> if b then  unRSOptional' i else Just i ) $ v
      FKT a c d -> (\i -> FKT i c d) <$> (traverse (traComp (checkField' p) )  a )
      i -> errorWithStackTrace ( show (b,l,i))
checkField' i j = errorWithStackTrace (show (i,j))


checkFTB l (ArrayTB1 i )
  | otherwise =   ArrayTB1 <$> traverse (checkFTB  l) i

checkFTB l (LeftTB1 j) = LeftTB1 <$> traverse (checkFTB  l) j
checkFTB  l (DelayedTB1 j) = DelayedTB1 <$> traverse (checkFTB l) j
checkFTB  (Rec ix i) t = checkFTB  (replace ix i i ) t
checkFTB  (Many [m@(Many l)]) t = checkFTB  m t
checkFTB  (Many [m@(Rec _ _ )]) t = checkFTB  m t

checkFTB f (TB1 k) = TB1 <$> checkTable' f k

checkTable' :: Access Text -> TBData Key Showable -> Errors [Access Text] (TBData Key Showable)
checkTable' (ISum []) v
  = failure [ISum []]
checkTable'  f@(ISum ls) (m,v)
  = fmap (tblist . pure . _tb) $ maybe (failure [f]) id  $ listToMaybe . catMaybes $  fmap (\(Many [l]) ->  fmap (checkField' l) . join . fmap ( traFAttr  unRSOptional') $ indexField l $ (m,v)) ls
checkTable' (Many l) (m,v) =
  ( (m,) . _tb . KV . mapFromTBList ) <$> T.traverse (\k -> maybe (failure [k]) (fmap _tb. checkField' k ). indexField  k $ (m,v)) l


checkTable l b = eitherToMaybe $ runErrors (checkTable' l b)



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
         FKT [v] _ _  -> safeHead $ aattr v
         i ->  errorWithStackTrace (show i)

hasProd :: (Access Text -> Bool) -> Access Text ->  Bool
hasProd p (Many i) = any p i
hasProd p i = False

findProd :: (Access Text -> Bool) -> Access Text -> Maybe (Access Text)
findProd p (Many i) = L.find p i
findProd p i = Nothing

isNested :: Access Text -> Access Text -> Bool
isNested p (Nested pn i) =  p == pn
isNested p i =  False

uNest :: Access Text -> Access Text
uNest (Nested pn i) = i


class KeyString i where
  keyString :: i -> Text

instance KeyString Key where
  keyString = keyValue

instance KeyString Text where
  keyString = id

instance Eq a => Monoid (Access a ) where
  mempty = Many []
  mappend (Many j) (Many i) = Many (i <> j)
  mappend y@(Nested i l ) z@(Nested j m)
    | i == j = Nested i (mappend l m)
    | otherwise = Many [ y,z]
  mappend i j@(Many _) = mappend (Many [i]) j
  mappend j@(Many _) i  = mappend j (Many [i])
  mappend i j = mappend (Many [i]) (Many [j])

instance (Monoid s ,Applicative (a i)) => Applicative (Parser a s i) where
  pure i = P mempty (pure i)
  P i  j <*> P l m  = P (i <> l) (j <*> m )

instance (Monoid s ,Applicative (a i) , IsString m) => IsString (Parser a s i m) where
  fromString s = pure (fromString s)

instance (Monoid s ,Applicative (a i),Monoid m) => Monoid (Parser a s i m) where
  mempty = P mempty (pure mempty)
  mappend (P i  l) (P j m ) =  P (mappend i j) (liftA2 mappend l  m )

findPK = concat . fmap keyattr  .toList . _kvvalues  . unTB . tbPK




attrT :: (a,FTB b) -> Compose Identity (TB Identity) a b
attrT (i,j) = Compose . Identity $ Attr i j

{-
findOne l  e
  = L.find (\i -> S.fromList (proj i) == e ) $ case l of
    Many l ->  l
    ISum l -> l
  where proj (IProd _ i) = i
        proj (Nested (IProd _ i) n) = i
        proj (Many [i]) = proj i
        proj i = errorWithStackTrace (show i )

accessTB i t = go t
  where
      go t = case t of
        LeftTB1 j ->  LeftTB1 $ go <$> j
        ArrayTB1 j -> ArrayTB1 $ go <$> j
        DelayedTB1 (Just j) -> go j
        TB1 (m,k) -> TB1   (m,mapComp (\m -> KV $ {-fmap (justError "") $ M.filterWithKey (\k v -> isJust v) $-} M.mapWithKey  modify (_kvvalues $ m)) k )
          where modify k =  mapComp (\v ->maybe v (flip accessAT v) $ findOne i (S.map (keyValue. _relOrigin) k))

accessAT (Nested (IProd b t) r) at
    = case at of
        IT k v -> IT (alterKeyType forceDAttr  k ) (accessTB r v)
        FKT k rel v -> FKT (mapComp (firstTB (alterKeyType forceDAttr )) <$> k) rel (accessTB r v)
accessAT i@(IProd b t) at
    = case at of
        Attr k v -> Attr (alterKeyType forceDAttr k ) v
        (FKT a r t) -> FKT (mapComp (accessAT i ) <$> a )  r t
accessAT (Many [i]) at = accessAT i at
-}
