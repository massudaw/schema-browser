{-# LANGUAGE TypeFamilies,Arrows,OverloadedStrings,DeriveFoldable,DeriveTraversable,StandaloneDeriving,FlexibleContexts,NoMonomorphismRestriction,Arrows,TupleSections,FlexibleInstances, DeriveFunctor  #-}
module Step where

import Types
import RuntimeTypes
import Control.Monad.Reader
import Query
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Maybe
import Data.Foldable (toList)
import Control.Applicative
import qualified Data.Text as T
import Data.Text (Text)
-- import Warshal
import Data.Functor.Identity
import Data.String
import qualified Data.List as L


import Control.Monad.Reader
import GHC.Stack
import Control.Arrow
import Control.Category (Category(..),id)
import Prelude hiding((.),id,head)
import Data.Monoid
import qualified Data.Bifunctor as BF
import Utils

import qualified Data.Traversable as T

deriving instance Functor m => Functor (Kleisli m i )


instance Show (a -> Maybe Showable) where
  show _ = ""

instance Show (a -> String) where
  show _ = ""

{-
data FKEdit
  = FKEInsertGenerated
  | FKEInsertFind
  | FKEUpdateAttr
  | FKEUpdateFK
  deriving(Show)

data AEdit
  = AEInsert
  | AEUpdate
  deriving(Show)

data TEdit
  = TInsert
  | TUpdate
  | TDelete
  | TGenerated
  deriving(Show)

data TablePlan a = TablePlan TEdit Table [StepPlan a]
data StepPlan a
  = SPAttr AEdit Key a
  | SPFK FKEdit (Path (Set Key) (SqlOperation Table)) [StepPlan a]
  | TBPlan TEdit Table [StepPlan a]
  deriving(Show,Functor)
-}


liftParser (P i j) = (P i ((\l -> Kleisli $  return <$> l ) $ j ) )
liftParserR (P i j) = (P i ((\(Kleisli  l) -> Kleisli $  return  <$> l ) $ j ) )

dynP ~(P s d) = d

dynPK =  runKleisli . dynP

staticP ~(P s d) = s

liftReturn = Kleisli . (return <$> )

instance (Monoid s ,Arrow m)  => Arrow (Parser m s ) where
  arr f = (P mempty (arr f ))
  first (P s d )  = P s (first d )

instance (Monoid s,Arrow m) => Category (Parser m s ) where
   id = P mempty id
   P (i) (j) . P (l ) (m) = P (i <> l) (j . m  )

printStatic (P (i) _ ) =  show i

act :: (Monoid s,Monad m) => (a -> m b) ->  Parser (Kleisli m) s a b
act a = P mempty (Kleisli a )

atO i j = proc t -> do
  idx i -< t
  at i j -< t

atI i j = proc t ->do
  idx i -< t
  at i j -< t


checkOutput i = proc t -> do
      o <- odx i -< fst t
      v <- odx i -< snd t
      returnA -< if isJust o  && fmap snd o == fmap snd v
         then Nothing
         else v


{-
test1 = do
  let testP = atAny "tbtest" [join . fmap unSOptional <$> idxR "ewfew" ,join . fmap unSOptional <$> idxR "ooooo":: Parser (Kleisli (ReaderT (Maybe (TB2 Text Showable)) IO) ) (Access Text) b (Maybe (Showable))]
      testData = Just (TB1 (KV (PK [] []) [Compose $ Identity $ TBEither "tbtest" [Compose $ Identity $ Attr "ewfew" (),Compose $ Identity $ Attr "ooooo" () ] (Just $ Compose $ Identity $ Attr "ewfew" (SOptional $ Just $ SText "24124"))] ))

  print $ staticP testP
  print =<< runReaderT (dynPK testP  () ) testData
-}

just (Just i ) (Just j) = Nothing
just i Nothing = i
just  Nothing i  = i


atAny k ps = P (nest fsum,nest ssum ) (Kleisli (\i -> local (indexTB1 ind)$foldr1 (liftA2 just)  (fmap ($i) asum)))
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

atRA
  :: (KeyString t2,
      MonadReader (Maybe (FTB1 Identity t2 Showable)) m, Ord t2) =>
     String
     -> Parser (Kleisli m) (Access Text) t t1
     -> Parser (Kleisli m) (Access Text) t [t1]
atRA i (P s (Kleisli j) )  =  P (BF.second (nest ind) . BF.first (nest ind) $ s) (Kleisli (\i -> maybe (return []) (mapM (\env -> local (const (Just env))  (j i ))) =<<  (return . Just . maybe [] (\(ArrayTB1 l) -> l) . join . fmap (\(LeftTB1 i )-> i) . indexTB1 ind)  =<< ask ))
  where ind = splitIndex True i

unLeftTB1 = join . fmap (\v -> case v of
               (LeftTB1 i ) -> i
               i@(TB1 _ ) -> Just i)

atR i (P s (Kleisli j) )  =  P (BF.second (nest ind) . BF.first (nest ind) $ s) (Kleisli (\i -> local (unLeftTB1 . indexTB1 ind) (j i )  ))
  where ind = splitIndex True i


at i (P s j)  =  P (BF.second ( nest  ind) . BF.first (nest  ind) $ s)  (j . arr (indexTB1 ind )  )
  where ind = splitIndex True i

messages
  :: (k ~ Text
      , m ~ Reader (Maybe (FTB (KVMetadata k, Compose Identity (KV (Compose Identity (TB Identity))) k Showable)))
      , KeyString k,Applicative m, Show k, Ord k) =>
     Parser
       (Kleisli m) (Access Text) () [Maybe (FTB Showable, FTB Showable)]
messages = name 0 $ proc t -> do
          enc <- liftA2 (liftA2 (,)) (atR "body"  (idxR "data")) (idxR "mimeType") -< ()
          part <- atRA "parts"
              (call 0 messages ) -< ()
          returnA -< ([enc ])

name  i (P (Many l,Many v) d)=  P (Rec i (Many l) ,  Rec i (Many v) )  d
call  i ~(P _ d) = P (Many[Point i],Many [Point i] ) d

idx = indexTableInter False
idxT = indexTableInter True

odx = logTableInter False
odxT = logTableInter True


instance Applicative m => Applicative (Kleisli m a ) where
  pure i = Kleisli (const (pure i ))
  Kleisli f <*> Kleisli j  =  Kleisli  $ (\i -> f i <*> j i )


splitIndex b l = (fmap T.pack . IProd b . unIntercalate (','==) $ l)

  -- Obrigatory value with maybe wrapping
odxR  l =
  let ll = splitIndex True l
   in  P (Many [],Many [ll] ) (Kleisli $ const $  ask >>= (return . fmap snd . join . fmap (indexTable ll)))

-- Optional value with maybe wrapping
idxM  l =
  let ll = splitIndex False l
   in  P (Many [ll],Many [] ) (Kleisli $ const $  ask >>= (return . join . fmap (unRSOptional' . snd) . join  . fmap (indexTable ll)))

-- Obrigatory value without maybe wrapping


idxK  l =
  let ll = splitIndex True l
   in  P (Many [ll],Many [] ) (Kleisli $ const $  ask >>= (return . justError "no value found " . join . fmap (unRSOptional' . snd) . join . fmap (indexTable ll)))


idxR  l =
  let ll = splitIndex True l
   in  P (Many [ll],Many [] ) (Kleisli $ const $  ask >>= (return . fmap snd . join . fmap (indexTable ll)))

{-indexTableInter
  :: (Show k ,KeyString k ,Arrow a) =>
      Bool -> String -> Parser  a (Bool,[[Text]]) (Maybe (TB1 (k, Showable))) (Maybe (k, Showable))-}
indexTableInter b l =
  let ll = splitIndex b l
   in  P (Many [ll],Many [] ) (arr (join . fmap (indexTable ll)))

logTableInter
  :: (Ord k ,Show k ,KeyString k ,Arrow a) =>
      Bool -> String -> Parser  a AccessTag (Maybe (TB2 k   Showable)) (Maybe (k, FTB Showable))
logTableInter b l =
  let ll = splitIndex b l
   in  P (Many [] ,Many [ll]) (arr (join . fmap (indexTable ll)))


indexTB1 (IProd _ l) t
  = do
    (TB1  (m,v)) <- t
    i <-   M.lookup (S.fromList l) $ M.mapKeys (S.map (keyString. _relOrigin))$ _kvvalues $ unTB v
    case runIdentity $ getCompose $i  of
         Attr _ l -> Nothing
         FKT l  _ j -> return j
         IT l  j -> return j


firstCI f = mapComp (firstTB f)

findAttr l v =  M.lookup (S.fromList l) $ M.mapKeys (S.map (keyString. _relOrigin)) $ _kvvalues $ unTB v

replace ix i (Nested k nt) = Nested k (replace ix i nt)
replace ix i (Many nt) = Many (fmap (replace ix i) nt )
replace ix i (Point p)
  | ix == p = Rec ix i
  | otherwise = (Point p)
replace ix i v = v
-- replace ix i v= errorWithStackTrace (show (ix,i,v))

checkField (Point ix) t = Nothing
checkField (Nested (IProd _ l) nt ) t@(TB1 (m,v))
  = do
    let
    i <- findAttr l v
    case runIdentity $ getCompose $ i  of
         IT l  i -> Compose . Identity <$> (IT l  <$> checkTable nt i)
         FKT a   c  d -> Compose . Identity <$> (FKT a  c <$>  checkTable nt d)
         Attr k v -> Nothing
checkField  (IProd b l) t@(TB1 (m,v))
  = do
    let
    i <-  findAttr l v
    Compose . Identity <$> case runIdentity $ getCompose $ i  of
         Attr k v -> fmap (Attr k ) . (\i -> if b then  unRSOptional' i else Just i ) $ v
         i -> errorWithStackTrace ( show (l,i))
checkField  (ISum []) t@(TB1 v)
  = Nothing
checkField  (ISum ls) t@(TB1 (m,v) )
  = foldr1 just $  fmap (\(Many [l]) ->  join $ fmap (traComp ( traFAttr  unRSOptional')) $  checkField l t) ls
checkField i j = errorWithStackTrace (show (i,j))



-- indexTable :: [[Text]] -> TB1 (Key,Showable) -> Maybe (Key,Showable)
checkTable l (LeftTB1 j) = join $ fmap (checkTable l) j
checkTable l (DelayedTB1 j) = join $ fmap (checkTable l) j
checkTable (Rec ix i) t = checkTable (replace ix i i ) t
checkTable (Many [m@(Many l)]) t = checkTable m t
checkTable (Many [m@(Rec _ _ )]) t = checkTable m t
checkTable (Many l) t@(TB1 (m,v)) =
  fmap (TB1 . (m,) . Compose . Identity . KV . mapFromTBList ) . allMaybes $ flip checkField t <$> l

checkTable l (ArrayTB1 i )
  | i == []  = Nothing
  | otherwise =   fmap ArrayTB1 $ allMaybes $ checkTable l <$> i

checkTable (ISum []) t@(TB1  v)
  = Nothing
checkTable (ISum ls) t@(TB1 (m,v) )
  = fmap  (TB1 . (m,) . Compose . Identity . KV . mapFromTBList) . (\i -> if L.null i then Nothing else Just i) . catMaybes $ fmap (\(Many [l]) ->  join $ fmap (traComp (traFAttr unRSOptional')) $    checkField l t) ls

checkTable i j = errorWithStackTrace (show ("checkTable" , i,j))

-- indexTable :: [[Text]] -> TB1 (Key,Showable) -> Maybe (Key,Showable)
indexTable l (LeftTB1 j) = join $ fmap (indexTable l) j
indexTable (IProd _ l) t@(TB1 (m,v))
  = do
    let finder = L.find (L.any (==l). L.permutations .fmap _relOrigin. keyattr. firstCI keyString )
    i <- finder (toList $ _kvvalues $ unTB v )
    case runIdentity $ getCompose $ i  of
         Attr k l -> return (k,l)
indexTable l (ArrayTB1 j) =  liftA2 (,) ((head <$> fmap (fmap fst) i) ) ( (\i -> ArrayTB1   i ) <$> fmap (fmap snd) i)
       where i =   T.traverse  (indexTable l) j
indexTable i j = errorWithStackTrace (show (i,j))

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



type AccessTag = (Access Text)

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




type FunArrowPlug o = RuntimeTypes.Parser (->) AccessTag (Maybe (TB1 Showable)) o
type ArrowPlug a o = RuntimeTypes.Parser a AccessTag (Maybe (TB1 Showable)) o


attrT :: (a,FTB b) -> Compose Identity (TB Identity) a b
attrT (i,j) = Compose . Identity $ Attr i j


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
        TB1 (m,k) -> TB1   (m,mapComp (\m -> KV $ M.mapWithKey  modify (_kvvalues $ m)) k )
          where modify k =  mapComp (\v -> maybe v (flip accessAT v) $ findOne i (S.map (keyValue. _relOrigin) k))

accessAT (Nested (IProd b t) r) at
    = case at of
        IT k v -> IT (mapComp (firstTB (alterKeyType forceDAttr )) k ) (accessTB r v)
        FKT k rel v -> FKT (mapComp (firstTB (alterKeyType forceDAttr )) <$> k) rel (accessTB r v)
accessAT (IProd b t) at
    = case at of
        Attr k v -> Attr (alterKeyType forceDAttr k ) v
accessAT (Many [i]) at = accessAT i at
