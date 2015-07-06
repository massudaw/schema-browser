{-# LANGUAGE Arrows,OverloadedStrings,DeriveFoldable,DeriveTraversable,StandaloneDeriving,FlexibleContexts,NoMonomorphismRestriction,Arrows,TupleSections,FlexibleInstances, DeriveFunctor  #-}
module Step where

import qualified Data.Bifunctor as B
import Types
import Query
import Data.Foldable (Foldable,toList)
import Data.Maybe (isJust)
import Data.Traversable (Traversable)
import Control.Applicative
import qualified Data.Text.Lazy as T
import Data.Text.Lazy (Text)
-- import Warshal
import Data.Functor.Compose
import Data.Functor.Identity
import Data.String
import Data.Set (Set)
import qualified Data.List as L
import qualified Data.Vector as Vector


import Control.Monad.Reader
import GHC.Stack
import Control.Arrow
import Control.Category (Category(..),id)
import Prelude hiding((.),id)
import Data.Monoid
import Control.Monad
import qualified Data.Bifunctor as BF
import Utils

import qualified Data.Traversable as T

deriving instance Functor m => Functor (Kleisli m i )

data Step a
  = SAttr (String,(Text, a -> String))
  | SFK (Set Text) [Step a]
  deriving(Show)


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

data Parser m s a b = P (s,s) (m a b) deriving Functor

liftParser (P i j) = (P i ((\l -> Kleisli $  return <$> l ) $ j ) )

dynP (P s d) = d

dynPK =  runKleisli . dynP

staticP (P s d) = s

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



atAny ps = P (ISum fsum,ISum ssum) (foldr (<+>) zeroArrow asum)
  where
    fsum = fmap (\(j,P s _ )-> fst s ) ps
    ssum = fmap (\(j,P s _ )-> snd s ) ps
    asum = fmap (\(li,P _ j) -> j . arr ( join. join . fmap (\(TBEither _ l j)->  (\m ->  if [li]  == keyattr (firstCI keyString m) then Just (runIdentity $ getCompose m) else Nothing ) <$> j ))) ps

atR i (P s (Kleisli j) )  =  P (BF.second nest . BF.first nest $ s)  ( Kleisli (\i -> local (indexTB1 ind) (j i )  ))
  where ind = splitIndex i
        nest (Many []) = Many []
        nest (Many j) = Many . pure . Nested ind $ Many j

at i (P s j)  =  P (BF.second nest  . BF.first nest  $ s)  (j . arr (indexTB1 ind )  )
  where ind = splitIndex i
        nest (Many i) = Many . pure . Nested ind $ Many i
        nest (Many [] ) = Many []

idx = indexTableInter False
idxT = indexTableInter True

odx = logTableInter False
odxT = logTableInter True


instance Applicative m => Applicative (Kleisli m a ) where
  pure i = Kleisli (const (pure i ))
  Kleisli f <*> Kleisli j  =  Kleisli  $ (\i -> f i <*> j i )

url :: Parser  (Kleisli (ReaderT (Maybe (TB1 (Key,Showable))) IO )) (Access Text)()  (Maybe Showable)
url = proc _ -> do
      descontado <-  liftA2 (\v k -> v*(1 - k) )
              <$> atR "frequencia,meses"
                  (liftA2 (\v m -> v * fromIntegral m) <$> idxR "price" <*> idxR "meses")
              <*> idxR "desconto" -< ()
      atR "pagamento" (proc descontado -> do
          pinicio <- idxR "inicio"-< ()
          p <- idxR "vezes" -< ()
          let valorParcela = liftA2 (/)  descontado p
          returnA -< valorParcela
          ) -< descontado


splitIndex l = (fmap T.pack . IProd . unIntercalate (','==) $ l)

odxR  l =
  let ll = splitIndex l
   in  P (Many [],Many [ll] ) (Kleisli $ const $  ask >>= (return . fmap snd . join . fmap (indexTable ll)))



idxR  l =
  let ll = splitIndex l
   in  P (Many [ll],Many [] ) (Kleisli $ const $  ask >>= (return . fmap snd . join . fmap (indexTable ll)))

{-indexTableInter
  :: (Show k ,KeyString k ,Arrow a) =>
      Bool -> String -> Parser  a (Bool,[[Text]]) (Maybe (TB1 (k, Showable))) (Maybe (k, Showable))-}
indexTableInter b l =
  let ll = splitIndex l
   in  P (Many [ll],Many [] ) (arr (join . fmap (indexTable ll)))

logTableInter
  :: (Show k ,KeyString k ,Arrow a) =>
      Bool -> String -> Parser  a AccessTag (Maybe (TB1 (k, Showable))) (Maybe (k, Showable))
logTableInter b l =
  let ll = splitIndex l
   in  P (Many [] ,Many [ll]) (arr (join . fmap (indexTable ll)))


indexTB1 (IProd l) t
  = do
    (TB1 (KV (PK k d)  v)) <- t
    let finder = L.find (L.any (==l). L.permutations . keyattr . firstCI keyString)
        i = justError ("indexTB1 error finding key: " <> T.unpack (T.intercalate (","::Text) l :: Text) ) $  finder v `mplus` finder k `mplus` finder d
    case runIdentity $ getCompose $i  of
         Attr _ l -> Nothing
         FKT l _ _ j -> return j

data Access a
  = IProd [a]
  | ISum  [Access a]
  | Nested (Access a) (Access a)
  | Many [Access a]
  deriving(Show,Eq,Ord,Functor,Foldable,Traversable)

firstCI f (Compose (Identity i)) = Compose (Identity $ B.first f i)

-- checkField (Nested (IProd l) (Many []) ) t@(TB1 (KV (PK k d)  v)) = uu
checkField (Nested (IProd l) nt ) t@(TB1 (KV (PK k d)  v))
  = do
    let finder = L.find (L.any (==l). L.permutations . keyattr . firstCI keyString  )
        i = justError ("indexTable error finding key: " <> T.unpack (T.intercalate "," l) <> show t ) $ finder v `mplus` finder k `mplus` finder d
    Compose . Identity <$> case runIdentity $ getCompose $ i  of
         IT l  i -> IT l  <$> checkTable nt i
         FKT a  b c  d -> FKT a b c <$>  checkTable nt d
checkField  (IProd l) t@(TB1 (KV (PK k d)  v))
  = do
    let finder = L.find (L.any (==l). L.permutations . keyattr . firstCI keyString  )
        i = justError ("indexTable error finding key: " <> T.unpack (T.intercalate "," l) <> show t ) $ finder v `mplus` finder k `mplus` finder d
    Compose . Identity <$> case runIdentity $ getCompose $ i  of
         Attr k l -> return $ Attr k l

-- indexTable :: [[Text]] -> TB1 (Key,Showable) -> Maybe (Key,Showable)
checkTable l (LeftTB1 j) = join $ fmap (checkTable l) j
checkTable (Many l) t@(TB1 (KV (PK k d)  v)) =
  fmap (TB1 . (KV (PK [] []))). allMaybes $ flip checkField t <$> l

checkTable l (ArrayTB1 i )
  | i == []  = Nothing
  | otherwise =   fmap ArrayTB1 $ allMaybes $ checkTable l <$> i
checkTable i j = errorWithStackTrace (show (i,j))


-- indexTable :: [[Text]] -> TB1 (Key,Showable) -> Maybe (Key,Showable)
indexTable l (LeftTB1 j) = join $ fmap (indexTable l) j
indexTable (IProd l) t@(TB1 (KV (PK k d)  v))
  = do
    let finder = L.find (L.any (==l). L.permutations .keyattr. firstCI keyString )
        i = justError ("indexTable error finding key: " <> T.unpack (T.intercalate "," l) <> show t ) $ finder v `mplus` finder k `mplus` finder d
    case runIdentity $ getCompose $ i  of
         Attr _ l -> return l
indexTable l (ArrayTB1 j) =  liftA2 (,) ((head <$> fmap (fmap fst) i) ) ( (\i -> SComposite . Vector.fromList $ i ) <$> fmap (fmap snd) i)
       where i =   T.traverse  (indexTable l) j
indexTable i j = errorWithStackTrace (show (i,j))



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

findPK = concat . fmap (attrNonRec . runIdentity . getCompose) . _pkKey  . _kvKey . _unTB1

findPKM (LeftTB1 i ) =  join $ fmap findPKM i
findPKM i  = Just $ findPK i


attrNonRec (FKT ifk _ _ _ ) = concat $ fmap kattr ifk
attrNonRec (TBEither _ _  ifk ) =   (maybe [] id $ fmap kattr ifk)
attrNonRec (IT ifk  _ ) = []
attrNonRec (Attr _ i ) = [i]

kattr = kattri . runIdentity . getCompose
kattri (Attr _ i ) = [i]
kattri (TBEither _ i l  ) =  (maybe [] id $ fmap kattr l )
kattri (FKT i _ _ _ ) =  (L.concat $ kattr  <$> i)
kattri (IT _  i ) =  recTB i
  where recTB (TB1 i ) =  concat $ fmap kattr (toList i)
        recTB (ArrayTB1 i ) = concat $ fmap recTB i
        recTB (LeftTB1 i ) = concat $ toList $ fmap recTB i


keyattr = keyattri . runIdentity . getCompose
keyattri (Attr i  _ ) = [i]
keyattri (TBEither _ i l  ) =  (maybe [] id $ fmap keyattr l )
keyattri (FKT i _ _ _ ) =  (L.concat $ keyattr  <$> i)
keyattri (IT i  _ ) =  [i ]



varT t = join . fmap (unRSOptional'.snd)  <$> idxT t
varN t = fmap snd  <$> idx t

type FunArrowPlug o = Step.Parser (->) AccessTag (Maybe (TB1 (Key,Showable))) o
type ArrowPlug a o = Step.Parser a AccessTag (Maybe (TB1 (Key,Showable))) o

