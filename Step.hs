{-# LANGUAGE OverloadedStrings,StandaloneDeriving,FlexibleContexts,NoMonomorphismRestriction,Arrows,TupleSections,FlexibleInstances, DeriveFunctor  #-}
module Step where

import Types
import Query
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
data Parser m s a b = P ([s],[s]) (m a b) deriving Functor

liftParser (P i j ) = (P i ((\l -> Kleisli $  return <$> l ) $ j ) )

dynP (P s d) = d

dynPK =  runKleisli . dynP

staticP (P s d) = s

liftReturn = Kleisli . (return <$> )

instance Arrow m  => Arrow (Parser m s ) where
  arr f = (P mempty (arr f ))
  first (P s d )  = P s (first d )

instance Arrow m => Category (Parser m s ) where
   id = P mempty id
   P (i) (j) . P (l ) (m) = P (i <> l) (j . m  )

printStatic (P (i) _ ) =  show i

act :: Monad m => (a -> m b) ->  Parser (Kleisli m) s a b
act a = P mempty (Kleisli a )


at i (P s j)  =  P (BF.second(fmap (BF.second (ind ++))) . BF.first (fmap (BF.second (ind ++))) $ s)  (j . arr (indexTB1 ind )  )
  where ind = splitIndex i

idx = indexTableInter False
idxT = indexTableInter True

odx = logTableInter False
odxT = logTableInter True

splitIndex l = (fmap T.pack . unIntercalate (','==)<$> unIntercalate (':'==) l)

{-indexTableInter
  :: (Show k ,KeyString k ,Arrow a) =>
      Bool -> String -> Parser  a (Bool,[[Text]]) (Maybe (TB1 (k, Showable))) (Maybe (k, Showable))-}
indexTableInter b l =
  let ll = (fmap T.pack . unIntercalate (','==)<$> unIntercalate (':'==) l)
   in  P ([(b ,ll)],[] ) (arr (join . fmap (indexTable ll)))

logTableInter
  :: (Show k ,KeyString k ,Arrow a) =>
      Bool -> String -> Parser  a (Bool,[[Text]]) (Maybe (TB1 (k, Showable))) (Maybe (k, Showable))
logTableInter b l =
  let ll = (fmap T.pack . unIntercalate (','==)<$> unIntercalate (':'==) l)
   in  P ([],[(b ,ll)]) (arr (join . fmap (indexTable ll)))


indexTB1 (l:xs) t
  = do
    (TB1 (KV (PK k d)  v)) <- t
    let finder = L.find (L.any (==l). L.permutations . fmap (keyString.fst).kattr)
        i = justError ("indexTB1 error finding key: " <> T.unpack (T.intercalate (","::Text) l :: Text) ) $  finder v `mplus` finder k `mplus` finder d
    case runIdentity $ getCompose $i  of
         Attr l -> Nothing
         FKT l _ _ j -> case xs of
                         [] -> Just j
                         i  -> indexTB1 xs (Just j)


-- indexTable :: [[Text]] -> TB1 (Key,Showable) -> Maybe (Key,Showable)
indexTable l (LeftTB1 j) = join $ fmap (indexTable l) j
indexTable (l:xs) t@(TB1 (KV (PK k d)  v))
  = do
    let finder = L.find (L.any (==l). L.permutations . fmap (keyString .fst) .kattr)
        i = justError ("indexTable error finding key: " <> T.unpack (T.intercalate "," l) <> show t ) $ finder v `mplus` finder k `mplus` finder d
    case runIdentity $ getCompose $ i  of
         Attr l -> return l
         FKT l _ _ j -> indexTable xs j
         IT l _ j -> indexTable xs j
indexTable l (ArrayTB1 j) =  liftA2 (,) ((head <$> fmap (fmap fst) i) ) ( (\i -> SComposite . Vector.fromList $ i ) <$> fmap (fmap snd) i)
       where i =   T.traverse  (indexTable l) j
indexTable i j = errorWithStackTrace (show (i,j))



class KeyString i where
  keyString :: i -> Text

instance KeyString Key where
  keyString = keyValue

instance KeyString Text where
  keyString = id


instance Applicative (a i) => Applicative (Parser a s i) where
  pure i = P mempty (pure i)
  P i  j <*> P l m  = P (i <> l) (j <*> m )

instance (Applicative (a i) , IsString m) => IsString (Parser a s i m) where
  fromString s = pure (fromString s)

instance (Applicative (a i),Monoid m) => Monoid (Parser a s i m) where
  mempty = P mempty (pure mempty)
  mappend (P i  l) (P j m ) =  P (mappend i j) (liftA2 mappend l  m )

findPK = concat . fmap (attrNonRec . runIdentity . getCompose) . _pkKey  . _kvKey . _unTB1

findPKM (LeftTB1 i ) =  join $ fmap findPKM i
findPKM i  = Just $ findPK i


attrNonRec (FKT ifk _ _ _ ) = concat $ fmap kattr ifk
attrNonRec (TBEither _ _ ifk ifk2 ) =  (maybe [] id $ fmap kattr ifk) <> (maybe [] id $ fmap kattr ifk)
attrNonRec (IT ifk _ _ ) = concat $ fmap kattr ifk
attrNonRec (Attr i ) = [i]

kattr = kattri . runIdentity . getCompose
kattri (Attr i ) = [i]
kattri (TBEither i j k l  ) = (maybe [] id $ fmap kattr k ) <> (maybe [] id $ fmap kattr l )
kattri (FKT i _ _ _ ) =  (L.concat $ kattr  <$> i)
kattri (IT i  _ _ ) =  (L.concat $ kattr  <$> i)


varT t = join . fmap (unRSOptional'.snd)  <$> idxT t
varN t = fmap snd  <$> idx t

type FunArrowPlug o = Step.Parser (->) (Bool,[[Text]]) (Maybe (TB1 (Key,Showable))) o
type ArrowPlug a o = Step.Parser a (Bool,[[Text]]) (Maybe (TB1 (Key,Showable))) o

