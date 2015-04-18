{-# LANGUAGE OverloadedStrings,StandaloneDeriving,FlexibleContexts,NoMonomorphismRestriction,Arrows,TupleSections,FlexibleInstances, DeriveFunctor  #-}
module Step where

import Query
import Control.Applicative
import qualified Data.Text.Lazy as T
import Warshal
import Data.String
import Data.Text.Lazy
import Data.Set (Set)
import qualified Data.List as L

import Control.Arrow.Transformer.Static
import Control.Monad
import Control.Monad.IO.Class
import Control.Arrow
import Control.Category (Category(..),id)
import Prelude hiding((.),id)
import Data.Monoid
import Control.Monad
import qualified Data.Bifunctor as BF

deriving instance Functor m => Functor (Kleisli m i )

data Step a
  = SAttr (String,(Text, a -> String))
  | SFK (Set Text) [Step a]
  deriving(Show)


instance Show (a -> Maybe Showable) where
  show _ = ""

instance Show (a -> String) where
  show _ = ""

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

data Parser m s a b = P ([s],[s]) (m a b) deriving Functor

dynP (P s d) = d

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

indexTableInter
  :: (KeyString k ,Arrow a) =>
      Bool -> String -> Parser  a (Bool,[[Text]]) (Maybe (TB1 (k, b))) (Maybe (k, b))
indexTableInter b l =
  let ll = (fmap T.pack . unIntercalate (','==)<$> unIntercalate (':'==) l)
   in  P ([(b ,ll)],[] ) (arr (join . fmap (indexTable ll)))

logTableInter
  :: (KeyString k ,Arrow a) =>
      Bool -> String -> Parser  a (Bool,[[Text]]) (Maybe (TB1 (k, b))) (Maybe (k, b))
logTableInter b l =
  let ll = (fmap T.pack . unIntercalate (','==)<$> unIntercalate (':'==) l)
   in  P ([],[(b ,ll)]) (arr (join . fmap (indexTable ll)))


indexTB1 (l:xs) t
  = do
    (TB1 (KV (PK k d)  v)) <- t
    let finder = L.find (L.any (==l). L.permutations . fmap (keyString.fst).kattr)
        i = justError ("error finding key: " <> T.unpack (T.intercalate (","::Text) l :: Text) ) $  finder v `mplus` finder k `mplus` finder d
    case i  of
         Attr l -> Nothing
         FKT l _ j -> case xs of
                         [] -> Just j
                         i  -> indexTB1 xs (Just j)


indexTable (l:xs) (TB1 (KV (PK k d)  v))
  = do
    let finder = L.find (L.any (==l). L.permutations . fmap (keyString .fst) .kattr)
        i = justError ("error finding key: " <> T.unpack (T.intercalate ","l) ) $ finder v `mplus` finder k `mplus` finder d
    case i  of
         Attr l -> return l
         FKT l _  j -> indexTable xs j


kattr (Attr i ) = [i]
kattr (FKT i _ _ ) = L.concat $ kattr <$> i
kattr (AKT i _ _ ) = L.concat $ kattr <$> i

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


