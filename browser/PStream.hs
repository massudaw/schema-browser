{-# LANGUAGE FlexibleInstances,TypeSynonymInstances,TypeFamilies,TypeOperators,FlexibleContexts #-}
module PStream where

import qualified Types.Patch as P
import Types.Patch(Compact(..),Patch(..),Index)
import Data.Foldable(foldl')
import Reactive.Threepenny
import Control.Monad.Trans
import Data.Monoid

data PStream a = PStream { psvalue :: (Behavior a ) , psevent :: (Event (Index a))}

type a |> b = PAction a b
type a *|> b = (a -> Index b)

data PAction a b = PAction
  { total :: a -> b
  , partial :: (a ,Index a) -> Index b
  }

instance Compact String where
  compact = pure .concat

instance Patch String where
  type Index String = String
  apply =  (++)

instance Patch (a -> b ) where
  type Index (a -> b) = ((a,Index a) -> Index b)

instance Patch (PAction a b ) where
  type Index (PAction a b) = (a,Index a) -> Index b

class PFunctor f where
  pmap :: (a |> b ) -> f a -> f b

class PApplicative f where
  ppure :: a -> f a
  papply :: (Monoid (Index a),Monoid (Index b))  => f (a |> b) -> f a -> f b

instance PFunctor (PAction a ) where
  pmap (PAction i j ) (PAction l m) = PAction (i . l)  (\(a,b) -> j (l  a, m (a,b)))

instance PApplicative PStream where
  ppure  i= PStream (pure  i) never
  papply (PStream bx ex ) (PStream by ey) =  PStream  b (merge x y)
   where
    b = total <$> bx <*> by
    x = (\i -> curry ( partial  i)) <$> bx <*> by <@> ey
    y = (\i j ->  j (i,mempty)) <$> by <@> ex

infixl 4 <$|>
infixl 4 <*|>

paction2
  :: Monoid (Index t) => (t -> a -> b)
  -> ((t, Index t) -> (a, Index a) -> Index b)
  -> PAction t (PAction a b)
paction2 i  k = PAction (liftA2 PAction i (\i (a,b) -> k (i,mempty) (a,b)) ) k

paction3
  ::  (Monoid (Index v), Monoid (Index t))
  => (v -> t -> a -> b)
  -> ((v,Index v) -> (t, Index t) -> (a, Index a) -> Index b)
  -> PAction v (PAction t (PAction a b))
paction3 i  k = PAction (liftA2 PAction (liftA2 (liftA2 PAction) i (\i a (c,d)-> k (i,mempty) (a,mempty) (c,d))) (\i (a,b) (c,d)-> k (i,mempty) (a,b) (c,d))) k


unaction2 (PAction i j)  = (fmap total i,j,fmap partial i )
unaction3 (PAction i j)  = (fmap (fmap total.total ) i,fmap (fmap partial.total ) i,fmap partial i ,j)

(<*|>) :: (PApplicative f ,Monoid (Index a),Monoid (Index b) )=> f (a |> b) -> f a -> f b
(<*|>)  = papply

(<$|>) ::  PFunctor f => (a |> b ) -> f a -> f b
(<$|>) = pmap


instance PFunctor PStream where
  pmap (PAction f g) (PStream b e) = PStream (f <$> b) (curry g <$> b <@> e)

test = runDynamic $ do
  (e,h) <- newEvent
  (e2,h2) <- newEvent
  (e3,h3) <- newEvent
  t <- accumS "wfew" e
  t2 <- accumS "abc" e2
  t3 <- accumS "poi" e3
  let a = (paction3 (\i j k-> (i ,j <> k))   (\(a,b) (c,d) (e,f) -> (b ,d <> f)) <$|>  t <*|> t2 <*|> t3 )  :: PStream (String,String)
  i <- currentValue (facts . toTidings $ a)
  onEventIO (psevent a) $   print . ("EventP: " ++) . show
  onEventIO (rumors $ toTidings a) $   print . ("EventT: " ++) . show
  onChangeDyn (psvalue a)    (liftIO . print . ("Behavior: "++). show )
  liftIO $ mapM h2 ["a11","a22","a33"]
  liftIO $ mapM h3 ["p11","p22","p33"]
  liftIO $ mapM h ["w11","w22","w33"]
  liftIO $print i
  liftIO $print "End"


focus :: Patch b => (a -> b) -> (Index a -> Maybe (Index b)) -> PStream a -> PStream b
focus  f fp (PStream b e) =
  PStream (f <$> b) (filterJust $ fp <$> e)



toTidings :: Patch a => PStream a -> Tidings a
toTidings  (PStream b e) = tidings b (P.apply <$> b <@> e)

toPStream :: Patch a =>  Tidings a -> PStream a
toPStream t = PStream (facts t) (filterJust $ P.diff <$> facts t <@> rumors t)


accumS :: Patch a => a -> Event (Index a) -> Dynamic (PStream a)
accumS i l = do
  b <- accumB i (flip P.apply <$> l)
  return $ PStream b l

merge :: Monoid a => Event a -> Event a -> Event a
merge = unionWith mappend

addEvent :: (Monoid (Index a), Patch a) =>  PStream a -> Event (Index a) -> Dynamic (PStream a)
addEvent  (PStream ob oe) e = do
  i <- currentValue ob
  let newE = merge oe (e)
  b <-  accumB i (unionWith (.) ( flip P.apply  <$> oe) (flip (P.apply) <$> e) )
  return $ PStream b newE

