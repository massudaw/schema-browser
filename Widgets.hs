{-# LANGUAGE NoMonomorphismRestriction,RecursiveDo #-} module Widgets where


import Control.Monad
import Reactive.Threepenny
import qualified Graphics.UI.Threepenny as UI
import Graphics.UI.Threepenny.Core hiding (delete)

import qualified Data.Map as M
import Data.Map (Map)
import Data.Traversable(traverse)
import Data.Monoid
import Data.Foldable (foldl')


instance Widget (TrivialWidget  a) where
    getElement (TrivialWidget t e) = e

data TrivialWidget a =
    TrivialWidget { triding :: (Tidings a) , trielem ::  Element}


-- Generate a accum the behaviour and generate the ahead of promised event
accumT :: MonadIO m => a -> Event (a -> a) -> m (Tidings a)
accumT e ev = do
  b <- accumB e ev
  return $ tidings b (flip ($) <$> b <@> ev)

foldrTds ::  Applicative  f => (b -> a -> a ) -> f a -> [f b] -> f a
foldrTds fun  =  foldr (liftA2 fun)

fmapTds ::  Tidings a  -> (b -> a -> a ) -> [Event  b] -> Tidings a
fmapTds e fun l =   tidings (facts e) $ (\li ii ->  foldr fun li ii) <$> facts e <@> unions  l

applyTds ::  Tidings a  ->  Event  (a -> a) -> Tidings a
applyTds e l =   tidings (facts e) $ (flip ($)) <$> facts e <@> unionWith const (const <$> rumors e) l

foldTds ::  Tidings a  ->  [Event  (a -> a)] -> Tidings a
foldTds =  foldl' applyTds


accumTds :: MonadIO m => Tidings a -> [Event (a -> a)] -> m (Tidings a)
accumTds e l = do
	ve <- currentValue (facts e)
	accumT ve $ foldl1 (unionWith (.)) (l ++ [const <$> rumors e ])


accumTs :: MonadIO m => a -> [Event (a -> a)] -> m (Tidings a)
accumTs e = accumT e . foldr1 (unionWith (.))

addTs :: MonadIO m => Tidings a -> [Event a] -> m (Tidings a)
addTs t e = do
  i <- currentValue (facts t)
  accumTs i $ fmap const  <$> ((rumors t) : e)

joinT :: MonadIO m => Tidings (IO a) -> m (Tidings a)
joinT = mapT id

adEvent :: Event a -> Tidings a -> UI (Tidings a)
adEvent ne t = do
  c <- currentValue (facts t)
  let ev = unionWith const (rumors t) ne
  nb <- stepper c ev
  return $ tidings nb ev

mapT :: MonadIO m => (a -> IO b) -> Tidings a -> m (Tidings b)
mapT f x =  do
  let ev = unsafeMapIO f $ rumors x
  c <- currentValue  (facts x)
  b <- liftIO $ f c
  bh <- stepper  b ev
  return $ tidings bh (bh <@ rumors x)


insdel :: (Ord a,Ord b,Monoid b,Show a,Show b) => Behavior (Map a b) -> UI (TrivialWidget (Map a b))
insdel binsK =do
  add <- UI.button # set text "Save"
  remove <- UI.button # set text "Delete"
  res <- filterWB (UI.click add) (UI.click remove) binsK
  out <- UI.div # set children [getElement res,add,remove]
  return $ TrivialWidget (triding res ) out
    where
    filterWB emap erem bkin = mdo
      let
          insB =  M.unionWith mappend <$> bkin
          delB = foldr (.) id . fmap M.delete <$> bsel2
          recAdd = insB <@ emap
          recDel =  (facts delB) <@ erem
      recT <- accumTs M.empty  [recAdd,recDel]
      let sk i = UI.li # set text (show i)
      resSpan <- UI.multiListBox  (fmap M.toList recT) (pure []) (pure sk)
      element resSpan # set (attr "size") "10" # set style [("width","400px")]
      let bsel2 = fmap fst <$> UI.multiUserSelection resSpan
      -- Return the triding
      return $ TrivialWidget recT (getElement resSpan)


-- Style show/hide
noneShow True = [("display","block")]
noneShow False = [("display","none")]

-- Background Style green/red
greenRed True = [("background-color","green")]
greenRed False = [("background-color","red")]

switch all (Just k) = do
        mapM_ (\e -> element e # set UI.style (noneShow False) ) all
        element k # set style (noneShow True)
        return ()

tabbedChk :: [(String,Element)] -> [TrivialWidget Bool] -> UI Element
tabbedChk tabs chk = do
  header <- buttonSet  (fst <$> tabs) show
  let lk k = M.lookup k (M.fromList tabs)
  v <- currentValue (facts $ lk <$> triding header)
  switch (snd <$> tabs) v
  onEvent (rumors $ lk <$> triding header) (switch (snd <$> tabs))
  body <- UI.div # set children (snd <$> tabs)
  UI.div # set children [getElement header,body]


tabbed :: [(String,Element)] -> UI Element
tabbed  tabs = do
  header <- buttonSet  (fst <$> tabs) show
  let lk k = M.lookup k (M.fromList tabs)
  v <- currentValue (facts $ lk <$> triding header)
  switch (fmap snd tabs) v
  onEvent (rumors $ lk <$> triding header) (switch (fmap snd tabs))
  body <- UI.div # set children (snd <$> tabs)
  UI.div # set children [getElement header,body]

-- List of buttons with constant value
buttonSet :: [a] -> (a -> String) -> UI (TrivialWidget a)
buttonSet ks h =do
  buttons <- mapM (buttonString h) ks
  dv <- UI.div # set children (fst <$> buttons)
  let evs = foldr1 (unionWith (const))  (snd <$> buttons)
  bv <- stepper (head ks) evs
  return (TrivialWidget (tidings bv evs) dv)
    where
      buttonString h k= do
        b <- UI.button # set text (h k)
        let ev = pure k <@ UI.click  b
        return (b,ev)

items :: WriteAttr Element [UI Element]
items = mkWriteAttr $ \i x -> void $ return x # set children [] #+ i

-- Simple checkbox
checkedWidget :: UI (TrivialWidget Bool)
checkedWidget = do
  i <- UI.input # set UI.type_ "checkbox"
  let e = UI.checkedChange i
  b <- stepper False e
  return $ TrivialWidget  (tidings b e) i


