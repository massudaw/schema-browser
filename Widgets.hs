{-# LANGUAGE TupleSections,LambdaCase,RankNTypes,RecordWildCards,DeriveFunctor,NoMonomorphismRestriction,RecursiveDo #-} module Widgets where


import Control.Monad
import Reactive.Threepenny
import qualified Graphics.UI.Threepenny as UI
import Graphics.UI.Threepenny.Core hiding (delete)

import qualified Data.Map as M
import qualified Data.Set as S
import Data.Map (Map)
import Data.Traversable(traverse)
import Data.Monoid
import Data.Foldable (foldl')
import Data.Interval (Interval(..),interval)
import qualified Data.ExtendedReal as ER
import qualified Data.Interval as Interval
import qualified Data.List as L
import Text.Read
import Query
import Postgresql
import Data.Maybe
import Data.Distributive



instance Widget (TrivialWidget  a) where
    getElement (TrivialWidget t e) = e

data TrivialWidget a =
    TrivialWidget { triding :: (Tidings a) , trielem ::  Element} deriving(Functor)



-- Generate a accum the behaviour and generate the ahead of promised event
accumT :: MonadIO m => a -> Event (a -> a) -> m (Tidings a)
accumT e ev = do
  b <- accumB e ev
  return $ tidings b (flip ($) <$> b <@> ev)

foldrTds ::  Applicative  f => (b -> a -> a ) -> f a -> [f b] -> f a
foldrTds fun  =  foldr (liftA2 fun)

fmapTds ::  Tidings a  -> (a -> a -> a ) -> [Event  a] -> Tidings a
fmapTds e fun l =   tidings (facts e) $ (\li ii ->  foldr fun li ii) <$> facts e <@> unions  (rumors e: l)

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

mapUIT :: Element -> (a -> UI b) -> Tidings a -> UI (Tidings b)
mapUIT e f x =  do
  let ev = unsafeMapUI e f $ rumors x
  c <- currentValue  (facts x)
  b <- f c
  bh <- stepper  b ev
  return $ tidings bh (bh <@ rumors x)


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

noneShowSpan True = [("display","inline")]
noneShowSpan False = [("display","none")]

-- Background Style green/red
greenRed True = [("background-color","green")]
greenRed False = [("background-color","red")]

switch all (Just k) = do
        mapM_ (\e -> element e # set UI.style (noneShow False) ) all
        element k # set style (noneShow True)
        return ()

tabbedChk :: [(String,(TrivialWidget Bool,Element))] -> UI (Element)
tabbedChk [] = UI.div
tabbedChk tabs = do
    (tds,headers) <- checkeds tabs
    header <- UI.div # set children headers
    let lk td (k,(_,e))  = do
          let enab = S.member  k <$> td
          element e # sink UI.style (noneShow <$> facts enab)
    mapM_ (lk tds) tabs
    body <- UI.div # set children (snd .snd <$> tabs)
    UI.div # set children [header,body]
  where
    checked i = do
      label <- UI.span # set UI.text (fst i)
      dv <- UI.span # set children [label,getElement (fst $ snd i)]
      return (((\b -> if  b then S.singleton (fst i) else S.empty) <$> (triding $fst $ snd i)) ,dv)
    checkeds is  = do
      chks <- mapM checked is
      return $ foldr (\(t,d) (ta,da) -> (liftA2 S.union t ta, d : da) ) (pure S.empty,[]) chks


data RangeBox a
  = RangeBox
  { _rangeSelection ::  Tidings (Maybe (Interval a))
  , _rangeElement :: Element
  }

rangeBoxes fkbox bp = do
  rangeInit <- UI.listBox bp (const <$> pure Nothing <*> fkbox) (pure (\i-> UI.li # set text (show i)))
  rangeEnd <- UI.listBox bp (const <$> pure Nothing <*> fkbox) (pure (\i-> UI.li # set text (show i)))
  range <- UI.div # set children (getElement <$> [rangeInit,rangeEnd])
  return $ RangeBox (  liftA2 interval'' <$> (UI.userSelection rangeInit) <*> (UI.userSelection rangeEnd)) range

instance Widget (RangeBox a) where
  getElement = _rangeElement

tabbedB :: [(String,(Element,Behavior Bool))] ->  UI Element
tabbedB [] = UI.div
tabbedB  tabs = do
  header <- buttonSetB  ((\(i,(e,b)) -> (i,b))<$> tabs) id
  let lk k = M.lookup k (M.fromList $ (\(s,(e,_))-> (s,e)) <$> tabs)
  v <- currentValue (facts $ lk <$> triding header)
  switch (fmap (fst.snd) tabs) v
  onEvent (rumors $ lk <$> triding header) (switch (fst.snd <$> tabs))
  body <- UI.div # set children (fst.snd <$> tabs)
  UI.div # set children [getElement header,body]


tabbed :: [(String,Element)] ->  UI Element
tabbed [] = UI.div
tabbed  tabs = do
  header <- buttonSet  (fst <$> tabs) id
  let lk k = M.lookup k (M.fromList tabs)
  v <- currentValue (facts $ lk <$> triding header)
  switch (fmap snd tabs) v
  onEvent (rumors $ lk <$> triding header) (switch (fmap snd tabs))
  body <- UI.div # set children (snd <$> tabs)
  UI.div # set children [getElement header,body]

-- List of buttons with constant value
buttonFSet :: [a] -> Behavior (Maybe a) -> Behavior (String -> Bool ) ->  (a -> String) -> UI (TrivialWidget a)
buttonFSet ks binit bf h =do
  buttons <- mapM (buttonString h) ks
  dv <- UI.div # set children (fst <$> buttons)
  let evs = foldr (unionWith (const)) never (snd <$> buttons)
  v <- currentValue binit
  bv <- stepper (maybe (head ks) id v) evs
  return (TrivialWidget (tidings bv evs) dv)
    where
      buttonString h k= do
        b <- UI.button # set text (h k)# sink UI.style ((\i-> noneShowSpan (i (h k))) <$> bf)
        let ev = pure k <@ UI.click  b
        return (b,ev)

buttonSetB :: [(a,Behavior Bool)]  ->  (a -> String) -> UI (TrivialWidget a)
buttonSetB ks h =do
  buttons <- mapM (\i ->  buttonString h (fst i)  (snd i) ) ks
  dv <- UI.div # set children (fst <$> buttons)
  let evs = foldr (unionWith (const)) never (snd <$> buttons)
  bv <- stepper (fst $ head ks) evs
  return (TrivialWidget (tidings bv evs) dv)
    where
      buttonString h k l = do
        b <- UI.button # set text (h k) # sink UI.style (noneShow <$> l)
        let ev = pure k <@ UI.click  b
        return (b,ev)


buttonSet :: [a]  ->  (a -> String) -> UI (TrivialWidget a)
buttonSet ks h =do
  buttons <- mapM (buttonString h) ks
  dv <- UI.div # set children (fst <$> buttons)
  let evs = foldr (unionWith (const)) never (snd <$> buttons)
  bv <- stepper (head ks) evs
  return (TrivialWidget (tidings bv evs) dv)
    where
      buttonString h k= do
        b <- UI.button # set text (h k)
        let ev = pure k <@ UI.click  b
        return (b,ev)



items :: WriteAttr Element [UI Element]
items = mkWriteAttr $ \i x -> void $ return x # set children [] #+ i

appendItems :: WriteAttr Element [UI Element]
appendItems = mkWriteAttr $ \i x -> void $ return x  #+ i

-- Simple checkbox
checkedWidget :: Tidings Bool -> UI (TrivialWidget Bool)
checkedWidget init = do
  i <- UI.input # set UI.type_ "checkbox" # sink UI.checked (facts init)
  let e = unionWith const (rumors init) (UI.checkedChange i)
  v <- currentValue (facts init)
  b <- stepper v e
  dv <- UI.span # set children [i] # set UI.style [("margin","2px")]
  return $ TrivialWidget  (tidings b e) dv


wrapListBox l p q = do
  o <- UI.listBox l p q
  return $ TrivialWidget (UI.userSelection o ) (getElement o)

optionalListBox l o s = do
  o <-UI.listBox ((Nothing:) <$>  fmap (fmap Just) l) (fmap Just <$> o) s
  return $TrivialWidget  (fmap join $ UI.userSelection o)(getElement o)

interval'' i j = Interval.interval (ER.Finite i ,True) (ER.Finite j , True)


read1 (EventData (Just s:_)) = read s

onkey :: Element -> (Int -> Maybe Int ) -> Event String
onkey el f = unsafeMapUI el (const $ UI.get value el) (filterJust $ f . read1 <$> domEvent "keydown" el)

onEnter el = onkey el (\case {13-> Just 13; i -> Nothing})


testPointInRange ui = do
  startGUI defaultConfig {tpPort = Just 8000} (\w -> do
                      e1 <- ui
                      getBody w #+ [element e1]
                      return () )



unsafeMapUI el f = unsafeMapIO (\a -> getWindow el >>= \w -> runUI w (f a))

paint e b = element e # sink UI.style (greenRed . isJust <$> b)
paintBorder e b = element e # sink UI.style (greenRed . isJust <$> b)
  where
      greenRed True = [("border-color","green")]
      greenRed False = [("border-color","red")]


