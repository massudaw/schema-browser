{-# LANGUAGE TupleSections,ScopedTypeVariables,LambdaCase,RankNTypes,DeriveFunctor,RecordWildCards,NoMonomorphismRestriction,RecursiveDo #-}
module TP.Widgets where


import Control.Monad
import Reactive.Threepenny
import qualified Graphics.UI.Threepenny as UI
import Graphics.UI.Threepenny.Core hiding (delete)

import qualified Data.Map as M
import qualified Data.Set as S
import Data.Map (Map)
import Data.Monoid
import Data.Foldable (foldl')
import Data.Interval (Interval(..))
import qualified Data.ExtendedReal as ER
import qualified Data.Interval as Interval
import qualified Data.List as L
import Data.Maybe
import Control.Concurrent
import qualified Data.Aeson as JSON

import Safe


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


evalUI el f  = getWindow el >>= \w -> runUI w f

accumTds :: MonadIO m => Tidings a -> [Event (a -> a)] -> m (Tidings a)
accumTds e l = do
	ve <- currentValue (facts e)
	accumT ve $ concatenate <$> unions (l ++ [const <$> rumors e ])


accumTs :: MonadIO m => a -> [Event (a -> a)] -> m (Tidings a)
accumTs e = accumT e . foldr1 (unionWith (.))

joinTEvent = mapTEvent id

adEvent :: Event a -> Tidings a -> UI (Tidings a)
adEvent ne t = do
  c <- currentValue (facts t)
  let ev = unionWith const (rumors t) ne
  nb <- stepper c ev
  return $ tidings nb ev



liftEvent :: MonadIO m => Event (Maybe a) -> (MVar (Maybe a) -> m void) -> m ()
liftEvent e h = do
    ivar <- liftIO $ newEmptyMVar
    liftIO $ register e (void .  maybe (return ()) ( putMVar ivar .Just )  )
    h  ivar
    return ()

cutEvent :: MonadIO m => Event b -> Tidings a -> m (Tidings a)
cutEvent ev b = do
 v <- currentValue (facts b)
 let nev = facts b <@ ev
 nbev <- stepper v nev
 return  $tidings nbev nev

updateEvent :: MonadIO m =>  (a -> Maybe a) -> Event a -> Tidings a -> m (Tidings a)
updateEvent validate ev b = do
 v <- currentValue (facts b)
 let nev = unionWith const (filterJust (validate <$> ev)) (rumors b)
 nbev <- stepper v nev
 return  $tidings nbev nev



addEvent :: MonadIO m => Event a -> Tidings a -> m (Tidings a)
addEvent ev b = do
 v <- currentValue (facts b)
 let nev = unionWith const ev (rumors b)
 nbev <- stepper v nev
 return  $tidings nbev nev

mapUITEvent body f x = do
  (e,h) <- liftIO $ newEvent
  onEvent (rumors x) (\i -> liftIO . forkIO $ (evalUI body $  f i)  >>= h)
  i <- currentValue (facts x)
  be <- liftIO $ evalUI body $ f i
  t <- stepper be e
  return $ tidings t e


mapEvent f x = do
  (e,h) <- liftIO $ newEvent
  onEvent x (\i -> liftIO . forkIO $ (f i)  >>= h)
  return  e



mapTEvent f x = do
  (e,h) <- liftIO $ newEvent
  onEvent (rumors x) (\i -> liftIO $  (f i)  >>= h)
  i <- currentValue (facts x)
  be <- liftIO $ f i
  t <- stepper be e
  return $ tidings t e
{-
mapT :: MonadIO m => (a -> IO b) -> Tidings a -> m (Tidings b)
mapT f x =  do
  let ev = unsafeMapIO f $ rumors x
  c <- currentValue  (facts x)
  b <- liftIO $ f c
  bh <- stepper  b ev
  return $ tidings bh (bh <@ rumors x)
-}

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
      let sk i =  set text (show i)
      resSpan <- multiListBox  (fmap M.toList recT) (pure []) (pure sk)
      element resSpan # set (attr "size") "10" # set style [("width","400px")]
      let bsel2 = fmap fst <$> multiUserSelection resSpan
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
  rangeInit <- listBox bp (const <$> pure Nothing <*> fkbox) (pure id) (pure (set text . show ))
  rangeEnd <- listBox bp (const <$> pure Nothing <*> fkbox) (pure id) (pure (UI.set text . show ))
  range <- UI.div # set children (getElement <$> [rangeInit,rangeEnd])
  return $ RangeBox (  liftA2 interval'' <$> (userSelection rangeInit) <*> (userSelection rangeEnd)) range

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


wrapListBox l p f q = do
  o <- listBox l p f q
  return $ TrivialWidget (userSelection o ) (getElement o)

optionalListBox' l o  s = mdo
  ol <- UI.listBox ((Nothing:) <$>  fmap (fmap Just) l) (fmap Just <$> st) (maybe UI.div <$> s)
  let sel = unionWith const (rumors $ fmap join $ UI.userSelection ol) (rumors o)
  v <- currentValue ( facts o)
  st <- stepper v sel
  return $ TrivialWidget (tidings st sel ) (getElement ol)


optionalListBox l o f s = do
  o <- listBox ((Nothing:) <$>  fmap (fmap Just) l) (fmap Just <$> o) f s
  return $TrivialWidget  (fmap join $ userSelection o)(getElement o)

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
paintEdit e b i  = element e # sink UI.style ((\ m n -> pure . ("background-color",) $ cond  m n ) <$> b <*> i )
  where cond i j
          | isJust i  && isNothing j  = "green"
          | isNothing i  && isNothing j = "red"
          | isNothing i && isJust j  = "purple"
          | i /= j = "yellow"
          | i == j = "blue"
          | otherwise = "green"

paintBorder e b = element e # sink UI.style (greenRed . isJust <$> b)
  where
      greenRed True = [("border-color","green")]
      greenRed False = [("border-color","red")]



-- Convert html to Pdf using wkhtmltopdf
-- Botão de imprimir frame no browser
printIFrame i = do
   print <- UI.button # set UI.text "Imprimir"
   bh <- stepper "" (pure ("<script> window.frames[\"" <> i <>  "\"].focus(); window.frames[\"" <> i <> "\"].print();</script>") <@ UI.click print)
   dv <- UI.div # UI.sink UI.html bh
   UI.div # set children [print,dv]




{-----------------------------------------------------------------------------
    List box
------------------------------------------------------------------------------}
-- | A list of values. The user can select entries.
data ListBox a = ListBox
    { _elementLB   :: Element
    , _selectionLB :: Tidings (Maybe a)
    }

data MultiListBox a = MultiListBox
    { _elementMLB   :: Element
    , _selectionMLB :: Tidings [a]
    }


instance Widget (ListBox a) where getElement = _elementLB
instance Widget (MultiListBox a) where getElement = _elementMLB

-- | User changes to the current selection (possibly empty).
userSelection :: ListBox a -> Tidings (Maybe a)
userSelection = _selectionLB

multiUserSelection :: MultiListBox a -> Tidings [a]
multiUserSelection = _selectionMLB

setLookup x s = if S.member x s then Just x else Nothing

-- | Create a 'ListBox'.
listBox :: forall a. Ord a
    => Tidings [a]               -- ^ list of items
    -> Tidings (Maybe a)         -- ^ selected item
    -> Tidings ([a] -> [a])      -- ^ view list to list transform (filter,sort)
    -> Tidings (a -> UI Element -> UI Element) -- ^ display for an item
    -> UI (ListBox a)
listBox bitems bsel bfilter bdisplay = do
    list <- UI.select # set UI.class_ "selectpicker"
    -- animate output items
    element list # sink oitems (facts $ map <$> bdisplay <*> bitems )

    -- animate output selection
    let
        bindex   = lookupIndex <$> facts bitems <*> facts bsel
        lookupIndex indices Nothing    = Nothing
        lookupIndex indices (Just sel) = L.findIndex (== sel)  indices

    element list # sink UI.selection bindex


    -- changing the display won't change the current selection
    -- eDisplay <- changes display
    -- sink listBox [ selection :== stepper (-1) $ bSelection <@ eDisplay ]

    -- user selection
    let
        eindexes = (\l i -> join (fmap (\is -> either (const Nothing) Just (at_ l  is)) i)) <$> facts bitems <@> UI.selectionChange list
    e <- currentValue (facts bsel)
    let
        ev =  unionWith const eindexes (rumors bsel)
    bsel2 <- stepper e ev
    let
        _selectionLB = tidings bsel2 ev
        _elementLB   = list

    return ListBox {..}

at_ :: [a] -> Int -> Either String a
at_ xs o | o < 0 = Left $ "index must not be negative, index=" ++ show o
         | otherwise = f o xs
    where f 0 (x:xs) = Right x
          f i (x:xs) = f (i-1) xs
          f i [] = Left $ "index too large, index=" ++ show o ++ ", length=" ++ show (o-i)

-- | Create a 'ListBox'.
multiListBox :: forall a. Ord a
    => Tidings [a]               -- ^ list of items
    -> Tidings [a]         -- ^ selected item
    -> Tidings (a -> UI Element -> UI Element) -- ^ display for an item
    -> UI (MultiListBox a)
multiListBox bitems bsel bdisplay = do
    list <- UI.select # set UI.multiple True

    -- animate output items
    element list # sink oitems (facts $ map <$> bdisplay <*> bitems)

    -- animate output selection
    let bindices :: Tidings (M.Map a Int)
        bindices = (M.fromList . flip zip [0..]) <$> bitems
        bindex   = lookupIndex <$> bindices <*> bsel

        lookupIndex indices sel = catMaybes $ (flip M.lookup indices) <$> sel

    element list # sink selectedMultiple (facts bindex)

    -- changing the display won't change the current selection
    -- eDisplay <- changes display
    -- sink listBox [ selection :== stepper (-1) $ bSelection <@ eDisplay ]

    -- user selection
    let bindices2 :: Tidings (M.Map Int a)
        bindices2 = M.fromList . zip [0..] <$> bitems
        eindexes = lookupIndex <$> facts bindices2 <@> selectionMultipleChange list
    e <- currentValue (facts bsel)
    let
        -- eindexes2 = (\m-> catMaybes $ fmap (flip setLookup m) e)  <$> (S.fromList <$> rumors bitems)
        ev =  foldr1 (unionWith const) [rumors bsel,eindexes]
    bsel2 <- stepper e ev
    let
        _selectionMLB = tidings bsel2 ev
        _elementMLB   = list

    return MultiListBox {..}




oitems = mkWriteAttr $ \i x -> void $ do
    return x # set children [] #+ map (\i -> UI.option # i) i



fileChange :: Element -> Event (Maybe String)
fileChange el = unsafeMapUI el (const $ UI.get readFileAttr el) (UI.valueChange el)

selectionMultipleChange :: Element -> Event [Int]
selectionMultipleChange el = unsafeMapUI el (const $ UI.get selectedMultiple el) (UI.click el)

readFileAttr :: ReadAttr Element (Maybe String)
readFileAttr = mkReadAttr get
  where
    get   el = fmap (headMay . from ) $  callFunction $ ffi "readFileInput($(%1))" el
    from s = let JSON.Success x =JSON.fromJSON s in x


selectedMultiple :: Attr Element [Int]
selectedMultiple = mkReadWriteAttr get set
  where
    get   el = fmap from $ callFunction $ ffi "getOpts($(%1))" el
    set v el = runFunction $ ffi "setOpts($(%1),%2)" el (JSON.toJSON  v)
    from s = let JSON.Success x =JSON.fromJSON s in x


