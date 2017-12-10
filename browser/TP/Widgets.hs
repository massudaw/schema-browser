{-# LANGUAGE FlexibleContexts,TupleSections,ScopedTypeVariables,LambdaCase,RankNTypes,DeriveFunctor,RecordWildCards,NoMonomorphismRestriction,RecursiveDo #-}
module TP.Widgets where


import GHC.Stack
import Control.Concurrent.Async
import Control.Monad.Writer hiding((<>))
import Control.Monad
import Control.Arrow(first)
import Data.Tuple(swap)
import qualified Control.Monad.Trans.Writer as Writer
import Control.Monad
import Data.Ord
import Reactive.Threepenny
import qualified Graphics.UI.Threepenny as UI
import Graphics.UI.Threepenny.Core hiding (delete)
import Graphics.UI.Threepenny.Internal (wTimeZone)

import qualified Data.Map as M
import qualified Data.Foldable as F
import Data.Time.LocalTime
import qualified Data.Set as S
import Data.Map (Map)
import Data.Semigroup
import Data.Foldable (foldl')
import Data.Interval (Interval(..))
import qualified Data.ExtendedReal as ER
import qualified Data.Interval as Interval
import qualified Data.List as L
import Data.Maybe
import Control.Concurrent
import qualified Data.Aeson as JSON

import Safe


import Debug.Trace
import Utils

instance Widget (TrivialWidget  a) where
    getElement (TrivialWidget t e) = e

instance Semigroup a => Semigroup (Event a) where
  i <> j = unionWith (<>) i j

instance Semigroup a => Monoid (Event a) where
  mempty = never
  mappend i j =  i <>  j

data TrivialWidget a =
    TrivialWidget { triding :: (Tidings a) , trielem ::  Element}

instance Functor TrivialWidget where
    fmap = trmap

{-# NOINLINE[1] trmap #-}
trmap f (TrivialWidget e j) = TrivialWidget (fmap f e) j

{-# RULES
"trmap/trmap" forall f g xs . trmap f (trmap g xs) = trmap (f . g) xs
 #-}

-- Generate a accum the behaviour and generate the ahead of promised event


evalUI el f = liftIO (getWindow el) >>= \w ->  runUI w f

evalDyn el f = getWindow el >>= \w -> fmap fst $ runDynamic $ runUI w f



adEvent :: Event a -> Tidings a -> UI (Tidings a)
adEvent ne t = do
  c <- currentValue (facts t)
  let ev = unionWith const (rumors t) ne
  nb <- ui $ stepper c ev
  return $ tidings nb ev



liftEvent :: Event (Maybe a) -> (MVar (Maybe a) -> IO  void) -> Dynamic ()
liftEvent e h = do
  ivar <- liftIO$ newEmptyMVar
  register e (void .  maybe (return ()) ( putMVar ivar .Just )  )
  return ()

cutEvent :: Event b -> Tidings a -> Dynamic (Tidings a)
cutEvent ev b = do
 v <- currentValue (facts b)
 let nev = facts b <@ ev
 nbev <- stepper v nev
 return  $tidings nbev nev

updateTEvent :: (a -> Maybe a) -> Tidings a -> Tidings a -> Dynamic (Tidings a)
updateTEvent validate ev b = do
 v <- currentValue (facts b)
 evi <- currentValue (facts ev)
 let nev = unionWith const (filterJust (validate <$> rumors ev)) (rumors b)
 nbev <- stepper (maybe evi id (validate v)) nev
 return  $tidings nbev nev


updateEvent :: (a -> Maybe a) -> Event a -> Tidings a -> Dynamic (Tidings a)
updateEvent validate ev b = do
 v <- currentValue (facts b)
 let nev = unionWith const (filterJust (validate <$> ev)) (rumors b)
 nbev <- stepper v nev
 return  $tidings nbev nev


diffTidings f = tidings (facts f) (diffEvent (facts f ) (rumors f))
diffEvent b ev = filterJust $ (\i j -> if i == j then Nothing else Just j ) <$> b <@> ev
notdiffEvent b ev = filterJust $ (\i j -> if i /= j then Nothing else Just j ) <$> b <@> ev

addEvent :: Event a -> Tidings a -> Dynamic (Tidings a)
addEvent ev b = do
 v <- currentValue (facts b)
 let nev = unionWith const (rumors b) ev
 nbev <- stepper v nev
 return  $tidings nbev nev



mapEventFin f x = ui $ mdo
  i <- mapEventDyn (\(s,x) -> liftIO (sequence s) >>  f x)  ((,)<$> t <@> x)
  t <- stepper [] (snd <$> i)
  return (fst <$> i)

mapEvent :: (a -> IO b) -> Event a -> Dynamic (Event b)
mapEvent f x = do
  (e,h) <- newEvent
  onEventIO x (\i -> void  $ (f i)  >>= h)
  return  e

mapTEventDynInterrupt f x = do
  i <- currentValue  (facts x)
  mapT0EventDynInterrupt i f x

mapTEventDyn :: (a -> Dynamic b) -> Tidings a -> Dynamic (Tidings b)
mapTEventDyn f x = do
  i <- currentValue  (facts x)
  mapT0EventDyn i f x

cacheTidings :: Tidings a -> Dynamic (Tidings a)
-- cacheTidings  t = return t
cacheTidings  t = do
  (e,h) <- newEvent
  onEventIO (rumors t) h
  v <- currentValue (facts t)
  bt <- stepper v e
  return $ tidings bt e

mapT0EventDyn :: a -> (a -> Dynamic b) -> Tidings a -> Dynamic (Tidings b)
mapT0EventDyn i f x = mdo
  ini <- liftIO $ runDynamic $ f i
  e <- mapEventDyn (\ ~(a,b) -> liftIO (sequence_ a) >>  f b) ((,)<$> (snd <$> t) <@> rumors x)
  t <- stepper ini e
  registerDynamic $ sequence_ . snd =<< currentValue t
  return $ tidings (fst <$>t) (fst <$> e)



mapT0EventDynInterrupt :: a -> (a -> Dynamic b) -> Tidings a -> Dynamic (Tidings b)
mapT0EventDynInterrupt i f x = mdo
  ini <- liftIO $ runDynamic $ f i
  (e,ei) <- mapEventDynInterrupt (\ ~(a,i ,b) -> liftIO i >> liftIO (sequence_ a) >>  f b) ((,,)<$> (snd <$> t)  <*> ti <@> rumors x)
  t <- stepper ini e
  ti <- stepper (return ()) ei
  registerDynamic $ sequence_ . snd =<< currentValue t
  return $ tidings (fst <$>t) (fst <$> e)





-- Style show/hide
noneShow = noneDisplay "block"

noneShowFlex = noneDisplay "inline-flex"

noneShowSpan = noneDisplay "inline"

noneDisplay e True = [("display",e)]
noneDisplay e False = [("display","none")]

-- Background Style green/red

greenRed True = [("background-color","green")]
greenRed False = [("background-color","red")]

greenRedBlue True True = [("background-color","blue")]
greenRedBlue True False = [("background-color","green")]
greenRedBlue False True = [("background-color","purple")]
greenRedBlue False False= [("background-color","red")]

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
  return $ RangeBox (  liftA2 interval'' <$> (triding rangeInit) <*> (triding rangeEnd)) range

instance Widget (RangeBox a) where
  getElement = _rangeElement

checkDivSetTGen :: (Ord a,Eq a) => [a] -> Tidings (S.Set a ) ->  (a -> UI (a,(Element,Event Bool) ))-> Tidings (a -> Element  -> UI Element ) -> UI (TrivialWidget (S.Set a))
checkDivSetTGen ks binit   el st = do
  buttons <- mapM el  ks
  vini <- currentValue (facts binit)
  let
    evs = unionWith const (const <$> rumors binit) (foldr (unionWith (.)) never $ (\(i,(_,ev)) -> (\ab -> if not ab then S.delete i else S.insert i)  <$> ev) <$> buttons)
  bv <- ui $ accumT vini  evs
  -- Place sorted Itens
  dv <- UI.div # sink items (facts $(\ sti -> fmap (\ (k,(v,_)) -> sti k v)  $ buttons) <$> st )
  -- Sink check state to elems
  mapM (\(k,e) -> element (fst e) # set UI.checked (S.member k $ vini) # sink UI.checked (S.member k <$> facts bv  )) buttons
  return (TrivialWidget bv dv)


checkDivSetT :: (Ord b ,Eq a) => [a] -> Tidings (a -> b) -> Tidings [a] ->  (a -> UI Element ) -> (a -> UI Element  -> UI Element ) -> UI (TrivialWidget [a])
checkDivSetT ks sort binit   el st = do
  buttons <- mapM (buttonString  )  ks
  let
    evs = unionWith const (const <$> rumors binit) (foldr (unionWith (.)) never $ fmap (\(i,b) -> if b then (i:) else L.delete i) . snd .snd <$> buttons)
  v <- currentValue (facts binit)
  bv <- ui $ accumT v  evs
  dv <- UI.div # sink items ((\f -> fmap (\ (k,(v,_)) -> st k (element v) # sink UI.checked (elem k <$> facts bv)) . L.sortBy (flip $ comparing (f . fst))  $ buttons) <$>  facts sort )
  return (TrivialWidget bv  dv)
    where
      buttonString   k = do
        v <- currentValue (facts binit)
        b <- el k # set UI.checked  (elem k v )
        checki  <- UI.checkedChange b
        let ev = (k,)<$>checki
        return (k,(b,ev))


buttonDivSetT :: (Ord b ,Eq a) => [a] -> Tidings (a -> b) -> Tidings (Maybe a) ->  (a -> UI Element ) -> (a -> UI Element  -> UI Element ) -> UI (TrivialWidget (Maybe a))
buttonDivSetT ks sort binit   el st = mdo
  buttons <- mapM (buttonString  )  ks
  dv <- UI.div # sink items ((\f -> fmap (\ (k,(v,_)) -> st k (element v) # sink UI.enabled (not . (Just k==) <$> bv)) . L.sortBy (flip $ comparing (f . fst))  $ buttons) <$>  facts sort )
  let evs = foldl (unionWith const) (filterJust $ rumors binit) (snd .snd <$> buttons)
  v <- currentValue (facts binit)
  bv <- ui $ stepper  v  (Just <$> evs)
  return (TrivialWidget (tidings bv (Just <$> evs)) dv)
    where
      buttonString   k = do
        b <- el k
        cli <- UI.click b
        let ev = pure k <@ cli
        return (k,(b,ev))

buttonDivSetFun :: Eq a => [a] -> Tidings (Maybe a)  ->  (a -> UI Element ) -> UI (TrivialWidget a)
buttonDivSetFun ks binit   el = mdo
  buttons <- mapM (buttonString  bv ) ks
  dv <- UI.div # set children (fst <$> buttons)
  let evs = foldl (unionWith const) (filterJust $ rumors binit) (snd <$> buttons)
  v <- currentValue (facts binit)
  bv <- ui $ stepper (maybe (justError "no head" $ safeHead ks) id v) evs
  return (TrivialWidget (tidings bv evs) dv)
    where
      buttonString   bv k = do
        b <- el k # sink UI.enabled (not . (k==) <$> bv)
        cli <- UI.click b
        let ev = pure k <@ cli
        return (b,ev)



buttonDivSet  ks binit el = buttonDivSetO ks binit (sink UI.enabled ) el

buttonDivSetO :: Eq a => [a] -> Tidings (Maybe a)  ->  (Behavior Bool -> UI Element -> UI Element  )  -> (a -> UI Element ) -> UI (TrivialWidget a)
buttonDivSetO ks binit   op el = mdo
  buttons <- mapM (buttonString  bv ) ks
  dv <- UI.div # set children (fst <$> buttons)
  let evs = foldl (unionWith const) (filterJust $ rumors binit) (snd <$> buttons)
  v <- currentValue (facts binit)
  bv <- ui $ stepper (maybe (justError "no head" $ safeHead ks) id v) evs
  return (TrivialWidget (tidings bv evs) dv)
    where
      buttonString   bv k = do
        b <- el k # op (not . (k==) <$> bv)
        cli <- UI.click b
        let ev = pure k <@ cli
        return (b,ev)



items :: WriteAttr Element [UI Element]
items = mkWriteAttr $ \i x -> void $ return x # set children [] #+ i

appendItems :: WriteAttr Element [UI Element]
appendItems = mkWriteAttr $ \i x -> void $ return x  #+ i

-- Simple checkbox
checkedWidget :: Tidings Bool -> UI (TrivialWidget Bool)
checkedWidget init = do
  i <- UI.input # set UI.type_ "checkbox" # sink UI.checked (facts init)
  ev <- UI.checkedChange i
  let e = unionWith const (rumors init) ev
  v <- currentValue (facts init)
  b <- ui$ stepper v e
  dv <- UI.span # set children [i] # set UI.style [("padding","2px")]
  return $ TrivialWidget  (tidings b e) dv

checkedWidgetM :: Tidings (Maybe Bool) -> UI (TrivialWidget (Maybe Bool))
checkedWidgetM init = do
  i <- UI.input # set UI.type_ "checkbox" # sink UI.checked (maybe False id <$> facts init)
  ev <- UI.checkedChange i
  let e = unionWith const (rumors init) (Just <$>  ev )
  v <- currentValue (facts init)
  b <- ui $ stepper v e
  dv <- UI.span # set children [i] # set UI.style [("padding","2px")]
  return $ TrivialWidget  (tidings b e) dv


wrapListBox l p f q = do
  o <- listBox l p f q
  return $ TrivialWidget (triding o ) (getElement o)

optionalListBox' l o  s = mdo
  ol <- UI.listBox ((Nothing:) <$>  fmap (fmap Just) l) (fmap Just <$> st) (maybe UI.div <$> s)
  let sel = unionWith const (rumors $ fmap join $ UI.userSelection ol) (rumors o)
  v <- currentValue ( facts o)
  st <- ui $ stepper v sel
  return $ TrivialWidget (tidings st sel ) (getElement ol)


optionalListBox l o f s = do
  o <- listBox ((Nothing:) <$>  fmap (fmap Just) l) (fmap Just <$> o) f s
  return $TrivialWidget  (fmap join $ triding o)(getElement o)

interval'' i j = Interval.interval (ER.Finite i ,True) (ER.Finite j , True)

detailsLabel
  :: (UI Element -> UI Element) -> UI Element
  -> UI Element
detailsLabel lab gen = do
  l <- flabel # lab
  hl <- UI.div
  ht <- hoverTip2 l hl
  bh <- ui $ stepper False ht
  let dynShow True = pure <$> gen
      dynShow False = return []
  out <- traverseUI dynShow (tidings bh ht)
  details <- UI.div # sink children (facts out)
  element hl # set children [l,details]

read1 s = unsafeFromJSON s
-- read1 (EventData i )  = errorWithStackTrace $show i

readBool "true" = Just True
readBool "false" = Just False
readBool i = Nothing


onkey :: Element -> (Int,Bool,Bool,Bool) -> UI (Event ())
onkey el f = fmap (const ()) <$>  UI.keydownFilter f el

onAltEnter el = onkey el (13,False,True,False)
onAltE el = onkey el (69,False,True,False)
onAltU el = onkey el (85,False,True,False)
onAltI el = onkey el (73,False,True,False)
onAltO el = onkey el (79,False,True,False)
onAlt ix el = onkey el (ix,False,True,False)
onShiftAlt ix el = onkey el (ix,True,True,False)
onEnter el = onkey el (13,False,False,False)
onEsc el = onkey el (27,False,False,False)


testPointInRange ui = do
  startGUI defaultConfig {jsPort = Just 8000} (\w -> do
                      e1 <- ui
                      addBody [e1]
                      return () )


-- paint e b = element e # sink UI.style (greenRed . isJust <$> b)
paintEdit e b i  = element e # sinkDiff UI.style ((\ m n -> pure . ("background-color",) $ cond  m n ) <$> b <*> i )
  where cond i j
          | isJust i  && isNothing j  = "green"
          | isNothing i  && isNothing j = "red"
          | isNothing i && isJust j  = "purple"
          | i /= j = "yellow"
          -- | isNothing i && isJust j  = traceShow j "purple"
          | i /= j = trace ((concat $ fmap differ $   zip  si sj) <> L.drop (L.length sj) si  <> L.drop (L.length si) sj ) "yellow"
          | i == j = "blue"
          | otherwise = "green"
              where si = show i
                    sj = show j

differ = (\(i,j) -> if i == j then [i]  else "(" <> [i] <> "|" <> [j] <> ")" )
paintBorder e b i  = element e # sink0 UI.style ((\ m n -> (:[("border-style","solid"),("border-width","1px")]).("border-color",) $ cond  m n ) <$> b <*> i )
  where cond i j
          | isJust i  && isNothing j  = "green"
          | isNothing i  && isNothing j = "red"
          | isNothing i && isJust j  = "purple"
          | i /= j = "yellow"
          -- | i /= j = trace (concat $ zipWith (\i j -> if i == j then "_" else "(" <> [i] <> "|" <> [j] <> ")" ) (show i ) ( show j)) "yellow"
          | i == j = "blue"
          | otherwise = "green"




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
listBoxEl = listBoxElEq (==)
listBoxElEq :: forall a. (Show a)
    =>
    (a -> a -> Bool)
    ->  Element
    -> Tidings [a]               -- ^ list of items
    -> Tidings (Maybe a)         -- ^ selected item
    -> Tidings ([a] -> [a])      -- ^ view list to list transform (filter,sort)
    -> Tidings (a -> UI Element -> UI Element) -- ^ display for an item
    -> UI (TrivialWidget (Maybe a))
listBoxElEq eq list bitems bsel bfilter bdisplay = do
    let bindices :: Tidings [a]
        bindices =  bfilter <*> bitems
    -- animate output items
    let
        bindex   = lookupIndex <$> facts bitems <#> bsel
        lookupIndex indices Nothing    = Nothing
        lookupIndex indices (Just sel) = L.findIndex (eq sel)  indices
        els = liftA2 (\i j -> (\ix ->  UI.option # j ix )<$> i) bitems bdisplay
    element list # sink items (facts els )

    -- animate output selection

    element list # sinkDiff UI.selection bindex


    -- changing the display won't change the current selection
    -- eDisplay <- changes display
    -- sink listBox [ selection :== stepper (-1) $ bSelection <@ eDisplay ]

    -- user selection
    selEv <- fmap Just <$> UI.selectionChange list
    s <- ui $ calmE selEv
    selBh <- ui $stepper   Nothing s
    let
        eindexes = (\l i-> join (fmap (\is -> either (const Nothing) Just (at_ l  is)) i)) <$> facts bitems <#> tidings selBh selEv
    let
        _selectionLB = eindexes
        _elementLB   = list

    return $ TrivialWidget _selectionLB _elementLB


-- | Create a 'ListBox'.
listBox :: forall a. (Ord a,Show a)
    => Tidings [a]               -- ^ list of items
    -> Tidings (Maybe a)         -- ^ selected item
    -> Tidings ([a] -> [a])      -- ^ view list to list transform (filter,sort)
    -> Tidings (a -> UI Element -> UI Element) -- ^ display for an item
    -> UI (TrivialWidget (Maybe a))
listBox bitems bsel bfilter bdisplay = do
    list <- UI.select
    listBoxEl  list bitems bsel bfilter bdisplay

at_ :: [a] -> Int -> Either String a
at_ xs o | o < 0 = Left $ "index must not be negative, index=" ++ show o
         | otherwise = f o xs
    where f 0 (x:xs) = Right x
          f i (x:xs) = f (i-1) xs
          f i [] = Left $ "index too large, index=" ++ show o ++ ", length=" ++ show (o-i)

-- | Create a 'ListBox'.
multiListBox :: forall a.( Ord a,Show a)
    => Tidings [a]               -- ^ list of items
    -> Tidings [a]         -- ^ selected item
    -> Tidings (a -> UI Element -> UI Element) -- ^ display for an item
    -> UI (TrivialWidget [a])
multiListBox bitems bsel bdisplay = do
    list <- UI.select # set UI.multiple True

    -- animate output items

    let bindices :: Tidings (M.Map a Int)
        bindices = (M.fromList . flip zip [0..]) <$> bitems
        bindex   = lookupIndex <$> bindices <*> bsel
        lookupIndex indices sel = catMaybes $ (flip M.lookup indices) <$> sel
    els <- ui $ accumDiff (\k-> evalUI list $  UI.option ) (S.fromList <$> bitems )
    element list # sink items (facts $ (\m l  -> fmap (uncurry l) . M.toList .fmap element  $ m)<$> els <*> bdisplay )

    -- animate output selection


    element list # sink selectedMultiple (facts bindex)

    -- changing the display won't change the current selection
    -- eDisplay <- changes display
    -- sink listBox [ selection :== stepper (-1) $ bSelection <@ eDisplay ]

    -- user selection
    sel <- selectionMultipleChange list
    let bindices2 :: Tidings (M.Map Int a)
        bindices2 = M.fromList . zip [0..] <$> bitems
        eindexes = lookupIndex <$> facts bindices2 <@> sel
    e <- currentValue (facts bsel)
    let
        -- eindexes2 = (\m-> catMaybes $ fmap (flip setLookup m) e)  <$> (S.fromList <$> rumors bitems)
        ev =  foldr1 (unionWith const) [rumors bsel,eindexes]
    bsel2 <- ui $ stepper e ev
    let
        _selectionMLB = tidings bsel2 ev
        _elementMLB   = list

    return $ TrivialWidget (_selectionMLB ) (_elementMLB)


sink0 :: ReadWriteAttrMIO UI b i o -> Behavior i -> UI b -> UI b
sink0 attr uiv ui =  do
  v <- currentValue uiv
  ui # set attr v # sink attr uiv

source :: String -> ReadWriteAttrMIO JSFunction  Element  b a ->UI Element ->  UI (Event a)
source change attr mel = do
  el <- mel
  domEventH change el (UI.get attr el )

sourceT :: String -> ReadWriteAttrMIO JSFunction  Element  b a -> a -> UI Element ->  UI (TrivialWidget a)
sourceT change attr ini mel = do
  el <- mel
  ev <-domEventH change el (UI.get attr el )
  bh <-ui $ stepper ini ev
  return (TrivialWidget (tidings bh ev) el)



oitems = mkWriteAttr $ \i x -> void $ do
    return x # set children [] #+ map (\i -> UI.option # i) i


infixl 4 <#>
(<#>) :: Behavior (a -> b) -> Tidings a -> Tidings b
b <#>  t = tidings ( b <*> facts t ) (b <@> rumors t)

fileChange :: Element -> UI (Event (Maybe String))
fileChange el = domEventAsync "change" el (UI.get readFileAttrFFI el)

selectionMultipleChange :: Element -> UI (Event [Int])
selectionMultipleChange el = domEventH "change" el (UI.get selectedMultipleFFI el)


readFileAttrFFI :: ReadWriteAttrMIO JSAsync Element () (Maybe String)
readFileAttrFFI = ReadWriteAttr (\g ->ffi "handleFileSelect(%1,%2,$(%3))" UI.async UI.event g) (\_ _ -> JSAsync emptyFunction)

jsTimeZone = wTimeZone <$> askWindow

selectedMultiple :: Attr Element [Int]
selectedMultiple = ffiAttrCall selectedMultipleFFI

selectedMultipleFFI
    :: ReadWriteAttrMIO JSFunction Element [Int] [Int]
selectedMultipleFFI = ffiAttr "getOpts($(%1))" "setOpts($(%2),%1)"



emptyUI = TrivialWidget (pure  Nothing) <$> UI.div

pruneTidings chw tds =   tidings chkBH chkAll
  where
    chkEvent = fmap Just $ filterJust $ (\b e -> if b then e else Nothing ) <$> facts chw <@> rumors tds
    chkBehaviour = fmap Just $ filterJust $ (\e b -> if b then e else Nothing ) <$>  facts tds <@> rumors chw
    chkAll = unionWith const chkEvent chkBehaviour
    chkBH = (\b e -> if b then e else Nothing ) <$> facts chw <*> facts tds



testDyn = return $ do
  list <- multiListBox (pure [1,2,3,4,5]) (pure $ [1])  (pure (line.show))
  b <- checkedWidget (pure True)
  out <- ui $ accumDiff (\i -> evalUI (getElement list) $ do
    UI.div # set text (show i) # sink UI.style (noneShow <$> facts (triding b)))  (fmap S.fromList  $ triding list)
  nest <- UI.div # sink children (F.toList <$> facts out)
  UI.div # set children [getElement list,getElement b,nest]

importUI f = do
    runFunction $ ffi "jQuery.ajaxSettings.cache = true"
    w <- askWindow
    addHead f
    runFunction $ ffi "jQuery.ajaxSettings.cache = false"
    flushCallBuffer

js , css :: String -> UI Element
css ref =  mkElement "link" # set UI.href ("static/"<> ref)# set UI.rel "stylesheet"
js ref =  mkElement "script" # set UI.type_ "text/javascript" # set (UI.boolAttr "defer") False # set (UI.boolAttr "async") False # set UI.src ("static/"<> ref)
jsRemote ref =  mkElement "script" # set UI.type_ "text/javascript" # set (UI.boolAttr "defer") False # set (UI.boolAttr "async") False # set UI.src ref



testWidget e = startGUI (defaultConfig { jsPort = Just 10000 , jsStatic = Just "static", jsCustomHTML = Just "index.html" })
        ( \w ->  do
              els <- e
              addBody [els]
              return ())(return 1) (\w -> (return ()))


flabel = UI.span # set UI.class_ (L.intercalate " " ["label","label-default"])
hlabel h = UI.span # set UI.class_ (L.intercalate " "$ ["label","label-default"] ++ h )

onEventFT
  :: Event a ->  (a -> UI b) -> UI  ()
onEventFT = onEvent


infixl 4 <$|>


(<$|>) = traverseUI

-- | Returns a new behavior that only notifies for new values.
calmB :: Eq a => Behavior a -> Dynamic (Behavior a)
calmB b = do
  (e, trigger) <- newEvent
  current <- currentValue b
  liftIO $ trigger current
  onChangeDyn b (liftIO . trigger)
  eCalm <- calmE e
  fmap (fromMaybe (error "calmB")) <$> stepper Nothing (Just <$> eCalm)

data Memory a = Empty | New a | Same a
updateMemory :: Eq a => a -> Memory a -> Memory a
updateMemory x Empty  = New x
updateMemory x (New  a) | a /= x = New x
updateMemory x (Same a) | a /= x = New x
updateMemory x _ = Same x
isNew :: Memory a -> Maybe a
isNew (New x) = Just x
isNew _ = Nothing

-- | Returns a new 'Event' that skips consecutive triggers with the same value.
calmE :: Eq a => Event a -> Dynamic (Event a)
calmE e =
  filterJust . fmap isNew <$> accumE Empty (updateMemory <$> e)


calmT :: Eq a => Tidings a -> Dynamic (Tidings a )
calmT t = do
  (e, trigger) <- newEvent
  current <- currentValue (facts t)
  liftIO $ trigger current
  onChangeDyn (facts t) (liftIO . trigger)
  eCalm <- calmE (rumors t)
  bh <- stepper current eCalm
  return $ tidings bh eCalm


traverseUI
  :: (a -> UI b)
     -> Tidings a
     -> UI (Tidings b)
traverseUI m inp = do
  w <- askWindow
  ui $ mapTEventDynInterrupt (runUI w . m ) inp

line n =   set  text n

accumDiffCounter
  :: (Show k ,Prelude.Ord k) =>
    (Int -> k -> Dynamic b)
     -> Tidings (S.Set k)
     -> Dynamic
          (Tidings (M.Map k b))
accumDiffCounter  f t = mdo
  ini <- currentValue (facts t)
  iniout <- liftIO$ mapM (\(ix,v)-> evalDynamic (f ix) v)$ zip [0..] $S.toList ini
  let (del,addpre) = diffAddRemove t
  add <- mapEvent (\((ix,_),v) -> mapM (\(ix,v)-> evalDynamic (f ix) v) $zip [ix..] (S.toList $ v) )  $(,)<$>facts bs <@>addpre
  del2 <- mapEvent (\((ix,fin),d) -> do
         let fins =  catMaybes $ fmap (flip M.lookup fin) d
         _ <- traverse sequence_ $ fmap snd fins
         return d)  ((,) <$> facts bs <@> (S.toList  <$> del ))
  let evadd = ((\s (acc,m) -> ( acc + length s,foldr (uncurry M.insert ) m s)) <$> add )
      evdel = ( (\s (acc,m) -> (acc,foldr (M.delete ) m s)) <$> del2 )
  let eva = unionWith (.) evdel evadd
  bs <- accumT  (S.size ini,M.fromList iniout)  eva
  registerDynamic (void $ join $ traverse sequence_ . fmap snd . F.toList  .snd <$> currentValue (facts bs))
  return (fmap (fmap fst ) $ fmap snd $ bs)


accumDiff
  :: (Show k ,Prelude.Ord k) =>
     (k -> Dynamic b)
     -> Tidings (S.Set k)
     -> Dynamic
          (Tidings (M.Map k b))
accumDiff  f t = mdo
  ini <- currentValue (facts t)
  iniout <- liftIO$ mapM (evalDynamic f)$ S.toList ini
  let (del,addpre) = diffAddRemove t
  add <- mapEvent (mapM (evalDynamic f). S.toList) addpre
  del2 <- mapEvent (\(fin,d) -> do
         let fins =  catMaybes $ fmap (flip M.lookup fin) d
         _ <- traverse sequence_ $ fmap snd fins
         return d)  ((,) <$> facts bs <@> (S.toList  <$> del ))
  let eva = unionWith (.) ( (\s m -> foldr (M.delete ) m s) <$> del2 ) ((\s m -> foldr (uncurry M.insert ) m s) <$> add )
  bs <- accumT  (M.fromList iniout)  eva
  registerDynamic (void $ join $ traverse sequence_ . fmap snd . F.toList  <$> currentValue (facts bs))
  return (fmap (fmap fst ) $ bs)

evalDynamic :: (k -> Dynamic b) -> k -> IO (k,(b,[IO ()]))
evalDynamic f l =  fmap (l,) . runDynamic $ f l

closeDynamic  m = do
  (i,v) <- runDynamic m
  sequence_ v
  return i

diffAddRemove :: (Show k,Ord k) => Tidings (S.Set k)  -> (Event (S.Set k) ,Event (S.Set k))
diffAddRemove l= (delete,add)
    where
      delete  = filterJust $ prune <$> evdell
      add =  filterJust $ prune <$> evadd
      diff i j = S.difference i  j
      evdiff = diffEventKeys (facts l ) (rumors l)
      evadd = flip diff <$> facts l <@> evdiff
      evdell =  diff <$> facts l <@> evdiff
      prune i = if S.null i  then Nothing else Just i
      diffEventKeys b ev = filterJust $ (\i j -> if  i ==  j then Nothing else Just j ) <$> b <@> ev

onFFI ff handler = do
    (e,h) <- ui $ newEvent
    obj <- ffiExport (void $ (runDynamic $ handler) >>= h . snd )
    runFunction $ ffi ff obj
    onEvent e (ui . registerDynamic . sequence_)


hoverTip elemD= do
  ho <- UI.hover elemD
  le <- UI.leave elemD
  return $ unionWith const (const True <$> ho) (const False <$> le )

hoverTip2 elemIn elemOut = do
  (hoev,h) <- ui newEvent
  ho <- UI.dblclick elemIn
  onEvent ho (\_ -> liftIO . h $ True )
  bh <- ui $ stepper False hoev
  traverseUI (\i ->
    if i
    then  do
      le <- UI.leave elemOut
      onEvent le (\_ -> liftIO . h $ False)
      return ()
    else return ()) (tidings bh hoev)
  return $ hoev


method s i = i >>= \e -> runFunctionDelayed e . ffi s $ e
