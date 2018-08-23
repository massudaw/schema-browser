{-# LANGUAGE BangPatterns,FlexibleContexts,TupleSections,ScopedTypeVariables,RecordWildCards,RecursiveDo #-}
module TP.Widgets where

import PStream
import Control.Monad.Writer hiding((<>))
import Debug.Trace
import Data.Ord
import qualified Types.Patch as P
import Reactive.Threepenny hiding (apply)
import qualified Graphics.UI.Threepenny as UI
import Types.Patch
import Graphics.UI.Threepenny.Core hiding (delete,apply)
import Graphics.UI.Threepenny.Internal (wTimeZone)
import qualified Data.Map as M
import qualified Data.Foldable as F
import qualified Data.Set as S
import Data.Map (Map)
import Data.Semigroup hiding (diff)
import Data.Interval (Interval(..))
import qualified Data.ExtendedReal as ER
import qualified Data.Interval as Interval
import qualified Data.List as L
import Data.Maybe
import Control.Concurrent
import Utils

class WidgetLayout a where
  getLayout :: a  -> Tidings (Int,Int)

class WidgetValue t  where
  triding ::  t a  -> Tidings a

data LayoutWidget a =
  LayoutWidget  (Tidings a) Element (Tidings (Int,Int))

instance WidgetLayout (LayoutWidget a) where
  getLayout (LayoutWidget _ _ l ) = l

instance WidgetValue LayoutWidget  where
  triding (LayoutWidget t _ _ ) = t

instance Widget (LayoutWidget a ) where
  getElement (LayoutWidget _ e _ ) = e

data TrivialWidget a =
  TrivialWidget  (Tidings a) Element

instance WidgetValue TrivialWidget where
  triding (TrivialWidget t _  ) = t

instance Widget (TrivialWidget a) where
  getElement (TrivialWidget t e ) = e

instance Semigroup a => Semigroup (Event a) where
  i <> j = unionWith (<>) i j

instance Semigroup a => Monoid (Event a) where
  mempty = never
  mappend i j =  i <>  j



instance Functor LayoutWidget where
  fmap f  (LayoutWidget e j  l) = LayoutWidget (fmap f e) j l

instance Functor TrivialWidget where
    fmap = trmap

{-# NOINLINE[1] trmap #-}
trmap f (TrivialWidget e j  ) = TrivialWidget (fmap f e) j

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
  ui $ stepperT c ev

liftEvent :: Event (Maybe a) -> (MVar (Maybe a) -> IO  void) -> Dynamic ()
liftEvent e h = do
  ivar <- liftIO$ newEmptyMVar
  register e (void .  maybe (return ()) ( putMVar ivar .Just )  )
  return ()

cutEvent :: Event b -> Tidings a -> Dynamic (Tidings a)
cutEvent ev b = do
 v <- currentValue (facts b)
 let nev = facts b <@ ev
 stepperT v nev

updateTEvent :: (a -> Maybe a) -> Tidings a -> Tidings a -> Dynamic (Tidings a)
updateTEvent validate ev b = do
 v <- currentValue (facts b)
 evi <- currentValue (facts ev)
 let nev = unionWith const (filterJust (validate <$> rumors ev)) (rumors b)
 stepperT (maybe evi id (validate v)) nev


updateEvent :: (a -> Maybe a) -> Event a -> Tidings a -> Dynamic (Tidings a)
updateEvent validate ev b = do
 v <- currentValue (facts b)
 let nev = unionWith const (filterJust (validate <$> ev)) (rumors b)
 stepperT v nev


diffTidings f = tidings (facts f) (diffEvent (facts f ) (rumors f))
diffEvent b ev = filterJust $ (\i j -> if i == j then Nothing else Just j ) <$> b <@> ev
notdiffEvent b ev = filterJust $ (\i j -> if i /= j then Nothing else Just j ) <$> b <@> ev

addEvent :: Event a -> Tidings a -> Dynamic (Tidings a)
addEvent ev b = do
 v <- currentValue (facts b)
 let nev = unionWith const (rumors b) ev
 stepperT v nev





mapTEventDyn :: (a -> Dynamic b) -> Tidings a -> Dynamic (Tidings b)
mapTEventDyn f x = mapTidingsDyn f x

cacheTidings :: Tidings a -> Dynamic (Tidings a)
-- cacheTidings  t = return t
cacheTidings  t = do
  (e,h) <- newEvent
  onEventIO (rumors t) h
  v <- currentValue (facts t)
  stepperT v e


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

tabbedChk :: [(String,(TrivialWidget Bool,Element))] -> UI Element
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
  rangeInit <- listBox bp (const <$> pure Nothing <*> fkbox) (pure (set text . show ))
  rangeEnd <- listBox bp (const <$> pure Nothing <*> fkbox) (pure (UI.set text . show ))
  range <- UI.div # set children (getElement <$> [rangeInit,rangeEnd])
  return $ RangeBox (  liftA2 interval'' <$> (triding rangeInit) <*> (triding rangeEnd)) range

instance Widget (RangeBox a) where
  getElement = _rangeElement

checkDivSetTGen'
  :: (Show a ,Ord b ,Ord a,Eq a)
  => Tidings [a]
  -> Tidings (a -> b)
  -> Tidings (S.Set a)
  -> (a -> UI (Element,Event Bool))
  -> Tidings (a -> Element  -> UI Element)
  -> UI (TrivialWidget (S.Set a))
checkDivSetTGen' ks sort binit   el st = do
  (ce,ch) <- ui newEvent
  w <- askWindow
  buttonsT <- ui $ accumDiff (\b -> runUI w $ do
    (e,ev) <-  el b
    let evs =  (\ab -> if not ab then S.delete b else S.insert b)  <$> ev
    ui$ onEventIO evs ch
    element e # sinkDiff UI.checked (S.member b <$> binit)
    UI.div # sink items ((\f -> pure <$> f b e) <$> facts st)
    ) (S.fromList <$> ks)
  vini <- currentValue (facts binit)
  let evs = unionWith (.) (const <$> rumors binit) ce
  bv <- ui $ accumT vini  evs
  -- Place sorted Itens
  let sortButtons nbuttons f sel =  snd <$> L.sortBy (flip $ comparing ((\i -> (L.elem i sel, f  i) ). fst)) nbuttons
      buttonsStyle = M.toList <$> buttonsT
  dv <- UI.div # sink children (facts $ sortButtons <$>  buttonsStyle <*> sort <*> bv)
  return (TrivialWidget bv dv )


checkDivSetTGen :: (Ord b ,Ord a,Eq a)
      => [a]
      -> Tidings (a -> b)
      -> Tidings (S.Set a)
      -> (a -> UI (Element,Event Bool))
      -> Tidings (a -> Element  -> Maybe (UI Element))
      -> UI (TrivialWidget (S.Set a))
checkDivSetTGen ks sort binit   el st = do
  buttons <- mapM (\k -> (k,) <$> el k) ks
  vini <- currentValue (facts binit)
  let
    evs = foldr (unionWith (.)) (const <$> rumors binit) $ (\(i,(_,ev)) -> (\ab -> if not ab then S.delete i else S.insert i)  <$> ev) <$> buttons
  bv <- ui $ accumT vini  evs
  -- Place sorted Itens
  dv <- UI.div
  onChanges (facts st) $ (\sti -> do
    nbuttons <- mapM fromJust . filter isJust . fmap (\(k,(v,_)) -> fmap (k,) <$> sti k v) $  buttons
    mapM (\(k,e) -> element (fst e) # sinkDiff UI.checked (S.member k <$> bv)) buttons
    let sortButtons sti f sel =  fmap snd $ L.sortBy (flip $ comparing (\i -> (L.elem (fst i) sel,). f . fst $ i )) $nbuttons
    element dv # sink children (facts $ sortButtons <$>  pure nbuttons <*> sort <*> bv))
  -- Sink check state to elems
  return (TrivialWidget bv dv)


buttonDivSetT :: (Ord b ,Eq a) => [a] -> Tidings (a -> b) -> Tidings (Maybe a) ->  (a -> UI Element ) -> (a -> UI Element  -> UI Element ) -> UI (TrivialWidget (Maybe a))
buttonDivSetT ks sort binit   el st = mdo
  buttons <- mapM buttonString ks
  dv <- UI.div # sink items ((\f -> mapM (\ (k,(v,_)) -> st k (element v) # sink UI.enabled (not . (Just k==) <$> bv)) . L.sortBy (flip $ comparing (f . fst))  $ buttons) <$>  facts sort )
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



items :: WriteAttr Element (UI [Element])
items = mkWriteAttr $ \i x -> void $ do
  c <- i
  return x # set children c

-- Boolean button
buttonClick :: Tidings Bool -> Behavior (Bool -> UI Element) -> UI (TrivialWidget Bool)
buttonClick init style = mdo
  i <- UI.button # sink items (fmap (fmap pure) $ ($) <$> style  <*> facts t)
  ev <- UI.click i
  let e = unionWith (.) (const <$> rumors init) (not <$ ev)
  v <- currentValue (facts init)
  t <- ui $ accumT v e
  return $ TrivialWidget  t i
buttonAction :: Tidings () -> UI (TrivialWidget ())
buttonAction init = do
  i <- UI.button # set UI.text "Submit"
  ev <- UI.click i
  let e = unionWith const (rumors init) ev
  v <- currentValue (facts init)
  t <- ui $ stepperT v e
  return $ TrivialWidget  t i


wrapListBox l p  q = do
  o <- listBox l p  q
  return $ TrivialWidget (triding o ) (getElement o)

optionalListBox' l o  s = mdo
  ol <- UI.listBox ((Nothing:) <$>  fmap (fmap Just) l) (fmap Just <$> st) (maybe UI.div <$> s)
  let sel = unionWith const (rumors $ fmap join $ UI.userSelection ol) (rumors o)
  v <- currentValue ( facts o)
  st <- ui $ stepper v sel
  return $ TrivialWidget (tidings st sel ) (getElement ol)


optionalListBox l o  s = do
  o <- listBox ((Nothing:) <$>  fmap (fmap Just) l) (fmap Just <$> o) s
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
                       )


-- paint e b = element e # sink UI.style (greenRed . isJust <$> b)
paintEdit e b i  = element e # sinkDiff UI.style ((\ m n -> pure . ("background-color",) $ cond  m n ) <$> b <*> i )
  where cond i j
          | isJust i  && isNothing j  = "green"
          | isNothing i  && isNothing j = "red"
          | isNothing i && isJust j  = "purple"
          | i /= j = "yellow"
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
listBoxEl :: (Eq a , Show a) => Element
    -> Tidings [a]               -- ^ list of items
    -> Tidings (Maybe a)         -- ^ selected item
    -> Tidings (a -> UI Element -> UI Element) -- ^ display for an item
    -> UI (TrivialWidget (Maybe a))

listBoxEl = listBoxElEq (==)

listBoxElEq ::
    forall a . Show a => (a -> a -> Bool)
    ->  Element
    -> Tidings [a]               -- ^ list of items
    -> Tidings (Maybe a)         -- ^ selected item
    -> Tidings (a -> UI Element -> UI Element) -- ^ display for an item
    -> UI (TrivialWidget (Maybe a))
listBoxElEq eq list bitems bsel bdisplay = do
    let bindices :: Tidings [a]
        bindices =  bitems
    -- animate output items
    let
        bindex   = lookupIndex <$> facts bitems <#> bsel
        lookupIndex indices Nothing    = Nothing
        lookupIndex indices (Just sel) = L.findIndex (eq sel)  indices
        els = liftA2 (\j -> mapM (\ix ->  UI.option # j ix )) bdisplay bitems
    element list # sink items (facts els)

    -- animate output selection

    element list # sinkDiff UI.selection bindex


    -- changing the display won't change the current selection
    -- eDisplay <- changes display
    -- sink listBox [ selection :== stepper (-1) $ bSelection <@ eDisplay ]

    -- user selection
    selEv <- fmap Just <$> UI.selectionChange list
    selBh <- ui $ stepper  Nothing selEv
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
    -> Tidings (a -> UI Element -> UI Element) -- ^ display for an item
    -> UI (TrivialWidget (Maybe a))
listBox bitems bsel bdisplay = do
    list <- UI.select
    listBoxEl  list bitems bsel bdisplay

at_ :: [a] -> Int -> Either String a
at_ xs o | o < 0 = Left $ "index must not be negative, index=" ++ show o
         | otherwise = f o xs
    where f 0 (x:xs) = Right x
          f i (x:xs) = f (i-1) xs
          f i [] = Left $ "index too large, index=" ++ show o ++ ", length=" ++ show (o-i)

-- | Create a 'ListBox'.
multiListBox a b c  = do
  el <- UI.select
  multiListBoxEl  el a b c

multiListBoxEl :: forall a.( Ord a,Show a)
    => Element
    -> Tidings [a]               -- ^ list of items
    -> Tidings [a]         -- ^ selected item
    -> Tidings (a -> UI Element -> UI Element) -- ^ display for an item
    -> UI (TrivialWidget [a])
multiListBoxEl el bitems pbsel bdisplay = do
    bsel <- ui $ cacheTidings pbsel
    _elementMLB <- element el # set UI.multiple True

    -- animate output items

    let bindices :: Tidings (M.Map a Int)
        bindices = (M.fromList . flip zip [0..]) <$> bitems
        bindex   = lookupIndex <$> bindices <*> bsel
        lookupIndex indices sel = catMaybes $ (flip M.lookup indices) <$> sel

        els = liftA2 (\i j -> mapM (\ix ->  UI.option # j ix ) i) bitems bdisplay
    element _elementMLB # sink items (facts els )

    -- animate output selection


    element _elementMLB # sinkDiff selectedMultiple bindex

    -- changing the display won't change the current selection
    -- eDisplay <- changes display
    -- sink listBox [ selection :== stepper (-1) $ bSelection <@ eDisplay ]

    -- user selection
    sel <- selectionMultipleChange _elementMLB
    let bindices2 :: Tidings (M.Map Int a)
        bindices2 = M.fromList . zip [0..] <$> bitems
        eindexes = lookupIndex <$> facts bindices2 <@> sel
    e <- currentValue (facts bsel)
    _selectionMLB <- ui $ stepperT e eindexes

    return $ TrivialWidget _selectionMLB _elementMLB


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
  t <-ui $ stepperT ini ev
  return (TrivialWidget t el)



oitems = mkWriteAttr $ \i x -> void $ do
    return x # set children [] #+ map (\i -> UI.option # i) i


infixl 4 <#>
(<#>) :: Behavior (a -> b) -> Tidings a -> Tidings b
b <#>  t = tidings ( b <*> facts t ) (b <@> rumors t)

(<#) :: Behavior b  -> Tidings a -> Tidings b
b <#  t = tidings  b  (b <@ rumors t)
fileChange :: Element -> UI (Event (Maybe String))
fileChange el = domEventAsync "change" el (\call ->ffi "handleFileSelect(%1,%2,$(%3))" call UI.event el)

selectionMultipleChange :: Element -> UI (Event [Int])
selectionMultipleChange el = domEventH "change" el (UI.get selectedMultipleFFI el)



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




importUI f = do
    runFunction $ ffi "jQuery.ajaxSettings.cache = true"
    w <- askWindow
    addHead f
    runFunction $ ffi "jQuery.ajaxSettings.cache = false"
    flushCallBuffer

js , css :: String -> UI Element
css ref =  mkElement "link" # set UI.href ("/static/"<> ref)# set UI.rel "stylesheet"
js ref =  mkElement "script" # set UI.type_ "text/javascript" # set (UI.boolAttr "defer") False # set (UI.boolAttr "async") False # set UI.src ("/static/"<> ref)
jsRemote ref =  mkElement "script" # set UI.type_ "text/javascript" # set (UI.boolAttr "defer") False # set (UI.boolAttr "async") False # set UI.src ref

testWidget e = startGUI (defaultConfig { jsPort = Just 10000 , jsStatic = Just "static", jsCustomHTML = Just "index.html" })
        (\w ->  do
              els <- e
              addBody [els]
              return ())(return 1)

flabel = UI.span # set UI.class_ (L.intercalate " " ["label","label-default"])
hlabel h = UI.span # set UI.class_ (L.intercalate " "$ ["label","label-default"] ++ h )

infixl 4 <$|>

(<$|>) = traverseUI


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
calmE :: Eq a => Memory a  -> Event a -> Dynamic (Event a)
calmE ini e =
  filterJust . fmap isNew <$> accumE ini (updateMemory <$> e)

calmD :: (Show a,Show (Index a),Patch a )=> Maybe a  -> Event (Maybe a) -> Dynamic (Event (Maybe a))
calmD ini e =
  filterJust . fmap isDiff <$> accumE (ini ,Just(patch ini)) ((\ i (j,_) -> (i , diff j i )) <$> e)
    where
      -- isDiff (_,i) | traceShow i False = undefined
      isDiff (i,Nothing) = Just i
      isDiff (i,Just Keep ) = Nothing
      isDiff (i,_) = Just i


calmDiff :: (Show a,Show (Index a),Patch a )=> Tidings (Maybe a) -> Dynamic (Tidings (Maybe a) )
calmDiff t = do
  current <- currentValue (facts t)
  eCalm <- calmD current (rumors t)
  stepperT current eCalm


calmT :: Eq a => Tidings a -> Dynamic (Tidings a )
calmT t = do
  current <- currentValue (facts t)
  eCalm <- calmE (New current) (rumors t)
  stepperT current eCalm

switchManyUI
  :: (Ord a, Show a) =>
     Tidings a
     -> Map a (UI (TrivialWidget a1))
     -> UI (TrivialWidget a1)
switchManyUI  bool map = do
  (evp,h) <- ui newEvent
  let
    fun x = do
      case M.lookup x map of
        Just i -> do
          el <- i
          liftIOLater $ do liftIO . h =<< currentValue (facts (triding el))
          ui $ onEventIO (rumors (triding el)) h
          return el
        Nothing -> error ("no ix " ++ (show x))

  els <- traverseUI fun bool
  currentEl <- currentValue (facts els)
  currentResult <- currentValue (facts $ triding currentEl)
  out <- UI.div # sink root (getElement <$> facts els)
  t <- ui $ stepperT currentResult evp
  return (TrivialWidget t out)


switchManyLayout
  :: (Ord a, Show a) =>
     Tidings a
     -> Map a (UI (LayoutWidget a1))
     -> UI (LayoutWidget a1)
switchManyLayout  bool map = do
  (evp,h) <- ui newEvent
  (levp,hl) <- ui newEvent
  let
    fun x = do
      case M.lookup x map of
        Just i -> do
          el <- i
          liftIO . h =<< currentValue (facts (triding el))
          ui $ onEventIO (rumors (triding el)) h
          liftIO . hl =<< currentValue (facts (getLayout el))
          ui $ onEventIO (rumors (getLayout el)) hl
          return el
        Nothing -> error ("no ix " ++ (show x))

  els <- traverseUI fun bool
  currentEl <- currentValue (facts els)
  currentLayout <- currentValue (facts $ getLayout currentEl)
  currentResult <- currentValue (facts $ triding currentEl)
  out <- UI.div # sink root (getElement <$> facts els)
  t <- ui $ stepperT currentResult evp
  l <- ui $ stepperT currentLayout levp
  return (LayoutWidget t out l)



switchUILayout
  :: Tidings a1
     -> UI Element
     -> Tidings Bool
     -> UI (LayoutWidget a1)
     -> UI (LayoutWidget a1)
switchUILayout  t def bool next  = switchManyLayout  bool (M.fromList [(True,next),(False , (\i -> LayoutWidget t i (pure (0,0))) <$> def )])




switchUI
  :: Tidings a1
     -> UI Element
     -> Tidings Bool
     -> UI (TrivialWidget a1)
     -> UI (TrivialWidget a1)
switchUI  t def bool next  = switchManyUI  bool (M.fromList [(True,next),(False , TrivialWidget t <$> def )])

traverseUIInt
  :: (a -> UI b)
     -> Tidings a
     -> UI (Tidings b)
traverseUIInt m inp = do
  w <- askWindow
  ui $ mapTidingsDynInterrupt (runUI w . m) inp



traverseUI
  :: (a -> UI b)
     -> Tidings a
     -> UI (Tidings b)
traverseUI m inp = do
  w <- askWindow
  ui $ mapTidingsDyn (runUI w . m) inp

line n =   set  text n

once i = do
  return $ pure i

accumDiffCounter :: Ord k =>
    (Int -> k -> Dynamic b)
     -> Tidings (S.Set k)
     -> Dynamic
          (Tidings (M.Map k b))

accumDiffCounter = accumDiffCounterIni 0

accumDiffCounterIni
  :: Ord k =>
    Int -> (Int -> k -> Dynamic b)
     -> Tidings (S.Set k)
     -> Dynamic
          (Tidings (M.Map k b))
accumDiffCounterIni  iniIx f t = mdo
  ini <- currentValue (facts t)
  iniout <- liftIO $ mapM (\(ix,v)-> evalDynamic (f ix) v)$ zip [iniIx..] $S.toList ini
  let diffEvent = diffAddRemove t
      evadd = (\s (acc,m) -> (acc + length s,foldr (uncurry M.insert ) m s))
      evdel = (\s (acc,m) -> (acc,foldr M.delete  m s))
      execFinalizers fins = traverse sequence_ $ fmap snd fins
  eva <- mapEventDynInterrupt (\((ix,!fin),(add,del)) -> liftIO $ do
    let fins =  catMaybes $ fmap (flip M.lookup fin) (S.toList del)
    execFinalizers fins
    out <- mapM (\(ix,v)-> evalDynamic (f ix) v) $zip [ix..] (S.toList add)
    return (evdel del . evadd out)
     )  $(,)<$>facts bs <@> diffEvent
  bs <- accumT  (iniIx + S.size ini, M.fromList iniout)  eva
  registerDynamic (void $ join $ execFinalizers . F.toList  .snd <$> currentValue (facts bs))
  return (fmap fst . snd <$> bs)

accumDiffMapCounter :: Ord k =>
     (Int -> (k,b) -> Dynamic c)
     -> Tidings (M.Map k b)
     -> Dynamic
          (Tidings (M.Map k c))

accumDiffMap f = accumDiffMapCounterIni 0 (const f)

accumDiffMapCounter = accumDiffMapCounterIni 0

accumDiffMapCounterIni
  :: Ord k =>
    Int
     -> (Int -> (k,b) -> Dynamic c)
     -> Tidings (M.Map k b)
     -> Dynamic
          (Tidings (M.Map k c))
accumDiffMapCounterIni iniIx f t = mdo
  ini <- currentValue (facts t)
  iniout <- liftIO $ mapM (\(ix,v)-> evalDynamicMap (f ix) v)$ zip [iniIx..] $M.toList ini
  let diffEvent = diffAddRemoveMap t
      evadd = (\s (acc,m) -> (acc + length s,foldr (uncurry M.insert ) m s))
      evdel = (\s (acc,m) -> (acc,foldr M.delete  m s))
      execFinalizers fins = traverse sequence_ $ fmap snd fins
  eva <- mapEventDynInterrupt (\((ix,!fin),(add,del)) -> liftIO $ do
    let fins =  catMaybes $ fmap (flip M.lookup fin) (M.keys del)
    execFinalizers fins
    out <- mapM (\(ix,v)-> evalDynamicMap (f ix) v) $zip [ix..] (M.toList add)
    return (evdel (M.keys del). evadd out)
     )  $(,)<$>facts bs <@> diffEvent
  bs <- accumT  (iniIx + M.size ini,M.fromList iniout)  eva
  registerDynamic (void $ join $ execFinalizers . F.toList  .snd <$> currentValue (facts bs))
  return (fmap fst . snd <$> bs)



accumDiff
  :: Ord k =>
     (k -> Dynamic b)
     -> Tidings (S.Set k)
     -> Dynamic
          (Tidings (M.Map k b))
accumDiff f = accumDiffCounter (const f)

evalDynamicMap :: ((k,a) -> Dynamic b) -> (k,a) -> IO (k,(b,[IO ()]))
evalDynamicMap  f l =  fmap (fst l,) . runDynamic $ f l

evalDynamic :: (k -> Dynamic b) -> k -> IO (k,(b,[IO ()]))
evalDynamic f l =  fmap (l,) . runDynamic $ f l

diffAddRemoveMap :: Ord k => Tidings (M.Map k b)  -> Event (M.Map k b,M.Map k b)
diffAddRemoveMap l= diff <$> facts l <@> rumors l
  where
    diff j i = (M.difference i  j,M.difference j i)

diffAddRemove :: Ord k => Tidings (S.Set k)  -> Event (S.Set k,S.Set k)
diffAddRemove l= diff <$> facts l <@> rumors l
  where
    diff j i = (S.difference i  j,S.difference j i)

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
  ui $ onEventIO ho (\_ -> h $ True )
  bh <- ui $ stepper False hoev
  traverseUI (\i ->
    if i
    then  do
      le <- UI.leave elemOut
      ui $ onEventIO le (\_ -> h $ False)
      return ()
    else return ()) (tidings bh hoev)
  return $ hoev

joinT t = do
  (e,h) <- newEvent
  init <- currentValue (facts t)
  el <- currentValue (facts init)
  mapTEventDyn  (mapTEventDyn (liftIO. h)) t
  b <- stepper el e
  return (tidings b e)


method s i = i >>= \e -> runFunctionDelayed e . ffi s $ e
