{-# LANGUAGE FlexibleContexts,TupleSections,ScopedTypeVariables,LambdaCase,RankNTypes,DeriveFunctor,RecordWildCards,NoMonomorphismRestriction,RecursiveDo #-}
module TP.Widgets where


import Control.Monad
import Data.Ord
import Reactive.Threepenny
import qualified Graphics.UI.Threepenny as UI
import Graphics.UI.Threepenny.Core hiding (delete)

import qualified Data.Map as M
import Data.Time.LocalTime
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


import Debug.Trace
import Utils

instance Widget (TrivialWidget  a) where
    getElement (TrivialWidget t e) = e

data TrivialWidget a =
    TrivialWidget { triding :: (Tidings a) , trielem ::  Element} deriving(Functor)



-- Generate a accum the behaviour and generate the ahead of promised event
accumT :: MonadIO m => a -> Event (a ->a) -> m (Tidings a)
accumT e ev = do
  b <- accumB e ev
  return $ tidings b (flip ($) <$> b <@> ev)


evalUI el f = getWindow el >>= flip runUI f

accumTds :: MonadIO m => Tidings a -> Event (a -> a) -> m (Tidings a)
accumTds e l = do
  ve <- currentValue (facts e)
  accumT ve $ concatenate <$> unions ([l,const <$> rumors e ])


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

updateTEvent :: MonadIO m =>  (a -> Maybe a) -> Tidings a -> Tidings a -> m (Tidings a)
updateTEvent validate ev b = do
 v <- currentValue (facts b)
 evi <- currentValue (facts ev)
 let nev = unionWith const (filterJust (validate <$> rumors ev)) (rumors b)
 nbev <- stepper (maybe evi id (validate v)) nev
 return  $tidings nbev nev


updateEvent :: MonadIO m =>  (a -> Maybe a) -> Event a -> Tidings a -> m (Tidings a)
updateEvent validate ev b = do
 v <- currentValue (facts b)
 let nev = unionWith const (filterJust (validate <$> ev)) (rumors b)
 nbev <- stepper v nev
 return  $tidings nbev nev


diffEvent b ev = filterJust $ (\i j -> if i == j then Nothing else Just j ) <$> b <@> ev
notdiffEvent b ev = filterJust $ (\i j -> if i /= j then Nothing else Just j ) <$> b <@> ev

addEvent :: (Eq a,MonadIO m) => Event a -> Tidings a -> m (Tidings a)
addEvent ev b = do
 v <- currentValue (facts b)
 let nev = unionWith const (rumors b) ev
 nbev <- stepper v (diffEvent (facts b) nev)
 return  $tidings nbev (diffEvent nbev nev)

mapUITEvent body f  = mapTEvent (\i -> evalUI body $ f i )

mapDynEvent f x = do
  t <- mapUITEvent (getElement x) f (triding x)
  sub <- UI.div # sink items (pure. element  <$> facts t )
  (e,h) <- liftIO $ newEvent
  onEvent (rumors t) (\x-> onEvent (rumors . triding $ x) (liftIOLater .  h) )
  v <- currentValue (facts t)
  i <- currentValue (facts (triding v))
  bh <- stepper i e
  return $ TrivialWidget (tidings bh e) sub


mapEvent :: MonadIO m => (a -> IO b) -> Event a -> m (Event b)
mapEvent f x = liftIO$ do
  (e,h) <- liftIO $ newEvent
  onEventIO x (\i -> void . forkIO $ (f i)  >>= h)
  return  e

mapT0Event i f x = fst <$> mapT0EventFin i f x

mapT0EventFin i f x = do
  (e,fin) <- mapEventFin f (rumors x)
  be <-  liftIO $ f i
  t <- stepper be e
  return $ (tidings t e,fin)

mapTEvent f x = fst <$> mapTEventFin f x

mapTEventFin f x = do
  i <- currentValue (facts x)
  mapT0EventFin i f x



-- Style show/hide
noneShow True = [("display","block")]
noneShow False = [("display","none")]

noneShowFlex True = [("display","inline-flex")]
noneShowFlex False = [("display","none")]

noneShowSpan True = [("display","inline")]
noneShowSpan False = [("display","none")]

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

buttonDivSetT :: (Ord b ,Eq a) => [a] -> Tidings (a -> b) -> Tidings (Maybe a) ->  (a -> UI Element ) -> (a -> UI Element  -> UI Element ) -> UI (TrivialWidget (Maybe a))
buttonDivSetT ks sort binit   el st = mdo
  buttons <- mapM (buttonString  )  ks
  dv <- UI.div # sink items ((\f -> fmap (\ (k,(v,_)) -> st k (element v) # sink UI.enabled (not . (Just k==) <$> bv)) . L.sortBy (flip $ comparing (f . fst))  $ buttons) <$>  facts sort )
  let evs = foldl (unionWith const) (filterJust $ rumors binit) (snd .snd <$> buttons)
  v <- currentValue (facts binit)
  bv <- stepper  v  (Just <$> evs)
  return (TrivialWidget (tidings bv (Just <$> evs)) dv)
    where
      buttonString   k = do
        b <- el k
        let ev = pure k <@ UI.click  b
        return (k,(b,ev))


buttonDivSet :: Eq a => [a] -> Tidings (Maybe a)  ->  (a -> UI Element ) -> UI (TrivialWidget a)
buttonDivSet ks binit   el = mdo
  buttons <- mapM (buttonString  bv ) ks
  dv <- UI.div # set children (fst <$> buttons)
  let evs = foldl (unionWith const) (filterJust $ rumors binit) (snd <$> buttons)
  v <- currentValue (facts binit)
  bv <- stepper (maybe (justError "no head" $ safeHead ks) id v) evs
  return (TrivialWidget (tidings bv evs) dv)
    where
      buttonString   bv k = do
        b <- el k # sink UI.enabled (not . (k==) <$> bv)
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
  bh <- stepper v (diffEvent  b e)
  dv <- UI.span # set children [i] # set UI.style [("margin","2px")]
  return $ TrivialWidget  (tidings bh (diffEvent bh e)) dv

checkedWidgetM :: Tidings (Maybe Bool) -> UI (TrivialWidget (Maybe Bool))
checkedWidgetM init = do
  i <- UI.input # set UI.type_ "checkbox" # sink UI.checked (maybe False id <$> facts init)
  let e = unionWith const (rumors init) (Just <$>  UI.checkedChange i)
  v <- currentValue (facts init)
  b <- stepper v e
  dv <- UI.span # set children [i] # set UI.style [("margin","2px")]
  return $ TrivialWidget  (tidings b e) dv


wrapListBox l p f q = do
  o <- listBox l p f q
  return $ TrivialWidget (triding o ) (getElement o)

optionalListBox' l o  s = mdo
  ol <- UI.listBox ((Nothing:) <$>  fmap (fmap Just) l) (fmap Just <$> st) (maybe UI.div <$> s)
  let sel = unionWith const (rumors $ fmap join $ UI.userSelection ol) (rumors o)
  v <- currentValue ( facts o)
  st <- stepper v sel
  return $ TrivialWidget (tidings st sel ) (getElement ol)


optionalListBox l o f s = do
  o <- listBox ((Nothing:) <$>  fmap (fmap Just) l) (fmap Just <$> o) f s
  return $TrivialWidget  (fmap join $ triding o)(getElement o)

interval'' i j = Interval.interval (ER.Finite i ,True) (ER.Finite j , True)


read1 (EventData (Just s:_)) = read s

onkey :: Element -> (Int -> Maybe Int ) -> Event String
onkey el f = unsafeMapUI el (const $ UI.get value el) (filterJust $ f . read1 <$> domEvent "keydown" el)

onEnter el = onkey el (\case {13-> Just 13; i -> Nothing})
onEsc el = onkey el (\case {27 -> Just 27; i -> Nothing})


testPointInRange ui = do
  startGUI defaultConfig {tpPort = Just 8000} (\w -> do
                      e1 <- ui
                      getBody w #+ [element e1]
                      return () )

unsafeMapUI el f = unsafeMapIO (\a -> getWindow el >>= \w -> runUI w (f a))

-- paint e b = element e # sink UI.style (greenRed . isJust <$> b)
paintEdit e b i  = element e # sink0 UI.style ((\ m n -> pure . ("background-color",) $ cond  m n ) <$> b <*> i )
  where cond i j
          | isJust i  && isNothing j  = "green"
          | isNothing i  && isNothing j = "red"
          | isNothing i && isJust j  = "purple"
          | i /= j = "yellow"
          -- | i /= j = trace ((concat $ fmap differ $   zip  si sj) <> L.drop (L.length sj) si  <> L.drop (L.length si) sj ) "yellow"
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

selectItem = mdo
  pan <- UI.div # sink text (fromMaybe "NO VALUE " <$>  facts (triding v))
  sel <-  UI.select # set UI.size "3"
  bh <- stepper False (unionWith const (const True <$> UI.click pan) (const False <$> UI.selectionChange sel ))
  element sel # sink UI.style (noneShow <$> bh)
  element pan # sink UI.style (noneShow . not <$> bh)
  v <- listBoxEl sel (pure ["A","B","C"]) (tidings lb  never) (pure id) (pure(\v -> set UI.text (show v)))
  lb <- stepper (Just "A") (rumors (triding  v))
  UI.div # set children [pan,sel]

setLookup x s = if S.member x s then Just x else Nothing
listBoxEl :: forall a. Ord a
    => Element
    -> Tidings [a]               -- ^ list of items
    -> Tidings (Maybe a)         -- ^ selected item
    -> Tidings ([a] -> [a])      -- ^ view list to list transform (filter,sort)
    -> Tidings (a -> UI Element -> UI Element) -- ^ display for an item
    -> UI (TrivialWidget (Maybe a))
listBoxEl list bitems bsel bfilter bdisplay = do
    let bindices :: Tidings [a]
        bindices =  bfilter <*> bitems
    -- animate output items
    element list # sink oitems (facts $ map <$> bdisplay <*> bitems )

    -- animate output selection
    let
        bindex   = lookupIndex <$> bitems <*> bsel
        lookupIndex indices Nothing    = Nothing
        lookupIndex indices (Just sel) = L.findIndex (== sel)  indices

    element list # sink UI.selection (facts bindex)


    -- changing the display won't change the current selection
    -- eDisplay <- changes display
    -- sink listBox [ selection :== stepper (-1) $ bSelection <@ eDisplay ]

    -- user selection
    let
        eindexes = (\l i -> join (fmap (\is -> either (const Nothing) Just (at_ l  is)) i)) <$> facts bitems <@> UI.selectionChange list
    let
        _selectionLB = tidings (facts bsel) eindexes
        _elementLB   = list

    return $ TrivialWidget _selectionLB _elementLB


-- | Create a 'ListBox'.
listBox :: forall a. Ord a
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


infixl 4 <#>
(<#>) :: Behavior (a -> b) -> Tidings a -> Tidings b
b <#>  t = tidings ( b <*> facts t ) (b <@> rumors t)

fileChange :: Element -> Event (Maybe String)
fileChange el = unsafeMapUI el (const $ UI.get readFileAttr el) (UI.valueChange el)

selectionMultipleChange :: Element -> Event [Int]
selectionMultipleChange el = unsafeMapUI el (const $ UI.get selectedMultiple el) (UI.click el)

readFileAttr :: ReadAttr Element (Maybe String)
readFileAttr = mkReadAttr get
  where
    get   el = fmap  from  $  callFunction $ ffi "readFileInput($(%1))" el
    from s = case JSON.fromJSON s of
                  JSON.Success x -> M.lookup ("filevalue" ::String) x
                  i -> Nothing -- errorWithStackTrace (show i)


jsTimeZone :: UI TimeZone
jsTimeZone  = do
  fmap ((\ i -> TimeZone (negate i) False "") .from )$ callFunction $ ffi "new Date().getTimezoneOffset()"
  where
    from s = let JSON.Success x =JSON.fromJSON s in x


selectedMultiple :: Attr Element [Int]
selectedMultiple = mkReadWriteAttr get set
  where
    get   el = fmap from $ callFunction $ ffi "getOpts($(%1))" el
    set v el = runFunction $ ffi "setOpts($(%1),%2)" el (JSON.toJSON  v)
    from s = let JSON.Success x =JSON.fromJSON s in x


mousewheel :: Element -> Event Int
mousewheel = fmap ((\i -> if i > 0 then 1 else -1) . read1 ) . domEvent "wheel"

sink0 attr uiv ui =  do
  v <- currentValue uiv
  ui # set attr v # sink attr uiv


emptyUI = TrivialWidget (pure Nothing) <$> UI.div

pruneTidings chw tds =   tidings chkBH chkAll
  where
    chkEvent = fmap Just $ filterJust $ (\b e -> if b then e else Nothing ) <$> facts chw <@> rumors tds
    chkBehaviour = fmap Just $ filterJust $ (\e b -> if b then e else Nothing ) <$>  facts tds <@> rumors chw
    chkAll = unionWith const chkEvent chkBehaviour
    chkBH = (\b e -> if b then e else Nothing ) <$> facts chw <*> facts tds

strAttr :: String -> WriteAttr Element String
strAttr name = mkWriteAttr (set' (attr name))

testWidget e = startGUI (defaultConfig { tpPort = Just 10000 , tpStatic = Just "static", tpCustomHTML = Just "index.html" })  ( \w ->  do
              els <- e
              getBody w #+ [els]
              return ()) (\w -> (return ()))


flabel = UI.span # set UI.class_ (L.intercalate " " ["label","label-default"])

line n =   set  text n
