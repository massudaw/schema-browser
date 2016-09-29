{-# LANGUAGE FlexibleContexts,TupleSections,ScopedTypeVariables,LambdaCase,RankNTypes,DeriveFunctor,RecordWildCards,NoMonomorphismRestriction,RecursiveDo #-}
module TP.Widgets where


import GHC.Stack
import Control.Concurrent.Async
import Control.Monad.Writer
import Data.Tuple(swap)
import qualified Control.Monad.Trans.Writer as Writer
import Control.Monad
import Data.Ord
import Reactive.Threepenny
import qualified Graphics.UI.Threepenny as UI
import Graphics.UI.Threepenny.Core hiding (delete)

import qualified Data.Map as M
import qualified Data.Foldable as F
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


evalUI el f = liftIO (getWindow el) >>= \w ->  runUI w f

evalDyn el f = getWindow el >>= \w -> fmap fst $ runDynamic $ runUI w f

accumTds :: MonadIO m => Tidings a -> Event (a -> a) -> m (Tidings a)
accumTds e l = do
  ve <- currentValue (facts e)
  accumT ve $ concatenate <$> unions ([l,const <$> rumors e ])


accumTs :: MonadIO m => a -> [Event (a -> a)] -> m (Tidings a)
accumTs e = accumT e . foldr1 (unionWith (.))


adEvent :: Event a -> Tidings a -> UI (Tidings a)
adEvent ne t = do
  c <- currentValue (facts t)
  let ev = unionWith const (rumors t) ne
  nb <- stepper c ev
  return $ tidings nb ev



liftEvent :: Event (Maybe a) -> (MVar (Maybe a) -> IO  void) -> Dynamic ()
liftEvent e h = do
  ivar <- liftIO$ newEmptyMVar
  register e (void .  maybe (return ()) ( putMVar ivar .Just )  )
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



mapEventFin f = fmap (fmap fst).ui . mapEventDyn (liftIO . f)

mapEvent :: (a -> IO b) -> Event a -> Dynamic (Event b)
mapEvent f x = do
  (e,h) <- liftIO $ newEvent
  onEventIO x (\i -> void . forkIO $ (f i)  >>= h)
  return  e


mapTEventDyn f x = do
  i <- currentValue  (facts x)
  mapT0EventDyn i f x

mapT0EventDyn :: a -> (a -> Dynamic b) -> Tidings a -> Dynamic (Tidings b)
mapT0EventDyn i f x = mdo
  (be,v) <- liftIO$ runDynamic $ f i
  (e,finmap) <- liftIO$ runDynamic $ mapEventDyn (\(a,b) -> liftIO (sequence (reverse $ zipWith (\i -> traceShow ("Finalizer",i) ) [0..] a)) >>  f b) ((,)<$> (snd <$> t) <@> rumors x)
  t <- stepper (be,v) e
  let finall = do
        (_,fin) <- currentValue t
        sequence fin
        sequence finmap
        return ()
  Writer.tell [finall]
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

checkDivSetTGen :: (Ord a,Ord b ,Eq a,Ord c) => [a] -> Tidings (a -> b) -> Tidings (Map a [c]) ->  (a -> UI (a,((Element,[Element]),Event (a,([c],[c]))))) -> Tidings (a -> (Element  , [Element])-> UI Element ) -> UI (TrivialWidget (Map a [c]))
checkDivSetTGen ks sort binit   el st = do
  buttons <- mapM el  ks
  -- dv <- UI.div
  -- tdout <- ui $ accumDiff (\(_,v) -> evalUI dv v ) ((\sti -> M.fromList $ fmap (\(k,(v,_)) -> (k,sti k v) ) buttons )<$> st )
  -- element dv # sink children (facts $ (\old f -> F.toList $ M.mapKeys f   old ) <$>  tdout <*> sort )
  dv <- UI.div # sink items ((\sti f -> fmap (\ (k,(v,_)) -> sti k (v) ) . L.sortBy (flip $ comparing (f . fst))  $ buttons) <$>  facts st <*> facts sort )
  let
    evs = unionWith const (const <$> rumors binit) (foldr (unionWith (.)) never $ fmap (\(i,(ab,db)) -> (if L.null ab then id else M.alter (Just . maybe ab (L.nub . mappend ab) ) i)  . (if L.null db then id else M.alter (join . fmap ((\i -> if L.null i then Nothing else Just i) . flip (foldr L.delete)  db )) i)  ) . snd .snd <$> buttons)
  v <- currentValue (facts binit)
  bv <- accumB v  evs
  return (TrivialWidget (tidings bv (flip ($) <$> bv <@> evs) ) dv)


checkDivSetT :: (Ord b ,Eq a) => [a] -> Tidings (a -> b) -> Tidings [a] ->  (a -> UI Element ) -> (a -> UI Element  -> UI Element ) -> UI (TrivialWidget [a])
checkDivSetT ks sort binit   el st = mdo
  buttons <- mapM (buttonString  )  ks
  dv <- UI.div # sink items ((\f -> fmap (\ (k,(v,_)) -> st k (element v) # sink UI.checked (elem k <$> bv)) . L.sortBy (flip $ comparing (f . fst))  $ buttons) <$>  facts sort )
  let
    evs = unionWith const (const <$> rumors binit) (foldr (unionWith (.)) never $ fmap (\(i,b) -> if b then (i:) else L.delete i) . snd .snd <$> buttons)
  v <- currentValue (facts binit)
  bv <- accumB v  evs
  return (TrivialWidget (tidings bv (flip ($) <$> bv <@> evs) ) dv)
    where
      buttonString   k = do
        v <- currentValue (facts binit)
        b <- el k # set UI.checked  (elem k v )
        let ev = (k,)<$>UI.checkedChange b
        return (k,(b,ev))


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

buttonDivSetFun :: Eq a => [a] -> Tidings (Maybe a)  ->  (a -> UI Element ) -> UI (TrivialWidget a)
buttonDivSetFun ks binit   el = mdo
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
  dv <- UI.span # set children [i] # set UI.style [("padding","2px")]
  return $ TrivialWidget  (tidings bh (diffEvent bh e)) dv

checkedWidgetM :: Tidings (Maybe Bool) -> UI (TrivialWidget (Maybe Bool))
checkedWidgetM init = do
  i <- UI.input # set UI.type_ "checkbox" # sink UI.checked (maybe False id <$> facts init)
  let e = unionWith const (rumors init) (Just <$>  UI.checkedChange i)
  v <- currentValue (facts init)
  b <- stepper v e
  dv <- UI.span # set children [i] # set UI.style [("padding","2px")]
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


read1 s = unsafeFromJSON s
-- read1 (EventData i )  = errorWithStackTrace $show i

readBool "true" = Just True
readBool "false" = Just False
readBool i = Nothing

readMouse :: EventData -> Maybe (Int,Bool,Bool,Bool)
readMouse v  =   (,,,) <$> readMay i<*>readMay a<*> readMay b <*>readMay c
  where
      readMay i = case JSON.fromJSON $ i of
                    JSON.Success i -> Just i
                    i -> Nothing
      [i,a,b,c] :: [JSON.Value] = unsafeFromJSON (v)
-- readMouse i = errorWithStackTrace $show i

onkey :: Element -> ((Int,Bool,Bool,Bool) -> Bool) -> Event String
onkey el f = unsafeMapUI el (const $ UI.get value el) (filterE f $ filterJust $ readMouse <$> domEvent "keydown" el)

onAltEnter el = onkey el (\case{(13,False,True,False)-> True ; i -> False})
onAltE el = onkey el (\case{(69,False,True,False)-> True ; i -> False})
onAltU el = onkey el (\case{(85,False,True,False)-> True ; i -> False})
onAltI el = onkey el (\case{(73,False,True,False)-> True ; i -> False})
onAltD el = onkey el (\case{(68,False,True,False)-> True ; i -> False})
onEnter el = onkey el (\case {(13,_,_,_)-> True; i -> False})
onEsc el = onkey el (\case {(27,_,_,_) -> True ; i -> False})


testPointInRange ui = do
  startGUI defaultConfig {jsPort = Just 8000} (\w -> do
                      e1 <- ui
                      getBody w #+ [element e1]
                      return () )

unsafeMapUI el f = unsafeMapIO (\a -> evalDyn el (f a))

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
    let
        bindex   = lookupIndex <$> bitems <*> bsel
        lookupIndex indices Nothing    = Nothing
        lookupIndex indices (Just sel) = L.findIndex (== sel)  indices
    els <- ui $ accumDiff (\(k,v)-> evalUI list $  UI.option # v) (liftA2 (\i j -> M.fromList $ (\ix -> (ix, j ix ))<$> i) bitems bdisplay)
    element list # sink children (facts $ (\m i -> F.toList . M.mapKeys ( flip L.findIndex i. (==) ) $ m)<$> els <*> bindices)
    --element list # sink children (facts (F.toList <$> els))

    -- animate output selection

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

    let bindices :: Tidings (M.Map a Int)
        bindices = (M.fromList . flip zip [0..]) <$> bitems
        bindex   = lookupIndex <$> bindices <*> bsel
        lookupIndex indices sel = catMaybes $ (flip M.lookup indices) <$> sel
    els <- ui $ accumDiff (\(k,v)-> evalUI list $  UI.option # v) (liftA2 (\i j -> M.fromList $ (\ix -> (ix, j ix ))<$> i) bitems bdisplay)
    element list # sink children (facts $ (\m i -> F.toList . M.mapKeys ( flip M.lookup i) $ m)<$> els <*> bindices)

    -- animate output selection


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
fileChange el = unsafeMapUI el (const $ UI.get readFileAttr el) (UI.onChangeE el)

selectionMultipleChange :: Element -> Event [Int]
selectionMultipleChange el = unsafeMapUI el (const $ UI.get selectedMultiple el) (UI.click el)

readFileAttr :: ReadAttr Element (Maybe String)
readFileAttr = mkReadAttr get
  where
    get   el = fmap  from  $  callFunction $ ffi "readFileInput($(%1))" el
    from s = case JSON.fromJSON s of
                  JSON.Success x -> M.lookup ("filevalue" ::String) x
                  i -> traceShow s Nothing -- errorWithStackTrace (show i)


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
mousewheel = fmap ((\i -> if (i :: Int) > 0 then 1 else -1) .  unsafeFromJSON ) . domEvent "wheel"

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

testWidget e = startGUI (defaultConfig { jsPort = Just 10000 , jsStatic = Just "static", jsCustomHTML = Just "index.html" })  {-( \w ->  do
              els <- e
              getBody w #+ [els]
              return ()) (\w -> (return ()))-}


flabel = UI.span # set UI.class_ (L.intercalate " " ["label","label-default"])

onEventFT
  :: Event a ->  (a -> UI b) -> UI  ()
onEventFT e h = do
  fin <- onEvent e h
  return ()

mapUIFinalizerT
  :: Element
     -> (b -> UI b1)
     -> Tidings b
     -> UI (Tidings b1)
mapUIFinalizerT el m inp = ui $ do
  mapTEventDyn (\i -> evalUI el  $ m i) inp

line n =   set  text n

accumDiff
  :: Prelude.Ord k =>
     ((k,a) -> Dynamic b)
     -> Tidings (M.Map k a )
     -> Dynamic
          (Tidings (M.Map k b))
accumDiff  f t = do
  ini <- currentValue (facts t)
  iniout <- liftIO$ mapConcurrently (execDynamic f)$ M.toList ini
  (del,add) <- diffAddRemove t f
  let eva = unionWith (.) ( (\s m -> foldr (M.delete ) m s). S.toList  <$> del ) ((\s m -> foldr (uncurry M.insert ) m s) <$> add )
  bs <- accumB  (M.fromList iniout)  eva
  onEventIO (filterJust$ (\m -> traverse (flip M.lookup  m) ) <$> bs <@> (S.toList <$> del)) (liftIO .sequence . concat . fmap snd)
  return (fmap (fmap fst ) $ tidings bs (flip ($) <$> bs <@> eva))

execDynamic :: ((k,a) -> Dynamic b) -> (k,a) -> IO (k,(b,[IO ()]))
execDynamic f l =  fmap ((fst l,)) . runDynamic $ f l

diffAddRemove :: Ord k => Tidings (M.Map k a ) -> ((k,a) -> Dynamic b) -> Dynamic (Event (S.Set k) ,Event [(k, (b,[IO()]))])
diffAddRemove l f = do
  let delete  = fmap M.keysSet $filterJust $ prune <$> evdell
  add <- mapEventDyn ( liftIO . mapConcurrently (execDynamic f). M.toList )  $ filterJust $ prune <$> evadd
  return (delete,fmap fst add)

    where
      diff i j = M.difference i  j
      evdiff = diffEventKeys (facts l ) (rumors l)
      evadd = flip diff <$> facts l <@> evdiff
      evdell =  diff <$> facts l <@> evdiff
      prune i = if M.null i  then Nothing else Just i



diffEventKeys b ev = filterJust $ (\i j -> if M.keysSet i == M.keysSet j then Nothing else Just j ) <$> b <@> ev

