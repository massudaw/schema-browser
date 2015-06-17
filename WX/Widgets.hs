{-# LANGUAGE TupleSections,ScopedTypeVariables,LambdaCase,RankNTypes,DeriveFunctor,RecordWildCards,NoMonomorphismRestriction,RecursiveDo #-}
module WX.Widgets where


import Control.Monad

import Graphics.UI.WX hiding (Identity,when,newEvent,Event,swap,Key)
import Reactive.Banana hiding (Identity)
import Reactive.Banana.WX hiding (Identity,when)
import Tidings



import qualified Data.Map as M
import qualified Data.Set as S
import Data.Map (Map)
import Data.Traversable(traverse)
import Data.Monoid
import Data.Foldable (foldl')
import Data.Interval (Interval(..))
import qualified Data.ExtendedReal as ER
import qualified Data.Interval as Interval
import qualified Data.List as L
import Data.Maybe
import Control.Concurrent
import qualified Data.Aeson as JSON

import System.Directory
import System.Process(callCommand)
import Data.String
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC
import qualified Data.ByteString.Lazy as BSL




data TrivialWidget t a =
    TrivialWidget { triding :: (Tidings t a) , trielem ::  Layout } deriving(Functor)



checkedWidget :: forall t . Frameworks t => CheckBox () -> Tidings t Bool -> Moment t (TrivialWidget t Bool)
checkedWidget check init = mdo
  i <-  sink check [checked :== b ]
  ev  <- eventChecked check
  let e = unionWith const (rumors init) ev
  v <- initial (facts init)
  let b =  stepper v e
  return $ TrivialWidget (tidings b e) (widget check)

buttonFSet :: forall b a t . Frameworks t => Window b -> [a] -> Behavior t (Maybe a) -> Behavior t (String -> Bool ) ->  (a -> String) ->  Moment t ([Layout] , Tidings t a)
buttonFSet f ks binit bf h =do
  buttons <- mapM (buttonString h) ks
  let dv = (widget . fst <$> buttons)
  let evs = foldr (unionWith (const)) never (snd <$> buttons)
  v <- initial binit
  let bv = stepper (maybe (head ks) id v) evs
  return (dv, (tidings bv evs) )
    where
      buttonString h k= do
        b <- liftIO $ button f [text :=  h k ]
        sink b [visible :== (\f -> f (h k) ) <$> bf]
        click <- event0 b command
        let ev = pure k <@ click
        return (b,ev)

-- | Event that occurs when the /user/ changed
-- the selection marker in a list box widget.
eventSelection' :: Frameworks t =>
    ComboBox b -> Moment t (Event t Int)
eventSelection' w = do
    liftIO $ fixSelectionEvent w
    addHandler <- liftIO $ event1ToAddHandler w (event0ToEvent1 select)
    fromAddHandler $ mapIO (const $ get w selection) addHandler

-- Fix @select@ event not being fired when items are *un*selected.
fixSelectionEvent :: (Selecting w, Reactive w, Selection w) => w -> IO ()
fixSelectionEvent listbox =
    set listbox [ on unclick := handler ]
    where
    handler _ = do
        propagateEvent
        s <- get listbox selection
        when (s == -1) $ get listbox (on select) >>= id

eventChecked :: Frameworks t =>
    CheckBox b -> Moment t (Event t Bool)
eventChecked w = do
    addHandler <- liftIO $ event1ToAddHandler w (event0ToEvent1 command )
    fromAddHandler $ mapIO (const $ get w checked ) addHandler

eventSelections :: Frameworks t =>
    MultiListBox b -> Moment t (Event t [Int])
eventSelections w = do
    -- liftIO $ fixSelectionEvent w
    addHandler <- liftIO $ event1ToAddHandler w (event0ToEvent1 select)
    fromAddHandler $ mapIO (const $ get w selections) addHandler

reactiveMultiListDisplay :: forall t a b. (Ord a, Frameworks t)
    => MultiListBox b          -- ListBox widget to use
    -> Behavior t [a]           -- list of items
    -> Behavior t [a]     -- selected element
    -> Behavior t (a -> String) -- display an item
    -> Moment t
        (Tidings t [a])   -- current selection as item (possibly empty)
reactiveMultiListDisplay w bitems bsel bdisplay = do
    -- animate output items

    sink w [ items :== map <$> bdisplay <*> bitems ]

    -- animate output selection
    let bindices :: Behavior t (Map a Int)
        bindices = (M.fromList . flip zip [0..]) <$> bitems
        bindex   = (\m a -> maybe [] id $ traverse (flip M.lookup m) a) <$>
                    bindices <*> bsel
    sink w [ selections :== bindex ]

    -- changing the display won't change the current selection
    -- eDisplay <- changes display
    -- sink listBox [ selection :== stepper (-1) $ bSelection <@ eDisplay ]

    -- user selection
    let bindices2 :: Behavior t (Map Int a)
        bindices2 = M.fromList . zip [0..] <$> bitems
    esel <- eventSelections w

    return $ tidings bsel $ (\m  e -> maybe [] id $ traverse (flip M.lookup m ) e ) <$> bindices2 <@> esel

reactiveListDisplay :: forall t a b. (Ord a, Frameworks t)
    => SingleListBox b          -- ListBox widget to use
    -> Behavior t [a]           -- list of items
    -> Behavior t (Maybe a)     -- selected element
    -> Behavior t (a -> String) -- display an item
    -> Moment t
        (Tidings t (Maybe a))   -- current selection as item (possibly empty)
reactiveListDisplay w bitems bsel bdisplay = do
    -- animate output items

    sink w [ items :== map <$> bdisplay <*> bitems ]

    -- animate output selection
    let bindices :: Behavior t (Map a Int)
        bindices = (M.fromList . flip zip [0..]) <$> bitems
        bindex   = (\m a -> fromMaybe (-1) $ flip M.lookup m =<< a) <$>
                    bindices <*> bsel
    sink w [ selection :== bindex ]

    -- changing the display won't change the current selection
    -- eDisplay <- changes display
    -- sink listBox [ selection :== stepper (-1) $ bSelection <@ eDisplay ]

    -- user selection
    let bindices2 :: Behavior t (Map Int a)
        bindices2 = M.fromList . zip [0..] <$> bitems
    esel <- eventSelection w
    return $ tidings bsel $ flip M.lookup <$> bindices2 <@> esel

mapIOEvent f ev = do
  (e,h) <- newEvent
  reactimate $ (\i->   ( f i)  >>=   h ) <$> ev
  return e

-- single text entry
reactiveTextEntry :: Frameworks t
    => TextCtrl a
    -> Tidings t String              -- text value
    -> Moment t (Tidings t String)    -- user changes
reactiveTextEntry w ttext = do
    let btext = facts ttext
        etexti = rumors ttext
    eUser <- eventText w        -- user changes

    -- filter text setting that are simultaneous with user events
    etext <- changes btext
    let
        etext2 = fst $ split $ unionWith (curry snd) (Left () <$ etext) (Right () <$ eUser)
        btext2 = imposeChanges btext etext2

    sink w [ text :== btext2 ]  -- display value
    ivalue <- initial btext
    let btext3 = stepper  ivalue (unions [eUser ,etexti])
    return $ tidings btext3 eUser




reactiveComboDisplay :: forall t a b. (Ord a, Frameworks t)
    => ComboBox b          -- ListBox widget to use
    -> Behavior t [a]           -- list of items
    -> Behavior t (Maybe a)     -- selected element
    -> Behavior t (a -> String) -- display an item
    -> Moment t
        (Tidings t (Maybe a))   -- current selection as item (possibly empty)
reactiveComboDisplay w bitems bsel bdisplay = do
    -- animate output items

    sink w [ items :== map <$> bdisplay <*> bitems ]

    -- animate output selection
    let bindices :: Behavior t (Map a Int)
        bindices = (M.fromList . flip zip [0..]) <$> bitems
        bindex   = (\m a -> fromMaybe (-1) $ flip M.lookup m =<< a) <$>
                    bindices <*> bsel
    sink w [ selection :== bindex ]

    -- changing the display won't change the current selection
    -- eDisplay <- changes display
    -- sink listBox [ selection :== stepper (-1) $ bSelection <@ eDisplay ]

    -- user selection
    let bindices2 :: Behavior t (Map Int a)
        bindices2 = M.fromList . zip [0..] <$> bitems
    esel <- eventSelection' w
    return $ tidings bsel $ flip M.lookup <$> bindices2 <@> esel




adEvent :: forall a t . Frameworks t => Event t a -> Tidings t a -> Moment t (Tidings t a)
adEvent ne t = do
  c <- initial (facts t)
  let ev = unionWith const (rumors t) ne
      nb = stepper c ev
  return $ tidings nb ev


{-
liftEvent :: MonadIO m => Window -> Event (Maybe a) -> (MVar (Maybe a) -> m void) -> m ()
liftEvent window e h = do
    ivar <- liftIO $ newEmptyMVar
    liftIO $ register e (void . runUI window . liftIO  . maybe (return ()) ( putMVar ivar .Just )  )
    h  ivar
    return ()
-}

currentValue = initial

cutEvent :: Event t b -> Tidings t a -> Moment t  (Tidings t a)
cutEvent ev b = do
 v <- currentValue (facts b)
 let nev = facts b <@ ev
     nbev = stepper v nev
 return  $tidings nbev nev

updateEvent :: (a -> Maybe a) -> Event t a -> Tidings t a -> Moment t  (Tidings t a)
updateEvent validate ev b = do
 v <- currentValue (facts b)
 let nev = unionWith const (filterJust (validate <$> ev)) (rumors b)
     nbev = stepper v nev
 return  $tidings nbev nev



addEvent :: Event t a -> Tidings t a -> Moment t  (Tidings t a)
addEvent ev b = do
 v <- currentValue (facts b)
 let nev = unionWith const ev (rumors b)
     nbev = stepper v nev
 return  $tidings nbev nev

onEvent e h = reactimate (h <$> e)




-- Style show/hide
noneShow True = [("display","block")]
noneShow False = [("display","none")]

noneShowSpan True = [("display","inline")]
noneShowSpan False = [("display","none")]

-- Background Style green/red
greenRed True = [("background-color","green")]
greenRed False = [("background-color","red")]

interval'' i j = Interval.interval (ER.Finite i ,True) (ER.Finite j , True)






