{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module PrimEditor where

import Types.Patch
import Safe
import Debug.Trace
import Control.Arrow
import Utils
import RuntimeTypes
import Control.Monad
import Control.Applicative
import Data.Time.Format
import Data.Time
import Data.Time.LocalTime
import Serializer
import TP.Widgets
import Data.Maybe
import qualified Graphics.UI.Threepenny as UI
import Graphics.UI.Threepenny.Core hiding(apply)
import qualified Control.Lens as Le
import Reactive.Threepenny hiding(apply)

horizontal :: [Element] -> UI Element
horizontal l = UI.div # set UI.style [("display","inline-flex")]  # set UI.children l

vertical :: [Element] -> UI Element
vertical l = UI.div # set UI.children l

data Transaction a
  = Transaction { getTransaction :: a }
instance (Patch a ) => Patch (Transaction a) where
  type Index (Transaction a ) = Index a
  create i = Transaction (create i)
  applyUndo (Transaction i )  j = fmap (first Transaction )$ applyUndo i j
  diff (Transaction i ) (Transaction j) = diff i j

class PrimEditor a where
  primDiff :: Tidings (Maybe a) -> Tidings (Editor (Index a)) -> UI (TrivialWidget (Editor (Index a)))
  default primDiff :: Patch a => Tidings (Maybe a) -> Tidings (Editor (Index a)) -> UI (TrivialWidget (Editor (Index a)))
  primDiff i l = do
    TrivialWidget d e <- primEditor (apply <$> i <*> l)
    return $ TrivialWidget (diff' <$> i <*> d) e

  primEditor :: Tidings (Maybe a) -> UI (TrivialWidget (Maybe a))
  default primEditor :: Patch a => Tidings (Maybe a) -> UI (TrivialWidget (Maybe a))
  primEditor i = do
    TrivialWidget d e <- primDiff i (pure Keep)
    return $ TrivialWidget (join <$> (applyIfChange <$> i <*> d)) e

newtype UIEditor a
  = UIEditor {uiEditor :: Tidings (Maybe a) -> UI (TrivialWidget (Maybe a))}

instance IsoProfunctor UIEditor where
  isoMap (IsoArrow ap unap) (UIEditor f) = UIEditor $ \ i -> fmap (fmap (ap)) <$> f (fmap unap <$> i )

instance (Patch a,Patch b,Patch c,Patch d) => Patch (a,b,c,d) where
  type Index (a,b,c,d) = (Index a , Index b , Index c, Index d)
  apply (i,j,k,l) (a,b,c,d) = (apply i a, apply j b, apply k c,apply l d)

instance Semigroup Integer where
  (<>) =  (+)

instance Semigroup Int where
  (<>) =  (+)

instance Semigroup Double where
  (<>) =  (+)

instance Monoid Double where
  mempty = 0

instance Monoid Int where
  mempty = 0

instance Monoid Integer where
  mempty = 0


instance Compact Integer where
  compact i = case sum i of
    0 -> []
    i -> [i]
instance Compact Int where
  compact i = case sum i of
    0 -> []
    i -> [i]

instance Compact Double where
  compact i = case sum i of
    0 -> []
    i -> [i]

instance (Compact (Index a),Compact (Index b), Compact (Index c),Patch a,Patch b,Patch c) => Patch (a,b,c) where
  type Index (a,b,c) = (Index (Atom a) , Index (Atom b) , Index (Atom c))
  createIfChange (i,j,k) = (,,) <$> (unAtom' <$> createIfChange i) <*> (unAtom' <$> createIfChange j) <*> (unAtom' <$> createIfChange k)
  applyUndo (i,j,k) (a,b,c) = do
    (v,l) <- applyUndo (Atom i) a
    (s,m) <- applyUndo (Atom j) b
    (t,n) <- applyUndo (Atom k) c
    return ((unAtom' v, unAtom' s, unAtom' t),(l,m,n))

instance (Show (Index a),Compact (Index a),Patch a ,PrimEditor a) => PrimEditor (Transaction a) where
  primDiff i dl = mdo
    let update = fmap getTransaction <$> i
    a <- primDiff  update d
    d <- ui $ accumT  Keep ((\i j -> maybe Keep id . safeHead  $ compact [i,j]) <$> rumors (triding a))
    log <- UI.div # sinkDiff text (show <$> d )
    u <- UI.div # set children [getElement a, log]
    return (TrivialWidget d u)

instance (Patch a ,PrimEditor a) => PrimEditor (Maybe a) where
  primEditor i = fmap Just <$> primEditor (join <$> i)

instance (Patch a,Patch b,Patch c,Patch d,PrimEditor a,PrimEditor b,PrimEditor c, PrimEditor d) => PrimEditor (a,b,c,d) where
  primEditor i = do
    f <- primEditor (fmap (Le.view Le._1)<$> i)
    s <- primEditor (fmap (Le.view Le._2)<$> i)
    t <- primEditor (fmap (Le.view Le._3)<$> i)
    u <- primEditor (fmap (Le.view Le._4)<$> i)
    TrivialWidget (liftA4 (,,,)<$> triding f <*> triding s <*> triding t<*> triding u) <$> horizontal [getElement f,getElement s,getElement t,getElement u]

liftA4 f i j k l = f <$> i <*> j <*> k <*> l

instance (Compact (Index a),Compact (Index b),Compact (Index c),Patch a ,Patch b ,Patch c,PrimEditor a,PrimEditor b,PrimEditor c) => PrimEditor (a,b,c) where
  primDiff i d = do
    let
        lower :: forall a . Compact a => [a] -> Editor a
        lower = maybe Keep Diff . safeHead . compact
        raise (Diff i) = [i]
        raise Keep = []
        --  All Keep, Any Delete and Merge Diff
        all Keep Keep Keep  = Keep
        all Delete _ _ = Delete
        all _ Delete _ = Delete
        all _ _ Delete = Delete
        all i j k = Diff (raise i ,raise j ,raise k)
    f <- primDiff (fmap (Le.view Le._1)<$> i) (join . fmap (lower.Le.view Le._1)<$> d)
    s <- primDiff (fmap (Le.view Le._2)<$> i) (join . fmap (lower . Le.view Le._2)<$> d)
    t <- primDiff (fmap (Le.view Le._3)<$> i) (join . fmap (lower . Le.view Le._3)<$> d)
    let r = (all <$> triding f <*> (triding s) <*> (triding t))
    TrivialWidget r <$> horizontal [getElement f,getElement s,getElement t]

instance (Compact (Index a),Compact (Index b),Patch a ,Patch b ,PrimEditor a,PrimEditor b) => PrimEditor (a,b) where
  primDiff i dl = do
    let
        lower :: forall a . Compact a => [a] -> Editor a
        lower = maybe Keep Diff . safeHead . compact
        raise (Diff i) = [i]
        raise Keep = []
        --  All Keep, Any Delete and Merge Diff
        all Keep Keep = Keep
        all Delete _  = Delete
        all _ Delete  = Delete
        all i j  = Diff (raise i ,raise j )
    f <- primDiff (fmap fst <$> i) (join .fmap (lower.fst) <$> dl)
    s <- primDiff (fmap snd <$> i) (join . fmap (lower.snd) <$> dl)
    let def Keep = Diff mempty
        def (Diff i) = (Diff i)
    TrivialWidget (all <$> (triding f) <*> (triding s)) <$> horizontal [getElement f,getElement s]

instance PrimEditor () where
  primEditor  i = fmap Just <$> buttonAction (justError "const prim" <$> i)

instance Patch Double where
  type Index Double = Double
  createIfChange i = Just i
  applyUndo i ix = Right $  (i + ix, negate ix)
  diff  i j =  Just (j - i)
  patch = id

instance Patch Int where
  type Index Int = Int
  applyUndo i ix = Right (i + ix, negate ix)
  diff i j = Just (j - i)
  createIfChange i = Just i
  patch = id

instance Patch Integer where
  type Index Integer = Integer
  applyUndo i ix = Right (i + ix, negate ix)
  diff i j = Just (j - i)
  createIfChange i = Just i
  patch = id

instance Patch Bool where
  type Index Bool = Bool
  apply i True = True
  apply i False = False
  createIfChange i = Just i
  patch = id

  diff True True  = Just True
  diff True False = Just False
  diff False True = Just True
  diff False False = Just  False

instance PrimEditor Bool where
  primEditor  = checkedWidgetM

instance PrimEditor Integer where
  primDiff =  readShowUIDiff

instance PrimEditor Double where
  primDiff =  readShowUIDiff

instance PrimEditor Int where
  primDiff =  readShowUIDiff

instance Patch UTCTime where
  type Index UTCTime =  NominalDiffTime
  apply = flip addUTCTime
  diff i = Just .  diffUTCTime i

instance Patch Day where
  type Index Day =  Integer
  apply = flip addDays
  diff i = Just .  diffDays i

instance PrimEditor UTCTime where
  primEditor tdi = timeUI ("%Y-%m-%d %H:%M:%S%Q", "yyyy-mm-dd hh:ii:ss") tdi

instance PrimEditor Day where
  primEditor tdi = timeUI ("%Y-%m-%d", "yyyy-mm-dd") tdi

readShowUIDiff :: (Eq (Index a),Show (Index a),Read a , Show a ,Patch a ) => Tidings (Maybe a) ->Tidings (Index (Maybe a)) ->  UI (TrivialWidget (Index (Maybe a)))
readShowUIDiff tdi del = mdo
    let res = join <$> (applyIfChange <$> tdi <*> del)
    inputUI <- UI.input # sink UI.value (maybe "" show <$> facts res) # set UI.style [("min-width","30px"),("max-width","120px")]
    onCE <- UI.onChangeE inputUI
    let pke = readMay <$> onCE
        filtered = unionWith const (const Keep <$>  rumors tdi) (unionWith const (diff'<$> facts res <@> pke) (rumors del))
    ini <- currentValue (facts del)
    p <- ui (stepperT ini filtered)
    return $  TrivialWidget  p inputUI


timeUI :: (FormatTime a ,ParseTime a) => (String,String) -> Tidings (Maybe a) -> UI (TrivialWidget (Maybe a))
timeUI (form1,form2) tdi = do
  let
    tdi1 = maybe "" (formatTime defaultTimeLocale form1) <$> tdi
  v <- currentValue (facts tdi)
  inputUI <- UI.input
    # set UI.style [("width","100%")]
    # set UI.class_ "date"
    # set (UI.strAttr "data-date-format") form2
    # set (UI.strAttr "data-provide") "datetimepicker"
    # sinkDiff UI.value tdi1
  onCE <- UI.onChangeE inputUI
  let pke = unionWith const (parseTimeM True defaultTimeLocale form1 <$> onCE ) (rumors tdi)
  pk <- ui $ stepperT v  pke
  return $ TrivialWidget pk inputUI

checkedWidgetM = checkedPWidgetM

checkedPWidgetM :: Tidings(Maybe Bool) -> UI (TrivialWidget (Maybe Bool))
checkedPWidgetM init = do
  i <- UI.input # set UI.type_ "checkbox" # sink UI.checked (fromMaybe False <$> facts init)
  ev <- UI.checkedChange i
  let e = unionWith const (rumors  init) (Just <$> ev)
  v <- currentValue (facts init)
  t <- ui$ stepperT v e
  dv <- UI.span # set children [i] # set UI.style [("padding","2px")]
  return $ TrivialWidget  t dv


checkedWidget = checkedPWidget

checkedPWidget :: Tidings Bool -> UI (TrivialWidget Bool)
checkedPWidget init = do
  i <- UI.input # set UI.type_ "checkbox" # sink UI.checked (facts init)
  ev <- UI.checkedChange i
  let e = unionWith const (rumors init ) ev
  v <- currentValue (facts init)
  t <- ui$ stepperT v e
  dv <- UI.span # set children [i] # set UI.style [("padding","2px")]
  return $ TrivialWidget  t dv


