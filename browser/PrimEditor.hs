{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module PrimEditor where

import PStream
import Types.Patch
import Safe
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

class PrimEditor a where
  primDiff :: Tidings (Maybe a) -> UI (TrivialWidget (Editor (Index a)))
  default primDiff :: Patch a => Tidings (Maybe a) -> UI (TrivialWidget (Editor (Index a)))
  primDiff i = do
    TrivialWidget d e <- primEditor i
    return $ TrivialWidget (diff' <$> i <*> d) e

  primEditor :: Tidings (Maybe a) -> UI (TrivialWidget (Maybe a))
  default primEditor :: Patch a => Tidings (Maybe a) -> UI (TrivialWidget (Maybe a))
  primEditor i = do
    TrivialWidget d e <- primDiff i
    return $ TrivialWidget (apply <$> i <*> d) e

newtype UIEditor a
  = UIEditor {uiEditor :: Tidings (Maybe a) -> UI (TrivialWidget (Maybe a))}

instance IsoProfunctor UIEditor where
  isoMap (IsoArrow ap unap) (UIEditor f) = UIEditor $ \ i -> fmap (fmap (ap)) <$> f (fmap unap <$> i )

instance (Patch a,Patch b,Patch c,Patch d) => Patch (a,b,c,d) where
  type Index (a,b,c,d) = (Index a , Index b , Index c, Index d)
  apply (i,j,k,l) (a,b,c,d) = (apply i a, apply j b, apply k c,apply l d)

instance (Patch a,Patch b,Patch c) => Patch (a,b,c) where
  type Index (a,b,c) = (Index a , Index b , Index c)
  apply (i,j,k) (a,b,c) = (apply i a, apply j b, apply k c)

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

instance (Patch a ,Patch b ,Patch c,PrimEditor a,PrimEditor b,PrimEditor c) => PrimEditor (a,b,c) where
  primEditor i = do
    f <- primEditor (fmap (Le.view Le._1)<$> i)
    s <- primEditor (fmap (Le.view Le._2)<$> i)
    t <- primEditor (fmap (Le.view Le._3)<$> i)
    TrivialWidget (liftA3 (,,)<$> triding f <*> triding s <*> triding t) <$> horizontal [getElement f,getElement s,getElement t]

instance (Patch a ,Patch b ,PrimEditor a,PrimEditor b) => PrimEditor (a,b) where
  primEditor i = do
    f <- primEditor (fmap fst <$> i)
    s <- primEditor (fmap snd <$> i)
    TrivialWidget (liftA2 (,)<$> triding f <*> triding s) <$> horizontal [getElement f,getElement s]

instance PrimEditor () where
  primEditor  i = fmap Just <$> buttonAction (fromJust <$> i)

instance Patch Double where
  type Index Double = Double
  apply i ix = i + ix
  diff  i j =  Just (j - i)

instance Patch Int where
  type Index Int = Int
  apply i ix = i + ix
  diff i j = Just ( j - i)

instance Patch Integer where
  type Index Integer = Integer
  apply i ix = i + ix
  diff  i j = Just ( j - i)

instance Patch Bool where
  type Index Bool = Bool
  apply i True = True
  apply i False = False
  patch = id

  diff True True  = Just True
  diff True False = Just False
  diff False True = Just True
  diff False False = Just  False

instance PrimEditor Bool where
  primEditor  = checkedWidgetM

instance PrimEditor Integer where
  primEditor =  readShowUI

instance PrimEditor Double where
  primEditor =  readShowUI

instance PrimEditor Int where
  primEditor =  readShowUI

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


readShowUI :: (Read a , Show a ) => Tidings (Maybe a) -> UI (TrivialWidget (Maybe a))
readShowUI tdi = do
    v <- currentValue (facts tdi)
    inputUI <- UI.input # sinkDiff UI.value (maybe "" show <$> tdi) # set UI.style [("min-width","30px"),("max-width","120px")]
    onCE <- UI.onChangeE inputUI
    let pke = unionWith const (readMay <$> onCE ) (rumors tdi)
    flip TrivialWidget inputUI <$> ui (stepperT v pke)

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


