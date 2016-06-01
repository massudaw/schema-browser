{-# LANGUAGE RecursiveDo,TupleSections #-}
module SortList where
import qualified Graphics.UI.Threepenny as UI
import Graphics.UI.Threepenny.DragNDrop as UI
import Graphics.UI.Threepenny.Core
import Data.Bifunctor
import Data.Maybe
import qualified Data.Map as M
import TP.Widgets
import Data.Monoid
import qualified Data.List as L
import qualified Data.Foldable as F


testUI e = startGUI (defaultConfig { jsPort = Just 10000 , jsStatic = Just "static", jsCustomHTML = Just "index.html" })  {-$ \w ->  do
              els <- e
              getBody w #+ [els]
              return ()-}

type SortList a = [(a,Maybe Bool)]

conv (l,t) = show l <>  " " <> maybe "" (\b -> if b then "Desc" else "Asc") t


sortItem conv ix bh  = do
  let
      step t = case t of
              Just True -> Just False
              Just False -> Nothing
              Nothing -> Just True
  dv <- UI.div # sink text (conv <$> bh)
  let ev = (\(l,t)-> const (l,step t)) <$>  bh <@> UI.click dv
  return $ TrivialWidget (tidings bh ev) dv



item ix t = do
  dr <- UI.input # sink value (show <$> t)
  return $ TrivialWidget (tidings t (read <$> UI.valueChange dr) ) dr


slot :: UI Element -> (Int -> Behavior a -> UI (TrivialWidget a)) -> Int -> Behavior a -> UI (Element,(Event (Int,Int),Event (Int,a)))
slot slote iteme ix el = do
    eld <- slote # set droppable True
    let eh = read <$> UI.drop eld
    TrivialWidget v i  <- iteme ix  el
    element i # set draggable True # set dragData (show ix)
    element eld  # set children [i]
    return (eld, ((\inew->  (inew,ix) )<$>  eh ,fmap (ix,) $ rumors v))



list :: UI Element -> UI Element -> (Int -> Behavior a -> UI (TrivialWidget a)) -> [a] -> UI (TrivialWidget [a])
list liste slote iteme els = mdo
    let size = length els
    slots <- mapM (\ix -> slot slote iteme ix (fromJust . M.lookup ix <$> facts res )) [0..size - 1]
    let  evs = head <$> (unions $ fst . snd <$> slots)
         ev2  = uncurry M.insert . head <$> (unions $ snd . snd <$> slots)
         swapKey (ixnew,ix) m =  M.insert ix elnew . M.insert ixnew el $ m
            where
              el = fromJust $ M.lookup ix m
              elnew = fromJust $ M.lookup ixnew m
         evres = unionWith (.)(swapKey  <$> evs) ev2
    res <- accumT (M.fromList $ zip [0..] els)  evres
    el <- liste # set children (fst <$> slots )
    return $ TrivialWidget (F.toList <$> res ) el


filterOrd = fmap (second fromJust) . filter (isJust .snd)
selSort l sel = ((\i j -> fmap (\e -> (e,,Nothing)  $ fmap snd $  L.find ((==e).fst) j) i ) l sel)




selectUI :: Eq a => [a] -> [(a,Bool)] -> UI Element -> UI Element -> ((a,Maybe Bool) -> String) -> UI (TrivialWidget [(a,Maybe Bool)])
selectUI l sel liste slote conv = do
    tds <- list liste slote (sortItem conv) ((\i j -> fmap (\e -> (e,)  $ fmap snd $  L.find ((==e).fst) j) i ) l sel)
    return $ TrivialWidget (triding tds) (getElement tds)


test = testUI (do
        ui <- selectUI [1,2,3,4,5,6] [(1,True)] UI.div UI.div conv
        out <- UI.div # sink text (show <$> facts (triding ui))
        UI.div # set children  [getElement ui,out] )
