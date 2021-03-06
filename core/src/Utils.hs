{-# LANGUAGE BangPatterns,OverloadedStrings #-}
module Utils where

import Data.Aeson
import Data.Unique
import Data.Time
import qualified Data.HashMap.Strict as HM
import Control.Monad.IO.Class
import Data.Interval as Interval
import qualified Data.List as L
import Data.Maybe
import Data.Monoid
import qualified Data.Text as TE
import qualified Data.Text.Lazy as T
import qualified Data.Vector as V
import Debug.Trace
import GHC.Exts

import qualified Data.Foldable as F
import qualified Data.Map as M

debugTime t f = do
  un <- liftIO $ newUnique
  t0 <- liftIO $ getCurrentTime
 -- liftIO $ putStrLn $ "## (" <> t  <>") " <> show (hashUnique un)
  v <- f
  tf <- liftIO $ getCurrentTime
  -- liftIO $ putStrLn $ "## (" <> t  <>") " <> show (hashUnique un) <> " - " <> show (diffUTCTime tf t0)
  return v




spanList :: ([a] -> Bool) -> [a] -> ([a], [a])
spanList _ [] = ([], [])
spanList func list@(x:xs) =
  if func list
    then (x : ys, zs)
    else ([], list)
  where
    (ys, zs) = spanList func xs

{- | Similar to Data.List.break, but performs the test on the entire remaining
list instead of just one element.
-}
breakList :: ([a] -> Bool) -> [a] -> ([a], [a])
breakList func = spanList (not . func)

splitL :: Eq a => [a] -> [a] -> [[a]]
splitL _ [] = []
splitL delim str =
  let (firstline, remainder) = breakList (L.isPrefixOf delim) str
  in firstline :
     case remainder of
       [] -> []
       x ->
         if x == delim
           then [] : []
           else splitL delim (drop (length delim) x)

safeHead [] = Nothing
safeHead i = Just $ head i

traceShowWith f i = trace (f i) i

ifApply p f a =
  if p a
    then f a
    else a

(|>) :: Maybe (HM.HashMap TE.Text Value) -> TE.Text -> Maybe Value
o |> v = o >>= HM.lookup (v :: TE.Text)

(!!>) :: Maybe Value -> Int -> Maybe (Value)
o !!> v = goArray o >>= (V.!? v)
  where
    goArray (Just (Array i)) = Just i
    goArray i = Nothing

(!>) :: Maybe Value -> TE.Text -> Maybe (Value)
o !> v = goObject o >>= HM.lookup (v :: TE.Text)
  where
    goObject (Just (Object i)) = Just i
    goObject i = Nothing

translateMonth :: T.Text -> T.Text
translateMonth v = foldr (\i -> (uncurry T.replace) i) v transTable
  where
    transTable =
      [ ("out", "oct")
      , ("dez", "dec")
      , ("set", "sep")
      , ("ago", "aug")
      , ("fev", "feb")
      , ("abr", "apr")
      , ("mai", "may")
      ]

justError e (Just i) = i
justError e v = error e

groupSplit f = fmap (\i -> (f $ head i, i)) . groupWith f

allMaybesMap m =
  if M.null filtered
    then Nothing
    else Just filtered
  where
    filtered = fmap fromJust $ M.filter isJust m

data Compose2 f g a b = Compose2
  { getCompose2 :: f (g a b)
  }

firstComp ::
     Functor t => (f a c -> g b c) -> Compose2 t f a c -> Compose2 t g b c
firstComp f = Compose2 . fmap f . getCompose2

allMaybes :: (Functor f, F.Foldable f) => f (Maybe a) -> Maybe (f a)
allMaybes i
  | F.all (const False) i = Nothing
allMaybes i =
  if F.all isJust i
    then Just $ fmap (justError "wrong invariant allMaybes") i
    else Nothing

allMaybesEmpty i
  | F.all (const False) i = Just []
allMaybesEmpty i =
  if F.all isJust i
    then Just $ fmap (justError "wrong invariant allMaybes") i
    else Nothing

unIntercalate :: (Char -> Bool) -> String -> [String]
unIntercalate pred s =
  case dropWhile pred s of
    "" -> []
    s' -> w : unIntercalate pred s''
      where (w, s'') = break pred s'

chuncksOf i [] = []
chuncksOf i v =
  let (h, t) = L.splitAt i v
  in h : chuncksOf i t

justLook k m = justError ("no key in map" <> show k <> show m) . M.lookup k $ m

justLookH k m =
  justError ("no key in map" <> show k <> show m) . HM.lookup k $ m

eitherToMaybe = either (const Nothing) Just

nonEmpty [] = Nothing
nonEmpty i = Just i

safeTail [] = []
safeTail i = tail i

buildMap f = M.fromListWith mappend . fmap  f

unFinite :: Interval.Extended a -> Maybe a
unFinite (Interval.Finite i) = Just i
unFinite i = Nothing

groupSplit2 :: Ord b => (a -> b) -> (a -> c) -> [a] -> [(b, [c])]
groupSplit2 f g =
  fmap (\i -> (f $ justError "cant group" $ safeHead i, g <$> i)) . groupWith f


