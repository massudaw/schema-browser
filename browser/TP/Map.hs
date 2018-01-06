{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}

module TP.Map (mapWidget,mapWidgetMeta) where


import Step.Host
import qualified NonEmpty as Non
import Data.String
import TP.MapSelector
import Utils
import Database.PostgreSQL.Simple
import Control.Monad.Writer as Writer
import Postgresql.Parser
import Control.Arrow (first)
import TP.View
import GHC.Stack
import Control.Concurrent
import Control.Lens ((^.),_1,_2,_3,_5)
import Safe
import Control.Concurrent.Async
import Data.Interval as Interval
import Data.Time.Calendar.WeekDate
import qualified Data.Vector as V
import Data.Char
import qualified Data.Text.Encoding as TE
import Query
import Data.Time
import qualified Data.Aeson as A
import Text
import qualified Types.Index as G
import Debug.Trace
import Types
import SchemaQuery
import TP.Widgets
import Prelude hiding (head)
import TP.QueryWidgets
import Control.Monad.Reader
import Schema
import Data.Maybe
import Reactive.Threepenny hiding(apply)
import qualified Data.List as L
import qualified Data.ByteString.Lazy.Char8 as BSL

import RuntimeTypes
import qualified Graphics.UI.Threepenny as UI
import Graphics.UI.Threepenny.Core hiding (get,delete,apply)
import Data.Monoid hiding (Product(..))

import qualified Data.Foldable as F
import qualified Data.Text as T
import Data.Text (Text)

import qualified Data.Map as M
import qualified Data.HashMap.Strict as HM


instance UI.ToJS (G.Node (TBIndex Showable)) where
  render  = render . A.toJSON

instance A.ToJSON (G.Node (TBIndex Showable)) where
  toJSON (G.TBIndexNode i) = A.toJSON i

instance A.ToJSON (Interval Showable) where
  toJSON i = A.toJSON [G.unFin $ fst $ lowerBound' i , G.unFin $ fst $ upperBound' i]

instance A.ToJSON (G.Node (FTB Showable)) where
  toJSON (G.FTBNode i) = A.toJSON i


mapWidget body (incrementT,resolutionT) (sidebar,prepositionT) sel inf = do
    let
      mapT = (,) <$> facts incrementT <#> resolutionT
    dashes <- mapWidgetMeta inf
    mapOpen <- liftIO getCurrentTime

    filterInp <- UI.input
    filterInpT <- element filterInp # sourceT "change" UI.valueFFI ""
    let
      parseMany t l =  parseInp t <$> unIntercalate ('&'==) l
      parseInp t i
        | not (L.null j ) && T.pack tnew == tableName t  =    (,tail r ) <$> liftAccessM inf (tableName t) ( nest (unIntercalate ('.'==) (tail j)))
        | not $ L.null r =  (,tail r ) <$> liftAccessM inf (tableName t) ( nest (unIntercalate ('.'==) l))
        | otherwise = Nothing
        where (l,r) = break(=='=') i
              (tnew,j ) = break (=='|') l
              nest [i] = keyRef (T.pack i)
              nest (i:xs) = Nested [keyRef (T.pack i)] (Many [One $ nest xs])
      filteringPred  (k,v) row = maybe True (L.isInfixOf (toLower <$> v)  . fmap toLower . renderShowable ) (indexFieldRec k row)
      filtering tb res = (\t -> filter (\row -> all (`filteringPred` row) (catMaybes  t  )) )<$> fmap (parseMany tb ) (triding filterInpT ) <*> fmap G.toList res
    map <-UI.div

    (eselg,hselg) <- ui$newEvent
    start <- ui$stepper Nothing (filterE (maybe False (not .snd.fst)) eselg)
    let render = maybe "" (\((t,_),i) -> show $ G.getIndex (tableMeta t) i)
    startD <- UI.div #  sink text (render <$> start)
    end <- ui$stepper Nothing (filterE (maybe False (snd.fst) ) eselg)
    endD <- UI.div #  sink text (render <$> end)

    (positionLocal,h) <- ui newEvent
    let positionE = unionWith const (rumors prepositionT) positionLocal
    pb <- currentValue (facts prepositionT)
    positionB <- ui $stepper  pb positionE
    let positionT = tidings positionB positionE


    element body # set children [filterInp,map]
    let
      calFun selected = do
        innermap <-UI.div # set UI.id_ "map" # set UI.style [("heigth","450px")]
        let
          evc = eventClick innermap
        pb <- currentValue (facts positionT)
        editor <- UI.div
        element map # set children [innermap,editor]
        mapCreate  innermap pb
        onEvent (moveend innermap) (liftIO . h. Just)
        onEvent (filterJust $ rumors prepositionT) (\(sw,ne) -> runFunction $ ffi "setPosition(%1,%2,%3)" innermap  sw ne)

        fin <- mapM (\(_,tb,fields,efields,proj) -> do
          let pcal =  liftA2 (,) positionT  mapT
              tname = tableName tb
          traverseUI (\(positionB,calT)-> do
            let pred = WherePredicate $ predicate inf tb (fmap  fieldKey <$>efields ) (fmap fieldKey <$> Just   fields ) (positionB,Just calT)
                fieldKey (TB1 (SText v))=  v
            reftb <- ui $ refTables' inf (lookTable inf tname) (Just 0) pred
            let v = reftb ^. _3
            let evsel = (\j ((tev,pk,_),s) -> fmap ((tev,s),) $ join $ if tev == tb then Just ( G.lookup pk j) else Nothing  ) <$> facts v <@> fmap (first (readPK inf . T.pack) ) evc
            onEvent evsel (liftIO . hselg)

            tdib <- ui $ stepper Nothing (fmap snd <$> evsel)
            let tdi = tidings tdib (fmap snd <$> evsel)
                table = lookTable inf tname
            (el,_) <- crudUITable inf table reftb mempty [] (allRec' (tableMap inf) table)  tdi

            traverseUI (\i ->
              createLayers innermap tname (T.unpack $ TE.decodeUtf8 $  BSL.toStrict $ A.encode  $ catMaybes  $ concatMap proj i)) (filtering tb v)

            stat <- UI.div  # sinkDiff text (show . M.lookup pred <$>   (reftb ^. _1))
            edit <- UI.div # set children [el] # sink UI.style  (noneShow . isJust <$> tdib)
            UI.div # set children [stat,edit]
            ) pcal
          ) selected
        let els = foldr (liftA2 (:)) (pure []) fin
        element editor  # sink children (facts els)
        return ()
    let calInp = (\i -> filter (flip L.elem (F.toList i) .  (^. _2)) dashes  )<$> sel
    onFFI "$(document).ready((%1))" (evalUI body $   traverseUI calFun calInp)
    return (legendStyle dashes ,dashes)
