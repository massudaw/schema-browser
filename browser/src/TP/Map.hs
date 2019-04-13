{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}

module TP.Map (mapDef,mapWidget,mapWidgetMeta) where


import Step.Host
import qualified NonEmpty as Non
import Data.String
import TP.MapSelector
import Environment
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

instance A.ToJSON (Interval Showable) where
  toJSON i = A.toJSON [G.unFin $ fst $ lowerBound' i , G.unFin $ fst $ upperBound' i]

instance A.ToJSON (G.Node (FTB Showable)) where
  toJSON (G.FTBNode i) = A.toJSON i

mapWidget (incrementT,resolutionT) (sidebar,prepositionT) sel inf = do
    dashes <- mapWidgetMeta inf
    let
      minf = meta inf
      chooser  = do
        map <-UI.div
        (eselg,hselg) <- ui newEvent
        start <- ui$stepper Nothing (filterE (maybe False (not .snd.fst)) eselg)
        let render = maybe "" (\((t,_),i) -> show $ G.getIndex (tableMeta t) i)
        startD <- UI.div #  sink text (render <$> start)
        end <- ui$stepper Nothing (filterE (maybe False (snd.fst) ) eselg)
        endD <- UI.div #  sink text (render <$> end)

        (positionLocal,h) <- ui newEvent
        let positionE = unionWith const (rumors prepositionT) positionLocal
        pb <- currentValue (facts prepositionT)
        positionT <- ui $ stepperT  pb positionE
        let
          calFun selected = do
            innermap <-UI.div # set UI.id_ "map" # set UI.style [("heigth","450px")]
            let
              mapT = (,) <$> facts incrementT <#> resolutionT
            evc <- eventClick innermap
            pb <- currentValue (facts positionT)
            editor <- UI.div
            element map # set children [innermap,editor]
            mapCreate innermap
            traverse (setPosition innermap ) pb
            move <- moveend innermap
            onEvent move (liftIO . h. Just)
            onEvent (filterJust $ rumors prepositionT) (setPosition innermap )

            fin <- mapM (\(_,tb,wherePred,proj) -> do
              let pcal =  liftA2 (wherePred mempty) positionT mapT
                  tname = tableName tb
              traverseUIInt (\pred ->
                if mempty /= pred
                  then do
                    reftb <- ui $ refTablesProj inf tb Nothing pred (projectFields inf tb (fst $ staticP proj) mempty $ allFields inf tb)
                    let v = primary <$> reftb ^. _2
                    let evsel = (\j ((tev,pk,_),s) -> fmap ((tev,s),) $ join $ if tev == tb then Just ( G.lookup pk j) else Nothing  ) <$> facts v <@> fmap (first (readPK inf . T.pack) ) evc
                    onEvent evsel (liftIO . hselg)
                    tdi <- ui $ stepperT Nothing (fmap snd <$> evsel)
                    el <- crudUITable inf tb reftb mempty [] (allRec' (tableMap inf) tb)  tdi
                    traverseUIInt (createLayers innermap tname . A.toJSON . catMaybes . concatMap (evalPlugin proj)) v
                    stat <- UI.div # sink text (show . M.lookup pred . unIndexMetadata <$> facts (reftb ^. _1))
                    edit <- UI.div # set children [getElement el] # sink UI.style (noneShow . isJust <$> facts tdi)
                    UI.div # set children [stat,edit]
                  else
                    UI.div) pcal
              ) selected
            let els = foldr (liftA2 (:)) (pure []) fin
            element editor # sink children (facts els)
            return ()
        let calInp = (\i -> filter (flip L.elem (F.toList i) .  (^. _2)) dashes) <$> sel
        (traverseUIInt calFun calInp)
        return [map]


    return (legendStyle dashes ,dashes,chooser)
