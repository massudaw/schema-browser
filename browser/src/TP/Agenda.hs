{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module TP.Agenda (agendaDef,eventWidget,eventWidgetMeta) where

import GHC.Stack
import Step.Host
import TP.AgendaSelector
import Control.Monad.Writer as Writer
import TP.View
import qualified Data.Interval as Interval
import Control.Concurrent
import Utils
import Types.Patch
import Control.Arrow
import Control.Lens ((^.), _1, mapped,_2, _3,_4,_5)
import qualified Data.List as L
import Data.Either
import Data.Interval (Interval(..))
import Data.Time.ISO8601
import Data.Time.Calendar.WeekDate
import Data.Char
import qualified Data.Text.Encoding as TE
import Control.Concurrent.Async
import Safe
import Query
import Data.Time hiding(readTime)
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
import Reactive.Threepenny hiding (apply)
import qualified Data.ByteString.Lazy.Char8 as BSL
import RuntimeTypes
import Environment
import qualified Graphics.UI.Threepenny as UI
import Graphics.UI.Threepenny.Core hiding (get, delete, apply)
import Data.Monoid hiding (Product(..))
import qualified Data.Foldable as F
import qualified Data.Text as T
import Data.Text (Text)
import qualified Data.Map as M
import qualified Data.Set as S

calendarCreate m cal def = runFunctionDelayed cal $ ffi "createAgenda(%1,%2,%3)" cal def m

calendarAddSource cal t evs = do
  runFunctionDelayed cal $ ffi "addSource(%1,%2,%3)" cal (tableName t) (T.unpack . TE.decodeUtf8 .  BSL.toStrict . A.encode  $ evs)
  ui $ registerDynamic (fmap fst $ runDynamic $ evalUI cal $ calendarRemoveSource cal t)

calendarRemoveSource cal t = runFunctionDelayed cal $ ffi "removeSource(%1,%2)" cal (tableName t)


eventWidget (incrementT,resolutionT) sel inf cliZone = do
    dashes <- eventWidgetMeta inf
    let
      legendStyle lookDesc table b =
        let item = M.lookup table (M.fromList  $ fmap (\i@(a,b,c,_)-> (b,i)) dashes)
        in traverse (\(k@(c,tname,_,_)) -> do
          element  b # set UI.class_"col-xs-1"
          label <- UI.div # set text  (T.unpack  lookDesc) # set UI.class_ "fixed-label col-xs-10"
          UI.label # set children [b,label]
            # set UI.style [("background-color",renderShowable c)]# set UI.class_ "table-list-item" # set UI.style [("display","-webkit-box")]
            ) item
      chooser = do
        agenda <- buttonDivSet [Basic,Agenda,Timeline] (pure $ Just Basic) (\i ->  UI.button # set text (show i) # set UI.class_ "buttonSet btn-xs btn-default pull-left")
        out <- traverseUI id $ calendarView inf Nothing cliZone dashes sel <$>  triding agenda <*> resolutionT <*> incrementT
        out2 <- traverseUI (traverseUI (traverse (\(t,tdi) -> do
          reftb <- ui $ refTables inf t
          crudUITable inf  t reftb mempty [] (allRec' (tableMap inf) t) (pure (Just tdi)))))  (fmap snd out)
        out3 <- ui $ joinT out2
        selector <- UI.div # sink UI.children (facts $ (fmap getElement .maybeToList) <$> out3)
        calendar <- UI.div # sink UI.children (facts $ fmap fst out )
        return [getElement agenda,calendar,selector]

    return  (legendStyle , dashes ,chooser )


