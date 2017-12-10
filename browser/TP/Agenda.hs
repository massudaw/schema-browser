{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module TP.Agenda (eventWidget,eventWidgetMeta) where

import GHC.Stack
import Step.Host
import TP.AgendaSelector
import Control.Monad.Writer as Writer
import TP.View
import TP.Selector
import qualified Data.Interval as Interval
import Control.Concurrent
import Utils
import Types.Patch
import Control.Arrow
import TP.Browser
import Control.Lens ((^.), _1, mapped,_2, _3,_4,_5)
import qualified Data.List as L
import Data.Either
import Data.Interval (Interval(..))
import Data.Time.ISO8601
import Control.Monad.Writer
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
import Schema
import Data.Maybe
import Reactive.Threepenny hiding (apply)
import qualified Data.List as L
import qualified Data.ByteString.Lazy.Char8 as BSL
import RuntimeTypes
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


eventWidget body (incrementT,resolutionT) sel inf cliZone = do
    dashes <- eventWidgetMeta inf cliZone
    let
      schemaPred2 =  WherePredicate $ PrimColl (liftAccess (meta inf) "event" $ keyRef "schema",Left (int (schemaId inf),Equals))
      legendStyle lookDesc table b
            =
              let item = M.lookup table (M.fromList  $ fmap (\i@(a,b,c,_)-> (b,i)) dashes)
              in traverse (\(k@((c,tname,_,_))) -> do
                element  b # set UI.class_"col-xs-1"
                label <- UI.div # sink text  (T.unpack .($table) <$> facts lookDesc ) # set UI.class_ "fixed-label col-xs-10"
                UI.label # set children [b,label]
                  # set UI.style [("background-color",renderShowable c)]# set UI.class_ "table-list-item" # set UI.style [("display","-webkit-box")]
                  ) item

    choose <- buttonDivSet ["Main","Config"] (pure $ Just "Main") (\i ->  UI.button # set text i # set UI.class_ "buttonSet btn-xs btn-default pull-right")
    let
      chooser "Config" = do
        let
            minf = meta inf
            table = lookTable minf "event"
        reftb@(vptmeta,vp,vpt,_,var) <- ui $ refTables' minf table Nothing schemaPred2
        config <- selector minf table reftb  (pure $ Just schemaPred2 ) (pure Nothing)
        let tds = triding config
        (cru,pretdi) <- crudUITable minf table reftb [] [] (allRec' (tableMap minf) table) (triding config)
        return [getElement config,cru]

      chooser "Main" = do
        agenda <- buttonDivSet [Basic,Agenda,Timeline] (pure $ Just Basic) (\i ->  UI.button # set text (show i) # set UI.class_ "buttonSet btn-xs btn-default pull-left")
        out <- traverseUI (fmap fst) $ calendarView inf Nothing cliZone dashes sel <$>  triding agenda <*> resolutionT <*> incrementT
        calendar <- UI.div # sink UI.children (facts out)
        return [getElement agenda,calendar]
    els <- traverseUI chooser (triding choose)

    content <- UI.div # sink children (facts els) # set UI.class_ "row"
    element choose  # set UI.class_ "row"

    element body # set children [getElement choose,content] # set UI.style [("overflow","auto")]

    return  (legendStyle , dashes )

type DateChange = (String, Either (Interval UTCTime) UTCTime)

readTime :: EventData -> Maybe DateChange
readTime v = case unsafeFromJSON v of
        [i,a,e]  -> (,) <$> Just i <*>
          ((\i j ->
                 Left $
                 Interval.interval
                     (Interval.Finite i, True)
                     (Interval.Finite j, True)) <$>
           parseISO8601 a <*>
           parseISO8601 e)
        [i,a] -> (,) <$> Just i <*> (Right <$> parseISO8601 a)

eventClick:: Element -> Event String
eventClick el = fmap fst $ filterJust $ readTime <$> domEvent "eventClick" el

eventDrop :: Element -> Event DateChange
eventDrop el = filterJust $ readTime <$> domEvent "eventDrop" el

eventDragDrop :: Element -> Event DateChange
eventDragDrop el = filterJust $ readTime <$> domEvent "drop" el

eventResize :: Element -> Event DateChange
eventResize el = filterJust $ readTime <$> domEvent "eventResize" el
