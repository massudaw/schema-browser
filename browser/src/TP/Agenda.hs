{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module TP.Agenda (eventWidget,agendaDefS,eventWidgetMeta,testAgendaDef) where

import TP.AgendaSelector
import Control.Monad.Writer as Writer
import Debug.Trace
import Query
import Text
import SchemaQuery
import TP.Widgets
import Prelude hiding (head)
import TP.QueryWidgets
import Reactive.Threepenny hiding (apply)
import RuntimeTypes
import qualified Graphics.UI.Threepenny as UI
import Graphics.UI.Threepenny.Core hiding (get, delete, apply)
import qualified Data.Foldable as F
import qualified Data.Text as T
import qualified Data.Map as M


eventWidget (incrementT,resolutionT) sel inf cliZone = do
    v <-  fmap F.toList <$> ui ( runMetaArrow inf agendaDefS)
    dashes <- currentValue (facts v)
    let
      legendStyle dashes lookDesc table b =
        let item = M.lookup table (M.fromList  $ fmap (\i@(a,b,c,_)-> (b,i)) dashes)
        in traverse (\k@(c,tname,_,_) -> do
          element  b # set UI.class_"col-xs-1"
          label <- UI.div
            # set text  (T.unpack  lookDesc)
            # set UI.class_ "fixed-label col-xs-10"
          UI.label
            # set children [b,label]
            # set UI.style [("background-color",renderShowable c)]
            # set UI.class_ "table-list-item"
            # set UI.style [("display","-webkit-box")]
            ) item
      chooser = do
        agenda <- buttonDivSet [Basic,Agenda,Timeline] (pure $ Just Basic) (\i -> UI.button # set text (show i) # set UI.class_ "buttonSet btn-xs btn-default pull-left")
        out <- traverseUI id $ (\i j k -> calendarView inf Nothing cliZone i  sel j k (pure Nothing)  ) <$>  v <*> triding agenda <*> resolutionT <*> incrementT
        selector <- UI.div 
        traverseUI (traverseUI (traverse (\(t,tdi) -> do
          reftb <- ui $ refTables inf t
          out3<- crudUITable inf  t reftb mempty [] (allRec' (tableMap inf) t) (pure (Just tdi))
          element selector # set UI.children [getElement out3]))
                               )  (fmap snd out)
        calendar <- UI.div # sink UI.children (facts $ fmap fst out )
        return [getElement agenda,calendar,selector]
    return  (legendStyle <$> v,  v ,chooser )


