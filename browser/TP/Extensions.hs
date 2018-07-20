module TP.Extensions where

import TP.View
import TP.QueryWidgets
import TP.Selector
import Safe
import qualified NonEmpty as Non
import Data.Maybe
import Data.Char
import Step.Common
import Query
import Step.Host
import Data.Time
import qualified Types.Index as G
import Data.Bifunctor (first)
import Debug.Trace
import Types
import SchemaQuery
import TP.Widgets
import Prelude hiding (head)
import Control.Monad.Reader
import Data.Ord
import Environment
import Utils
import Types.Patch
import Data.Maybe
import Reactive.Threepenny hiding (apply)
import qualified Data.List as L
import qualified Data.ByteString.Char8 as BS
import RuntimeTypes
import qualified Graphics.UI.Threepenny as UI
import Graphics.UI.Threepenny.Core hiding (get, delete, apply)
import Data.Monoid hiding (Product(..))
import qualified Data.Foldable as F
import qualified Data.Text as T
import qualified Data.Set as S
import qualified Data.Map as M
import GHC.Stack


configExtension inf model view = do
    choose <- buttonDivSet ["Main","Config"] (pure $ Just "Main") (\i ->  UI.button # set text i # set UI.class_ "buttonSet btn-xs btn-default pull-right")
    (legendStyle,dashes,viewW) <- view
    let
      minf = meta inf
      chooser "Config" = do
        let setupTables = (L.filter ((/=ReadOnly) .rawTableType.fst) $ (\(t,p) -> (lookTable minf t,tablePredicate minf t p)) <$>  tablesV (staticP (model inf)))
        headers <- buttonDivSet setupTables (pure $ safeHead setupTables) (\(i,_) ->  UI.button # set text (T.unpack $ tableName i) # set UI.class_ "pull-left buttonSet btn-md btn-default")
        tables <-  traverseUI (\(table ,pred)-> do
          tname <-UI.h4 # set text (T.unpack $ tableName table )
          tpred <-UI.h5 # set text (show pred)
          reftb@(vptmeta,vpt,_,var) <- ui $ refTables' minf table Nothing pred
          config <- selector minf table reftb  (pure (Just pred)) (pure Nothing)
          let tds = triding config
          LayoutWidget pretdi cru _ <- crudUITable minf table reftb mempty [] (allRec' (tableMap minf) table) (triding config)
          UI.div # set children [tname,tpred,getElement config,cru]) (triding headers)
        body <- UI.div # sink children (pure <$> facts tables) # set UI.class_ "row"
        element headers  # set UI.class_ "row"
        pure <$> UI.div # set children [getElement headers, body]
      chooser "Main" = do
        viewW
    els <- traverseUI chooser (triding choose)
    content <- UI.div # sink children (facts els)
    element choose
    out <- UI.div
      # set children [getElement choose,content]
      # set UI.style [("overflow","auto")]
    return  ((legendStyle , dashes ),out)



