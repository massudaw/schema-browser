{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module TP.Selector (tableOrder,calendarSelector,positionSel,tableChooser,selectFromTable) where

import TP.View
import Control.Monad.Writer (runWriterT, WriterT(..))
import Control.Lens (_1, _2, (^.), over)
import Safe
import qualified NonEmpty as Non
import Data.Char
import Step.Common
import Query
import Step.Host
import Data.Time
import Text
import qualified Types.Index as G
import Data.Bifunctor (first)
import Debug.Trace
import Types
import SchemaQuery
import TP.Widgets
import Prelude hiding (head)
import TP.QueryWidgets
import Control.Monad.Reader
import Data.Ord
import Utils
import Schema
import Types.Patch
import Data.Maybe
import Reactive.Threepenny hiding (apply)
import qualified Data.List as L
import qualified Data.ByteString.Char8 as BS
import RuntimeTypes
import OAuthClient
import qualified Graphics.UI.Threepenny as UI
import Graphics.UI.Threepenny.Core hiding (get, delete, apply)
import Data.Monoid hiding (Product(..))
import qualified Data.Foldable as F
import qualified Data.Text as T
import Data.Text (Text)
import qualified Data.Set as S
import qualified Data.Map as M
import GHC.Stack


calendarSelector = do
    let buttonStyle k e = e # set UI.text (fromJust $ M.lookup k transRes)# set UI.class_ "btn-xs btn-default buttonSet"
          where transRes = M.fromList [("year","Ano"),("month","Mês"),("week","Semana"),("day","Dia"),("hour","Hora")]
        defView = "week"
        viewList = ["year","month","day","week","hour"] :: [String]
        capitalize (i:xs) = toUpper i : xs
        capitalize [] = []

    iday <- liftIO getCurrentTime
    resolution <- fmap (fromMaybe defView) <$> buttonDivSetT  viewList (pure id) (pure $ Just defView ) (const UI.button)  buttonStyle

    next <- UI.button  # set text ">"
    today <- UI.button # set text "Hoje"
    prev <- UI.button  # set text "<"


    current <- UI.div # set children [prev,today,next]
    nextE <- UI.click next
    prevE <- UI.click prev
    todayE <- UI.click today
    let
      currentE = concatenate <$> unions  [ resRange False  <$> facts (triding resolution) <@ nextE
                                       , resRange True   <$> facts (triding resolution) <@ prevE
                                       , const (const iday) <$> todayE ]
    increment <- ui $ accumB iday  currentE
    let incrementT =  tidings increment (flip ($) <$> increment <@> currentE)

    -- currentOutput <- UI.div # sink text (fmap show $ (\i j -> (resRange False i j ,resRange True i j))<$>  facts (triding resolution) <*> facts incrementT )
    sidebar <- UI.div # set children [current,getElement resolution]
    return (sidebar,(incrementT,triding resolution))

positionSel = do
    cpos <-UI.div
    bcpos <-UI.button # set text "Localização Atual"
    (e,h) <- ui $ newEvent
    positionB <- ui $ stepper Nothing (Just <$>e)
    let
    bcpose <- UI.click bcpos
    onEventFT bcpose  (\_ -> runFunction $ ffi "fireCurrentPosition(%1)" bcpos)
    onEventFT (currentPosition bcpos ) (liftIO. h )
    runFunction $ ffi "fireCurrentPosition(%1)" bcpos
    return (bcpos,tidings positionB (diffEvent positionB  (Just <$> e)))



tableUsage inf orderMap table selection = (L.elem table (M.keys selection), tableOrder inf table orderMap )

tableChooser :: InformationSchemaKV Key Showable
                      -> [Table]
                      -> Tidings ( Tidings (Table -> Text) -> Table -> (Element) -> UI Element)
                      -> Tidings (TableK Key -> Bool)
                      -> Text
                      -> Text
                      -> Tidings [TableK Key]
                      -> UI
                           (
                            TrivialWidget (M.Map (TableK Key) [TableK Key]))
tableChooser  inf tables legendStyle tableFilter iniSchemas iniUsers iniTables = do
  let
      pred2 =  [(keyRef ["schema"],Left (int $ schemaId inf  ,Equals))]
      authPred =  [(keyRef ["grantee"],Left ( int $ fst $ username inf ,Equals))] <> pred2
  (orddb ,authorization,translation) <- ui $ transactionNoLog  (meta inf) $
      (,,) <$> (fst <$> (selectFromTable "ordering"  Nothing Nothing []  pred2))
           <*> (fst <$> (selectFromTable "authorization" Nothing Nothing [] authPred))
           <*> (fst <$> (selectFromTable "table_name_translation" Nothing Nothing []  pred2 ))
  filterInp <- UI.input # set UI.style [("width","100%")]
  filterInpE <- UI.valueChange filterInp
  filterInpBh <- ui $ stepper "" (T.pack <$> filterInpE)
  let filterInpT = tidings filterInpBh (T.pack <$> filterInpE )

  let
      -- Table Description
      lookDescT = (\i table -> lookDesc inf table i)<$> collectionTid translation
      -- Authorization
      authorize =  (\autho t -> isJust $ G.lookup (idex  (meta inf) "authorization"  [("schema", int (schemaId inf) ),("table",int $ tableUnique t),("grantee",int $ fst $ username inf)]) autho)  <$> collectionTid authorization
      -- Text Filter
      filterLabel = (\j d -> (\i -> T.isInfixOf (T.toLower j) (T.toLower  $ d i)))<$> filterInpT <*> lookDescT
      -- Usage Count
  all <- checkedWidget (pure False)
  bset <- mdo
    let

        buttonString k = do
          b <- UI.input # set UI.type_ "checkbox"
          chkE <- UI.checkedChange b
          let un = rawUnion k
              ev = (k,) . (\b -> if b then (if L.null un then [k] else un) else [])<$>chkE
          return (k,(b,ev))

    let
      visible  = (\i j k sel tb -> (i tb && j tb && k tb ) || (L.elem [tb] sel)) <$> filterLabel <*> authorize <*> tableFilter <*> triding bset

    let allTablesSel True = M.fromList . fmap  (\e -> (e,). (\i ->  if L.null (rawUnion i) then [i] else rawUnion  i)  $ e ) $ tables
        allTablesSel False = M.empty
        iniSel =  M.fromList . fmap  (\e -> (e,). (\i ->  if L.null (rawUnion i) then [i] else rawUnion  i)  $ e ) <$> iniTables
    iniValue <- currentValue (facts iniSel)
    let iniEvent = (unionWith const (rumors iniSel ) (allTablesSel <$> rumors (triding all)))
    iniBehaviour <- ui $ stepper iniValue  iniEvent

    bset <- checkDivSetTGen tables ((\i k j -> tableUsage inf i j k ) <$> collectionTid orddb <*> triding bset) (tidings iniBehaviour iniEvent ) buttonString ((\lg visible i j -> (if visible  i then (lg lookDescT i j # set UI.class_ "table-list-item" ) else UI.div # set children [j] )# set UI.style (noneDisplay "-webkit-box" $ visible i)) <$> legendStyle <*> visible )
    return bset
  let
      ordRow orderMap pkset =  field
          where
            field =  G.lookup pk orderMap
            pk = idex (meta inf ) "ordering" [("table",int $ tableUnique  pkset ), ("schema",int $ schemaId inf)]
              {-incClick field =  (fst field , G.getIndex field ,[patch $ fmap (+SNumeric 1) usage])
          where
            usage = lookAttr' (meta inf ) "usage"   field

  ui $ onEventDyn ((\i j -> fmap incClick <$> (ordRow i <$> M.keys j)) <$> facts (collectionTid orddb) <@> rumors (triding bset)
              )
    (traverse (traverse (\p -> do
      _ <- transactionNoLog (meta inf ) $ patchFrom  p
      putPatch (patchVar $  iniRef orddb) [p] )))
-}
  element bset # set UI.style [("overflow","auto"),("height","99%")]
  header <- UI.div # set children [getElement all,filterInp] # set UI.style [("display","inline-flex")]
  tbChooserI <- UI.div # set children [header,getElement bset]  # set UI.style [("height","50vh")]
  return $ (TrivialWidget (triding bset) tbChooserI)


