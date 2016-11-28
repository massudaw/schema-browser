{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module TP.Chart (chartWidget) where

import GHC.Stack
import qualified NonEmpty as Non
import Step.Host
import Control.Monad.Writer as Writer
import TP.View
import qualified Data.Interval as Interval
import Control.Concurrent
import Utils
import Types.Patch
import Control.Arrow
import Control.Lens ((^.), _1, mapped,_2, _3,_4)
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

calendarCreate cal def = runFunction $ ffi "createChart(%1,%2)" cal def

calendarAddSource cal t fields evs = runFunction $ ffi "addChartColumns(%1,%2,%3,%4)" cal (tableName t) fields evs
calendarRemoveSource cal t = runFunction $ ffi "removeChartColumns(%1,%2)" cal (tableName t)

chartWidget body (incrementT,resolutionT) (_,_,_,positionB) sel inf cliZone = do
    let

      schId = int (schemaId inf)
      schemaPred = [(keyRef ["schema"],Left (schId,Equals))]

    dashes <- ui$ do
      (_,(_,emap )) <-transactionNoLog  (meta inf) $ selectFromTable "event" Nothing Nothing [] schemaPred
      (_,(_,geomap )) <-transactionNoLog  (meta inf) $ selectFromTable "geo" Nothing Nothing [] schemaPred
      evMap <- transactionNoLog (meta inf) $ do
        (_,(_,evMap )) <- selectFromTable "metrics" Nothing Nothing [] schemaPred
        return evMap
      return $ fmap (\e ->
        let
            Just (TB1 (SText tname)) = unSOptional' $  _tbattr $ lookAttr' (meta inf) "table_name" $ unTB1 $ _fkttable $ lookAttrs' (meta inf) ["schema","table"] e
            table = lookTable inf tname
            tablId = int (_tableUnique table)
            Just (Attr _ (ArrayTB1 efields ))= indexField (liftAccess (meta inf )"metrics" $ keyRef ["metrics"]) e
            -- Just (Attr _ (ArrayTB1 timefields ))= indexField (liftAccess (meta inf )"event" $ keyRef ["event"]) e
            timeFields = fmap (unArray._tbattr) $ join $ indexField  (liftAccess (meta inf) "event" $ keyRef ["event"])  <$> G.lookup (idex (meta inf) "event" [("schema" ,schId ),("table",tablId )])  emap
            geoFields = fmap (unArray._tbattr) $ join $ indexField  (liftAccess (meta inf) "geo" $ keyRef ["geo"])  <$> G.lookup (idex (meta inf) "geo" [("schema" ,schId ),("table",tablId )])  geomap
            (Attr _ color )= lookAttr' (meta inf) "color" e
            projf  r efield  = M.fromList [("value" ,ArrayTB1 $  attr <$> efield), ("title",txt (T.pack $  L.intercalate "," $ fmap renderShowable $ allKVRec' $  r)) , ("table",txt tname),("color" , txt $ T.pack $ "#" <> renderShowable color )] :: M.Map Text (FTB Showable)
              where attr  (TB1 (SText field)) = _tbattr $ unTB $justError ("no attr " <> show field) (findAttr [lookKey inf tname field] r)
            isKInterval (KInterval i) = True
            isKInterval (KOptional i) = isKInterval i
            isKInterval (Primitive i ) = False
            isKInterval i = False

            proj r = (txt (T.pack $  L.intercalate "," $ fmap renderShowable $ allKVRec' $  r),)$  projf r efields
            attrValue (Attr k v) = v
         in (txt $ T.pack $ "#" <> renderShowable color ,lookTable inf tname,F.toList efields,(timeFields,geoFields),proj) ) ( G.toList evMap)

    iday <- liftIO getCurrentTime
    let
      legendStyle  lookDesc table b
            =  do
              let item = M.lookup table (M.fromList  $ fmap (\i@(a,b,c,t,_)-> (b,i)) dashes)
              maybe UI.div (\(k@((c,tname,_,_,_))) -> mdo
                expand <- UI.input # set UI.type_ "checkbox" # sink UI.checked evb # set UI.class_ "col-xs-1"
                evc <- UI.checkedChange expand
                evb <- ui $ stepper False evc
                missing <- UI.div  # set UI.style [("width","100%"),("height","150px") ,("overflow-y","auto")] # sink UI.style (noneShow <$> evb)
                header <- UI.div
                  # set items [element b # set UI.class_"col-xs-1", UI.div # sink text  (T.unpack .($table) <$> facts lookDesc ) # set UI.class_ "fixed-label col-xs-10", element expand ]
                  # set UI.style [("background-color",renderShowable c)]
                UI.div # set children [header,missing]
                  ) item
    calendar <- UI.div # set UI.class_ "col-xs-10"
    element body # set children [calendar]
    let inpCal = sel
    let calFun (resolution,incrementT,positionB) = mdo
            let
              evc = eventClick calendar
            edits <- ui$ accumDiff (\(tref,_)->  evalUI calendar $ do
              charts <- UI.div  # set UI.style [("height", "300px"),("width", "900px")]
              calendarCreate  charts (show incrementT)
              let ref  =  (\i j ->  L.find ((== i) .  (^. _2)) j ) tref dashes
              traverse (\((_,t,fields,(timeFields,geoFields),proj))-> do
                    let pred = fromMaybe mempty (fmap (\fields -> WherePredicate $  timePred inf t (fieldKey <$> fields) (incrementT,resolution)) timeFields  <> liftA2 (\field pos-> WherePredicate $ geoPred inf t(fieldKey <$>  field) pos ) geoFields positionB )
                        fieldKey (TB1 (SText v))=   v
                    reftb <- ui $ refTables' inf t Nothing pred
                    let v = fmap snd $ reftb ^. _1
                    let evsel = (\j (tev,pk,_) -> if tev == t then Just ( G.lookup pk j) else Nothing  ) <$> facts (v) <@> fmap (readPK inf . T.pack ) evc
                    tdib <- ui $ stepper Nothing (join <$> evsel)
                    let tdi = tidings tdib (join <$> evsel)
                    (el,ediff,_) <- crudUITable inf ((\i -> if isJust i then "+" else "-") <$> tdi)  reftb [] [] (allRec' (tableMap inf) $ t)  tdi
                    ui $ onEventDyn (pure <$> ediff) (liftIO .  putPatch (reftb ^. _4 ))
                    mapUIFinalizerT charts
                      (\i -> do
                        calendarAddSource charts t (renderShowable <$> fields ) ((T.unpack . TE.decodeUtf8 .  BSL.toStrict . A.encode  .   fmap (snd.proj) $ G.toList i))
                        ui $ registerDynamic (fmap fst $ runDynamic $ evalUI charts $ calendarRemoveSource charts t))
                       (v)
                    mapM (\i -> element i # sink UI.style  (noneShow . isJust <$> tdib)) el
                    UI.div # set children (charts:el) # set UI.class_ "row"
                                   ) ref) inpCal

            element calendar # sink children ( catMaybes .F.toList <$> facts edits)


    onFFI "google.charts.setOnLoadCallback(%1)" (evalUI body $  mapUIFinalizerT calendar calFun ((,,) <$> resolutionT <*> incrementT <*> positionB))

    return  (legendStyle , dashes )


onFFI ff handler = do
    (e,h) <- ui $ newEvent
    obj <- ffiExport (void $ (runDynamic $ handler) >>= h . snd )
    runFunction $ ffi ff obj
    onEvent e (ui . registerDynamic . sequence_)



type DateChange = (String, Either (Interval UTCTime) UTCTime)

-- readPosition:: EventData -> Maybe DateChange
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
eventDragDrop el = filterJust $ readTime <$> domEvent "externalDrop" el

eventResize :: Element -> Event DateChange
eventResize el = filterJust $ readTime <$> domEvent "eventResize" el
