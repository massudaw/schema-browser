{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module TP.Agenda where

import qualified Data.Interval as Interval
import Data.Time.Calendar.WeekDate
import qualified NonEmpty as Non
import Data.Char
import qualified Data.Text.Encoding as TE
import Query
import Data.Time
import qualified Data.Aeson as A
import Text
import qualified Types.Index as G
import Data.Bifunctor (first)
import Debug.Trace
import Types
import SchemaQuery
import Plugins
import TP.Widgets
import PostgresQuery (postgresOps,connRoot)
import SortList
import Prelude hiding (head)
import TP.QueryWidgets
import Control.Monad.Reader
import Control.Concurrent
import Data.Functor.Apply
import System.Environment
import Network.Google.OAuth2 (OAuth2Tokens(..))
import Data.Ord
import Utils
import Schema
import Types.Patch
import Data.Char (toLower)
import Data.Maybe
import Reactive.Threepenny hiding(apply)
import Data.Traversable (traverse)
import qualified Data.List as L
import qualified Data.ByteString.Char8 as BS
import qualified Data.ByteString.Lazy.Char8 as BSL

import RuntimeTypes
import OAuthClient
import qualified Graphics.UI.Threepenny as UI
import Graphics.UI.Threepenny.Core hiding (get,delete,apply)
import Data.Monoid hiding (Product(..))

import qualified Data.Foldable as F
import qualified Data.Text as T
import Data.Text (Text)
import qualified Data.Set as S

import Database.PostgreSQL.Simple
import qualified Data.Map as M
calendarCreate m cal def evs= runFunction $ ffi "$(%1).fullCalendar({header: { left: '',center: 'title' , right: ''},defaultDate: %2,lang: 'pt-br',editable: true,eventLimit: true,events: JSON.parse(%3), defaultView : %4 });" cal def evs m

eventWidget inf body = do
    (_,(_,tmap)) <- liftIO $ transaction (meta inf) $ selectFrom "table_name_translation" Nothing Nothing [] [("=",liftField (meta inf) "table_name_translation" $ uncurry Attr $("schema_name",TB1 $ SText (schemaName inf) ))]
    (evdb,(_,evMap )) <- liftIO $ transaction  (meta inf) $ selectFrom "event" Nothing Nothing [] [("=",liftField (meta inf) "event" $ uncurry Attr $("schema_name",TB1 $ SText (schemaName inf) ))]
    dashes <- mapM (\e -> do
        let t@(Attr _ (TB1 (SText tname))) = lookAttr' (meta inf) "table_name" e
            lookDesc = (\i  -> maybe (T.unpack $ tname)  ((\(Attr _ v) -> renderShowable v). lookAttr' (meta inf)  "translation") $ G.lookup (idex (meta inf) "table_name_translation" [("schema_name" ,txt $ schemaName inf),("table_name",txt tname )]) i ) $ tmap

            (Attr _ (ArrayTB1 efields ))= lookAttr' (meta inf) "event" e
            (Attr _ color )= lookAttr' (meta inf) "color" e

        (evdb,(_,tmap )) <- liftIO $ transaction  inf $ selectFrom tname Nothing Nothing [] []
        let v = F.toList evMap
            convField (Attr _ (IntervalTB1 i )) = [("start", (\(Interval.Finite i) -> i)$ Interval.lowerBound i),("end",(\(Interval.Finite i) -> i)$ Interval.upperBound i)]
            convField (Attr _ v) = [("start",v)]
            projf  r efield@(TB1 (SText field))  = M.fromList $ convField (lookAttr' inf field r) <> [ ("title",TB1 $ SText (T.pack $  L.intercalate "," $ fmap renderShowable $ allKVRec' $  r)) , ("color" , color),("field", efield )] :: M.Map Text (FTB Showable)
            proj r = projf r <$> F.toList efields
        return ((lookDesc,color),filter (isJust . join . fmap unSOptional . M.lookup "start") $concat $ proj <$> G.toList tmap)) ( G.toList evMap)

    iday <- liftIO getCurrentTime
    filterInp <- UI.input # set UI.style [("width","100%")]
    filterInpBh <- stepper "" (UI.valueChange filterInp)
    let allTags =  (fst <$> dashes)
        filterLabel d = (\j ->  L.isInfixOf (toLower <$> j) (toLower <$> d)) <$> filterInpBh
        legendStyle (t,c) b
              =  UI.div
              # set items [UI.div # set items [b], UI.div # set text  t ]
              # sink0 UI.style (mappend [("background-color",renderShowable c),("color","white")]. noneDisplay "-webkit-box" <$> filterLabel t)

    legend <- checkDivSetT  allTags  (pure id) (pure allTags) (\_ -> UI.input # set UI.type_ "checkbox") legendStyle
    let buttonStyle k e = e # set UI.text (fromJust $ M.lookup k transRes)# set UI.class_ "btn-xs btn-default buttonSet"
          where transRes = M.fromList [("month","Mês"),("week","Semana"),("day","Dia")]
        defView = "month"
        viewList = ["month","day","week"] :: [String]
        transMode _ "month" = "month"
        transMode True i = "agenda" <> capitalize i
        transMode False i = "basic" <> capitalize i
        capitalize (i:xs) = toUpper i : xs
        capitalize [] = []

    resolution <- fmap (fromMaybe defView) <$> buttonDivSetT  viewList (pure id) (pure $ Just defView ) (const UI.button)  buttonStyle

    next <- UI.button  # set text ">"
    today <- UI.button # set text "Hoje"
    prev <- UI.button  # set text "<"
    agenda <- mdo
      agenda <- UI.button # sink text ((\b -> if b then "Agenda" else "Basic") <$> agB)
      let agE = pure not <@ UI.click agenda
      agB <- accumB False agE
      return $ TrivialWidget (tidings agB (flip ($) <$> agB <@> agE)) agenda

    current <- UI.div # set children [prev,today,next]
    let
      resRange b "month" d =  d {utctDay = addGregorianMonthsClip (if b then -1 else 1 )  (utctDay d)}
      resRange b "day" d = d {utctDay =addDays (if b then -1 else 1 ) (utctDay d)}
      resRange b "week" d = d {utctDay =addDays (if b then -7 else 7 ) (utctDay d)}
    let currentE = (concatenate <$> unions  [resRange False  <$> facts (triding resolution) <@ UI.click next ,resRange True   <$> facts (triding resolution) <@ UI.click prev , const (const iday) <$> UI.click today ])
    increment <- accumB iday  currentE

    calendar <- UI.div # set UI.class_ "col-xs-10"
    sidebar <- UI.div # set children [getElement agenda,current,getElement resolution,filterInp , getElement legend] #  set UI.class_ "col-xs-2"
    element body # set children [sidebar,calendar]
    let calFun (agenda,iday,res ,selected) = do
            innerCalendar <-UI.div
            element calendar # set children [innerCalendar]
            let

              inRange "day" d (SDate c)=   d == c
              inRange "week" d (SDate c)=    oy == cy && ow == cw
                where
                  (oy,ow,_) = toWeekDate d
                  (cy,cw,_) = toWeekDate c
              inRange "month" d (SDate c)=   oy == cy && od == cd
                where
                  (oy,od,_) = toGregorian d
                  (cy,cd,_) = toGregorian c
              inRange m d (STimestamp c)=   inRange m d (SDate (utctDay (localTimeToUTC utc c)))

            calendarCreate (transMode agenda res) innerCalendar (show iday) (T.unpack $ TE.decodeUtf8 $  BSL.toStrict $ A.encode  (filter (inRange res (utctDay iday ) . unTB1 . fromJust . join . fmap unSOptional. M.lookup "start"  ) $ concat $fmap snd ( filter (flip L.elem (selected) . fst) dashes)))
            return ()
    calFun (False,iday,defView, allTags)
    onEvent (rumors $ (,,,) <$> triding agenda <*> tidings increment (flip ($) <$> increment <@> currentE) <*>(triding resolution) <*> (triding legend)) calFun
    return body

txt = TB1. SText

instance A.ToJSON a => A.ToJSON (FTB a ) where
  toJSON (TB1 i) = A.toJSON i
  toJSON (LeftTB1 i) = fromMaybe (A.toJSON ("" ::String)) (A.toJSON <$> i)

instance A.ToJSON Showable where
  toJSON (SText i ) = A.toJSON i
  toJSON i = A.toJSON (renderPrim i)



