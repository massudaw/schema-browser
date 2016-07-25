{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module TP.Map where

import Step.Host
import GHC.Stack
import Control.Concurrent
import Control.Lens ((^.),_1,_2)
import Safe
import Control.Concurrent.Async
import qualified Data.Interval as Interval
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

createLayers el Nothing evs= runFunction $ ffi "createLayers (%1,null,null,null,%2)" el evs
createLayers el (Just (p,ne,sw)) evs= runFunction $ ffi "createLayers (%1,%2,%3,%4,%5)" el (show p) (show ne) (show sw) evs
calendarCreate el Nothing evs= runFunction $ ffi "createMap (%1,null,null,null,%2)" el evs
calendarCreate el (Just (p,ne,sw)) evs= runFunction $ ffi "createMap (%1,%2,%3,%4,%5)" el (show p) (show ne) (show sw) evs


mapWidget body sel inf = do
    (_,(_,tmap)) <- liftIO $ transactionNoLog (meta inf) $ selectFrom "table_name_translation" Nothing Nothing [] (LegacyPredicate [("=",liftField (meta inf) "table_name_translation" $ uncurry Attr $("schema_name",TB1 $ SText (schemaName inf) ))])
    (evdb,(_,evMap )) <- liftIO $ transactionNoLog  (meta inf) $ selectFrom "geo" Nothing Nothing [] (LegacyPredicate [("=",liftField (meta inf) "geo" $ uncurry Attr $("schema_name",TB1 $ SText (schemaName inf) ))])
    cliZone <- jsTimeZone
    dashes <- liftIO $ mapConcurrently (\e -> do
        let (Attr _ (TB1 (SText tname))) = lookAttr' (meta inf) "table_name" e
            lookDesc = (\i  -> maybe (T.unpack $ tname)  ((\(Attr _ v) -> renderShowable v). lookAttr' (meta inf)  "translation") $ G.lookup (idex (meta inf) "table_name_translation" [("schema_name" ,txt $ schemaName inf),("table_name",txt tname )]) i ) $ tmap
            (Attr _ (ArrayTB1 efields ))= lookAttr' (meta inf) "geo" e
            (Attr _ color )= lookAttr' (meta inf) "color" e
            (Attr _ size )= lookAttr' (meta inf) "size" e
        evdb <- refTable inf (lookTable inf tname)
        let
            projf  r efield@(TB1 (SText field))  = fmap (\i ->  HM.fromList $ i <> [("title"::Text , TB1 $ SText $ (T.pack $  L.intercalate "," $ fmap renderShowable $ allKVRec' $  r)),("size", size),("color",  color)]) $ join $ convField <$> indexFieldRec (indexer field) r
            proj r = projf r <$> F.toList efields
            convField (Attr k (LeftTB1 v)) = join $ convField . Attr k <$> v
            convField (Attr _ (TB1 v )) = Just $ to $ v
              where to p@(SPosition (Position (y,x,z) ))  =  [("position",TB1 p )]
            convField i  = errorWithStackTrace (show i)
        return ((lookDesc,(color,tname,efields)), catMaybes . concat . fmap proj  . G.toList  <$> collectionTid evdb)) ( G.toList evMap)


    filterInp <- UI.input # set UI.style [("width","100%")]
    filterInpBh <- stepper "" (UI.valueChange filterInp)
    let allTags =  (fst <$> dashes)
        filterLabel d = (\j ->  L.isInfixOf (toLower <$> j) (toLower <$> d)) <$> filterInpBh
        legendStyle table (b,_)
            =  do
              let item = M.lookup (tableName (fromJust $ M.lookup table (pkMap inf))) (M.fromList  $ fmap (\i@(t,(a,b,c))-> (b,i)) allTags)
              maybe (UI.div) (\(k@(t,(c,_,_))) ->
                UI.div # set items [UI.div
                  # set items [element b # set UI.class_ "col-xs-1", UI.div # set text  t #  set UI.class_ "fixed-label col-xs-11" # set UI.style [("background-color",renderShowable c)] ]
                  # set UI.style [("background-color",renderShowable c)]]) item



    cpos <- UI.div
    bcpos <- UI.button # set text "Localização Atual"
    calendar <- UI.div # set UI.class_ "col-xs-10"
    sidebar <- UI.div # set children [bcpos,cpos]#  set UI.class_ "col-xs-2"
    element body # set children [sidebar,calendar]
    (e,h) <- liftIO$ newEvent
    positionB <- stepper Nothing (Just <$>e)
    element cpos # sink text (show <$> positionB)
    let
      calFun selected = do
        innerCalendar <-UI.div # set UI.id_ "map"
        pb <- currentValue positionB
        element calendar # set children [innerCalendar]
        calendarCreate  innerCalendar pb ("[]"::String)
        let ev = moveend innerCalendar
        fin <- onEvent ev (liftIO . h )
        onEvent (UI.click bcpos) (\_ -> runFunction $ ffi "fireCurrentPosition(%1)" innerCalendar)
        liftIO$ onEventIO (currentPosition innerCalendar ) (liftIO. h .traceShowId )
        liftIO $ addFin innerCalendar [fin]
        let
          pruneBounds positionB r= isJust $ join $ (\pos (_,ne,sw) -> if Interval.member pos ( Interval.interval (makePos sw) (makePos ne)) then Just pos else  Nothing)<$> (HM.lookup "position" r) <*>  positionB
        (inner ,fin)<- mapUITEventFin innerCalendar (\(dashes ,positionB)-> do
          createLayers innerCalendar positionB (T.unpack $ TE.decodeUtf8 $  BSL.toStrict $ A.encode  $ fmap (filter (pruneBounds positionB)) dashes )
          return ()
          ) $ liftA2 (,) (foldr (liftA2 (:)) (pure []) $fmap snd ( filter (flip L.elem (selected) . fst) dashes)) (tidings positionB (Just <$> e))
        liftIO$ addFin innerCalendar [fin]
        return ()
    pb <- currentValue positionB
    (_,fin) <- mapUITEventFin calendar calFun (((\i j -> filter (flip L.elem (tableName <$> concat (F.toList i)) .  (^. _2._2)) j )<$> sel <*> pure allTags))
    liftIO$ addFin calendar [fin]
    liftIO $ mapConcurrently (\(_,(_,tname,fields))-> do
        mapTEvent  (traverse (\(_,ne,sw) ->  forkIO $ void $ transactionNoLog  inf $ selectFromA tname Nothing Nothing [] (WherePredicate $ OrColl $ PrimColl . (,"<@",(IntervalTB1 $ Interval.interval (makePos sw) (makePos ne))) . indexer . T.pack . renderShowable <$> F.toList fields))) (tidings positionB (Just <$> e))
      ) allTags
    return (legendStyle,dashes)

makePos [b,a,z] = (Interval.Finite $ TB1 $ SPosition (Position (a,b,z)),True)
makePos i = errorWithStackTrace (show i)

txt = TB1. SText

readPosition:: EventData -> Maybe ([Double],[Double],[Double])
readPosition (v) = (,,) <$> readP i a z <*> readP ni na nz <*>readP si sa sz
  where
     [i,a,z,ni,na,nz,si,sa,sz] = unsafeFromJSON v

readP i a z = (\i j z-> [i,j, z]) <$> readMay i<*> readMay a <*> readMay z

currentPosition :: Element -> Event ([Double],[Double],[Double])
currentPosition el = filterJust $ readPosition<$>  domEvent "currentPosition" el

moveend :: Element -> Event ([Double],[Double],[Double])
moveend el = filterJust $ readPosition <$>  domEvent "moveend" el

instance A.ToJSON a => A.ToJSON (FTB a ) where
  toJSON (TB1 i) = A.toJSON i
  toJSON (LeftTB1 i) = fromMaybe (A.toJSON ("" ::String)) (A.toJSON <$> i)

instance A.ToJSON Showable where
  toJSON (SText i ) = A.toJSON i
  toJSON (SPosition (Position (y,x,z))) = A.Array $ V.fromList [A.String $ T.pack (show x),A.String $ T.pack (show y),A.String $ T.pack (show z)]
  toJSON i = A.toJSON (renderPrim i)



