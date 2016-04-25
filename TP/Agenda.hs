{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module TP.Agenda where

import GHC.Stack
import Step.Host
import qualified Data.Interval as Interval
import Control.Concurrent
import Types.Patch
import Control.Arrow
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
calendarCreate m cal def evs= runFunction $ ffi "createAgenda(%1,%2,%3,%4)"  cal def evs m
calendarAddSource cal t evs= runFunction $ ffi "addSource(%1,%2,%3)"  cal t evs

eventWidget inf body = do
    (_,(_,tmap)) <- liftIO $ transactionNoLog (meta inf) $ selectFrom "table_name_translation" Nothing Nothing [] (LegacyPredicate[("=",liftField (meta inf) "table_name_translation" $ uncurry Attr $("schema_name",TB1 $ SText (schemaName inf) ))])
    (evdb,(_,evMap )) <- liftIO $ transactionNoLog  (meta inf) $ selectFrom "event" Nothing Nothing [] (LegacyPredicate[("=",liftField (meta inf) "event" $ uncurry Attr $("schema_name",TB1 $ SText (schemaName inf) ))])
    cliZone <- jsTimeZone
    dashes <- liftIO $ mapConcurrently (\e -> do
        let (Attr _ (TB1 (SText tname))) = lookAttr' (meta inf) "table_name" e
            lookDesc = (\i  -> maybe (T.unpack $ tname)  ((\(Attr _ v) -> renderShowable v). lookAttr' (meta inf)  "translation") $ G.lookup (idex (meta inf) "table_name_translation" [("schema_name" ,txt $ schemaName inf),("table_name",txt tname )]) i ) $ tmap
            (Attr _ (ArrayTB1 efields ))= lookAttr' (meta inf) "event" e
            (Attr _ color )= lookAttr' (meta inf) "color" e
        evdb <- refTable inf  (lookTable inf tname )
        let toLocalTime = fmap to
              where to (STimestamp i )  = STimestamp $  utcToLocalTime cliZone $ localTimeToUTC utc i
                    to (SDate i ) = SDate i
            convField ((IntervalTB1 i )) = [("start", toLocalTime $ unFinite $ Interval.lowerBound i),("end",toLocalTime $ unFinite $ Interval.upperBound i)]
            convField (LeftTB1 i) = concat $   convField <$> maybeToList i
            convField (v) = [("start",toLocalTime $v)]
            convField i = errorWithStackTrace (show i)
            projf  r efield@(TB1 (SText field))  = (if (isJust . unSOptional $ attr) then Left else Right) (M.fromList $ convField attr  <> [("id", TB1 $ SText $ writePK r efield   ),("title",TB1 $ SText (T.pack $  L.intercalate "," $ fmap renderShowable $ allKVRec' $  r)) , ("table",TB1 (SText tname)),("color" , color),("field", efield )] :: M.Map Text (FTB Showable))
                  where attr  = attrValue $ lookAttr' inf field r
            proj r = (TB1 $ SText (T.pack $  L.intercalate "," $ fmap renderShowable $ allKVRec' $  r),)$  projf r <$> F.toList efields
            attrValue (Attr k v) = v
        return ((lookDesc,(color,tname,efields)), fmap proj  . G.toList <$> collectionTid evdb  )) ( G.toList evMap)

    iday <- liftIO getCurrentTime
    filterInp <- UI.input # set UI.style [("width","100%")]
    filterInpBh <- stepper "" (UI.valueChange filterInp)
    let allTags =  (fst <$> dashes)
    itemListEl2 <- mapM (\i ->
      (i,) <$> UI.div  # set UI.style [("width","100%"),("height","150px") ,("overflow-y","auto")]) allTags
    let
        filterLabel d = (\j ->  L.isInfixOf (toLower <$> j) (toLower <$> d)) <$> filterInpBh
        legendStyle k@(t,(c,_,_)) b
            =  mdo
              expand <- UI.input # set UI.type_ "checkbox" # sink UI.checked evb # set UI.class_ "col-xs-1"
              let evc = UI.checkedChange expand
              evb <- stepper False evc
              missing <- (element $ fromJust $ M.lookup k (M.fromList itemListEl2)) # sink UI.style (noneShow <$> evb)
              header <- UI.div
                # set items [b # set UI.class_"col-xs-1", UI.div # set text  t # set UI.class_ "col-xs-10", element expand ]
                # sink0 UI.style (mappend [("background-color",renderShowable c),("color","white")]. noneDisplay "-webkit-box" <$> filterLabel t)
              UI.div # set children [header,missing]
                # sink0 UI.style (mappend [("border","solid black 1px"),("background-color",renderShowable c),("color","white")]. noneShow <$> filterLabel t)
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
      currentE = concatenate <$> unions  [resRange False  <$> facts (triding resolution) <@ UI.click next
                                       ,resRange True   <$> facts (triding resolution) <@ UI.click prev , const (const iday) <$> UI.click today ]
    increment <- accumB iday  currentE
    let incrementT =  tidings increment (flip ($) <$> increment <@> currentE)
        rangeT = (\r d -> Interval.interval (Interval.Finite $ resRange True r d,True) (Interval.Finite $ resRange False r d,True))<$> triding resolution <*>  incrementT
    calendar <- UI.div # set UI.class_ "col-xs-10"
    sidebar <- UI.div # set children ([getElement agenda,current,getElement resolution,filterInp , getElement legend]<> (snd <$> itemListEl2)) #  set UI.class_ "col-xs-2"
    element body # set children [sidebar,calendar]

    let calFun (agenda,iday,res ,selected) = do
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
              inRange m d (STimestamp c)=   inRange m d (SDate (localDay (utcToLocalTime utc $ localTimeToUTC cliZone c)))
            let
                visible =  mergeData selectedData
                mergeData selectedData = fmap  concat $ foldr (liftA2 (:)) (pure []) $ snd <$> selectedData
                selectedData = filter (flip L.elem (selected) . fst) dashes
                calHand innerCalendar  visible = calendarCreate (transMode agenda res) innerCalendar (show iday) (T.unpack . TE.decodeUtf8 .  BSL.toStrict . A.encode  . filter (inRange res (utctDay iday ) . unTB1 . fromJust . M.lookup "start") . concat .fmap (lefts  .snd)  $ visible )
            innerCalendar  <- UI.div
            element calendar # set children [innerCalendar]
            let evd = eventDrop innerCalendar
            let evr = eventResize innerCalendar
            let evdd = eventDragDrop innerCalendar
                evs =  fmap (makePatch cliZone . first (readPK inf . T.pack))<$> unions [evr,evdd,evd]
            fin <- onEvent evs (liftIO . transaction inf . mapM (\i -> do
                        patchFrom i >>= traverse (tell . pure )))
            calHand innerCalendar  =<< currentValue   (facts visible)
            fins <- mapM (\((_,(_,t,_)),s)->  fmap snd $ mapUITEventFin innerCalendar (
                      (\i -> do
                      calendarAddSource innerCalendar  (T.unpack t) ((T.unpack . TE.decodeUtf8 .  BSL.toStrict . A.encode  . filter (inRange res (utctDay iday ) . unTB1 . fromJust .  M.lookup "start"  ) . concat . fmap (lefts.snd) $ i)))
                      ) s ) selectedData
            liftIO $ addFin innerCalendar (fin:fins)
            mapM (\(k,el) -> do
              traverse (\t -> do
                element  el
                  # sink items (fmap (\(t,i) -> do
                         h<- UI.div # set text (renderShowable t)
                         b <- UI.div # set items (fmap (\i->do
                           dv <-  UI.div # set text ((maybe "" renderShowable  $M.lookup "field" i )) # set UI.style ([("border","solid black 1px"),("padding-left","10px")]<> (maybeToList $ ("background-color",) . renderShowable<$>  M.lookup "color" i))
                           runFunction $ ffi "$(%1).data('event', {title: %2 ,id:%3, color :%4 ,stick: false })" dv  (maybe ""  renderShowable $ M.lookup "title" i) (maybe ""  renderShowable $ M.lookup "id" i) (maybe ""  renderShowable $ M.lookup "color" i)
                           runFunction $ ffi "$(%1).draggable({ helper: 'clone',scroll:false,appendTo: 'body' ,'z-index' : 999,revert:true,revertDuration:0})" dv
                           return dv) i)
                         UI.div # set children [h,b] # set UI.style [("border","dotted 1px black")]
                          ) . filter (not .L.null .snd) . fmap (fmap rights) <$> facts t) # set UI.style [("border","solid 1px black")])  $ M.lookup k (M.fromList selectedData) ) itemListEl2
            return ()
    (_,fin) <- mapUITEventFin calendar calFun ((,,,)
        <$> triding agenda
        <*> incrementT
        <*> triding resolution
        <*> triding legend
        )
    liftIO$ addFin calendar [fin]

    liftIO $mapM (\(tdesc ,(_,tname,fields))-> do
        mapTEvent  ((\i ->  forkIO $ void $ transactionNoLog  inf $ selectFromA (tname) Nothing Nothing [] (WherePredicate $ OrColl $ PrimColl . (,"<@",(IntervalTB1 $ fmap (TB1 . SDate . localDay . utcToLocalTime utc )i)) . indexer . T.pack . renderShowable <$> F.toList fields))) rangeT
      ) allTags
    return body

txt = TB1. SText

writePK :: TBData Key Showable -> FTB Showable ->  Text
writePK r efield = (\i -> _kvname (fst r) <> "->"  <> i <>  "->" <> T.pack (renderShowable efield ))$T.intercalate  ","  $ fmap ((\(i,j) -> keyValue i <> "=" <> T.pack (renderShowable j))) $ getPKM r

makePatch :: TimeZone -> ((Table,[(Key ,FTB Showable)],Key),Either (Interval UTCTime ) UTCTime ) -> TBIdx Key Showable
makePatch zone ((t,pk,k), a) = (tableMeta t , pk, PAttr k <$>  (ty  (keyType k)$   a))
 where ty (KOptional k )  i = fmap (POpt . Just)   . ty k $ i
       ty (KSerial k )  i = fmap (PSerial . Just )  . ty k $ i
       ty (KInterval k )  (Left i )=  [PatchSet $ (fmap (PInter True . (,True)). (ty k.Right . unFinite) $ Interval.lowerBound i) <>  (fmap (PInter False . (,True)). (ty k.Right .unFinite ) $ Interval.upperBound i)]
       ty (Primitive p ) (Right r )= pure .PAtom . cast p $ r
       cast (AtomicPrim PDate ) = SDate . utctDay
       cast (AtomicPrim (PTimestamp l)) = STimestamp . utcToLocalTime utc .localTimeToUTC zone . utcToLocalTime utc

unFinite (Interval.Finite i ) = i
unFinite (i ) = errorWithStackTrace (show i)

readPK :: InformationSchema -> Text -> (Table,[(Key ,FTB Showable)],Key)
readPK  inf s = (tb,pk,editField)
  where [t,pks,f] = T.splitOn "->"  s
        pk = (\(k,v) -> (k,fromJust  $ readType (keyType k) (T.unpack $ T.drop 1 v))) . first (\k -> fromJust $ L.find ((k==).keyValue)pksk).  T.break ('='==) <$> T.splitOn "," pks
        tb = lookTable inf t
        editField = lookKey inf t f
        pksk = rawPK tb

instance A.ToJSON a => A.ToJSON (FTB a ) where
  toJSON (TB1 i) = A.toJSON i
  toJSON (LeftTB1 i) = fromMaybe (A.toJSON ("" ::String)) (A.toJSON <$> i)
  toJSON (SerialTB1 i)  =  fromMaybe (A.toJSON ("" ::String)) (A.toJSON <$> i)

instance A.ToJSON Showable where
  toJSON (SText i ) = A.toJSON i
  toJSON i = A.toJSON (renderPrim i)


type DateChange  =  (String,Either (Interval UTCTime ) UTCTime)

-- readPosition:: EventData -> Maybe DateChange
readPosition (EventData v@(Just i:Just a:Just e :_)) =  (,) <$> Just i <*> ((\i j ->  Left $ Interval.interval (Interval.Finite i,True) (Interval.Finite j,True))<$> parseISO8601 a <*> parseISO8601 e)
readPosition (EventData v@(Just i:Just a:_)) =   (,) <$> Just i <*> (Right <$> parseISO8601 a )
readPosition (EventData v) = Nothing


eventDrop :: Element -> Event DateChange
eventDrop el = filterJust $ readPosition <$>  domEvent "eventDrop" el

eventDragDrop :: Element -> Event DateChange
eventDragDrop el = filterJust $ readPosition <$>  domEvent "externalDrop" el

eventResize :: Element -> Event DateChange
eventResize el = filterJust $ readPosition <$>  domEvent "eventResize" el

