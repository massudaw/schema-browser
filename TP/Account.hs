{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module TP.Account where

import GHC.Stack
import Data.Ord
import Step.Host
import Control.Lens (_1,_2,(^.))
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

resRange b "month" d =  d {utctDay = addGregorianMonthsClip (if b then -1 else 1 )  (utctDay d)}
resRange b "day" d = d {utctDay =addDays (if b then -1 else 1 ) (utctDay d)}
resRange b "week" d = d {utctDay =addDays (if b then -7 else 7 ) (utctDay d)}

calendarSelector = do
    let buttonStyle k e = e # set UI.text (fromJust $ M.lookup k transRes)# set UI.class_ "btn-xs btn-default buttonSet"
          where transRes = M.fromList [("month","Mês"),("week","Semana"),("day","Dia")]
        defView = "month"
        viewList = ["month","day","week"] :: [String]
        transMode _ "month" = "month"
        transMode True i = "agenda" <> capitalize i
        transMode False i = "basic" <> capitalize i
        capitalize (i:xs) = toUpper i : xs
        capitalize [] = []

    iday <- liftIO getCurrentTime
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
      currentE = concatenate <$> unions  [resRange False  <$> facts (triding resolution) <@ UI.click next
                                       ,resRange True   <$> facts (triding resolution) <@ UI.click prev , const (const iday) <$> UI.click today ]
    increment <- accumB iday  currentE
    let incrementT =  tidings increment (flip ($) <$> increment <@> currentE)
    sidebar <- UI.div # set children [getElement agenda,current,getElement resolution] #  set UI.class_ "col-xs-2"
    return (sidebar,(,,) <$> triding agenda <*> incrementT <*> triding resolution)


accountWidget body sel inf = do
    (_,(_,tmap)) <- liftIO $ transactionNoLog (meta inf) $ selectFrom "table_name_translation" Nothing Nothing [] (LegacyPredicate[("=",liftField (meta inf) "table_name_translation" $ uncurry Attr $("schema_name",TB1 $ SText (schemaName inf) ))])
    (evdb,(_,emap )) <- liftIO $ transactionNoLog  (meta inf) $ selectFrom "event" Nothing Nothing [] (LegacyPredicate[("=",liftField (meta inf) "event" $ uncurry Attr $("schema_name",TB1 $ SText (schemaName inf) ))])
    (evdb,(_,aMap )) <- liftIO $ transactionNoLog  (meta inf) $ selectFrom "accounts" Nothing Nothing [] (LegacyPredicate[("=",liftField (meta inf) "accounts" $ uncurry Attr $("schema_name",TB1 $ SText (schemaName inf) ))])
    cliZone <- jsTimeZone
    dashes <- liftIO $ mapConcurrently (\e -> do
        let (Attr _ (TB1 (SText tname))) = lookAttr' (meta inf) "table_name" e
            lookDesc = (\i  -> maybe (T.unpack $ tname)  ((\(Attr _ v) -> renderShowable v). lookAttr' (meta inf)  "translation") $ G.lookup (idex (meta inf) "table_name_translation" [("schema_name" ,txt $ schemaName inf),("table_name",txt tname )]) i ) $ tmap
            (Attr _ (ArrayTB1 efields )) =lookAttr' (meta inf)  "event" $ fromJust $ G.lookup (idex (meta inf) "event" [("schema_name" ,txt $ schemaName inf),("table_name",txt tname )])  emap
            (Attr _ (ArrayTB1 afields ))= lookAttr' (meta inf) "account" e
            (Attr _ color )= lookAttr' (meta inf) "color" e
        evdb <- refTable inf  (lookTable inf tname )
        let toLocalTime = fmap to
              where to (STimestamp i )  = STimestamp $  utcToLocalTime cliZone $ localTimeToUTC utc i
                    to (SDate i ) = SDate i
            convField ((IntervalTB1 i )) = [("start", toLocalTime $ unFinite $ Interval.lowerBound i),("end",toLocalTime $ unFinite $ Interval.upperBound i)]
            convField (LeftTB1 i) = concat $   convField <$> maybeToList i
            convField (v) = [("start",toLocalTime $v)]
            convField i = errorWithStackTrace (show i)
            projf  r efield@(TB1 (SText field)) afield@(TB1 (SText aafield))  = (if (isJust . unSOptional $ attr) then Left else Right) (M.fromList $ convField attr  <> [("id", TB1 $ SText $ writePK r efield   ),("title",TB1 $ SText (T.pack $  L.intercalate "," $ fmap renderShowable $ allKVRec' $  r)) , ("table",TB1 (SText tname)),("color" , color),("field", efield ), ("commodity", accattr )] :: M.Map Text (FTB Showable))
                  where attr  = attrValue $ lookAttr' inf field r
                        accattr  = attrValue $ lookAttr' inf aafield r
            proj r = (TB1 $ SText (T.pack $  L.intercalate "," $ fmap renderShowable $ allKVRec' $  r),)$  zipWith (projf r) ( F.toList efields) (F.toList afields)
            attrValue (Attr k v) = v
        return ((lookDesc,(color,tname,efields,afields)), fmap proj  . G.toList <$> collectionTid evdb  )) ( G.toList aMap)

    let allTags =  (fst <$> dashes)
    itemListEl2 <- mapM (\i ->
      (i,) <$> UI.div  # set UI.style [("width","100%"),("height","150px") ,("overflow-y","auto")]) allTags
    let
        legendStyle table (b,_)
            =  do
              let item = M.lookup (tableName (fromJust $ M.lookup table (pkMap inf))) (M.fromList  $ fmap (\i@(t,(a,b,_,c))-> (b,i)) allTags)
              maybe UI.div (\k@(t,(c,_,_,_)) ->   mdo
                expand <- UI.input # set UI.type_ "checkbox" # sink UI.checked evb # set UI.class_ "col-xs-1"
                let evc = UI.checkedChange expand
                evb <- stepper False evc
                missing <- (element $ fromJust $ M.lookup k (M.fromList itemListEl2)) # sink UI.style (noneShow <$> evb)
                header <- UI.div
                  # set items [element b # set UI.class_"col-xs-1", UI.div # set text  t # set UI.class_ "col-xs-10", element expand ]
                  # set UI.style [("background-color",renderShowable c)]
                UI.div # set children [header,missing]) item

    (sidebar,calendarSelT) <- calendarSelector
    calendar <- UI.div # set UI.class_ "col-xs-10"
    element body # set children [sidebar,calendar]

    let calFun ((agenda,iday,res ),selected) = do
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
                calHand innerCalendar  visible = do
                  return ()
            innerCalendarSet <- M.fromList <$> mapM (\((_,(_,i,_,_)),s) -> (i,) <$> UI.table)  selectedData
            innerCalendar  <- UI.div # set children (F.toList innerCalendarSet)
            element calendar # set children [innerCalendar]
            let evd = eventDrop innerCalendar
            let evr = eventResize innerCalendar
            let evdd = eventDragDrop innerCalendar
                evs =  fmap (makePatch cliZone . first (readPK inf . T.pack))<$> unions [evr,evdd,evd]
            fin <- onEvent evs (liftIO . transaction inf . mapM (\i -> do
                        patchFrom i >>= traverse (tell . pure )))
            calHand innerCalendar  =<< currentValue   (facts visible)
            fins <- mapM (\((cap,(_,t,_,_)),s)->  fmap snd $ mapUITEventFin (fromJust $ M.lookup t innerCalendarSet) (
                      (\i -> do
                      let caption =  UI.caption # set text cap
                          header = UI.tr # set items [UI.th # set text "Date" , UI.th # set text "Title" ,UI.th # set text "Commodity"]
                          row i = UI.tr # set items [UI.td # set text (maybe "" renderShowable $ M.lookup "start" i), UI.td # set text (maybe "" renderShowable $ M.lookup "title" i), UI.td # set text (maybe "" renderShowable $ M.lookup "commodity" i)]
                          body = fmap row dat
                          dat = L.sortBy (comparing (M.lookup "start")) $filter (inRange res (utctDay iday ) . unTB1 . fromJust . M.lookup "start") . concat .fmap (lefts  .snd)  $ i
                      element (fromJust $ M.lookup t innerCalendarSet) # set items (caption:header:body))
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
    (_,fin) <- mapUITEventFin calendar calFun ((,)
        <$> calendarSelT
        <*> ((\i j -> filter (flip L.elem (tableName <$> concat (F.toList i)) .  (^. _2._2)) j )<$> sel <*> pure allTags)
        )
    liftIO$ addFin calendar [fin]

    liftIO $mapM (\(tdesc ,(_,tname,efields,afields))-> do
        mapTEvent  ((\(_,incrementT,resolution) ->  do
                   let i = (\r d -> Interval.interval (Interval.Finite $ resRange True r d,True) (Interval.Finite $ resRange False r d,True)) resolution   incrementT
                   forkIO $ void $ transactionNoLog  inf $ selectFromA (tname) Nothing Nothing [] (WherePredicate $ OrColl $ PrimColl . (,"<@",(IntervalTB1 $ fmap (TB1 . SDate . localDay . utcToLocalTime utc )i)) . indexer . T.pack . renderShowable <$> F.toList efields))) calendarSelT
      ) allTags
    return (legendStyle,dashes)

txt = TB1. SText

writePK :: TBData Key Showable -> FTB Showable ->  Text
writePK r efield = (\i -> _kvname (fst r) <> "->"  <> i <>  "->" <> T.pack (renderShowable efield ))$T.intercalate  ","  $ fmap ((\(i,j) -> keyValue i <> "=" <> T.pack (renderShowable j))) $ M.toList $ getPKM r

makePatch :: TimeZone -> ((Table,[(Key ,FTB Showable)],Key),Either (Interval UTCTime ) UTCTime ) -> TBIdx Key Showable
makePatch zone ((t,pk,k), a) = (tableMeta t , G.Idex $ M.fromList pk, PAttr k <$>  (ty  (keyType k)$   a))
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
readPosition  v =
 ( let [i,a,e]  = unsafeFromJSON v
   in (,) <$> Just i <*> ((\i j ->  Left $ Interval.interval (Interval.Finite i,True) (Interval.Finite j,True))<$> parseISO8601 a <*> parseISO8601 e)) <|>  (let [i,a] = unsafeFromJSON v in (,) <$> Just i <*> (Right <$> parseISO8601 a ))



eventDrop :: Element -> Event DateChange
eventDrop el = filterJust $ readPosition <$>  domEvent "eventDrop" el

eventDragDrop :: Element -> Event DateChange
eventDragDrop el = filterJust $ readPosition <$>  domEvent "externalDrop" el

eventResize :: Element -> Event DateChange
eventResize el = filterJust $ readPosition <$>  domEvent "eventResize" el

