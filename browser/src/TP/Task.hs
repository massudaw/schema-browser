{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE Arrows #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module TP.Task where

import Control.Arrow
import Control.Lens ((^.), _2)
import Control.Monad.Writer
import Data.Either
import qualified Data.Foldable as F
import qualified Data.Interval as Interval
import qualified Data.List as L
import qualified Data.Map as M
import Data.Maybe
import Data.Ord
import qualified Data.Set as S
import qualified Data.Text as T
import Data.Void
import Environment
import qualified Graphics.UI.Threepenny as UI
import Graphics.UI.Threepenny.Core hiding (apply, delete, get)
import MasterPlan.Backend.Graph as MP
import MasterPlan.Data as MP
import MasterPlan.Parser as MP
import NonEmpty (NonEmpty)
import qualified NonEmpty as Non
import qualified Data.Sequence.NonEmpty as NonS
import Prelude hiding (head)
import PrimEditor
import RuntimeTypes
import SchemaQuery
import Step.Host
import TP.View
import TP.Widgets
import Text
import Types
import qualified Types.Index as G
import Utils

columnName name = ivalue $ irecord $ iforeign [Rel "schema" Equals "schema" , Rel "table" Equals "table", Rel name Equals "ordinal_position"] (ivalue $ irecord (ifield  "column_name" (ivalue $  readV PText)))

taskWidgetMeta inf = do
  fmap F.toList $ ui $ transactionNoLog (meta inf) $ dynPK (taskDef inf) ()

taskDef inf
  = projectV
     (innerJoinR
        (leftJoinR
          (innerJoinR
            (innerJoinR
              (fromR "tables" `whereR` schemaPred)
              (fromR "planner" `whereR` schemaPred) schemaI "task")
            (fromR "event" `whereR` schemaPred) schemaI "event")
          (fromR "table_description" `whereR` schemaNamePred ) [Rel "schema_name" Equals "table_schema", Rel "table_name" Equals "table_name"] "description")
        (fromR "pks" `whereR` schemaNamePred2 ) [Rel "schema_name" Equals "schema_name", Rel "table_name" Equals "table_name"]  "pks") fields

  where
      schemaNamePred2 = [(keyRef "schema_name",Left (txt $schemaName inf ,Equals))]
      schemaPred = [(keyRef "schema",Left (int (schemaId inf),Equals))]
      schemaNamePred = [(keyRef "table_schema",Left (txt (schemaName inf),Equals))]
      schemaI = [Rel "schema" Equals "schema", Rel "oid" Equals "table"]
      schemaN = [Rel "schema_name" Equals "table_schema", Rel "table_name" Equals "table_name"]
      fields =  irecord $ proc t -> do
        SText tname <-
            ifield "table_name" (ivalue (readV PText))  -< ()
        desc <- iinline "description" (iopt $  ivalue $ irecord (ifield "description" (imap $ ivalue $  readV PText))) -< ()
        pksM <- iinline "pks" (ivalue $ irecord (iforeign [Rel "schema_name" Equals "schema_name" , Rel "table_name" Equals "table_name", Rel "pks" Equals "column_name"] (iopt $ imap $ ivalue $ irecord (ifield  "column_name" (ivalue $  readV PText))))) -< ()
        efields <- iinline "event" (ivalue $ irecord (iforeign [Rel "schema" Equals "schema" , Rel "table" Equals "table", Rel "column" Equals "ordinal_position"] (imap $ ivalue $ irecord (ifield  "column_name" (ivalue $  readV PText))))) -< ()
        (color,child) <- iinline "task"  (
           (,)<$> ivalue ( irecord (ifield "color" (ivalue $  readV PText)))
              <*> columnName "task") -< ()
        let
          toLocalTime = fmap to
            where
              to (STime (STimestamp i ))  = STime $ STimestamp $  i
              to (STime (SDate i )) = STime $ SDate i
          convField (IntervalTB1 i) = catMaybes [fmap (("start",). toLocalTime )$ unFinite $ Interval.lowerBound i,fmap (("end",).toLocalTime) $ unFinite $ Interval.upperBound i]
          convField v = [("start",toLocalTime $v)]
          convField i = error (show i)
          scolor =  "#" <> renderPrim color
          renderTitle t = L.intercalate "," $ renderShowable <$> F.toList t
          lkRel i r=  unSOptional =<< recLookupInf inf tname (indexerRel i) r
          unText (SText i) = i
          lkProjectProperties r = do
            TB1 (STime (STimestamp date)) <- lkRel (unText $  NonS.head efields) r
            pks <- pksM
            pkfields <- mapM (\(SText i) -> lkRel  i r) pks
            fields <- mapM (\(SText i) -> lkRel i r) (fromMaybe pks desc)
            return (ProjectProperties
                      (Just (renderTitle fields))
                      Nothing
                      Nothing
                      Nothing
                      (Just date)
                      (Just (renderTitle pkfields)) )

          projf r desc (SText field)  (SText deps)  =
            (do
              i <- lkRel (deps <> ":product:id") r
              proj <- lkProjectProperties r
              return (MP.Product   proj (NonS.toNonEmpty $ Annotated . renderShowable <$> unArray i) ,F.toList $ renderShowable <$> unArray i)
            ) <|>
            (do
              i <- lkRel  (deps<> ":sum:id") r
              proj <- lkProjectProperties r
              return (MP.Sum proj  (NonS.toNonEmpty $ Annotated . renderShowable <$> unArray i) ,F.toList $ renderShowable <$> unArray i)
            ) <|>
            (do
              i <- lkRel  (deps<> ":sequence:id") r
              proj <- lkProjectProperties r
              return (MP.Sequence proj (NonS.toNonEmpty $ Annotated . renderShowable <$> unArray i) ,F.toList $ renderShowable <$> unArray i)
            ) <|>
            (do
              i <- lkRel field r
              let costV = fromMaybe (TB1 0) $ lkRel (deps <> ":atomic:cost") r
              let trustV = fromMaybe (TB1 1) $ lkRel (deps <> ":atomic:trust") r
              let progressV = fromMaybe (TB1 0) $ lkRel (deps <> ":atomic:progress") r
              let durationV = fromMaybe (TB1 0) $ lkRel (deps <> ":atomic:duration") r
              proj <- lkProjectProperties r
              return
                (Atomic
                  proj
                  (Cost $ float costV)
                  (Trust $ float trustV)
                  (Progress $ float progressV)
                  (Duration $ float durationV):: Project String,[]))
          float (TB1 (SDouble i)) =  realToFrac i
          proj r = projf r desc (NonS.head efields) child
        returnA -< (txt $ T.pack $ scolor ,lookTable inf tname,TB1 <$> (Non.fromList  $ F.toList efields),proj )


taskWidget (incrementT,resolutionT) sel inf = do
    let
      calendarSelT = liftA2 (,) incrementT resolutionT

    dashes <- taskWidgetMeta inf
    let allTags =  dashes
    itemListEl2 <- mapM (\i ->
      (i^. _2,) <$> UI.div  # set UI.style [("width","100%"),("height","150px") ,("overflow-y","auto")]) dashes
    let
      legendStyle lookDesc table b
          =  do
            let item = M.lookup table  (M.fromList  $ fmap (\i@(_,b,_,_)-> (b,i)) dashes )
            traverse (\k@(c,tname,_,_) ->   do
              header <-  UI.div # set text  (T.unpack  lookDesc) # set UI.class_ "col-xs-11"
              element b # set UI.class_ "col-xs-1"
              UI.label # set children [b,header]
                       # set UI.style [("background-color",renderShowable c)] # set UI.class_ "table-list-item" # set UI.style [("display","-webkit-box")]
              ) item
    calendar <- UI.div # set UI.class_ "col-xs-10"

    let
      calFun :: UI [Element]
      calFun = do
         els <- traverseUI
            (\(selected ,calT )->
              mapM (\(_,table,fields,proj) -> do
                let pred = WherePredicate $ timePred inf table (fieldKey <$> fields ) calT
                    fieldKey (TB1 (SText v))=   v
                v <-  ui $ transactionNoLog  inf $ selectFrom (tableName table) Nothing mempty
                width <- primEditor (pure (Just 1000))
                height <- primEditor (pure (Just 500))
                hideDone <- fmap fromJust <$> primEditor (pure (Just True))
                els <- traverseUI
                  (\(done,i) -> do
                    let caption =  UI.caption # set text (T.unpack  (tableName table) )
                        headers =  ["Id"
                                   ,"Description"
                                   ,L.intercalate "," $ F.toList $ renderShowable <$> fields
                                   ,"Cost"
                                   ,"Trust"
                                   ,"Progress"
                                   ,"Duration"]
                        header = UI.tr # set items (mapM (\ i-> UI.th # set text i) headers)
                        mpProject p = [ fromMaybe "No Id" $ MP.project_id p,fromMaybe "No Title" $ MP.title p,maybe "" show $ MP.creation_date p ]
                        computeProp a = [showCost (cost a), showTrust (trust a) , showProgress (progress a),showDuration (duration a)]
                        values a@(MP.Sum p l)
                          = mpProject p <> computeProp a
                        values a@(MP.Sequence p l)
                          = mpProject p <> computeProp a
                        values a@(MP.Product p l)
                          = mpProject p <> computeProp a
                        values (Atomic p (Cost c) (Trust t) (Progress pro) (Duration dur))
                          = mpProject p <> [  show  c, show  t, show  pro,show dur]
                        row v = UI.tr # set items  (mapM (\i -> UI.td # set text i) (values v) )
                        body = row <$> (either (const []) (tail . subprojectsDeep) figure)
                        dat =  catMaybes $ fmap proj  $ G.toList (primary i)
                        figure = join $ maybe (Left "No pending tasks") Right  .  filterProject (\ ~(_,_,_,Duration d) -> (if done then d > 0 else True )) <$> groupTopLevel (T.unpack $ tableName table) dat

                    t <- UI.table # set items (sequence $ caption:header:body)
                    svg <- UI.div # sink UI.html (facts $ fmap (fromMaybe "" )$ liftA2 (\w h -> either id  (MP.renderWithSVG (RenderOptions  False w  h allattrs))  figure ) <$> triding width <*> triding height )
                    UI.div # set children [t,svg]
                    ) (liftA2 (,) (triding hideDone) (collectionTid v))

                inp  <- UI.div # set children ([getElement hideDone,getElement width,getElement height])
                svg <- UI.div # sink UI.children (pure <$> facts els)
                UI.div # set children [inp,svg]
                    ) (filter (flip L.elem (F.toList selected) .  (^. _2)) dashes )

                ) $ (,) <$> sel <*> calendarSelT
         pure <$> UI.div # sink children (facts  els)
    return (legendStyle,dashes,calFun )

showCost (Cost i) = show i
showProgress (Progress i) = show i
showTrust (Trust i) = show i
showDuration (Duration i) = show i

allattrs = [PTitle , PCost , PTrust , PProgress,PDuration]
projectId = fromJust . join . fmap project_id . properties

filterProjectList :: ((Cost,Progress,Trust,Duration) -> Bool) -> NonEmpty (Project Void ) -> Maybe (NonEmpty (Project Void))
filterProjectList f v = Non.catMaybes $ filterProject f <$> v

filterProject :: ((Cost,Progress,Trust,Duration) -> Bool) ->  Project Void -> Maybe (Project Void)
filterProject f v@(MP.Sequence d ps) = if (f (cost v,progress v , trust v , duration v) ) then (MP.Sequence d <$>filterProjectList f ps) else Nothing
filterProject f v@(MP.Product d ps)  = if (f (cost v,progress v , trust v , duration v) ) then (MP.Product d <$>filterProjectList f ps) else Nothing
filterProject f v@(MP.Sum d ps)      = if (f (cost v,progress v , trust v , duration v) ) then (MP.Sum d <$> filterProjectList f ps) else Nothing
filterProject f v               = if f (cost v,progress v , trust v , duration v)  then Just v else Nothing

subprojectsDeep :: Project a -> [Project a]
subprojectsDeep v@(MP.Sequence _ ps) = v : concat (subprojectsDeep <$> Non.toList ps)
subprojectsDeep v@(MP.Product _ ps)  = v : concat (subprojectsDeep <$> Non.toList ps)
subprojectsDeep v@(MP.Sum _ ps)      = v : concat (subprojectsDeep <$> Non.toList ps)
subprojectsDeep i               = [i]


groupTopLevel tname list =  maybe (Left "No task in period") (resolveReferences False ((\(j,_) -> (projectId j ,j)) <$> list) ["root"] .MP.Product (ProjectProperties (Just tname) Nothing Nothing Nothing Nothing Nothing)  ) (fmap (fmap (\(i,_) -> i ) . Non.fromList )$ nonEmpty $ filter (\(j,_) -> not $  S.member  (projectId j) refs) list)
  where refs = S.fromList $ concat $ fmap (\(_,i) -> i) list
