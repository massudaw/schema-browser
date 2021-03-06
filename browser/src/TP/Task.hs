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


taskWidgetMeta inf = do
    fmap F.toList $  join . fmap (currentValue .facts )  $ runMetaArrow inf taskDef
  -- (fmap F.toList . currentValue .facts ) =<< transactionNoLog (meta inf) ( dynPK (taskDef inf) mempty)


taskDef inf
  = projectS
    (innerJoinS
      (innerJoinS
         (tableDef inf `whereS` schemaPred)
         (fromS "planner") (schemaI "planner"))
      (fromS "event" ) (schemaI "event")) fields
  where
      schemaPred = [(keyRef "schema",Left (int (schemaId inf),Equals))]
      schemaI t = [Rel "oid" Equals (NInline t "table")]
      fields =  irecord $ proc t -> do
        (tname,desc,dir,pks) <- tableProj inf -< ()
        efields <- iforeign (schemaI "event") (ivalue $ irecord 
            (iforeign [ Rel "column" (AnyOp Equals) "ordinal_position"] 
              (imap $ ivalue $ irecord (ifield  "column_name" (ivalue $  readV PText))))) -< ()
        (color,child) <- iforeign (schemaI "planner")  (
           (,)<$> ivalue ( irecord (ifield "color" (ivalue $  readV PText)))
              <*> columnName "task") -< ()
        let
          toLocalTime = fmap to
            where
              to (STime (STimestamp i ))  = STime $ STimestamp $  i
              to (STime (SDate i )) = STime $ SDate i
          convField (IntervalTB1 i) = catMaybes [fmap (("start",). toLocalTime )$ unFinite $ Interval.lowerBound i,fmap (("end",).toLocalTime) $ unFinite $ Interval.upperBound i]
          convField v = [("start",toLocalTime $v)]
          scolor =  "#" <> renderPrim color
          renderTitle t = L.intercalate "," $ renderShowable <$> F.toList t
          lkRel i r=  unSOptional =<< recLookupInf inf tname (indexerRel i) r
          unText (SText i) = i
          lkProjectProperties r = do
            TB1 (STime (STimestamp date)) <- lkRel (unText $  NonS.head efields) r
            pkfields <- mapM (\(SText i) -> lkRel  i r) pks
            fields <- mapM (\(SText i) -> lkRel i r) (fromMaybe pks (toListTree <$> desc))
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
                  (Duration $ float durationV) :: Project String,[]))
          float (TB1 (SDouble i)) =  realToFrac i
          proj r = projf r desc (NonS.head efields) child
        returnA -< (txt $ T.pack $ scolor ,lookTable inf tname,TB1 <$> (Non.fromList  $ F.toList efields),proj )


taskWidget (incrementT,resolutionT) sel inf = do
    let
      calendarSelT = liftA2 (,) incrementT resolutionT

    dashes <- ui $ taskWidgetMeta inf
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

                        headers =  ["Description"
                                   ,L.intercalate "," $ F.toList $ renderShowable <$> fields
                                   ,"Cost"
                                   ,"Trust"
                                   ,"Progress"
                                   ,"Duration"]
                        header = UI.tr # set items (mapM (\ i-> UI.th # set text i) headers)
                        mpProject p = [fromMaybe "No Title" $ MP.title p,maybe "" show $ MP.creation_date p ]
                        computeProp a = [showCost (cost a), showTrust (trust a) , showProgress (progress a),showDuration (duration a)]
                        values a@(MP.Sum p l)
                          = ("sum", mpProject p <> computeProp a)
                        values a@(MP.Sequence p l)
                          =  ("sequence",mpProject p <> computeProp a)
                        values a@(MP.Product p l)
                          =  ("product",mpProject p <> computeProp a)
                        values (Atomic p (Cost c) (Trust t) (Progress pro) (Duration dur))
                          =  ("primitive",mpProject p <> [  show  c, show  t, show  pro,show dur])
                        row v = UI.tr # set items  (mapM (\i -> UI.td # set text i) l )
                                      # set UI.class_ t 
                          where (t,l) = values v
                        list i l= do
                          let cid = fromMaybe "root" $  MP.project_id =<< (properties i)
                          v <- row i 
                              # set (UI.strAttr "data-tt-id") cid
                              # set UI.style (if isAtomic i then [("background-color","smokewhite")] else [("background-color","lightgrey")])
                          when (cid == "root" ) $ void $ do
                            element v # set UI.class_ "expanded"
                          mapM_ (traverse (\e-> element  e  # set (UI.strAttr "data-tt-parent-id") cid)) (safeHead <$> l)
                          return (v:concat l) 
                        body = either (const (return [])) (subprojectsDeep list) figure
                        dat =  catMaybes $ fmap proj  $ G.toList (primary i)
                        figure = join $ maybe (Left "No pending tasks") Right  .  filterProject (\ ~(_,_,_,Duration d) -> (if done then d > 0 else True )) <$> groupTopLevel (T.unpack $ tableName table) dat


                    c <- caption 
                    h <- header
                    b <- body
                    t <- UI.table # set UI.class_ "table-condensed treetable" # set children (c:h:b)
                    runFunctionDelayed t (ffi "$(%1).treetable({expandable: true})" t)
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

isAtomic (MP.Atomic _ _ _ _ _) = True
isAtomic _ = False

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

subprojectsDeep :: Monad m => (Project a -> [b] -> m b) -> Project a -> m b 
subprojectsDeep f v@(MP.Sequence _ ps) = f v =<< mapM (subprojectsDeep f) (Non.toList ps)
subprojectsDeep f v@(MP.Product _ ps)  = f v =<< mapM (subprojectsDeep f) (Non.toList ps)
subprojectsDeep f v@(MP.Sum _ ps)      = f v =<< mapM (subprojectsDeep f) (Non.toList ps)
subprojectsDeep f v@(MP.Atomic _ _ _ _ _ )               = f v [] 


groupTopLevel tname list =  maybe (Left "No task in period") (resolveReferences False ((\(j,_) -> (projectId j ,j)) <$> list) ["root"] .MP.Product (ProjectProperties (Just tname) Nothing Nothing Nothing Nothing Nothing)  ) (fmap (fmap fst . Non.fromList )$ nonEmpty $ filter (\(j,_) -> not $  S.member  (projectId j) refs) list)
  where refs = S.fromList $ concat $ fmap (\(_,i) -> i) list
