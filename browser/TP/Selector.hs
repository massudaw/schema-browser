{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module TP.Selector
  ( paginateList
  , tableOrder
  , calendarSelector
  , positionSel
  , tableChooser
  , selectFromTable
  , offsetFieldFiltered
  , offsetField
  , selectListUI
  , multiSelector
  , selector
  , attrLine
  ) where

import Control.Monad.Reader
import Data.Char
import qualified Data.Foldable as F
import PrimEditor
import qualified Data.Functor.Contravariant as C
import qualified Data.List as L
import qualified Data.Map as M
import Data.Maybe
import Data.Monoid hiding (Product(..))
import Data.Ord
import qualified Data.Set as S
import qualified Data.Text as T
import Data.Text (Text)
import Data.Time
import qualified Graphics.UI.Threepenny as UI
import Graphics.UI.Threepenny.Core hiding (apply, delete, get)
import Prelude
import RuntimeTypes
import Safe
import Schema
import SchemaQuery
import Step.Common
import TP.View
import TP.Widgets
import Text
import Types
import qualified Types.Index as G
import Types.Patch
import Utils


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
    w <- askWindow
    ui $ onEventIO  bcpose  (\_ -> runDynamic $ runUI w $ runFunction $ ffi "fireCurrentPosition(%1)" bcpos)
    ui $ onEventIO (currentPosition bcpos ) h
    runFunction $ ffi "fireCurrentPosition(%1)" bcpos
    return (bcpos,tidings positionB (diffEvent positionB  (Just <$> e)))


filterString :: UI (TrivialWidget String)
filterString = do
  filterInp <- UI.input # set UI.placeholder "Search.." # set UI.style [("width","100%")]
  filterInpE <- UI.valueChange filterInp
  filterInpT <- ui $ stepperT "" filterInpE
  return $ TrivialWidget filterInpT filterInp

tableChooser
  :: InformationSchemaKV Key Showable
    -> [Table]
    -> Tidings (Text -> Table -> Element -> UI (Maybe Element))
    -> Tidings (TableK Key -> Bool)
    -> Tidings [TableK Key]
    -> UI (TrivialWidget (S.Set  (TableK Key) ))
tableChooser  inf tables legendStyle tableFilter iniTables = do
  let
    tablePred =  [(keyRef "schema",Left (int $ schemaId inf  ,Equals))]
    authPred = [(keyRef "grantee",Left ( int $ fst $ username inf ,Equals))] <> tablePred
  (orddb ,authorization,translation) <- ui $ transactionNoLog  (meta inf) $
      (,,) <$> selectFromTable "ordering" Nothing Nothing [] tablePred
           <*> selectFromTable "authorization" Nothing Nothing [] authPred
           <*> selectFromTable "table_name_translation" Nothing Nothing [] tablePred
  let
    ordRow orderMap pkset = field
      where
        field =  lookAttr' "usage" <$> G.lookup pk orderMap
        pk = ordPK pkset
    ordPK pkset = idex (meta inf) "ordering" [("table",int $ tableUnique pkset),("schema",int $ schemaId inf)]
  filterInp <- filterString
  let
    -- Table Description
    lookDescT =  flip (lookDesc inf) <$> collectionTid translation
    -- Authorization
    autho_pk t = idex (meta inf) "authorization" [("schema", int (schemaId inf) ),("table",int $ tableUnique t),("grantee",int $ fst $ username inf)]
    authorize =  (\autho t -> isJust $ G.lookup (autho_pk t) autho) <$> collectionTid authorization
    -- Text Filter
    filterLabel = (\j d i -> T.isInfixOf (T.toLower (T.pack j)) (T.toLower  $ d i)) <$> triding filterInp <*> lookDescT
  all <- checkedWidget (pure False)
  bset <- do
    let
      buttonString k = do
        b <- UI.input # set UI.type_ "checkbox"
        chkE <- UI.checkedChange b
        return (b,chkE)
      visible  = (\i j k tb -> i tb && j tb && k tb ) <$> filterLabel <*> authorize <*> tableFilter
      allTablesSel True = S.fromList  $ tables
      allTablesSel False = S.empty
      iniSel =  S.fromList  <$> iniTables
    iniValue <- currentValue (facts iniSel)
    let iniEvent = unionWith const (rumors iniSel) (allTablesSel <$> rumors (triding all))
    iniT <- ui $ stepperT iniValue  iniEvent
    checkDivSetTGen
      tables
      (ordRow <$>  collectionTid orddb)
      iniT
      buttonString
      ((\lg desc visible i j -> if (visible i) then Just (maybe UI.div return =<<  lg (desc i) i j) else Nothing  )
       <$> legendStyle <*> lookDescT <*>  visible )
  let
    incClick = [PAttr (lookKey (meta inf) "ordering" "usage") (PAtom . SDelta $ DSInt 1)]
  sel0 <- ui $ currentValue (facts $ triding bset)
  let diffSet = (\j (o,_) -> (j, S.difference j o )) <$> rumors (triding bset)
  old <- ui $ accumT (sel0,S.empty)  diffSet
  ui $ onEventDyn
    (fmap ordPK . F.toList . snd <$> rumors old)
    (traverse (transaction (meta inf) . patchFrom (lookMeta (meta inf) "ordering") . (,PatchRow incClick)))

  element bset # set UI.style [("overflow","auto"),("height","99%")]
  header <- UI.div # set children [getElement all, getElement filterInp] # set UI.style [("display","inline-flex")]
  tbChooserI <- UI.div # set children [header,getElement bset]  # set UI.style [("height","100%")]
  return $ (TrivialWidget (triding bset) tbChooserI)

data AscDesc a
  = AscW a
  | DescW a
  deriving(Eq)

instance Ord a => Ord (AscDesc a) where
  compare (AscW a ) (AscW b) =  compare a b
  compare (DescW a ) (DescW b) = compare (Down a ) (Down b)


paginateList inf table itemListEl predicate (vpt,gist,_,_) constr tdi =  do
      filterInp <- filterString
      wheel <- fmap negate <$> UI.mousewheel itemListEl
      let
        filtering i k = filter (T.isInfixOf (T.pack $ toLower <$> i) . T.toLower . T.pack . showFKText inf (tableMeta table)) k
        pageSize = 20
        lengthPage (IndexMetadata fixmap)  predicate = (s  `div` pageSize) +  if s `mod` pageSize /= 0 then 1 else 0
          where s = maybe 0 fst $  M.lookup (fromMaybe mempty predicate) fixmap
        sortList = reverse . L.sortOn (G.getIndex (tableMeta table))

      presort <- ui $ cacheTidings ( G.toList <$> gist)
      -- Filter and paginate
      (offset,res3)<- do
        let
          aconstr = liftA2 applyConstr presort constrT
          constrT =  traverse  snd constr
          applyConstr m l =  filter (F.foldl' (\l (C.Predicate c) ->  liftA2 (&&) l (not <$> c) ) (pure True)  l) m
        res3 <- ui$ cacheTidings (filtering  <$> triding filterInp <*> aconstr)
        element itemListEl # sink UI.size (show . (\i -> if i > 21 then 21 else (i +1 )) . length <$> facts res3)
        offset <- offsetField ((\j i -> maybe 0  (`div`pageSize) $ join $ fmap (\i -> L.elemIndex i j ) i) <$>  facts res3 <#> tdi) wheel  (flip lengthPage <$> facts predicate <#> vpt)
        return (offset, res3)

      -- Load offseted items
      let
        idxRequest = (,,) <$> facts vpt <#> predicate<*> triding offset
        loadPage (m,pred,i) = do
          let page = i `div` (opsPageSize (schemaOps inf) `div` pageSize)
          transactionNoLog inf $ selectFrom (tableName table) (Just page ) Nothing  [] (fromMaybe mempty pred)
      ui $ onEventDyn (rumors idxRequest) loadPage
      res4 <- ui $ cacheTidings ((\o -> L.take pageSize . L.drop (o*pageSize)) <$> triding offset <*> (fmap sortList res3))
      element filterInp # set UI.class_ "col-xs-10"
      element offset # set UI.class_ "label label-default col-xs-2 pull-right"
      fInp <-  UI.div # set children [getElement filterInp,getElement offset]
      return (res4,fInp)

multiSelectListUI
  :: InformationSchema
  -> TableK CoreKey
  -> Element
  -> Tidings (Maybe WherePredicate)
  -> RefTables
  -> SelTBConstraint
  -> Tidings [TBData Key Showable]
  -> UI (Tidings [TBData Key Showable], Element)
multiSelectListUI inf table itemListEl predicate ref@(_,vpt,_,_) constr tdi = do
  let m = tableMeta table
  (res4, fInp) <- paginateList inf table itemListEl predicate  ref constr (safeHead <$> tdi)
  lbox <- multiListBoxEl itemListEl (fmap (G.getIndex m )<$> res4 ) (fmap (G.getIndex m) <$> tdi) (showFKLook inf (tableMeta table) vpt)
  out <- UI.div # set children [fInp,itemListEl]
  return ((\i j -> catMaybes $ fmap (flip G.lookup  j) i) <$> triding lbox <*> vpt ,  out  )


selectListUI
  :: InformationSchema
   -> TableK CoreKey
   -> Element
   -> Tidings (Maybe WherePredicate)
   -> RefTables
   -> SelTBConstraint
   -> Tidings (Maybe (TBData Key Showable))
   -> UI (Tidings (Maybe (TBData Key Showable)), Element)
selectListUI inf table itemListEl predicate ref@(_,vpt,_,_)  constr tdi = do
  let m = tableMeta table
  (res4, fInp) <- paginateList inf table itemListEl predicate  ref constr tdi
  lbox <- listBoxEl itemListEl ((Nothing:) . fmap (Just  . G.getIndex m) <$> res4 ) (fmap (Just . G.getIndex m)<$> tdi) ((\i -> maybe (set text "None") (i$) )<$> showFKLook inf (tableMeta table) vpt)
  out <-  UI.div # set children [fInp,itemListEl]
  return ((\i j -> join $ fmap (flip G.lookup  j) (join i)) <$> triding lbox <*> vpt   ,out)

multiSelector
  :: InformationSchema
     -> TableK Key
     -> RefTables
     -> Tidings (Maybe WherePredicate)
     -> Tidings [TBData Key Showable]
     -> UI (TrivialWidget [TBData Key Showable])
multiSelector inf table reftb@(vptmeta,vpt,_,var) predicate tdi = mdo
  itemListEl <- UI.select # set UI.style [("width","100%")] # set UI.size "21"
  runFunction $ ffi "$(%1).selectpicker('mobile')" itemListEl
  (tds ,el) <- multiSelectListUI inf table itemListEl predicate reftb [] tdi
  itemSel <- UI.div # set children [el] # set UI.class_ "col-xs-12"
  return (TrivialWidget tds itemSel)


selector
  :: InformationSchema
     -> TableK Key
     -> RefTables
     -> Tidings (Maybe WherePredicate)
     -> Tidings (Maybe (TBData Key Showable))
     -> UI (TrivialWidget (Maybe (TBData Key Showable)))
selector inf table reftb@(vptmeta,vpt,_,var) predicate tdi = mdo
  itemListEl <- UI.select # set UI.style [("width","100%")] # set UI.size "21"
  runFunction $ ffi "$(%1).selectpicker('mobile')" itemListEl
  (tds ,el) <- selectListUI inf table itemListEl predicate reftb [] tdi
  itemSel <- UI.div # set children [el] # set UI.class_ "col-xs-12"
  return (TrivialWidget tds itemSel)


showFKLook inf m collection = (\col v j -> j  # set text (maybe "No reference" (showFKText inf m) (G.lookup v col ))) <$>  collection
showFK inf m = pure (\v j -> j  # set text (showFKText inf m v))

offsetField  initT eve  max = offsetFieldFiltered initT eve [max]

offsetFieldFiltered  initT eve maxes = do
  init <- currentValue (facts initT)
  offset <- UI.span# set (attr "contenteditable") "true" #  set UI.style [("width","50px")]

  lengs  <- mapM (\max -> UI.span # sinkDiff text (("/" ++) .show  <$> max )) maxes
  offparen <- UI.div # set children (offset : lengs) # set UI.style [("text-align","center")]

  enter  <- UI.onChangeE offset
  whe <- UI.mousewheel offparen
  let max  = facts $ foldr1 (liftA2 min) maxes
  let offsetE =  filterJust $ (\m i -> if i <m then Just i else Nothing ) <$> max <@> (filterJust $ readMay <$> enter)
      ev = unionWith const (negate <$> whe ) eve
      saturate m i j
          | m == 0 = 0
          | i + j < 0  = 0
          | i + j > m  = m
          | otherwise = i + j
      diff o m inc
        | saturate m inc o /= o = Just (saturate m inc )
        | otherwise = Nothing

  (offsetB ,ev2) <- mdo
    let
      filt =  filterJust $ diff <$> offsetB <*> max <@> ev
      ev2 = (fmap concatenate $ unions [fmap const offsetE,filt ])
    offsetB <- ui $ accumB 0 ev2
    return (offsetB,ev2)
  element offset # sink UI.text (show <$> offsetB)
  let
     cev = flip ($) <$> offsetB <@> ev2
     offsetT = tidings offsetB cev
  return (TrivialWidget offsetT offparen)


attrLine inf ref i = L.intercalate "," (fmap renderShowable .  allKVRec' inf ref  $ i)
