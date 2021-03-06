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
import Debug.Trace
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
import TP.View
import TP.Widgets
import Text
import Types
import qualified Types.Index as G
import Types.Patch
import Utils


calendarSelector ini = do
    let buttonStyle k e = e # set UI.text (fromJust $ M.lookup k transRes)# set UI.class_ "btn-xs btn-default buttonSet"
          where transRes = M.fromList [("year","Ano"),("month","Mês"),("week","Semana"),("day","Dia"),("hour","Hora")]
        defView = "week"
        viewList = ["year","month","day","week","hour"] :: [String]
        capitalize (i:xs) = toUpper i : xs
        capitalize [] = []

    iday <- liftIO getCurrentTime
    v <- currentValue (facts ini)
    resolution <- fmap (fromMaybe defView) <$> buttonDivSetT  viewList (pure id) (pure $ Just defView ) (const UI.button)  buttonStyle

    next <- UI.button  # set text ">"
    today <- UI.button # set text "Hoje"
    prev <- UI.button  # set text "<"


    current <- UI.div # set children [prev,today,next]
    nextE <- UI.click next
    prevE <- UI.click prev
    todayE <- UI.click today
    let
      currentE = concatenate <$> unions  [ const <$> filterJust (rumors ini)
                                       , resRange False  <$> facts (triding resolution) <@ nextE
                                       , resRange True   <$> facts (triding resolution) <@ prevE
                                       , const (const iday) <$> todayE ]
    increment <- ui $ accumB (fromMaybe iday v) currentE
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
    authPred = [(keyRef "grantee",Left ( int $ usernameId inf ,Equals))] <> tablePred
  (orddb ,authorization,translation) <- ui $ transactionNoLog  (meta inf) $
      (,,) <$> selectFromTable "ordering" Nothing tablePred
           <*> selectFromTable "authorization" Nothing authPred
           <*> selectFromTable "table_name_translation" Nothing tablePred
  let
    ordRow orderMap pkset = field
      where
        field =  lookAttr' "usage" <$> G.lookup pk orderMap
        pk = ordPK pkset
    ordPK pkset = idex (meta inf) "ordering" [("table",int $ tableUnique pkset)]
  filterInp <- filterString
  let
    -- Table Description
    lookDescT =  flip (lookDesc inf) . primary <$> collectionTid translation
    -- Authorization
    autho_pk t = idex (meta inf) "authorization" [("table",int $ tableUnique t),("grantee",int $ usernameId inf)]
    authorize =  (\autho t -> isJust $ G.lookup (autho_pk t) autho) .primary <$> collectionTid authorization
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
      (ordRow . primary <$>  collectionTid orddb)
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
    (traverse (transaction (meta inf) . patchFrom (lookMeta (meta inf) "ordering") . (,PatchRow $ kvlistp incClick)))

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


paginateList
  :: Foldable t =>
     InformationSchema
     -> TableK Key
     -> Element
     -> Tidings (Maybe (WherePredicateK Key))
     -> (Tidings (IndexMetadata Key v), Tidings (TableRep Key Showable),
         c)
     -> t ([Rel Key],
           Tidings
             (C.Predicate (TBData Key Showable)))
     -> KVMeta Key
     -> Tidings (Maybe (TBData Key Showable))
     -> UI (Tidings [TBData Key Showable], Element)
paginateList inf table itemListEl predicate (vpt,gist,_) constr proj tdi =  do
      filterInp <- filterString
      wheel <- fmap negate <$> UI.mousewheel itemListEl
      let
        filtering i k = filter (T.isInfixOf (T.pack $ toLower <$> i) . T.toLower . T.pack . showFKText inf (tableMeta table)) k
        pageSize = 20
        lengthPage (IndexMetadata fixmap)  predicate = (s  `div` pageSize) +  if s `mod` pageSize /= 0 then 1 else 0
          where s = maybe 0 fst $  M.lookup (fromMaybe mempty predicate) fixmap
        sortList = reverse . L.sortOn (G.getIndex (tableMeta table))

      presort <- ui $ cacheTidings ( G.toList . primary <$> gist)
      -- Filter and paginate
      (offset,res3)<- do
        let
          aconstr = F.foldl' (\c (p,o) -> liftA2 (applyConstr p) c o ) presort constr
          applyConstr p m (C.Predicate c) =  filter (\f ->   not (c f))  m
        res3 <- ui$ cacheTidings (filtering  <$> triding filterInp <*> aconstr)
        element itemListEl # sink UI.size (show . (\i -> if i > 21 then 21 else (i +1 )) . length <$> facts res3)
        offset <- offsetField ((\j i -> maybe 0  (`div`pageSize) $ join $ fmap (\i -> L.elemIndex i j ) i) <$>  facts res3 <#> tdi) wheel  (flip lengthPage <$> facts predicate <*> facts vpt)
        return (offset, res3)

      -- Load offseted items
      let
        idxRequest = (,,) <$> facts vpt <#> predicate<*> triding offset
        loadPage (m,pred,i) = do
          let page = i `div` (opsPageSize (schemaOps inf) `div` pageSize)
          transactionNoLog inf $ selectFromProj (tableName table) (Just page ) (fromMaybe mempty pred) proj
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
  -> KVMeta Key
  -> Tidings [TBData Key Showable]
  -> UI (Tidings [TBData Key Showable], Element)
multiSelectListUI inf table itemListEl predicate ref@(_,vpt,_) constr proj tdi = do
  let m = tableMeta table
  (res4, fInp) <- paginateList inf table itemListEl predicate  ref constr proj (safeHead <$> tdi)
  lbox <- multiListBoxEl itemListEl (fmap (G.getIndex m )<$> res4 ) (fmap (G.getIndex m) <$> tdi) (showFKLook inf (tableMeta table) (primary <$> vpt))
  out <- UI.div # set children [fInp,itemListEl]
  return ((\i j -> catMaybes $ fmap (flip G.lookup  (primary j)) i) <$> triding lbox <*> vpt ,  out  )


selectListUI
  :: InformationSchema
   -> TableK CoreKey
   -> Element
   -> Tidings (Maybe WherePredicate)
   -> RefTables
   -> SelTBConstraint
   -> KVMeta Key
   -> Tidings (Maybe (TBData Key Showable))
   -> UI (Tidings (Maybe (TBData Key Showable)), Element)
selectListUI inf table itemListEl predicate ref@(_,vpt,_)  constr proj tdi = do
  first <- currentValue (facts tdi)
  -- When first item exist on creation always hold the selected item
  let buildList  a b = ((if isJust first && isJust b then (b :) else id) $ fmap Just (if isJust first && isJust b then L.delete (fromJust b) a else a))
  let m = tableMeta table
  (res4, fInp) <- paginateList inf table itemListEl predicate  ref constr proj tdi
  let resultItem = ((\a b -> Nothing: fmap (fmap (G.getIndex m)) (buildList a b) ) <$> res4 <*> tdi) 
  lbox <- listBoxEl 
      itemListEl 
      resultItem
      (fmap (Just . G.getIndex m)<$> tdi) 
      ((\i -> maybe (set text "None") (i$) )<$> showFKLook inf (tableMeta table) (primary <$> vpt))
  out <-  UI.div # set children [fInp,itemListEl]
  return ((\i j -> flip G.lookup  (primary j) =<< i) <$> (join <$> triding lbox) <*> vpt   ,out)

multiSelector
  :: InformationSchema
     -> TableK Key
     -> RefTables
     -> Tidings (Maybe WherePredicate)
     -> KVMeta Key
     -> Tidings [TBData Key Showable]
     -> UI (TrivialWidget [TBData Key Showable])
multiSelector inf table reftb@(vptmeta,vpt,var) predicate proj tdi = mdo
  itemListEl <- UI.select # set UI.style [("width","100%")] # set UI.size "21"
  (tds ,el) <- multiSelectListUI inf table itemListEl predicate reftb [] proj tdi
  itemSel <- UI.div # set children [el] # set UI.class_ "col-xs-12"
  return (TrivialWidget tds itemSel)


selector
  :: InformationSchema
     -> TableK Key
     -> RefTables
     -> Tidings (Maybe WherePredicate)
     -> KVMeta Key
     -> Tidings (Maybe (TBData Key Showable))
     -> UI (TrivialWidget (Maybe (TBData Key Showable)))
selector inf table reftb@(vptmeta,vpt,var) predicate proj tdi = mdo
  itemListEl <- UI.select # set UI.style [("width","100%")] # set UI.size "21"
  (tds ,el) <- selectListUI inf table itemListEl predicate reftb [] proj tdi
  itemSel <- UI.div # set children [el] # set UI.class_ "col-xs-12"
  return (TrivialWidget tds itemSel)


showFKLook inf m collection = (\col v j -> j  # set text (maybe ("No reference: " <> show  v) (showFKText inf m) (G.lookup v col ))) <$>  collection
showFK inf m = pure (\v j -> j  # set text (showFKText inf m v))

offsetField  initT eve  max = offsetFieldFiltered initT eve [max]

offsetFieldFiltered  initT eve maxes = do
  init <- currentValue (facts initT)
  offset <- UI.span# set (attr "contenteditable") "true" #  set UI.style [("width","50px")]
  lengs  <- mapM (\max -> UI.span # sink text (("/" ++) . show <$> max )) maxes
  offparen <- UI.div # set children (offset : lengs) # set UI.style [("text-align","center")]

  enter  <- UI.onChangeE offset
  whe <- UI.mousewheel offparen
  let max  = foldr1 (liftA2 min) (maxes)
  let offsetE =  filterJust $ (\m i -> if i <m then Just i else Nothing ) <$> max <@> (filterJust $ readMay <$> enter)
      ev = unionWith const (negate <$> whe ) eve
      saturate m i j
          | m == 0 = 0
          | i + j < 0  = 0
          | i + j > m  = m
          | otherwise = i + j
      diff  m inc
        = (saturate m inc )

  (offsetB ,ev2) <- mdo
    let
      filt =  diff <$> max <@> ev
      ev2 = (fmap concatenate $ unions [fmap const offsetE,filt ])
    offsetB <- ui $ accumB 0 ev2
    return (offsetB,ev2)
  element offset # sink UI.text (show <$> offsetB)
  let
     cev = flip ($) <$> offsetB <@> ev2
     offsetT = tidings offsetB cev
  return (TrivialWidget offsetT offparen)


attrLine inf ref i = L.intercalate "," (fmap renderShowable .  allKVRec' inf ref  $ i)
