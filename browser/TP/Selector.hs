{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module TP.Selector (tableOrder,calendarSelector,positionSel,tableChooser,selectFromTable,offsetFieldFiltered,offsetField,sorting',selectListUI) where

import TP.View
import Control.Monad.Writer (runWriterT, WriterT(..))
import Control.Lens (_1, _2, (^.), over)
import Safe
import qualified NonEmpty as Non
import Data.Maybe
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
      pred2 =  [(keyRef "schema",Left (int $ schemaId inf  ,Equals))]
      authPred =  [(keyRef "grantee",Left ( int $ fst $ username inf ,Equals))] <> pred2
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
      {-
  let
    ordRow orderMap pkset =  field
        where
          field =  G.lookup pk orderMap
          pk = idex (meta inf ) "ordering" [("table",int $ tableUnique  pkset ), ("schema",int $ schemaId inf)]
    incClick field =  (fst field , G.getIndex field ,[patch $ fmap (+SNumeric 1) usage])
        where
          usage = lookAttr' (meta inf ) "usage"   field
  onEvent
      ((\i j -> fmap incClick . ordRow i <$> M.keys j) <$> facts (collectionTid orddb) <@> rumors (triding bset))
      (ui . traverse (traverse (\p -> do
          _ <- transactionNoLog (meta inf ) $ patchFrom  p
          putPatch (patchVar $  iniRef orddb) [PatchRow p] )))
          -}

  element bset # set UI.style [("overflow","auto"),("height","99%")]
  header <- UI.div # set children [getElement all,filterInp] # set UI.style [("display","inline-flex")]
  tbChooserI <- UI.div # set children [header,getElement bset]  # set UI.style [("height","50vh")]
  return $ (TrivialWidget (triding bset) tbChooserI)

data AscDesc a
  = AscW a
  | DescW a
  deriving(Eq)

instance Ord a => Ord (AscDesc a) where
  compare (AscW a ) (AscW b) =  compare a b
  compare (DescW a ) (DescW b) = compare (Down a ) (Down b)


sorting' :: Ord k=> [(k ,Bool)] -> [TBData k Showable]-> [TBData k Showable]
sorting' ss  =  L.sortBy (comparing   (L.sortBy (comparing fst) . fmap (\((ix,i),e) -> (ix,if i then DescW e  else AscW e) ) . F.toList .M.intersectionWith (,) (M.fromList (zipWith (\i (k,v) -> (k ,(i,v))) [0::Int ..] ss)) . M.fromList . concat . fmap aattr  . F.toList . _kvvalues . unTB . snd )  )


selectListUI
  ::
     InformationSchema
     -> TableK CoreKey
     -> Tidings (Maybe WherePredicate)
     -> RefTables
     -> SelTBConstraint
     -> Tidings (Maybe (TBData Key Showable))
     -> UI (Tidings (Maybe (Maybe (TBData Key Showable))), [Element])
selectListUI inf targetTable predicate (vpt,_,gist,sgist,_) constr tdi = do
      filterInp <- UI.input # set UI.class_ "col-xs-3"
      filterInpE <- UI.valueChange filterInp
      filterInpBh <- ui $ stepper "" filterInpE
      itemListEl <- UI.select #  set UI.class_ "col-xs-5 fixed-label" # set UI.size "21" # set UI.style ([("position","absolute"),("z-index","999"),("top","22px")] )
      wheel <- fmap negate <$> UI.mousewheel itemListEl
      let
        filtering i  = T.isInfixOf (T.pack $ toLower <$> i) . T.toLower . T.pack . showFKText
        filterInpT = tidings filterInpBh filterInpE
        pageSize = 20
        lengthPage fixmap = (s  `div` pageSize) +  if s `mod` pageSize /= 0 then 1 else 0
          where (s,_) = fromMaybe (sum $ fmap fst $ F.toList fixmap ,M.empty ) $ M.lookup mempty fixmap
        preindex = maybe id (\i -> filterfixed targetTable i) <$> predicate <*> gist
        sortList :: Tidings ([TBData CoreKey Showable] -> [TBData CoreKey Showable])
        sortList =  sorting' <$> pure (fmap (,True) $ rawPK targetTable)

      presort <- ui $ cacheTidings (sortList <*> fmap G.toList  preindex)
      -- Filter and paginate
      (offset,res3)<- do
        let
          aconstr = liftA2 applyConstr presort constrT
          constrT =  traverse  snd constr
          applyConstr m l =  filter (F.foldl' (\l c ->  liftA2 (&&) l (not <$> c) ) (pure True)  l) m
        res3 <- ui$ cacheTidings (filter .filtering  <$> filterInpT <*> aconstr)
        element itemListEl # sink UI.size (show . (\i -> if i > 21 then 21 else (i +1 )) . length <$> facts res3)
        offset <- offsetField ((\j i -> maybe 0  (`div`pageSize) $ join $ fmap (\i -> L.elemIndex i j ) i )<$>  (facts res3) <#> tdi) wheel  (lengthPage <$> vpt)
        return (offset, res3)

      -- Load offseted items
      ui $onEventDyn (filterE (isJust . fst) $ (,) <$> facts predicate<@> rumors (triding offset)) $ (\(o,i) ->  do
        traverse (transactionNoLog inf . selectFrom' targetTable (Just $ i `div` (opsPageSize $ schemaOps inf) `div` pageSize) Nothing  []) o )

      -- Select page
      res4 <- ui $ cacheTidings ((\o -> L.take pageSize . L.drop (o*pageSize) ) <$> triding offset <*> res3)
      lbox <- listBoxEl itemListEl ((Nothing:) . fmap (Just ) <$>    res4 ) (fmap Just <$> tdi) (pure id) ((\i -> maybe id (i$) )<$> showFK)
      return ( triding lbox ,[itemListEl,filterInp,getElement offset])

showFK = pure (\v j -> j  # set text (showFKText v))

offsetField  initT eve  max = offsetFieldFiltered initT eve [max]

offsetFieldFiltered  initT eve maxes = do
  init <- currentValue (facts initT)
  offset <- UI.span# set (attr "contenteditable") "true" #  set UI.style [("width","50px")]

  lengs  <- mapM (\max -> UI.span # sink text (("/" ++) .show  <$> facts max )) maxes
  offparen <- UI.div # set children (offset : lengs) # set UI.style [("border","2px solid black"),("margin-left","4px") , ("margin-right","4px"),("text-align","center")]

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
      filt = ( filterJust $ diff <$> offsetB <*> max <@> fmap (*3) ev  )
      ev2 = (fmap concatenate $ unions [fmap const offsetE,filt ])
    offsetB <- ui $ accumB 0 (  ev2)
    return (offsetB,ev2)
  element offset # sink UI.text (show <$> offsetB)
  let
     cev = flip ($) <$> offsetB <@> ev2
     offsetT = tidings offsetB cev
  return (TrivialWidget offsetT offparen)


