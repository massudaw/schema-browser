{-# LANGUAGE
    OverloadedStrings
   ,ScopedTypeVariables
   ,TypeFamilies
   ,FlexibleContexts
   ,GADTs
   ,RecursiveDo
 #-}

module TP.QueryWidgets (
    crudUITable,
    batchUITable,
    metaTable,
    ) where

import Data.Tuple
import Debug.Trace
import Safe
import qualified Data.Functor.Contravariant as C
import Serializer
import qualified Data.Aeson as A
import Control.Lens ((^?), _1, _2)
import PrimEditor
import qualified Control.Lens as Le
import qualified Control.Category as Cat
import Serializer (decodeT)
import Control.Monad
import Control.Arrow hiding (first,second)
import Control.Monad.Catch
import Control.Monad.Writer hiding ((<>))
import Data.Bifunctor
import qualified Data.ByteString.Base64 as B64
import qualified Data.ByteString.Char8 as BSC
import qualified Data.ByteString.Lazy.Char8 as BSL
import Data.Either
import qualified Data.Foldable as F
import Data.Foldable (foldl')
import qualified Data.GiST.GiST as G
import qualified Data.HashMap.Strict as HM
import qualified Data.Interval as Interval
import qualified Data.List as L
import qualified Data.Map as M
import Data.Map (Map)
import Data.Maybe
import qualified Data.Poset as P
import Data.Semigroup hiding (diff)
import qualified Data.Set as S
import Data.Set (Set)
import Data.Text (Text)
import qualified Data.Text as T
import Data.Time
import qualified Data.Traversable as Tra
import Default
import Expression
import qualified Graphics.UI.Threepenny as UI
import Graphics.UI.Threepenny.Core hiding (apply)
import Graphics.UI.Threepenny.Internal (ui)
import qualified NonEmpty as Non
import Query
import RuntimeTypes
import Schema
import SchemaQuery
import Step.Host
import TP.AgendaSelector
import TP.MapSelector
import TP.Selector
import TP.Widgets
import Text
import Types
import qualified Types.Index as G
import Types.Patch
import Utils

type ColumnTidings = Map (S.Set (Rel CoreKey )) (Tidings (Editor (Index(Column CoreKey Showable))),Tidings (Maybe (Column CoreKey Showable)))

genAttr :: InformationSchema -> CoreKey -> Column CoreKey ()
genAttr inf k =
  case keyType k of
    Primitive ty p ->
       case p of
         AtomicPrim l -> Attr k (kfold ty $ TB1 ())
         RecordPrim (s,t) ->
           let table =  lookTable sch t
               sch = fromMaybe inf (HM.lookup s (depschema inf))
            in IT k $ kfold ty $  TB1 $ allRec' (tableMap sch) table
  where
    kfold l = F.foldl' (.) id (kgen <$> l)
    kgen :: KTypePrim -> FTB a -> FTB a
    kgen KOptional = LeftTB1 . pure
    kgen KArray = ArrayTB1 . pure

execute
  :: InformationSchema
  -> Text
  -> Plugins
  -> Maybe (TBData Key Showable)
  -> IO (Maybe (TBIdx Key Showable))
execute inf t (idp,p) = fmap join . traverse (\ v -> fmap (join . eitherToMaybe) . catchPluginException inf (tableUnique table ) idp ( getPKM (tableMeta table)   v)   . exec (_plugAction p ) $ v )
  where
    table = lookTable inf t
    actiona f v = fmap (join . fmap (diff v . liftTable' inf t)) . f  $  mapKey' keyValue v
    actiond f v = fmap (join . fmap (\a -> diff v  =<< (applyIfChange v .liftPatch inf t $a))) . f $ mapKey' keyValue v
    exec p@(PurePlugin _) = actiona (pluginAction' p)
    exec p@(DiffPurePlugin _) = actiond (pluginActionDiff' p)
    exec p@(DiffIOPlugin _) = actiond (pluginActionDiff' p)
    exec p@(IOPlugin _) = actiona (pluginAction' p)

pluginUI
  :: InformationSchema
  -> Tidings (Maybe (TBData CoreKey Showable) )
  -> Plugins
  -> UI (Element ,(Union (Access Key),Tidings (Maybe (Index (TBData CoreKey Showable)))))
pluginUI oinf trinp (idp,FPlugins n tname (StatefullPlugin ac)) = do
  let
    fresh :: [([VarDef],[VarDef])]
    fresh = fmap fst ac
  b <- flabel # set UI.text (T.unpack n)
  inf <- liftIO $ foldl' (\i (kn,kty) -> (\m -> createFresh  tname m kn kty) =<< i ) (return  oinf) (concat $ fmap fst fresh <> fmap snd fresh )
  let
      freshKeys :: [([CoreKey],[CoreKey])]
      freshKeys = first (fmap lookK ) . second (fmap lookK) <$> fresh
      lookK = lookKey inf tname . fst
  freshUI <- foldl' (\old (aci ,(inpfresh,outfresh)) -> (old >>= (\(l,unoldItems)-> do
      let inputs fresh = attrB   (genAttr oinf fresh)
          attrB a = do
            let pre = const Nothing <$> unoldItems
            wn <-  tbCaseDiff  inf  (lookTable oinf tname) mempty a mempty  mempty pre
            v <- labelCaseDiff inf a pre (triding wn)
            out <- UI.div # set children [getElement v,getElement wn]#  set UI.class_ ("col-xs-" <> show (fst $  attrSize a))
            return  $ TrivialWidget (apply <$> facts pre <#> triding v) out
      elemsIn <- mapM  inputs inpfresh
      let
        inp :: Tidings (Maybe (TBData CoreKey Showable))
        inp = fmap kvlist <$> foldr (liftA2 (liftA2 (:))) (pure (Just [])) (fmap triding elemsIn)

      (preinp,(_,liftedE )) <- pluginUI  inf (liftA2 mergeTB1 <$>  unoldItems <*>  inp) (idp,FPlugins n tname aci)

      let outputs fresh =  attrB (fmap (\v ->  justError ("no key " <> show fresh <> " in " <>  show v ) .fmap snd $ findKV ((== (S.singleton $ Inline fresh)) . index) =<< createIfChange v)  <$> liftedE  )  (genAttr oinf fresh)
          attrB pre a = do
            wn <-  tbCaseDiff inf (lookTable oinf tname) []  a M.empty [] pre
            TrivialWidget v e <- labelCaseDiff inf a  pre (triding wn)
            out <- UI.div # set children [getElement e,getElement wn] #  set UI.class_ ("col-xs-" <> show (fst $  attrSize a))
            return $ TrivialWidget (apply <$> pre <*> v ) out

      elemsOut <- mapM outputs outfresh

      let styleUI =  set UI.class_ "row"
            . set UI.style [("border","1px"),("border-color","gray"),("border-style","solid"),("margin","1px")]
      j <- UI.div # styleUI  # set children (fmap getElement elemsIn <> [preinp]) # sink UI.style (noneShow .isJust <$> facts unoldItems)
      k <- UI.div # styleUI  # set children (fmap getElement elemsOut) # sink UI.style (noneShow .isJust <$> facts liftedE  )
      return  ( l <> [j , k] , mergePatches  <$> facts unoldItems <#>  liftedE  ))
           ) ) (return ([],trinp)) $ zip (fmap snd ac) freshKeys
  el <- UI.div  # set children (b: fst freshUI)
  let evdiff = fmap join $ liftA2 diff <$>  facts trinp <#> snd freshUI
  return (el , (liftAccessU inf tname  $snd $ pluginStatic' $ snd $ last ac , evdiff ))

pluginUI inf oldItems pl@(idp,FPlugins n t p) =
    case p of
      IOPlugin _ -> uiio
      DiffIOPlugin _ -> uiio
      PurePlugin _ -> uipure
      DiffPurePlugin _ -> uipure
  where
    (tdInput, tdOutput,out)
        = checkAccessFull inf t (pluginStatic' p) oldItems
    headerUI
      = UI.button
      # set UI.class_ "btn btn-sm"
      # set text (T.unpack n)
      # sink UI.enabled (isJust <$> facts tdInput)
      # set UI.style [("color","white")]
      # sink UI.style (liftA2 greenRedBlue  (isJust <$> facts tdInput) (isJust <$> facts tdOutput))
    uiio = do
      headerP <-  headerUI
      cliHeader <- UI.click headerP
      let ecv = const <$> facts tdInput <@ cliHeader
      ini <- currentValue (facts tdInput)
      let ecv1 = unionWith const (const (const Nothing) <$> rumors tdInput ) ecv
      bcv <- ui $ accumT ini ecv1
      pgOut  <- ui $mapTEventDyn (liftIO . execute inf t pl)  bcv
      return (headerP, (out,  pgOut ))
    uipure = do
      headerP <- headerUI
      pgOut <- ui $mapTEventDyn (liftIO . execute inf t pl) tdInput
      return (headerP, (out,   pgOut ))


checkAccessFull
  :: Functor f =>
     InformationSchema
     -> Text
     -> (Union (Access Text),Union (Access Text))
     -> f (Maybe (TBData Key Showable))
     -> (f (Maybe (TBData Key Showable)),
         f (Maybe (TBData Key Showable)),
         Union (Access Key))
checkAccessFull inf  t arrow oldItems = (tdInput,tdOutput,out)
    where
      (inp,out) = second (liftAccessU inf t ). first (liftAccessU  inf t ) $ arrow
      pred =  WherePredicate . fmap fixrel<$> genPredicateFullU True inp
      tdInput = join . fmap (checkPredFull pred) <$> oldItems
      predOut =  WherePredicate . fmap fixrel <$> genPredicateFullU True out
      tdOutput = join . fmap (checkPredFull predOut)  <$> oldItems
      checkPredFull pred i
          =  if maybe False (G.checkPred i) pred then  Just i else Nothing

prodRef = IProd Nothing

indexPluginAttrDiff
  :: Column Key ()
  -> [(Union (Access Key), Tidings (Maybe (Index (TBData Key Showable))))]
  -> [(Union (Access Key), Tidings (Maybe (Index (Column Key Showable))))]
indexPluginAttrDiff a@(Attr i _ )  plugItens =  evs
  where
    match (IProd _ l) ( IProd _ f) = l == f
    match i f = False
    thisPlugs = filter (hasProd (`match` head (prodRef . _relOrigin <$> keyattr a)) . fst)  plugItens
    evs  = fmap (fmap (join . fmap (F.find ((== index a)  . index )  ))) <$>  thisPlugs
indexPluginAttrDiff  i  plugItens = pfks
  where
    thisPlugs = filter (hasProd (isNested (fmap (prodRef . _relOrigin) (keyattr i) )) .  fst) plugItens
    pfks =  first (uNest . justError "No nested Prod FKT" .  findProd (isNested(fmap ( prodRef . _relOrigin ) (keyattr i) ))) . second (fmap (join . fmap (F.find ((==  index i)  . index ) ))) <$>  thisPlugs


--- Style and Attribute Size
--
attrSize :: Column CoreKey b -> (Int,Int)
attrSize FKT{} = (12,4)
attrSize (IT _ _ ) = (12,4)
attrSize (Attr k _ ) = goAttSize  (keyType k)
attrSize (Fun k _ _ ) = goAttSize  (keyType k)

goAttSize :: KType CorePrim -> (Int,Int)
goAttSize (Primitive l (AtomicPrim i)) = go l
  where
    go [] = case  i of
       PInt _ -> (3,1)
       PText-> (3,1)
       PDimensional _ _ -> (3,1)
       PTime PDate -> (3,1)
       PColor-> (3,1)
       PTime (PTimestamp _ )-> (3,1)
       PTime PDayTime -> (3,1)
       PAddress -> (12,8)
       PMime m -> case m of
              "image/jpg" ->  (4,8)
              "application/pdf" ->  (6,8)
              "application/x-ofx" ->  (6,8)
              "text/plain" ->  (12,8)
              "text/html" ->  (12,8)
              i  ->  (6,8)
       i -> (3,1)
    go  (i:l) = case i of
      KOptional  ->  go l
      KSerial  -> go l
      KArray  -> let (i1,i2) = go l in (i1,i2*8)
      KInterval  -> let (i1,i2) = go l in (i1*2 ,i2)

getRelOrigin :: [Column k () ] -> [k ]
getRelOrigin =  fmap _relOrigin . concatMap keyattr

attributeLabel :: Column CoreKey () -> String
attributeLabel = L.intercalate "," . fmap renderRel .  F.toList . index

labelCaseDiff
  ::  InformationSchema
  -> Column CoreKey ()
  -> Tidings (Maybe (Column CoreKey Showable))
  -> Tidings (Editor (Index (Column CoreKey Showable)))
  -> UI (TrivialWidget (Editor (Index (Column CoreKey Showable))))
labelCaseDiff inf a o wid = do
  let
    dynShow = do
      lref <- UI.div
        # set text (show $ keyattr  a)
      ltype <- UI.div
        # set text (show $ keyType . _relOrigin <$> keyattr  a)
      ldelta <- UI.div
        # sinkDiff text  (show <$> wid)
      UI.div # set children [lref,ltype,ldelta]
  hl <- detailsLabel (set UI.text (attributeLabel a) . (>>= paintEditDiff o wid)) dynShow
  return $ TrivialWidget wid hl

paintEditDiff o i e = element e # sinkDiff UI.style ( st <$> (cond <$> o <*> i ))
  where cond _ Delete = ("red","white")
        cond Nothing Keep = ("purple","white")
        cond (Just i)  Keep = ("black","white")
        cond (Just _) (Diff i) = ("yellow","black")
        cond Nothing  (Diff i) = ("lightblue","black")
        st (back,font)= [("background-color",back),("color",font)]


filterConstr rel  = filter ((`S.isSubsetOf` S.fromList  rel) . S.map _relOrigin. S.unions . fst)

tbCaseDiff
  :: InformationSchema
  -> Table
  -> SelPKConstraint
  -> Column CoreKey ()
  -> ColumnTidings
  -> PluginRef (Column CoreKey Showable)
  -> Tidings (Maybe (Column CoreKey Showable))
  -> UI (LayoutWidget (Editor (Index (Column CoreKey Showable))))
tbCaseDiff inf table constr i@(FKT ifk  rel tb1) wl plugItens oldItems= do
    let
      nonInj = S.fromList (_relOrigin <$> rel) `S.difference` S.fromList (getRelOrigin $ unkvlist ifk)
      nonInjRefs = M.filterWithKey (\k _ -> (\i -> not (S.null i) && S.isSubsetOf i nonInj ) . S.map _relOrigin $ k) wl
      relTable = M.fromList $ fmap (_relTarget &&& _relOrigin) rel
      restrictConstraint =  filterConstr (fmap _relOrigin rel) constr
      reflectFK' rel box = (\ref -> pure $ FKT ref rel (TB1 box)) <$> reflectFK frel box
        where frel = filter (\i -> isJust $ M.lookup (S.singleton (Inline (_relOrigin i))) (_kvvalues ifk)) rel
      convertConstr (f,j) = (f, fmap (\(C.Predicate constr) ->  C.Predicate $ maybe False constr  .  reflectFK' rel ) j)
    fkUITableGen inf table (convertConstr <$>  restrictConstraint) plugItens  nonInjRefs oldItems  i

tbCaseDiff inf table constr i@(IT na tb1 ) wl plugItems oldItems = do
    let restrictConstraint = filter ((`S.isSubsetOf` S.singleton na ) . S.map _relOrigin. S.unions  .fst) constr
    iUITableDiff inf restrictConstraint plugItems oldItems i
tbCaseDiff inf table _ a@(Attr i _ ) wl plugItens preoldItems = do
  let oldItems = maybe preoldItems (\v-> fmap (maybe (Attr i <$> (evaluateKeyStatic v)) Just ) preoldItems  ) ( keyStatic i)
      tdiv = fmap _tbattr <$> oldItems
      insertT = fmap (PAttr i)
  fmap insertT <$> buildUIDiff (buildPrimitive (keyModifier i)) (keyType i) (fmap (fmap (fmap (\(PAttr _ v) -> v))) <$> plugItens) tdiv

tbCaseDiff inf table _ a@(Fun i rel ac ) wl plugItens preoldItems = do
  let
    search (Inline t) = fmap (fmap _tbattr) . recoverValue <$> M.lookup (S.singleton  (Inline t)) wl
    search (RelAccess t m) =  fmap (fmap joinFTB . join . fmap (traverse (recLookup m) . _fkttable)) . recoverValue <$> M.lookup (S.fromList t)  wl
    refs = sequenceA . catMaybes $ search <$> snd rel

  funinp <- traverseUI (traverse (liftIO . evaluateFFI (rootconn inf) (fst rel) funmap (buildAccess <$> snd rel)) . allMaybes) refs
  ev <- buildUIDiff (buildPrimitive [FRead]) (keyType i) [] funinp
  return $ LayoutWidget (diff' <$> preoldItems <*> (fmap (Fun i rel) <$>  funinp)) (getElement ev) (getLayout ev)



recoverValue (i,j) = liftA2 (\i j -> join (applyIfChange i j) <|> (join $ createIfChange j) <|> i ) j i


select table  = do
  inf <-askInf
  (_,(_,TableRep (_,_,evMap ))) <- tableLoaderAll (lookTable inf table) Nothing Nothing [] mempty Nothing
  return (decodeT . mapKey' keyValue <$> evMap)

loadPlugins :: InformationSchema -> Dynamic [Plugins]
loadPlugins inf =  do
  code <- liftIO$ indexSchema  (rootRef inf) "code"
  F.toList <$> transactionNoLog  code (select "plugin_code")


traRepl :: Ord k => Union (Access k) -> Union (Access k)
traRepl  = foldMap repl
  where
    repl :: Ord k =>Access k-> Union (Access k)
    repl (Rec  ix v ) = replaceU ix v v
    repl v = Many [v]

instance Compact a => Semigroup (Editor a) where
  i <> j = fromMaybe Keep $ safeHead $ compact [i,j]


anyColumns
  :: InformationSchema
   -> Bool
   -> UI Element
   -> SelPKConstraint
   -> Table
   -> ColumnTidings
   -> PluginRef (TBData CoreKey Showable)
   -> TBData Key ()
   -> Tidings (Maybe (TBData CoreKey Showable))
   -> [(Set (Rel Key),TB Key ())]
   ->  UI (LayoutWidget  (Editor (TBIdx CoreKey Showable)))
anyColumns inf hasLabel el constr table refs plugmods  k oldItems cols =  mdo
      let
        fks2 = M.fromList $ run <$> cols
        initialAttr = join . fmap (\ j -> safeHead $ catMaybes  $ unLeftItens <$> F.toList (_kvvalues j))  <$>oldItems
        sumButtom itb =  do
          el <- UI.div
          element =<< labelCaseDiff inf (fromJust $ M.lookup itb (unKV k)) (join . fmap (M.lookup itb . unKV) <$> oldItems) ((\i j -> if i == itb then j else Keep) <$> triding chk <*> triding fks)
        marker i = sink  UI.style ((\b -> if not b then [("border","1.0px gray solid"),("background","gray"),("border-top-right-radius","0.25em"),("border-top-left-radius","0.25em")] else [("border","1.5px white solid"),("background","white")] )<$> i)

      chk <- buttonDivSetO (M.keys (unKV k))  (fmap index <$> initialAttr)  marker sumButtom
      fks <- switchManyLayout (triding chk) fks2
      element chk # set UI.style [("display","inline-flex")]
      let
        resei :: Tidings (Editor (TBIdx CoreKey Showable))
        resei = fmap pure <$> triding fks
      listBody <- UI.div #  set children (getElement chk : [getElement fks])
      return (LayoutWidget resei listBody (getLayout fks))
  where
    meta = tableMeta table
    run (l,m) = (l,do
      let hasEl = L.any (mAny (maybe False (l==) . safeHead ))  (fmap (fmap S.fromList ) <$> _kvrecrels meta)
          plugattr = indexPluginAttrDiff m plugmods
          oldref = join . fmap ((^?  Le.ix l ) . _kvvalues ) <$> oldItems
      tbCaseDiff inf table constr m  M.empty plugattr oldref
      )



buildFKS
  :: InformationSchema
   -> Bool
   -> UI Element
   -> SelPKConstraint
   -> Table
   -> ColumnTidings
   -> PluginRef (TBData CoreKey Showable)
   -> Tidings (Maybe (TBData CoreKey Showable))
   -> [(Set (Rel Key),TB Key ())]
   -> UI [(Set (Rel Key), (LayoutWidget (Editor (PathAttr CoreKey Showable)),
                             Tidings (Maybe (Column CoreKey Showable))))]
buildFKS inf hasLabel el constr table refs plugmods   oldItems =  F.foldl'  run (return [])
  where
    meta = tableMeta table
    run jm (l,m) = do
        w <- jm
        let hasEl = L.any (mAny (maybe False (l==) . safeHead ))  (fmap (fmap S.fromList ) <$> _kvrecrels meta)
            plugattr = indexPluginAttrDiff m plugmods
            oldref = join . fmap ((^?  Le.ix l ) . _kvvalues) <$> oldItems
            aref = M.lookup l refs
            replaceNonInj = maybe [] (\j -> pure (Many ((IProd Nothing. _relOrigin <$> F.toList l)), onDiff  Just  (const Nothing)<$> fst j))  aref
        wn <-  tbCaseDiff inf table constr m  (M.fromList $ fmap (first triding) <$> w) (replaceNonInj <> plugattr) oldref
        lab <- if
          hasLabel
          then do
            (\i -> LayoutWidget (triding wn) i (getLayout wn)) <$> el # set children [getElement wn]
          else do
            v <- labelCaseDiff inf m oldref (diff' <$> oldref <*> checkDefaults inf table  (index m) (wn,oldref))
            out <- el # set children [getElement v,getElement  wn]
            return $ LayoutWidget (triding wn) out (getLayout wn)
        return (w <> [( index m,(lab,oldref))] )

deleteCurrentUn
  :: Foldable f
  => KVMetadata Key
  -> [Key]
  -> f (TBData Key Showable)
  -> G.GiST (TBIndex Showable) a
  -> G.GiST (TBIndex Showable) a
deleteCurrentUn m un l e =  foldl' (\l e -> G.delete (G.getUnique un e) G.indexParam l) e l

tableConstraints
  :: Foldable f =>
     (KVMetadata Key,
      Tidings (Map [Key] (G.GiST (TBIndex Showable) a1)),
      Tidings (G.GiST (TBIndex Showable) a3))
     -> Tidings (f (TBData Key Showable)) -> KV Key a -> SelPKConstraint
tableConstraints (m ,sgist,gist) preoldItems ftb = constraints
  where
    primaryConstraint = (M.keys $ _kvvalues $ tbPK m ftb ,  C.Predicate . flip ( checkGist m un .kvlist ) <$> (deleteCurrentUn m un  <$> preoldItems <*> gist))
      where un = _kvpk m
    secondaryConstraints un = (M.keys $ _kvvalues $ tbUn (S.fromList un ) ftb ,  C.Predicate . flip ( checkGist m un .kvlist ) <$>  (deleteCurrentUn m un <$> preoldItems <*> (fromJust . M.lookup un <$>  sgist)))
    constraints :: SelPKConstraint
    constraints = primaryConstraint : (secondaryConstraints <$> _kvuniques m)

batchUITable
   :: InformationSchema
   -> Table
   -> RefTables
   -> ColumnTidings
   -> PluginRef (TBData CoreKey Showable)
   -> TBData CoreKey ()
   -> Tidings [TBData CoreKey Showable]
   -> UI (TrivialWidget [Editor (TBIdx CoreKey Showable)])
batchUITable inf table reftb@(_, gist ,sgist,tref) refs pmods ftb  preoldItems2 = do
  let
    m = tableMeta table
  preoldItems <- ui $ loadItems inf table  preoldItems2
  let arraySize = 30
      index = flip atMay
      constraints = tableConstraints (m,sgist,gist) preoldItems ftb
      unIndexEl ix =  index ix <$> preoldItems
      dyn = dynHandlerPatch  (\ix valix plix ->do
        (listBody,tablebdiff) <- rowTableDiff inf table constraints refs pmods ftb ix valix
        return $ LayoutWidget tablebdiff listBody (pure (12,0))) unIndexEl (\ix -> [])

  widgets <- fst <$> foldl' (\i j -> dyn j =<< i ) (return ([],pure True)) [0..arraySize -1 ]

  let
    widgets2 = Tra.sequenceA (triding <$> widgets)
  headers <- rowTableHeaders ftb
  out <- UI.div # set UI.style [("display","flex"),("flex-flow","column")]
      # set children (headers : (getElement <$> widgets))
  divTable <- UI.div
      # set children [out]
      # set UI.class_ "col-xs-12"
      # set UI.style [("overflow-x","auto")]
  TrivialWidget widgets2 <$> UI.div # set children [divTable]


rowTableHeaders
  :: TBData CoreKey () -> UI Element
rowTableHeaders  ftb = do
  ixE <- UI.div # set UI.class_ "col-xs-1" # set text "#"
  operation <- UI.div # set UI.class_ "col-xs-1"# set text "Action"
  let
    label (k,x) = do
      l <- detailsLabel (set UI.text (attributeLabel x )) (UI.div # set text (show $ index x))
      UI.div # set children [l] # set UI.class_ ("col-xs-" <> show (fst (attrSize x)))
    srefs = P.sortBy (P.comparing (RelSort .F.toList . fst) ) . M.toList $ (_kvvalues ftb)
  els <- mapM label srefs
  UI.div # set children (ixE : operation : els) # set UI.style [("display", "flex")]

validateRow :: WidgetValue f =>
     InformationSchema
  -> Table
  -> [( S.Set (Rel CoreKey)
      , ( f (Editor (PathAttr CoreKey Showable))
        , Tidings (Maybe (Column CoreKey Showable))))]
  -> Tidings (Editor (TBIdx CoreKey Showable))
validateRow inf table fks =
  ifValid <$>
  sequenceTable fks <*>
  isValid fks
  where
    ifValid i j =
      if isJust j
        then i
        else Keep
    sequenceTable fks =
      reduceTable <$> Tra.sequenceA (triding . fst . snd <$> fks)
    isValid fks = sequenceA <$> sequenceA (uncurry (checkDefaults inf table) <$> fks)

checkDefaults inf table k  (r, i) = liftA2 applyDefaults i (triding r)
  where
    defTable = defaultTableType inf table
    applyDefaults i j =
      join (applyIfChange i j) <|> join (createIfChange (def j)) <|> i
    def (Diff i) =
      Diff . maybe i (\a -> head $ compact [a, i]) $
      L.find (\a -> index a == k) defTable
    def Keep = maybe Keep Diff $ L.find (\a -> index a == k) defTable


rowTableDiff
  :: InformationSchema
  -> Table
  -> SelPKConstraint
  -> ColumnTidings
  -> PluginRef (TBData CoreKey Showable)
  -> TBData CoreKey ()
  -> Int
  -> Tidings (Maybe (TBData CoreKey Showable))
  -> UI (Element,Tidings (Editor (TBIdx CoreKey Showable)))
rowTableDiff inf table constr refs plmods ftb@k ix preOldItems = do
  ixE <- UI.div # set text (show ix) # set UI.class_ "col-xs-1"
  operation <- UI.div # set UI.class_ "col-xs-1"
  oldItems <- ui $ cacheTidings preOldItems
  plugins <- ui $ loadPlugins inf
  let
    meta = tableMeta table
  res <- mapM (pluginUI inf oldItems) (filter ((== rawName table ) . _bounds .  snd) plugins )

  let
    resdiff =   snd <$> res
    srefs :: [(Set (Rel Key),TB Key ())]
    srefs = P.sortBy (P.comparing (RelSort .F.toList . fst)) . M.toList $ replaceRecRel (_kvvalues ftb) (fmap (fmap S.fromList )  <$> _kvrecrels meta)
    plugmods = first traRepl <$> (resdiff <> plmods)

    isSum = rawIsSum table
  (listBody,output) <- do
      fks <- buildFKS inf True UI.div constr table refs plugmods oldItems srefs
      mapM (\(s,(i,_)) -> element (getElement  i) #  sink UI.class_ (facts $ (\i -> "col-xs-" <> show (fst   i)) <$> getLayout i)) fks
      listBody <- UI.div # set children (ixE :operation:( getElement .fst . snd  <$> fks)) # set UI.style [("display", "flex"),("min-width","max-content")]
      return (listBody, validateRow inf table fks)
  element listBody
    # set style [("border","1px"),("border-color",maybe "gray" (('#':).T.unpack) (schemaColor inf)),("border-style","solid"),("margin","1px")]
  let out = output

  reftb <- ui $ refTables inf table
  (outI ,_)<- processPanelTable listBody inf reftb  out table preOldItems
  element operation #  set children (fmap fst res <> [outI])
  return (listBody , out)

eiTableDiff
  :: InformationSchema
  -> Table
  -> SelPKConstraint
  -> ColumnTidings
  -> PluginRef (TBData CoreKey Showable)
  -> TBData CoreKey ()
  -> Tidings (Maybe (TBData CoreKey Showable))
  -> UI (LayoutWidget (Editor (TBIdx CoreKey Showable)))
eiTableDiff inf table constr refs plmods ftb@k preOldItems = do
  oldItems <- ui $ cacheTidings preOldItems
  plugins <- ui $ loadPlugins inf
  let
    meta = tableMeta table
  res <- mapM (pluginUI inf oldItems) (filter ((== rawName table ) . _bounds .  snd) plugins )

  let
    resdiff =   snd <$> res
    srefs :: [(Set (Rel Key),TB Key ())]
    srefs = P.sortBy (P.comparing (RelSort .F.toList . fst) ) . M.toList $ (_kvvalues ftb) -- replaceRecRel (_kvvalues ftb) (fmap (fmap S.fromList )  <$> _kvrecrels meta)
    plugmods = first traRepl <$> (resdiff <> plmods)

  let isSum = rawIsSum table
  LayoutWidget output listBody layout <- if isSum
    then
      anyColumns inf isSum UI.div constr table refs plugmods ftb oldItems srefs
    else  do
      fks <- buildFKS inf isSum UI.div constr table refs plugmods oldItems srefs
      mapM (\(s,(i,_)) -> element (getElement  i) #  sink UI.class_ (facts $ (\i -> "col-xs-" <> show (fst   i)) <$> getLayout i)) fks
      listBody <- UI.div # set children (getElement .fst . snd  <$> fks)
      let vertical = (\i -> (min (fst i )  12,max (snd i)  1 ) ) . foldl1 horizontalL <$> sequenceA(getLayout . fst .snd <$>  fks)
      return $ LayoutWidget (validateRow inf table fks) listBody  vertical
  element listBody
    # set UI.class_ "row"
    # set style [("border","1px"),("border-color",maybe "gray" (('#':).T.unpack) (schemaColor inf)),("border-style","solid"),("margin","1px")]
  plugins <-
    pure <$> UI.div # set children (fst <$> res)
  body <- UI.div
    # set children (plugins  <> pure listBody)
    # set style [("margin-left","0px"),("border","2px"),("border-color",maybe "gray" (('#':).T.unpack) (schemaColor inf)),("border-style","solid")]
  return $ LayoutWidget output body layout


loadItems
  :: Traversable t =>
     InformationSchema
     -> Table
     -> Tidings (t (TBData CoreKey Showable))
     -> Dynamic (Tidings (t (TBData CoreKey Showable)))
loadItems inf table preoldItems
  = mapTidingsDyn
    (traverse
      (\i -> do
        v <- transactionNoLog inf . getItem $ i
        return $ maybe i (justError "cant apply" . applyIfChange i) v))
    preoldItems
  where
    getItem v = getFrom table v

crudUITable
   :: InformationSchema
   -> Table
   -> RefTables
   -> ColumnTidings
   -> PluginRef (TBData CoreKey Showable)
   -> TBData CoreKey ()
   -> Tidings (Maybe (TBData CoreKey Showable))
   -> UI (LayoutWidget (Editor (TBIdx CoreKey Showable)))
crudUITable inf table reftb@(_,gist ,sgist,_) refs pmods ftb  preoldItems2 = do
  let
    m = tableMeta table
  preoldItems <- ui $ loadItems inf table preoldItems2
  let
    constraints = tableConstraints (m,sgist,gist) preoldItems ftb
  LayoutWidget tablebdiff listBody layout <- eiTableDiff inf  table constraints refs pmods ftb preoldItems
  (panelItems ,e)<- processPanelTable listBody inf reftb tablebdiff table preoldItems

  errors <- printErrors e
  debug <- debugConsole   preoldItems tablebdiff
  let
  out <- UI.div # set children [listBody,panelItems,errors,debug]
  return $ LayoutWidget tablebdiff out layout

openClose open = do
  let translate True = "expand"
      translate False = "collapse-up"
  nav  <- buttonDivSet [True,False] (fmap Just open)
      (\i -> UI.button
          # set UI.style [("font-size","unset"),("font-weight","bolder")]
          # set UI.class_ ("buttonSet btn-xs btn-default btn pull-left glyphicon glyphicon-" <> translate i))
  return nav

dynCrudUITable
   :: InformationSchema
   -> Tidings Bool
   -> ColumnTidings
   -> PluginRef (TBData CoreKey Showable)
   -> Table
   -> Tidings (Maybe (TBData CoreKey Showable))
   -> UI (LayoutWidget (Editor (TBIdx CoreKey Showable)))
dynCrudUITable inf nav refs pmods table preoldItems = do
  switchUILayout delta UI.div nav
      (do
        reftb@(_,gist,sgist,_) <- ui $ refTables inf   table
        crudUITable inf table reftb refs pmods (allRec' (tableMap inf) table) preoldItems)
    where delta = compactPlugins preoldItems pmods

mergePatches i j = join $ (liftA2 applyIfChange i j)<|> (createIfChange <$> j) <|> Just i

onDiff f g (Diff i ) = f i
onDiff f g v = g v

filterKey enabled k = void (filterApply (const <$> enabled) k)
containsOneGist table ref = (==1).  L.length . conflictGist  table ref
containsGist table ref = not . L.null .   conflictGist  table ref
conflictGist table ref map = case  G.tbpredM (tableMeta table) ref of
              Just i -> G.search i map
              Nothing -> []

catchEd  m  = (Right <$> sequence m) `catchAll` (\ e -> return (Left (show e)))

insertCommand lbox inf table inscrudp inscrud  authorize gist = do
    altI <- onAltI lbox
    let insertEnabled = liftA3 (\i j k -> i && j && k ) (isDiff <$> inscrudp ) (maybe False  (\i -> (isRight .tableCheck m  $ i) || isJust (matchInsert inf (tableMeta table ) i) ) <$>  inscrud) (liftA2 (\j -> maybe True (not. (flip (containsGist table) j))) gist inscrud)
        m = tableMeta table
    insertI <- UI.span # set UI.class_ "glyphicon glyphicon-plus"
    insertB <- UI.button
        # set UI.class_ "btn btn-sm btn-default"
        # set children [insertI]
        # sinkDiff UI.style ((\i j -> noneShowSpan (maybe False (txt "INSERT" `elem`) i && j)) <$>authorize <*> insertEnabled)
    cliIns <- UI.click insertB
    let  crudIns j  =  transaction inf (fullInsert m j)
    diffIns <- ui $ mapEventDyn catchEd $ fmap crudIns <$> facts inscrud <@ unionWith const cliIns (filterKey  (facts insertEnabled) altI )
    return $ (diffIns ,insertB)

editCommand lbox inf table oldItemsi inscrudp inscrud  authorize gist = do
    altU <- onAltU lbox
    let
      m = tableMeta table
      editEnabled = (\i j k l m -> i && j && k && l && m ) <$> (maybe False (\i -> (isRight .tableCheck m  $ i) || isJust (matchUpdate inf (tableMeta table ) i)) <$> inscrud ) <*> (isJust <$> oldItemsi) <*>   liftA2 (\i j -> maybe False (flip (containsOneGist table) j) i ) inscrud gist <*>   liftA2 (\i j -> maybe False (flip (containsGist table) j) i ) oldItemsi gist <*>  (isDiff  <$> inscrudp)
      crudEdi i j =  transaction inf $ fullEdit m i j
    editI <- UI.span # set UI.class_ "glyphicon glyphicon-edit"
    editB <- UI.button
        # set UI.class_ "btn btn-sm btn-default"
        # set children [editI]
        # sinkDiff UI.style ((\i j -> noneShowSpan (maybe False (txt "UPDATE" `elem`) i && j)) <$>authorize <*> editEnabled)
    -- Edit when any persistent field has changed
    cliEdit <- UI.click editB
    diffEdi <- ui $ mapEventDyn catchEd $ liftA2 crudEdi <$> facts oldItemsi <*> facts inscrud <@ unionWith const cliEdit (filterKey (facts editEnabled)  altU)
    return (diffEdi,editB)

deleteCommand lbox inf table oldItemsi authorize gist = do
    let
      m = tableMeta table
      deleteEnabled = liftA2 (\i j -> (maybe False (isJust .matchDelete inf m) i || (isJust i &&  rawTableType table == ReadWrite))  && j ) ( oldItemsi)  (liftA2 (\i j -> maybe False (flip (containsGist table) j) i  ) oldItemsi gist)
      crudDel :: TBData Key Showable  ->  Dynamic (RowPatch Key Showable)
      crudDel j  = transaction inf (deleteFrom m j)
    deleteI <- UI.span # set UI.class_ "glyphicon glyphicon-trash"
    deleteB <- UI.button
        # set UI.class_ "btn btn-sm btn-default"
        # set children [deleteI]
        # sinkDiff UI.style ((\i j -> noneShowSpan (maybe False (txt "DELETE" `elem`) i && j)) <$>authorize <*> deleteEnabled)

    altD <- onAltO lbox
    cliDel <- UI.click deleteB
    diffDel <- ui $ mapEventDyn catchEd $ fmap crudDel <$> facts oldItemsi <@ unionWith const cliDel (filterKey (facts deleteEnabled) altD)
    return (diffDel,deleteB)

mergeCommand lbox inf table inscrudp inscrud  authorize gist = do
    let
      m = tableMeta table
      mergeEnabled = liftA2 (&&) (isJust . fmap tableNonRef <$> inscrud) (liftA2 (\i j -> (>1) . L.length $ maybe [] (\e -> filter ((/= tableNonRef e) .tableNonRef) $  conflictGist table e j) i  ) inscrud gist)
      crudMerge :: TBData Key Showable  ->  G.GiST (TBIndex Showable) (TBData Key Showable )-> Dynamic ((RowPatch Key Showable))
      crudMerge i g = transaction inf ( do
            let confl = conflictGist table i g
            mapM_ (deleteFrom m) confl
            fullInsert  m i)
    mergeI <- UI.span # set UI.class_ "glyphicon glyphicon-share"
    mergeB <- UI.button
        # set UI.class_ "btn btn-sm btn-default"
        # set UI.children [mergeI]
        # sinkDiff UI.style ((\i j -> noneShowSpan (maybe False (txt "UPDATE" `elem`) i && j)) <$>authorize <*> mergeEnabled)
    cliMerge <- UI.click mergeB
    diffMerge <- ui $ mapEventDyn catchEd $ liftA2 crudMerge <$> facts inscrud <*> fmap Just (facts gist) <@ cliMerge
    return (diffMerge,mergeB)


debugConsole oldItemsi inscrudp = do
    let
      inscrud = fmap join $ applyIfChange <$> oldItemsi <*> inscrudp
    debugBox <- checkedWidget (onDiff (const True) (const False )<$> inscrudp)
    debugT <- traverseUI (\i ->
            if i
            then do
              let
                gen (h,s) = do
                  v <- ui $ currentValue s
                  header <- UI.h6
                            # set UI.class_ "header"
                            # set UI.text h
                            # set UI.style [("text-align","center")]
                  out <- UI.mkElement "textarea"
                            # set UI.value v
                            # set UI.style [("max-height","300px"),("width","100%")]
                  element out # method  "textAreaAdjust(%1)"
                  UI.div # set children [header,out]
                         # set UI.class_ "col-xs-6"
              mapM gen
                  [-- ("Last", maybe "" (ident . renderTable) <$> facts oldItemsi),
                  -- ("New" , maybe "" (\i -> renderTyped (typeCheckTable (_rawSchemaL table,_rawNameL table) i ) i) <$> facts inscrud),
                  ("Diff", onDiff (ident . renderRowPatch) (const "") <$> facts inscrudp)
                  ,("Undo", maybe "" (onDiff (ident . renderRowPatch) (const "")) <$> (diff <$> facts inscrud <*> facts oldItemsi))]
            else  return [] ) (triding debugBox)
    debug <- UI.div # sink children (facts debugT) # set UI.class_ "col-xs-12"
    UI.div #  set children [getElement debugBox,debug]

processPanelTable
  :: Element
   -> InformationSchema
   -> RefTables
   -> Tidings (Editor (TBIdx CoreKey Showable))
   -> Table
   -> Tidings (Maybe (TBData CoreKey Showable))
   -> UI (Element,Event [String])
processPanelTable lbox inf reftb@(res,gist,_,_) inscrudp table oldItemsi = do
  let
    inscrud = fmap join $ applyIfChange <$> oldItemsi <*> inscrudp
    m = tableMeta table
    authPred =  [(keyRef "grantee",Left ( int $ usernameId inf ,Equals)),(keyRef "schema",Left (int $ schemaId inf  ,Equals))]
  auth <- ui (transactionNoLog (meta inf) $ selectFromTable "authorization" Nothing Nothing [] authPred)
  let authorize =  ((fmap unArray . unSOptional . lookAttr' "authorizations") <=< G.lookup (idex  (meta inf) "authorization"  [("schema", int (schemaId inf) ),("table",int $ tableUnique table),("grantee",int $ usernameId inf)]))  <$> collectionTid auth

  (diffInsert,insertB) <- insertCommand lbox inf table inscrudp inscrud authorize gist
  (diffEdit,editB) <-     editCommand lbox inf table oldItemsi inscrudp inscrud authorize gist
  (diffMerge,mergeB) <-   mergeCommand lbox inf table inscrudp inscrud authorize gist
  (diffDelete,deleteB) <- deleteCommand lbox inf table oldItemsi authorize gist

  transaction <- UI.div
    # set children [insertB,editB,mergeB,deleteB]

  let diffEvs = [diffEdit,diffInsert,diffMerge,diffDelete]
  return (transaction,unions $ fmap (fmap (\(Left i) -> i) . filterE isLeft) diffEvs)

printErrors diffEvs = do
  errors <- UI.div
  onEvent diffEvs
      (\i -> element errors # set text (show i))
  return errors

compactPlugins  valix plix= fromMaybe Keep .safeHead . compact <$> (F.foldl' (liftA2 (flip (:)))  (pure .const Keep <$> valix)  (fmap (maybe Keep Diff) .snd<$> plix))

dynHandlerPatch
  :: (Compact (Index a1),Patch a1,Eq (Index a1),Show (Index a1),Show a1,Eq a1)
  => (Int -> Tidings (Maybe a1) -> PluginRef a1 -> UI (LayoutWidget (Editor (Index a1))))
  -> (Int -> Tidings (Maybe a1))
  -> (Int -> PluginRef a1)
  -> Int
  -> ([LayoutWidget (Editor (Index a1))], Tidings Bool)
  -> UI ([LayoutWidget (Editor (Index a1))], Tidings Bool)
dynHandlerPatch hand val valp ix (l,old)= do
    valix <- ui $ calmT (val ix)
    plix <- ui $ traverse (traverse calmT) (valp ix)
    oldC <- ui (calmT old)
    let next = hand ix valix plix
    el <- switchUILayout (compactPlugins valix plix) UI.div oldC next
    return (l <> [el], (\i j ->  isJust i && j ) <$> ((\ i j -> join $ applyIfChange i j <|> createIfChange j <|> Just i )<$> valix <*> triding el) <*> oldC )


reduceDiffList
  :: Show a => Int -> Int
     -> [(Int, Editor (PathFTB a))]
     -> [Maybe (PathFTB a)]
     -> Editor (PathFTB a)
reduceDiffList arraySize o i plugM
   | F.length i  == 0 = Keep
   | F.all isKeep (snd <$> i) = Keep
   | otherwise = patchEditor $  removeOverlap plugl ++ notOverlap ++  removeOverlap plugu ++ reverse (rights diffs)
   where diffs = catMaybes $ (\(ix,v) -> treatA (o+ix)v) <$> i
         -- treatA i j | traceShow ("treatA",i,j) False = undefined
         treatA a (Diff v) = Just $ Left $ PIdx a  (Just v)
         treatA a Delete =  Just $ Right $ PIdx a Nothing
         treatA _ Keep = Nothing
         plug = catMaybes plugM
         (plugl ,plugu)= (F.concat $ unPatchSet <$> catMaybes (filterPatchSet (<o) <$> plug), F.concat $ unPatchSet <$>catMaybes (filterPatchSet (o + arraySize <=)<$> plug))
           where
             unPatchSet (PatchSet l ) = F.toList l
             unPatchSet i = [i]
         removeOverlap plugl = catMaybes $ fmap  proj plugl
         proj (PIdx ix a ) = if ( ix - o) `notElem` (fst <$> i) then  Just (PIdx ix a)  else unDiff ix  . snd =<<  atMay  i (ix -  o)
         proj (PAtom i) = Nothing
         proj v = error (show v)
         notOverlap =  lefts diffs
         unDiff o (Diff v) = Just $  PIdx o (Just v)
         unDiff o i = Nothing


reduceOptional :: Editor (PathFTB a) -> Editor (PathFTB a)
reduceOptional Delete   = Diff $ POpt Nothing
reduceOptional Keep  = Keep
reduceOptional (Diff i )  = Diff (POpt (Just  i))

maybeEdit :: t1 -> t -> Editor t1 -> t1
maybeEdit v id (Diff i) =  i
maybeEdit v id _  = v

unPOpt :: Show t => PathFTB t -> Maybe (PathFTB t)
unPOpt (POpt i ) = i
unPOpt i@(PAtom _ ) = Just i   -- TODO: Debug  what is triggering this and remove this case
unPOpt i = error (show i)

type AtomicUI k b = PluginRef b ->  Tidings (Maybe b) ->  k -> UI (LayoutWidget (Editor (Index b)))

buildUIDiff:: (Compact (Index b),Eq (Index b),Show (Index b),Show k ,Ord b ,Patch b, Show b) => AtomicUI k b -> KType k -> PluginRef (FTB b) -> Tidings (Maybe (FTB b)) -> UI (LayoutWidget (Editor (PathFTB (Index b) )))
buildUIDiff f (Primitive l prim) = go l
  where
    go [] plug tdi = fmap (fmap PAtom) <$> f (fmap (fmap (fmap unAtom)) <$>plug) (fmap unTB1 <$> tdi) prim
    go (i:ti) plug tdi = case i of
         KArray -> mdo
            ctdi' <- ui $  cacheTidings tdi
            cplug <- ui $ traverse (traverse cacheTidings) plug
            clearEl <- flabel # set text "clear" # set UI.class_ "label label-default pull-right col-xs-2"
            clearEv <- UI.click clearEl
            ini <- currentValue (facts ctdi')
            ctdi <- ui $ accumT ini (unionWith (.) ((\_ -> const Nothing )<$> clearEv ) (const <$> rumors ctdi'))
            offsetDiv  <- UI.div
            -- let wheel = fmap negate $ mousewheel offsetDiv
            TrivialWidget offsetT offset <- offsetField (pure 0)  never size
            let arraySize = 8
                tdi2  = fmap unArray <$> ctdi
                index o ix v = flip Non.atMay (o + ix) <$> v
                unIndexEl ix = fmap join$ index ix <$> offsetT <*> tdi2
                unplugix ix = fmap ((\o -> ((indexPatchSet (o + ix) )=<<)) <$> offsetT <*>) <$> cplug
                dyn = dynHandlerPatch  (\ix valix plix ->do
                  wid <- go ti  plix valix
                  lb <- hlabel ["col-xs-1"] # sink UI.text (show . (+ix) <$> facts offsetT )
                  paintEditDiff valix (triding wid) lb
                  element wid # set UI.class_ "col-xs-12"
                  row <- UI.div # set children [lb,getElement wid]
                  return $ LayoutWidget (triding wid) row (getLayout wid) ) unIndexEl unplugix

            element offset # set UI.class_ "label label-default pull-right col-xs-2"
            widgets <- fst <$> foldl' (\i j -> dyn j =<< i ) (return ([],pure True)) [0..arraySize -1 ]
            let
              widgets2 = Tra.sequenceA (zipWith (\i j -> (i,) <$> j) [0..] ( triding <$> widgets) )
              -- [Note] Array diff must be applied in the right order
              --  additions and edits first in ascending order than deletion in descending order
              --  this way the patch index is always preserved
              bres = reduceDiffList  arraySize <$> offsetT <*>  widgets2 <*> foldr (liftA2 (:)) (pure [])  ( snd <$>cplug)
            pini <- currentValue (facts bres)
            bres' <- ui $ calmT =<< accumT pini (unionWith (.) ((\_ -> const Delete)<$> clearEv ) (const <$> rumors bres))
            element offsetDiv # set children (fmap getElement widgets)
            size <- ui $ calmT (maybe 0 ((+ negate 1).Non.length .unArray)  . join <$> (applyIfChange <$> ctdi' <*> bres))
            composed <- UI.span # set children [offset ,clearEl, offsetDiv]
            return  $ LayoutWidget bres' composed (F.foldl1 verticalL  <$> (sequenceA $ getLayout <$> widgets))
         KOptional -> do
           let pretdi = join . fmap unSOptional <$> tdi
               plugtdi = fmap (fmap (join . fmap unPOpt ))<$> plug
           tdnew <- go ti  plugtdi pretdi
           -- Delete equals create
           return  (reduceOptional <$> tdnew)
         KSerial -> do
           let pretdi = join . fmap unSOptional <$> tdi
               plugtdi = fmap (fmap (join . fmap unPOpt )) <$> plug
           tdnew <- go ti  plugtdi pretdi
           -- Delete equals create
           return $ (reduceOptional <$> tdnew)
         KInterval -> do
            let unInterval f (IntervalTB1 i ) = f i
                unInterval _ i = error (show i)
                unfinp (Interval.Finite i) = Just i
                unfinp i = Nothing
                plugtdi i (PInter j l)
                  | i == j  =  unfinp $ fst l
                  | otherwise = Nothing
            composed <-  UI.div
            subcomposed <- UI.div # set UI.children [composed]
            inf <- go ti (fmap ( fmap (join . fmap (plugtdi True))) <$> plug) (join.fmap (unInterval inf' ) <$> tdi)
            lbd <- checkedWidget (maybe False (unInterval (snd . Interval.lowerBound') ) <$> tdi)

            sup <- go ti (fmap (fmap (join . fmap (plugtdi False ) ))<$> plug) (join.fmap (unInterval sup')  <$> tdi)
            ubd <- checkedWidget (maybe False (unInterval (snd . Interval.upperBound' ) ) <$> tdi)
            element composed # set UI.style [("display","inline-flex")] # set UI.children [getElement lbd ,getElement  inf,getElement sup,getElement ubd]
            let
              replaceL  Delete   h= Diff $ PInter True (Interval.NegInf,h)
              replaceL   i h =  fmap (PInter True  . (,h). Interval.Finite) i
              replaceU  Delete   h = Diff $ PInter False (Interval.PosInf,h)
              replaceU  i  h =  fmap (PInter False . (,h).Interval.Finite) i
              output = (\i j -> reduceDiff [i,j])<$> (replaceL <$>  triding inf <*> triding lbd ) <*> (replaceU <$> triding sup <*> triding ubd)
            return $ LayoutWidget output  subcomposed  (horizontalL  <$> getLayout inf <*> getLayout sup)

horizontalL (i,j) (a,b) =  (i + a ,max j b)
verticalL (i,j) (a,b) =  (max i a ,j + b)

reduceDiff :: [Editor (PathFTB a) ] -> Editor (PathFTB a)
reduceDiff i
  | F.all isKeep i = Keep
  | F.all isDelete i = Delete
  | otherwise = patchEditor $ filterDiff i


buildPrimitive :: [FieldModifier] -> PluginRef Showable ->  Tidings (Maybe Showable) ->  Prim KPrim (Text, Text)-> UI (LayoutWidget (Editor Showable))
buildPrimitive fm plug tdi2 (AtomicPrim i) = do
  let tdi = F.foldl' (liftA2 mergePatches) tdi2  (fmap snd plug)
  pinp <- buildPrim fm tdi i
  return $ LayoutWidget (diff' <$> tdi2 <*> triding pinp) (getElement pinp) (pure (goAttSize (Primitive [] (AtomicPrim i))))


buildPrim
  ::
     [FieldModifier]
     -> Tidings (Maybe Showable)
     -> KPrim
     -> UI (TrivialWidget (Maybe Showable))
buildPrim fm tdi i
  = case i of
     PGeom ix g ->
       let tdig = fmap (\(SGeo i) -> i) <$> tdi
       in fmap (fmap(fmap SGeo)) $ case g of
         PPosition -> do
           let tdip = fmap (\(SPosition i) -> i) <$> tdig
           fmap (fmap SPosition)<$> case ix of
             3-> fmap (fmap Position) <$> primEditor (fmap (\(Position l) -> l) <$> tdip)
             2-> fmap (fmap Position2D) <$> primEditor (fmap (\(Position2D l) -> l) <$> tdip)
     PDimensional s (a,b,c,d,e,f,g) -> do
       let mult = zip [a,b,c,d,e,f,g] un
           multP = filter ((>0).fst) mult
           multN = filter ((<0).fst) mult

           un = ["mol","K","A","l","kg","s","m"]
           pols = L.intercalate "." $ fmap (\(i,j)-> if i == 1 then j else j<> "^" <> show i) multP
           negs = L.intercalate "." $ fmap (\(i,j)-> j<> "^" <> show (abs i)) multN
           build i j
             | null i && null j = ""
             | null i  = "1/" <> negs
             | null j  = pols
             | otherwise = pols <> "/" <> negs
           scale i
             | i == 0 = ""
             | otherwise = "10^" <> show i  <> "."
       tag <- UI.span # set text  (scale s <> build pols negs)
       inp <- oneInput i tdi
       out <- horizontal [getElement inp,tag]
       element out # set UI.style [("width","100%")]
       return (TrivialWidget (triding inp) out)
     PBoolean -> do
       uiEditor (IsoArrow SBoolean (\(SBoolean i) -> i) <$$> UIEditor primEditor) tdi
     PTime ti -> do
       let
        time = IsoArrow STime (\(STime i) -> i)
       case ti of
         PTimestamp dbzone -> do
           let timestamp = IsoArrow STimestamp (\(STimestamp i) -> i)
           uiEditor (time Cat.. timestamp <$$> UIEditor primEditor) tdi
         PDate -> do
           let date = IsoArrow SDate (\(SDate i) -> i)
           uiEditor (time Cat.. date <$$> UIEditor primEditor) tdi
         PDayTime -> oneInput i tdi
         PInterval ->oneInput i tdi
     PAddress -> do
       let binarySrc = (\(SText i) -> "https://drive.google.com/embeddedfolderview?id=" <> T.unpack i <> "#grid")
       i <- UI.input  # sink UI.value ( maybe "" (\(SText t) -> T.unpack t) <$> facts tdi)
       vci <- UI.valueChange i
       let tdie = unionWith const (Just . SText . T.pack <$> vci ) (rumors tdi)
       vi <- currentValue (facts tdi)
       tdi2 <- ui $ stepperT vi tdie
       let fty = ("iframe",UI.strAttr "src",maybe "" binarySrc ,[("width","100%"),("max-height","300px")])

       f <- pdfFrame fty (facts tdi2) # sink0 UI.style (noneShow . isJust <$> facts tdi2)
       fd <- UI.div # set UI.style [("display","inline-flex")] # set children [i]
       res <- UI.div # set children [fd,f]
       return (TrivialWidget tdi2 res)
     PMime mime ->
       case mime of
        "text/json" -> do
           let fty = ("textarea",UI.value ,maybe "" (\(SJSON i) -> BSL.unpack $ A.encode i) ,[("width","100%"),("max-height","300px")])
           ini <- currentValue (facts tdi)
           f <- pdfFrame fty (facts tdi) # sink UI.style (noneShow . (\i -> isJust i || elem FWrite fm) <$> facts tdi)
           vcf <- UI.valueChange f
           let ev = if FWrite `elem` fm then unionWith const (rumors tdi) (fmap SJSON . A.decode . BSL.pack <$> vcf) else rumors tdi
           step <- ui $ stepperT  ini ev
           return (TrivialWidget step f)
        "text/plain" -> do
           let fty = ("textarea",UI.value ,maybe "" (\(SBinary i) -> BSC.unpack i) ,[("width","100%"),("max-height","300px")])
           ini <- currentValue (facts tdi)
           f <- pdfFrame fty (facts tdi) # sink UI.style (noneShow . (\i -> isJust i || elem FWrite fm) <$> facts tdi)
           vcf <- UI.valueChange f
           let ev = if FWrite `elem` fm then unionWith const (rumors tdi) (Just . SBinary . BSC.pack <$> vcf) else rumors tdi
           step <- ui $ stepperT  ini ev
           return (TrivialWidget step f)
        "application/dwg" -> do
           let fty = ("div",UI.value,maybe "" (\(SBinary i) -> BSC.unpack i) ,[("width","100%"),("max-height","300px")])
           ini <- currentValue (facts tdi)
           f <- pdfFrame fty (facts tdi) # sink UI.style (noneShow . (\i -> isJust i || elem FWrite fm) <$> facts tdi)
           vcf <- UI.valueChange f
           let ev = if FWrite `elem` fm then unionWith const (rumors tdi) (Just . SBinary . BSC.pack <$> vcf ) else rumors tdi
           step <- ui $ stepperT  ini ev
           return (TrivialWidget step f)
        "video/mp4" -> do
           let binarySrc = (\(SBinary i) -> "data:" <> T.unpack mime <> ";base64," <>  (BSC.unpack $ B64.encode i) )
           clearB <- UI.button # set UI.text "clear"
           file <- UI.input # set UI.type_ "file" # set UI.multiple True # set UI.style (noneShow $ elem FWrite fm)
           fchange <- fileChange file
           clearE <- UI.click clearB
           tdi2 <- ui $ addEvent (join . fmap (fmap SBinary . either (const Nothing) Just .   B64.decode .  BSC.drop 7. snd  . BSC.breakSubstring "base64," . BSC.pack ) <$> fchange) =<< addEvent (const Nothing <$> clearE ) tdi
           let fty = ("source",UI.src,maybe "" binarySrc  ,[])
           ini <- currentValue (facts tdi2)
           let f = (\i -> do
                f <- pdfFrame fty  i # set UI.type_ (T.unpack mime)
                mkElement "video" # set children (pure f) # set (UI.strAttr "width" ) "320" # set (UI.strAttr "height" ) "240" # set (UI.strAttr "controls") ""# set (UI.strAttr "autoplay") ""
                   ) <$> facts tdi2
               pdfFrame (elem,sr , call,st) pdf = mkElement elem  # set sr (call  pdf)
           v <- UI.div # sink items(fmap pure <$> f)
           o <- UI.div # set children [file,clearB,v]
           return (TrivialWidget tdi2 o)
        otherwise -> do
           let binarySrc = (\(SBinary i) -> "data:" <> T.unpack mime <> ";base64," <>  (BSC.unpack $ B64.encode i) )
           clearB <- UI.button # set UI.text "clear"
           file <- UI.input # set UI.type_ "file" # set UI.multiple True # set UI.style (noneShow $ elem FWrite fm)
           fchange <- fileChange file
           clearE <- UI.click clearB
           cur2 <- ui $currentValue (facts tdi)
           let evi2 = foldl1 (unionWith const) [rumors tdi,const Nothing <$> clearE,  join . fmap (either (const Nothing) (Just . SBinary).   B64.decode .  BSC.drop 7. snd  . BSC.breakSubstring "base64," . BSC.pack ) <$> fchange]
           tdi2 <- ui $ stepperT cur2  evi2
           let
             fty = case mime of
               "application/pdf" -> pdfFrame ("iframe" ,UI.strAttr "src",maybe "" binarySrc ,[("width","100%"),("max-height","300px")])
               "application/x-ofx" ->pdfFrame  ("textarea", UI.value ,maybe "" (\(SBinary i) -> BSC.unpack i) ,[("width","100%"),("max-height","300px")])
               "text/xml" ->pdfFrame  ("textarea", UI.value ,maybe "" (\(SBinary i) -> BSC.unpack i) ,[("width","100%"),("max-height","300px")])
               "application/gpx+xml" ->pdfFrame  ("textarea", UI.value ,maybe "" (\(SBinary i) -> BSC.unpack i) ,[("width","100%"),("max-height","300px")])
               "image/jpg" -> \i -> pdfFrame ("img" ,UI.strAttr "src",maybe "" binarySrc ,[("max-height","200px")]) i # set UI.class_ "img-responsive"
               "image/png" -> pdfFrame ("img" ,UI.strAttr "src",maybe "" binarySrc ,[("max-height","200px")])
               "image/bmp" -> pdfFrame ("img" ,UI.strAttr "src",maybe "" binarySrc ,[("max-height","200px")])
               "text/html" -> pdfFrame ("iframe" ,UI.strAttr "srcdoc",maybe "" (\(SBinary i) -> BSC.unpack i) ,[("width","100%"),("max-height","300px")])
           f <- fty (facts tdi2 ) # sinkDiff UI.style (noneShow. isJust <$> tdi2)
           fd <- UI.div # set UI.style [("display","inline-flex")] # set children [file,clearB]
           res <- UI.div # set children [fd,f]
           valChange <- UI.valueChange f
           tdi3 <- ui $ addEvent  (readPrim  i <$> valChange) tdi2
           return (TrivialWidget tdi3 res)
     PColor -> do
        let f = facts tdi
        v <- currentValue f
        inputUI <- UI.input # set UI.class_ "jscolor" # sink0 UI.value (maybe "FFFFFF" renderPrim <$> f)# set UI.style [("width","100%")]
        onCE <- UI.onChangeE inputUI
        let pke = unionWith const (readPrim i <$> onCE) (rumors tdi)
        pkt <- ui $ stepperT v  pke
        sp <- UI.div # set UI.children [inputUI ]
        runFunctionDelayed inputUI  $ ffi "new jscolor(%1)" inputUI
        onChanges f (runFunctionDelayed inputUI . ffi "updateColor(%1,%2)" inputUI . maybe "FFFFFF" renderPrim)
        return $ TrivialWidget pkt sp
     z ->
       oneInput z tdi

oneInput :: KPrim -> Tidings (Maybe Showable) ->   UI (TrivialWidget (Maybe Showable))
oneInput i tdi = do
    v <- currentValue (facts tdi)
    inputUI <- UI.input # sinkDiff UI.value (maybe "" renderPrim <$> tdi) # set UI.style [("min-width","30px"),("max-width","250px"),("width","100%")]
    onCE <- UI.onChangeE inputUI
    let pke = unionWith const  (decode <$> onCE) (Right <$> rumors tdi)
        decode v = maybe (if v == "" then Right Nothing else Left v) (Right . Just) .  readPrim i $ v
    pkt <- ui $ stepperT (Right v) pke
    element inputUI # sinkDiff UI.style ((\i -> [("border", either (const "solid red 1.5px") (const "") i)]) <$> pkt)
    return $ TrivialWidget (either (const Nothing) id <$> pkt) inputUI


inlineTableUI
  :: InformationSchemaKV Key Showable
  -> SelTBConstraint
  -> PluginRef (TBData CoreKey Showable)
  -> Tidings (Maybe (TBData CoreKey Showable))
  -> Prim KPrim (Text, Text)
  -> UI (LayoutWidget (Editor (TBIdx CoreKey Showable)))
inlineTableUI inf constr pmods oldItems (RecordPrim na) = do
    let
      tablefields = allRec' (tableMap inf) table
      convertConstr (_,j) =  (\i -> ([index i], C.contramap (\v -> kvlist (fmap addDefault (L.delete i attrs) ++ v)) <$> j )) <$> attrs
        where attrs = F.toList $ unKV tablefields
      table = lookTable rinf (snd na)
      rinf = fromMaybe inf (HM.lookup (fst na) (depschema inf))
    eiTableDiff rinf table (concat $ convertConstr <$> constr) M.empty pmods tablefields oldItems


iUITableDiff
  :: InformationSchema
  -- Plugin Modifications
  -> SelPKConstraint
  -> PluginRef (Column CoreKey Showable)
  -- Selected Item
  -> Tidings (Maybe (Column CoreKey Showable))
  -- Static Information about relation
  -> Column CoreKey ()
  -> UI (LayoutWidget (Editor (PathAttr CoreKey Showable)))
iUITableDiff inf constr pmods oldItems  (IT na  tb1)
  = fmap (fmap (PInline na)) <$> buildUIDiff (inlineTableUI inf (fmap (fmap (C.contramap (pure . IT na .TB1 ))) <$> constr)) (keyType na)   (fmap (fmap (fmap patchfkt)) <$> pmods) (fmap _fkttable <$> oldItems)


fkUITablePrim ::
  InformationSchema
  -- Plugin Modifications
  -> ([Rel Key],Table,[CoreKey])
  -> SelTBConstraint
  -- Same Table References
  -> ColumnTidings
  -> PluginRef  (TBRef Key Showable)
  -- Relation Event
  -> Tidings (Maybe (TBRef CoreKey Showable))
  -- Static Information about relation
  -> [CorePrim]
  -> UI (LayoutWidget (Editor (PTBRef Key Showable)))
fkUITablePrim inf (rel,targetTable,ifk) constr nonInjRefs plmods  oldItems  prim = do
      -- Top Level Widget
      top <- UI.div
      dblClick <- UI.dblclick top
      -- On dblclick edit
      dblClickT <- ui $ accumT False (const not <$> dblClick)
      -- On click select
      (eSelector,hSelector) <- ui newEvent
      selectT <- ui $ calmT =<< stepperT False  eSelector
      let
        reflectRels = filter ((`L.elem` ifk). _relOrigin) rel
        filterReflect m = filter (\k  -> _relOrigin (justError "no head notreflect" . safeHead $ F.toList (index k)) `L.elem` fmap _relOrigin reflectRels  ) m
        filterNotReflect (KV m) = KV $ M.filterWithKey (\k  _-> not $ _relOrigin (justError "no head notreflect" . safeHead $ F.toList k) `L.elem` fmap _relOrigin reflectRels) m
        filterReflectKV (KV m) = KV $ M.filterWithKey (\k  _-> _relOrigin (justError "no head reflect kv" . safeHead $ F.toList k) `L.elem` fmap _relOrigin reflectRels) m
        nonEmptyTBRef v@(TBRef (KV m,KV n )) = if  L.null n then Nothing else Just v
        relTable = M.fromList $ fmap (\(Rel i _ j ) -> (j,i)) rel
        ftdi = F.foldl' (liftA2 mergePatches)  oldItems (snd <$> plmods)

      inipl <- mapM (ui . currentValue . facts) (snd <$>  plmods)
      let
        inip = maybe Keep (Diff .head) $ nonEmpty $ catMaybes inipl
      (elsel, helsel) <- ui newEvent
      (eledit, heledit) <- ui newEvent
      (eleditu, heleditu) <- ui newEvent
      (elayout, hlayout) <- ui newEvent

      let
        evsel = unionWith const elsel  (const Keep <$> rumors oldItems)
      tsel <- ui $ stepperT (sourcePRef <$> inip) evsel
      tseledit <- ui $ stepperT (targetPRef <$> inip) eledit
      tedit <- ui $ stepperT (targetPRef <$> inip) eleditu

      nav <- openClose dblClickT
      let
        tdfk = merge <$> tsel <*> tedit
        iold2 :: Tidings (Maybe (Map Key (FTB Showable)))
        iold2 =  fmap (M.mapKeys (justError "no head iold2" . safeHead . F.toList . S.map _relOrigin ). fmap _tbattr . _kvvalues . filterNotReflect . fst.unTBRef) <$> ftdi
        predicatefk o = WherePredicate . AndColl $ catMaybes $ (\(k, v) ->  join $ (\ o ->  (\ rel -> PrimColl (keyRef (_relTarget rel),   [(_relTarget rel,Left  (o,Flip $ _relOperator rel))] )) <$> L.find ((==k) . _relOrigin ) rel) <$> unSOptional v) <$> M.toList o
        predicate = fmap predicatefk <$> iold2
        sel = liftA2 diff' oldItems ftdi
        selector False = do
          ui $ onEventDyn
            ((,,,) <$>   facts tsel <*> facts oldItems <*> facts tedit <@> rumors (fmap sourcePRef <$> sel))
            (\(oldsel,initial,oldedit,vv) -> do
              when (oldsel /= vv ) $ do
                liftIO $ helsel vv
                pred <- currentValue (facts predicate)
                reftb@(_,gist,sgist,_) <- refTablesDesc inf targetTable  Nothing  (fromMaybe mempty pred)
                g <- currentValue (facts gist)
                s <- currentValue (facts sgist)
                let search  i
                      | M.size  (_kvvalues  i) /= L.length rel =  Nothing
                      | otherwise = searchGist relTable targetTable  g s i
                    searchDiff i = diff' (snd .unTBRef<$> initial) (search =<< i)
                    newsel =  applyIfChange (fst .unTBRef<$> initial) vv
                    newEdit = maybe oldedit searchDiff newsel
                when (oldedit /=  newEdit) $ do
                  liftIO $  heledit (newEdit)
                return ()
              )
          pan <- UI.div
            # set UI.class_ "col-xs-11 fixed-label"
            # set UI.style [("border","1px solid gray"),("border-radius","4px"),("height","26px")]
            # sinkDiff  text ((\i  -> maybe "" (L.take 50 . L.intercalate "," . fmap renderShowable . allKVRec' inf (tableMeta targetTable). snd .unTBRef)  i) <$>  (fmap join $ applyIfChange <$>  oldItems <*>  tdfk))
          panClick <- UI.click pan
          ui $ onEventIO panClick (\ _ -> hSelector True)
          (nav,celem,layout) <- edit
          onChanges (facts  layout) (liftIO . hlayout)
          element nav
            # set UI.class_ "col-xs-1"
          hidden <- UI.div
            # set children celem
            # set UI.class_ "col-xs-12"
          return [nav,pan,hidden]
        selector True = do
          pred <- ui $ currentValue (facts predicate)
          reftb@(_,gist,sgist,_) <- ui $ refTablesDesc inf targetTable Nothing (fromMaybe mempty pred)
          let newSel = fmap (justError "fail apply") $ applyIfChange <$> (fmap (fst .unTBRef) <$> oldItems)<*>(fmap sourcePRef <$> sel)
          tdi <- ui $ cacheTidings ((\g s v -> searchGist relTable targetTable g s =<< v) <$> gist  <*> sgist <*> newSel)
          cv <- currentValue (facts tdi)
          metaMap <- mapWidgetMeta inf
          cliZone <- jsTimeZone
          metaAgenda <- eventWidgetMeta inf
          let
            hasMap = L.find ((== targetTable).(Le.^._2)) metaMap
            hasAgenda = L.find ((== targetTable).(Le.^._2)) metaAgenda
            add i m =  if i then (m:) else id
            availableModes = add (isJust hasAgenda) "Agenda" $ add (isJust hasMap) "Map" ["List"]
          navMeta  <- buttonDivSet  availableModes (pure $ Just "List") (\i -> UI.button # set UI.text i # set UI.style [("font-size","unset")] # set UI.class_ "buttonSet btn-xs btn-default btn pull-left")
          let navSize =  "col-xs-" ++ (show $ length availableModes - 1)
              selSize =  "col-xs-" ++ (show $ 12 - (length availableModes - 1))
          itemList <- do
              lboxeel <- switchManyLayout (triding navMeta) (M.fromList
                  [("List" , do
                    itemListEl <- UI.select # set UI.class_ "fixed-label" # set UI.size "21" # set UI.style [("width","100%"),("position","absolute"),("z-index","999"),("left","0px"),("top","22px")]
                    (lbox , l) <- selectListUI inf targetTable itemListEl (pure mempty) reftb constr tdi
                    element l # set UI.class_ selSize
                    return (LayoutWidget lbox l (pure (6,1)))),
                  ("Map" ,do
                    let selection = fromJust hasMap
                    t <- liftIO getCurrentTime
                    TrivialWidget i el <- mapSelector inf (pure mempty ) selection (pure (t,"month")) tdi (never, pure Nothing)
                    element el # set UI.class_ selSize
                    return (LayoutWidget i el (pure (12,1)))),
                  ("Agenda" ,do
                    let selection = fromJust hasAgenda
                    (sel ,(j,i)) <- calendarSelector
                    el <- traverseUI (\(delta ,time) -> do
                      (e,l) <- calendarView inf mempty cliZone [selection] (pure (S.singleton targetTable )) Basic delta time
                      c <- UI.div # set children e
                      return (TrivialWidget (fmap snd <$> l) c)) $ (,) <$> i <*> j
                    el2 <- UI.div  # sink children (pure . getElement <$> facts el)
                    tsel <- ui $ joinT (triding <$> el)
                    (\i -> LayoutWidget tsel i (pure (12,1))) <$> UI.div # set children [sel,el2] # set UI.class_ selSize)])

              onChanges (facts  (getLayout lboxeel)) (liftIO . hlayout)
              element navMeta # set UI.class_ navSize
              elout <- UI.div # set children [getElement navMeta ,getElement lboxeel]
              esc <- onEsc elout
              loaded <- ui $ loadItems inf targetTable (triding lboxeel)
              ui $ onEventIO esc (\ _ ->hSelector False)
              return (TrivialWidget  loaded elout)

          let nevsel = unionWith const (rumors tdi) (rumors $ triding itemList)
          tds <- ui $ stepperT cv nevsel
          let
            fksel =  fmap TBRef . (\box ->  (,) <$>  (reflectFK reflectRels  =<< box ) <*> box ) <$>   tds
            output = diff' <$> oldItems <*> fksel
          ui $ onEventIO (rumors output) (\i -> do
            when (not (L.null reflectRels)) $ do
              helsel $ (fmap (filterReflect.sourcePRef) i)
              heleditu $ fmap targetPRef i)
          return [getElement itemList]

        edit =  do
          let
            tdi =  fmap join $ applyIfChange <$>  (fmap (snd.unTBRef)<$>oldItems) <*> tseledit
            replaceKey :: TB CoreKey a -> TB CoreKey a
            replaceKey = firstTB swapKey
            replaceKeyP :: PathAttr CoreKey Showable  -> PathAttr CoreKey Showable
            replaceKeyP = firstPatchAttr swapKey
            swapKey k = maybe k _relTarget (L.find ((==k)._relOrigin) rel)

            staticold :: ColumnTidings
            staticold = fmap (\(i,j) -> (patch <$>  liftA2 apply  (projectValue j) (projectEdit i),pure Nothing  )) . M.mapKeys (S.map (fmap swapKey)) $ M.filterWithKey (\k _ -> all (\i ->  not (isInlineRel i ) &&  (_relOperator i == Equals))k) nonInjRefs
            projectEdit = fmap (fmap replaceKeyP . join . fmap (maybe Keep Diff . unLeftItensP ))
            projectValue = fmap (fmap replaceKey .join . fmap unLeftItens)

{-
          prev <- mapM (\r -> do
            let a = Attr (alterKeyType (\(Primitive i j) -> Primitive [] j  ) $ _relOrigin r) (TB1 ())
            el <- tbCaseDiff inf targetTable mempty a mempty mempty (join . fmap (M.lookup (S.singleton $ Inline $ _relOrigin r ) ._kvvalues.tableNonRef .fst.unTBRef)  <$> ftdi)
            v <- labelCaseDiff inf a (triding el)
            UI.div # set children [getElement v,getElement el] #  set UI.class_ ("col-xs-" <> show (fst $  attrSize a))) rel
          inp <- UI.div
             # set children prev
             # set UI.class_ "row"
             # sink  UI.style (noneShow  <$> facts (triding nav))
             # set style [("border","2px"),("border-color",maybe "gray" (('#':).T.unpack) (schemaColor inf)),("border-style","solid"),("margin","1px")]
-}
          LayoutWidget pretdi celem layout <- dynCrudUITable inf  (triding nav) staticold ((fmap (fmap (fmap targetPRef)) <$> plmods)) targetTable  tdi
          let
            serialRef = if L.any isSerial (keyType <$> rawPK targetTable) then Just (kvlist [])else Nothing
            fksel = fmap TBRef . (\box -> (,) <$> ((reflectFK reflectRels  =<< box) <|> serialRef ) <*> box ). join <$> (applyIfChange <$> tdi <*> pretdi)
            output = (\i j -> diff' i (j <|> i)) <$> oldItems <*> fksel
          ui $ onEventIO (rumors $ (,,) <$> facts tsel <*> facts tedit <#> output) (\(old,olde,i) -> do
            when (fmap filterReflect old /= fmap filterReflect (fmap sourcePRef i) && not (L.null reflectRels)) $ do
              helsel $ fmap (filterReflect.sourcePRef) i
            when (olde /= fmap targetPRef i) $ do
              heleditu $ (fmap targetPRef i)
            )
          return (getElement nav,[celem],max (6,1) <$> layout)
        -- merge i j | traceShow ("merge",i,j) False = undefined
        merge (Diff i) (Diff j) = if L.null (filterReflect i) && L.null j then Keep else Diff (PTBRef (filterReflect i) j )
        merge _ Keep = Keep
        merge _ Delete = Delete
        merge Keep  (Diff _) = Keep
        merge Delete (Diff _) = Delete

      layoutT <- ui $ stepperT (6,1) elayout
      selEls <- traverseUI selector selectT
      element top
        # sink children (facts selEls)
      let lintReflect item = join . fmap nonEmptyTBRef . (fmap (\(TBRef (i,j)) -> TBRef (filterReflectKV i,j ))) <$> item
          oldReflect = lintReflect oldItems
      out <- ui $ calmT (diff' <$> oldReflect <*> (lintReflect  ((\i -> join . applyIfChange  i)<$> oldReflect <*> tdfk )))
      return $ LayoutWidget out top layoutT

traceShowIdPrefix s i = traceShow (s,show i) i

fkUITableGen ::
  InformationSchema
  -- Plugin Modifications
  -> Table
  -> SelTBConstraint
  -> PluginRef  (Column CoreKey Showable)
  -- Same Table References
  -> ColumnTidings
  -- Relation Event
  -> Tidings (Maybe (Column CoreKey Showable))
  -- Static Information about relation
  -> Column CoreKey ()
  -> UI (LayoutWidget (Editor (PathAttr CoreKey Showable)))
fkUITableGen preinf table constr plmods nonInjRefs oldItems tb@(FKT ifk rel fkref)
  = fmap (fmap (recoverPFK setattr rel)) <$> buildUIDiff (fkUITablePrim inf (rel,lookTable inf target,setattr) constr nonInjRefs) (mergeFKRef  $ keyType . _relOrigin <$>rel) (fmap (fmap (fmap liftPFK)) <$> (plmods <> concat replaceNonInj) ) (fmap liftFK <$> foldl' (liftA2 mergeOrCreate) oldItems (snd <$> F.toList nonInjRefs ))
  where
    replaceNonInj = (\(i,j) -> (\v -> (Many [(IProd Nothing (_relOrigin v))],) $ onDiff  ( fmap (\m -> PFK rel [m] (patchChange m )).L.find ((== S.singleton (_relOrigin v) ) . S.map _relOrigin . index) .  nonRefPatch) (const Nothing)<$> fst j )<$> F.toList i ) <$> M.toList nonInjRefs
      where patchChange (PAttr i k ) = fmap (const []) k
    mergeOrCreate (Just i) j = (mergeRef i <$> j) <|> Just i
    mergeOrCreate Nothing j =  mergeRef emptyFKT <$> j
    emptyFKT = FKT  (kvlist []) rel (const (kvlist []) <$> fkref)
    mergeRef (FKT r rel v) i = FKT (foldl' addAttr r (nonRefTB i)) rel v
    addAttr  (KV i) v = KV $ if isNothing (unSOptional (_tbattr v)) then i else (M.insert (index v) v i)
    (targetSchema,target) = findRefTableKey table rel
    inf = fromMaybe preinf $ HM.lookup targetSchema (depschema preinf)
    setattr = keyAttr <$> unkvlist ifk


reduceTable :: [Editor a] -> Editor [a]
reduceTable l
  | L.any isDelete l = Delete
  | otherwise  = (\i -> if L.null i then Keep else Diff i) . filterDiff $ l

pdfFrame (elem,sr , call,st) pdf = mkElement elem UI.# sink0 sr (call <$> pdf)  UI.# UI.set style st

metaTable
  :: InformationSchemaKV Key Showable
  -> Text
  -> [(Rel Text, AccessOp Showable)]
  -> UI Element
metaTable inf metaname env =   do
  let modtable = lookTable (meta inf) metaname
  displayTable (meta inf) modtable (fixrel .Le.over _1 (liftRel (meta inf) metaname) <$> env)


displayTable :: InformationSchema -> Table -> [(Rel Key ,[(Key,AccessOp Showable)] )] -> UI Element
displayTable inf table envK = do
  let
    pred = WherePredicate $ AndColl $ PrimColl <$> envK
  reftb@(_,vpt,_,_) <- ui $ refTables' inf   table Nothing  pred
  tb <- UI.div
  (res,offset) <- paginateList inf table tb (pure $ Just pred) reftb  [] (pure Nothing)
  TrivialWidget pretdi cru <- batchUITable inf table reftb M.empty [] (allRec' (tableMap inf) table) res
  element tb # set UI.children [offset,cru]

filterPatchSet :: Show a => (Int -> Bool) -> PathFTB a -> Maybe (PathFTB a)
filterPatchSet f (PatchSet p) =
  patchSet $ catMaybes $ fmap (filterPatchSet f) (F.toList p)
filterPatchSet f (PIdx ix2 p)
  | f ix2 = Just $ PIdx ix2 p
  | otherwise = Nothing
filterPatchSet f i@(PAtom _) = Just i
filterPatchSet f v = error (show v)

indexPatchSet :: Show a => Int -> PathFTB a -> Maybe (PathFTB a)
indexPatchSet ix (PatchSet p) =
  patchSet $ catMaybes $ fmap (indexPatchSet ix) (F.toList p)
indexPatchSet ix (PIdx ix2 p)
  | ix == ix2 = p
  | otherwise = Nothing
indexPatchSet ix i@(PAtom _) = Just i -- TODO :  Debug  what is triggering this and remove this case
indexPatchSet ix v = error (show (ix, v))
