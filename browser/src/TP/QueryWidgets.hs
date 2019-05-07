{-# LANGUAGE
    OverloadedStrings
   ,ScopedTypeVariables
   ,TypeFamilies
   ,FlexibleContexts
   ,RecursiveDo
 #-}

module TP.QueryWidgets (
    crudUITable,
    batchUITable,
    metaTable,
    ) where

import Debug.Trace
import Safe
import Reactive.Threepenny.PStream  (accumS,PStream(..))
import qualified Data.Functor.Contravariant as C
import Serializer
import qualified Data.Aeson as A
import Control.Lens ( _1, _2)
import PrimEditor
import qualified Control.Lens as Le
import qualified Control.Category as Cat
import Control.Monad
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
import qualified Data.Set as S
import Data.Text (Text)
import qualified Data.Text as T
import Data.Time
import qualified Data.Traversable as Tra
import Default
import Expression
import qualified Graphics.UI.Threepenny as UI
import Graphics.UI.Threepenny.Core hiding (apply,render)
import Graphics.UI.Threepenny.Internal (ui)
import qualified NonEmpty as Non
import qualified Data.Sequence.NonEmpty as NonS
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

type ColumnTidings = Map (Rel CoreKey) (Tidings (Editor (Index(Column CoreKey Showable))),Tidings (Maybe (Column CoreKey Showable)))

genAttr :: InformationSchema -> CoreKey -> TBMeta CoreKey 
genAttr inf k =
  case keyType k of
    Primitive ty p ->
       case p of
         AtomicPrim l -> Attr k (Primitive ty p)
         RecordPrim (s,t) ->
           let table =  lookTable sch t
               sch = fromMaybe inf (HM.lookup s (depschema inf))
            in IT k . Primitive ty $ allFields sch table

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
pluginUI inf trinp (idp,FPlugins n tname (StatefullPlugin ac)) = do
  let
    fresh :: [([VarDef],[VarDef])]
    fresh = fmap fst ac
  b <- flabel # set UI.text (T.unpack n)

  let
    freshKeys :: [([CoreKey],[CoreKey])]
    freshKeys = first (fmap lookK ) . second (fmap lookK) <$> fresh
    lookK = lookKey inf tname . fst
  freshUI <- foldl' (\old (aci ,(inpfresh,outfresh)) -> (old >>= (\(l,unoldItems)-> do
      let inputs fresh = attrB   (genAttr inf fresh)
          attrB a = do
            let pre = const Nothing <$> unoldItems
            wn <-  tbCaseDiff inf (lookTable inf tname) mempty a mempty  mempty pre
            v <- labelCaseDiff inf a pre (triding wn)
            out <- UI.div # set children [getElement v,getElement wn]#  set UI.class_ ("col-xs-" <> show (fst $  attrSize a))
            return  $ TrivialWidget (apply <$> facts pre <#> triding v) out
      elemsIn <- mapM  inputs inpfresh
      let
        inp :: Tidings (Maybe (TBData CoreKey Showable))
        inp = fmap kvlist <$> foldr (liftA2 (liftA2 (:))) (pure (Just [])) (fmap triding elemsIn)

      (preinp,(_,liftedE)) <- pluginUI  inf (liftA2 mergeKV <$>  unoldItems <*>  inp) (idp,FPlugins n tname aci)

      let outputs fresh = attrB (fmap (\v -> justError ("no key " <> show fresh <> " in " <>  show v) . fmap snd $ findKV ((== (Inline fresh)) . index) =<< (createIfChange v :: Maybe (TBData Key Showable))) <$> liftedE)  (genAttr inf fresh)
          attrB pre a = do
            -- wn <- tbCaseDiff inf (lookTable inf tname) []  a M.empty [] pre
            -- TrivialWidget v e <- labelCaseDiff inf a  pre (triding wn)
            out <- UI.div -- # set children [getElement e,getElement wn] #  set UI.class_ ("col-xs-" <> show (fst $  attrSize a))
            return $ TrivialWidget (pre {-apply <$> facts pre <#> v-} ) out

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
      let ecv1 = unionWith const (const (const Nothing) <$> rumors tdInput) ecv
      bcv <- ui $ accumT ini ecv1
      pgOut  <- ui $ mapTidingsDyn (liftIO . execute inf t pl)  bcv
      return (headerP, (out,  pgOut ))
    uipure = do
      headerP <- headerUI
      pgOut <- ui $ mapTidingsDyn (liftIO . execute inf t pl) tdInput
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
checkAccessFull inf  t (inp,out) oldItems = (tdInput,tdOutput,liftAccessU inf t out)
  where
    tdInput = join . fmap (checkPredFull inf t inp) <$> oldItems
    tdOutput = join . fmap (checkPredFull inf t out) <$> oldItems



indexPluginAttrDiff
  ::  TBMeta Key 
  -> [(Union (Access Key), Tidings (Editor (Index (TBData Key Showable))))]
  -> [(Union (Access Key), Tidings (Editor (Index (Column Key Showable))))]
indexPluginAttrDiff a@(Attr i _ )  plugItems =  evs
  where
    match (IProd _ l) ( IProd _ f) = l == f
    match i f = False
    thisPlugs = filter (hasProd (`match` IProd Nothing i) . fst)  plugItems
    evs  = fmap (fmap (join . fmap (maybe Keep  (Diff . rebuild (keyattr a)) . M.lookup (keyattr a)  ))) <$>  thisPlugs
indexPluginAttrDiff i plugItems = pfks
  where
    prodRef = IProd Nothing
    thisPlugs = filter (hasProd (isNested (fmap (prodRef . _relOrigin) (relUnComp $ keyattr i) )) .  fst) plugItems
    pfks =  first (uNest . justError "No nested Prod FKT" .  findProd (isNested(fmap ( prodRef . _relOrigin ) (relUnComp $ keyattr i) ))) 
        . second (fmap (join . fmap (maybe Keep  (Diff . rebuild (keyattr i)) . M.lookup (keyattr i)  ))) <$>  thisPlugs


--- Style and Attribute Size
--
attrSize :: TBF CoreKey f b -> (Int,Int)
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
       PGeom 3 PPosition  -> (6,1)
       PGeom 2 PPosition  -> (3,1)
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

getRelOrigin :: Ord k => [TBF k f b ] -> [k ]
getRelOrigin =  fmap _relOrigin .  concatMap (relUnComp .keyattr)

attributeLabel :: TBMeta Key -> String
attributeLabel i =  renderRel (keyattr i)

labelCaseDiff
  ::  InformationSchema
  -> TBMeta Key
  -> Tidings (Maybe (Column CoreKey Showable))
  -> Tidings (Editor (Index (Column CoreKey Showable)))
  -> UI (TrivialWidget (Editor (Index (Column CoreKey Showable))))
labelCaseDiff inf a o wid = do
  let
    dynShow = do
      lref <- UI.div
        # set text (show $ keyattr  a)
      ltype <- UI.div
        # set text (show $ relType' $ keyattr  a)
      ldelta <- UI.div
        # sink text  (show <$> facts wid)
      UI.div # set children [lref,ltype,ldelta]
  hl <- detailsLabel (set UI.text (attributeLabel a) . (>>= paintEditDiff o wid)) dynShow
  return $ TrivialWidget wid hl

paintEditDiff o i e = element e # sink UI.style ( facts $ st <$> (cond <$> o <*> i ))
  where cond _ Delete = ("red","white")
        cond Nothing Keep = ("purple","white")
        cond (Just i)  Keep = ("black","white")
        cond (Just _) (Diff i) = ("yellow","black")
        cond Nothing  (Diff i) = ("lightblue","black")
        st (back,font)= [("background-color",back),("color",font)]

filterConstr rel  = filter ((relOutputSet (relComp rel) `S.isSubsetOf`). S.unions . fmap relOutputSet .fst)

tbCaseDiff
  :: InformationSchema
  -> Table
  -> SelPKConstraint
  -> TBMeta Key
  -> ColumnTidings
  -> PluginRef (Column CoreKey Showable)
  -> Tidings (Maybe (Column CoreKey Showable))
  -> UI (LayoutWidget (Editor (Index (Column CoreKey Showable))))
tbCaseDiff inf table constr i@(FKT ifk  rel tb1) wl plugItems oldItems= do
  let
    nonInj = S.fromList (_relOrigin <$> rel) `S.difference` S.fromList (getRelOrigin $ unkvlist ifk)
    nonInjRefs = M.filterWithKey (\k _ -> (\i -> not (S.null i) && S.isSubsetOf i nonInj ) .  relOutputSet $ k) wl
    restrictConstraint =  filterConstr rel constr
    reflectFK' rel box = (\ref -> pure $ FKT ref rel (TB1 box)) <$> reflectFK frel box
      where frel = filter (\(Rel i _ _) -> isJust $ kvLookup i ifk) rel
    convertConstr j =  fmap ((\(C.Predicate constr) ->  C.Predicate $ maybe False constr  .  reflectFK' rel)) j
    newConstraints = (fmap convertConstr <$>  restrictConstraint) 
  -- liftIO $ print ("Constraints FKT",rel, relOutputSet .relComp . fst <$> constr , fst <$> newConstraints)
  fkUITableGen inf table (fmap convertConstr <$>  restrictConstraint) plugItems nonInjRefs oldItems  i
tbCaseDiff inf table constr i@(IT na tb1 ) wl plugItems oldItems = do
    let isRelA (RelAccess i _ ) = i == Inline na
        isRelA _ = False
    let restrictConstraint = filter (L.any isRelA . fst) constr
    iUITableDiff inf (fmap (fmap (C.contramap (pure . IT na .TB1 ))) <$>restrictConstraint) plugItems oldItems i
tbCaseDiff inf table _ a@(Attr i _ ) wl plugItems preoldItems = do
  let oldItems = maybe preoldItems (\v-> fmap (maybe (Attr i <$> (evaluateKeyStatic (keyType i) v)) Just ) preoldItems) ( keyStatic i)
      tdiv = fmap _tbattr <$> oldItems
      insertT = fmap (PAttr i)
  fmap insertT <$> buildUIDiff (buildPrimitive (keyModifier i)) (const True) (keyType i) (fmap (fmap (fmap (\(PAttr _ v) -> v))) <$> plugItems) tdiv
tbCaseDiff inf table _ a@(Fun i rel ac ) wl plugItems preoldItems = do
  let
    search f (Inline t) = fmap (fmap (fmap _tbattr)) . f $ justError ("cant find: " <> show (a ,t , M.keys wl)) (M.lookup (Inline t) wl)
    search f (RelAccess t m) =  fmap (fmap (fmap joinFTB . join . fmap (traverse (recLookup m) . _fkttable))) . f $ justError ("cant find rel" <> show t) (M.lookup t  wl)
    search f i = error (show i)
    -- Add information if the patch is Keep
    refs = sequenceA $ search recoverValue <$> snd rel
    liftType (KOptional :xs) i = Just $ LeftTB1 (join $ liftType xs . Just <$> i)
    liftType [] i = i
    liftKey = fmap (liftType (_keyFunc $ keyType i).join)
  -- Only executes if not all patches are Keep and all values are Just
  funinp <-  ui $ liftKey <$> mapEventDyn (liftIO . traverse ( evaluateFFI inf (tableMeta table)  (fst rel) funmap (buildAccess <$> snd rel)) . allMaybes . fmap snd ) (filterE (not . all fst) $ rumors refs)

  -- FIXME : Function evaluation is producing Delete when using offset.
  let pout = (\i j ->  ignoreDelete $ diff' i j )<$> facts preoldItems <@> (fmap (Fun i rel) <$> funinp)
      ignoreDelete Delete  = Keep
      ignoreDelete i = i

  -- The new functions is
  -- t == 0 = initial value
  -- t  > 0 = latest (input event , function evaluated)
  out <- ui $ calmT =<< stepperT  Keep (unionWith const (const Keep <$> rumors preoldItems) pout)
  ev <- buildUIDiff (buildPrimitive [FRead]) (const True) (keyType i) ((fmap (fmap (fmap (\(PFun _ _ v) -> v)))<$>plugItems) <> [(Many [],((fmap (\(PFun _ _ v) -> v)))<$> out)]) (fmap _tbattr <$> preoldItems )
  return $ LayoutWidget  out (getElement ev) (getLayout ev)



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
   -> KVMeta Key
   -> Tidings (Maybe (TBData CoreKey Showable))
   -> [(Rel Key)]
   ->  UI (LayoutWidget  (Editor (TBIdx CoreKey Showable)))
anyColumns inf hasLabel el constr table refs plugmods  fields oldItems cols =  mdo

      let
        projectAttr = (L.find (isJust .  unLeftItens) . unkvlist =<<)
        initialAttr = projectAttr <$> oldItems
        fks2 = M.fromList  $ run <$> cols
        sumButtom itb =  do
          el <- UI.div
          let prev = join . fmap unLeftItens . join . fmap (kvLookup itb ) <$> oldItems
              edit = ((maybe Delete Diff. unLeftItensP <=< maybe Keep (Diff . rebuild itb) . M.lookup itb) =<< )<$> resei
              kb = justError "no sum column" $ kvLookup itb fields
          element =<< labelCaseDiff inf kb prev  ((\i j-> fromMaybe Keep $ diff i =<< (applyIfChange i j)) <$> prev <*> edit)
        marker i = sink  UI.style ((\b -> if not b then [("border","1.0px gray solid"),("background","gray"),("border-top-right-radius","0.25em"),("border-top-left-radius","0.25em")] else [("border","1.5px white solid"),("background","white")] )<$> i)

      chk <- buttonDivSetO (kvkeys fields)  (fmap index <$> initialAttr)  marker sumButtom
      fks <- switchManyLayout (triding chk) fks2
      element chk # set UI.style [("display","inline-flex")]
      let
        resei :: Tidings (Editor (TBIdx CoreKey Showable))
        resei = fmap defaultInitial  <$>  triding fks
        defaultInitial new
          = kvlistp $ defaults ++ [new]
            where defaults = patch <$> (addDefault' <$> filter ((/= index new ) . keyattr) (unkvlist fields) :: [TB Key Showable])
      listBody <- UI.div #  set children (getElement chk : [getElement fks])

      let computeResult i j = -- trace (show result ++ show (projectAttr (apply i j )) ++  "\n" ++ maybe "" (ident . render) (apply i j) )
                  result
            where result = case (isJust (projectAttr (apply i j)) ,isJust (projectAttr i)) of
                    (False,True) -> Delete
                    (False,False)-> Keep
                    (_,_) -> j
      return (LayoutWidget ( computeResult <$> facts oldItems <#> resei) listBody (getLayout fks))
  where
    meta = tableMeta table
    run l = (l,do
      let m = justError (show ("no fields",l,fields)) $ kvLookup l fields
          plugattr = indexPluginAttrDiff m plugmods
          oldref = (kvLookup l =<<) <$> oldItems
      tbCaseDiff inf table constr m M.empty plugattr oldref
      )



buildFKS
  :: InformationSchema
   -> Bool
   -> UI Element
   -> SelPKConstraint
   -> Table
   -> ColumnTidings
   -> PluginRef (TBData CoreKey Showable)
   -> KVMeta Key
   -> Map (Rel Key) Plugins
   -> Tidings (Maybe (TBData CoreKey Showable))
   -> [(Rel Key)]
   -> UI [(Rel Key, (LayoutWidget (Editor (PathAttr CoreKey Showable)),
                             Tidings (Maybe (Column CoreKey Showable))))]
buildFKS inf hasLabel el constr table refs plugmods ftb plugs oldItems = fmap fst . F.foldl' run (return ([],[]))
  where
    meta = tableMeta table
    replaceNonInj :: Rel Key -> [(Union (Access (Key)),
                        Tidings (Editor (PathAttr (FKey (KType CorePrim)) Showable)))]
    replaceNonInj l = maybe [] (\j -> pure (Many (IProd Nothing . _relOrigin <$> relUnComp l ),  fst j))  aref
       where aref = M.lookup l refs
    previous i = (kvLookup i =<<) <$> oldItems
    run jm l = do
      (w,oplug) <- jm
      let matchPlug plug = do
           let
              wl = M.fromList $ fmap (first triding) <$> w
              plugattr k v = case kvLookup k ftb of
                 Just i  -> flip apply <$> compactPlugins' (indexPluginAttrDiff i  (plugmods ++ oplug) <> replaceNonInj k)  <*> v
                 Nothing -> v
              search f t@(Inline _) = plugattr t $ maybe (previous t) f $ M.lookup t wl
              search f (Output t) =  previous t
              search f (RelAccess t m) = plugattr t $ maybe (previous t) f $ M.lookup t  wl
              inputs = sequenceA $ search (fmap snd . recoverValue) <$> relUnComp l
           (el,(i,o)) <- pluginUI inf (fmap kvlist . nonEmpty . catMaybes <$> inputs) plug
           label <- flabel #  set text (renderRel l)
           plug <- UI.div # set children [label,el]

           let out = (relComp [] ,(LayoutWidget (pure Keep) plug (pure (3,1)),pure Nothing))
           return (w <> [out],oplug ++ [(i,maybe Keep Diff <$> o)])
      let matchAttr m = do
              let
                plugattr = indexPluginAttrDiff m (plugmods ++ oplug)
                oldref = previous l
              wn <-  tbCaseDiff inf table constr m (M.fromList $ fmap (first triding) <$> w) (replaceNonInj l <> plugattr) oldref
              lab <- if
                hasLabel
                then do
                  (\i -> LayoutWidget (triding wn) i (getLayout wn)) <$> el # set children [getElement wn]
                else do
                  v <- labelCaseDiff inf m oldref (diff' <$> facts oldref <#> checkDefaults inf table  (keyattr m) (wn,oldref))
                  out <- el # set children [getElement v,getElement  wn]
                  return $ LayoutWidget (triding wn) out (getLayout wn)
              return (w <> [(keyattr m,(lab,oldref))] ,oplug)
      justError ("could not find attr: " <> show l <> "\n plugs "<> unlines (show <$> M.keys plugs ) <> "\nattrs " <> unlines (show <$> kvkeys ftb) ) $ (matchPlug <$> M.lookup l plugs) <|>  (matchAttr <$> kvLookup l ftb )


recoverValue (edit,old) = (\i j -> (isKeep j,join $ (applyIfChange i j) <|> (createIfChange j) <|> Just i ) ) <$> old <*> edit


deleteCurrentUn
  :: Foldable f
  => [Rel Key]
  -> f (TBData Key Showable)
  -> G.GiST (TBIndex Showable) a
  -> G.GiST (TBIndex Showable) a
deleteCurrentUn  un l e =  foldl' (\l e -> G.delete (G.getUnique un e) G.indexParam l) e l

tableConstraints
  :: Foldable f =>
     (KVMetadata Key,
      Tidings (TableRep Key Showable))
     -> Tidings (f (TBData Key Showable)) -> KVMeta Key  -> SelPKConstraint
tableConstraints (m ,gist) preoldItems ftb = constraints
  where
    constraintPred :: [Rel Key]
                      -> Tidings (Maybe (G.GiST (TBIndex Showable) a))
                      -> ([Rel Key], Tidings (C.Predicate [TB Key Showable]))
    constraintPred un gist =  (un,  
          (C.Predicate . maybe (const False) (flip (checkGist un .  kvlist)))<$> 
            ((\i -> fmap (deleteCurrentUn  un i)) <$> preoldItems <*> gist))
    primaryConstraint = constraintPred (_kvpk m) (Just . primary <$> gist)
    secondaryConstraints un = constraintPred  un  (M.lookup un . secondary <$>  gist)
    constraints :: SelPKConstraint
    constraints = primaryConstraint : (secondaryConstraints <$> _kvuniques m)

batchUITable
   :: InformationSchema
   -> Table
   -> RefTables
   -> ColumnTidings
   -> PluginRef (TBData CoreKey Showable)
   -> KVMeta CoreKey 
   -> Tidings [TBData CoreKey Showable]
   -> UI (TrivialWidget [Editor (TBIdx CoreKey Showable)])
batchUITable inf table reftb@(_, gist ,tref) refs pmods ftb  preoldItems2 = do
  let
    m = tableMeta table
  preoldItems <- ui $ loadItems inf table  ftb preoldItems2
  let arraySize = 30
      index = flip atMay
      constraints = tableConstraints (m,gist) preoldItems ftb
      unIndexEl ix =  index ix <$> preoldItems
      dyn = dynHandlerPatch  (\ix valix plix ->do
        (listBody,tablebdiff) <- rowTableDiff inf table constraints refs pmods ftb ix valix
        return $ LayoutWidget tablebdiff listBody (pure (12,0))) unIndexEl (\ix -> []) (const True)

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
  :: KVMeta Key -> UI Element
rowTableHeaders  ftb = do
  ixE <- UI.div # set UI.class_ "col-xs-1" # set text "#"
  operation <- UI.div # set UI.class_ "col-xs-1"# set text "Action"
  let
    label (k,x) = do
      l <- detailsLabel (set UI.text (attributeLabel x )) (UI.div # set text (show $ keyattr x))
      UI.div # set children [l] # set UI.class_ ("col-xs-" <> show (fst (attrSize x)))
    srefs = sortedFields ftb
  els <- mapM label srefs
  UI.div # set children (ixE : operation : els) # set UI.style [("display", "flex")]

validateRow :: WidgetValue f =>
     InformationSchema
  -> Table
  -> [( Rel CoreKey
      , (f (Editor (PathAttr CoreKey Showable))
        , Tidings (Maybe (Column CoreKey Showable))))]
  -> Tidings (Editor (TBIdx CoreKey Showable))
validateRow inf table fks =
  ifValid <$>
  sequenceTable fks <*>
  isValid fks
  where
    ifValid i j =
      kvlistp <$> if isJust j
        then i
        else (if isDiff i then Keep else i)
    sequenceTable fks =
      reduceTable <$> Tra.sequenceA (triding . fst . snd <$> fks)
    isValid fks = sequenceA <$> sequenceA (uncurry (checkDefaults inf table) <$>  fks)

checkDefaults inf table k  (r, i) =  applyDefaults inf table k  <$> facts i <#> triding r


applyDefaults inf table k i j = 
  join (applyIfChange i j) <|> join (createIfChange (def j)) <|> i
  where
    defTable = defaultTableType inf table
    defField = rebuild k <$> M.lookup k defTable
    def (Diff i) =
      Diff . maybe i (\a -> head $ compact [rebuild k a, i]) $ M.lookup k defTable
    def Keep = maybe Keep Diff defField
    def Delete = maybe Delete (const Keep) defField

plugKeyToRel
  :: InformationSchema
  -> Table
  -> KVMeta Key
  -> (Union (Access Text),Union (Access Text))
  -> (Rel Key)
plugKeyToRel inf table ftb (i,o) = relComp (inp <> out)
  where
    liftAccess i = filter (isJust. filterEmpty) (F.toList (liftAccessU inf tname i))
    inp = concat $ genRel M.empty <$>  liftAccess i
    out = concat  $ (fmap Output .relAccesGen') <$>  liftAccess  o
    tname = tableName table

rowTableDiff
  :: InformationSchema
  -> Table
  -> SelPKConstraint
  -> ColumnTidings
  -> PluginRef (TBData CoreKey Showable)
  -> KVMeta Key
  -> Int
  -> Tidings (Maybe (TBData CoreKey Showable))
  -> UI (Element,Tidings (Editor (TBIdx CoreKey Showable)))
rowTableDiff inf table constr refs plmods ftb@k ix oldItems= do
  ixE <- UI.div # set text (show ix) # set UI.class_ "col-xs-1"
  operation <- UI.div # set UI.class_ "col-xs-1"
  let
    meta = tableMeta table
    pluginMap = M.fromList $ fmap (\i -> (plugKeyToRel inf table ftb $ pluginStatic (snd i) ,i )) $ filter ((== rawName table )  . _pluginTable .snd) (fmap (\(PluginField i ) -> i) $ pluginFKS table)

  let
    srefs :: [Rel Key]
    srefs =  sortRels (M.keys pluginMap <> kvkeys ftb)
    plugmods = first traRepl <$> plmods

    isSum = rawIsSum table
  (listBody,out) <- do
      fks <- buildFKS inf True UI.div constr table refs plugmods ftb pluginMap oldItems srefs
      mapM (\(s,(i,_)) -> element (getElement  i) #  sink UI.class_ (facts $ (\i -> "col-xs-" <> show (fst   i)) <$> getLayout i)) fks
      listBody <- UI.div # set children (ixE : operation : (getElement . fst . snd <$> fks)) # set UI.style [("display", "flex"),("min-width","max-content")]
      return (listBody, validateRow inf table (filterEmptyPlugs fks))
  element listBody
    # set style [("border","1px"),("border-color",maybe "gray" (('#':).T.unpack) (schemaColor inf)),("border-style","solid"),("margin","1px")]

  reftb <- ui $ refTables inf table
  (outI ,_) <- processPanelTable listBody inf reftb  out table oldItems
  element operation #  set children [outI]
  return (listBody , out)

filterEmptyPlugs = filter (not. relNull . fst)
eiTableDiff
  :: InformationSchema
  -> Table
  -> SelPKConstraint
  -> ColumnTidings
  -> PluginRef (TBData CoreKey Showable)
  -> KVMeta Key
  -> Tidings (Maybe (TBData CoreKey Showable))
  -> UI (LayoutWidget (Editor (TBIdx CoreKey Showable)))
eiTableDiff inf table constr refs plmods ftb@k preoldItems = do
  oldItems <- ui $ calmT preoldItems
  let
    meta = tableMeta table
    pluginMap = M.fromList $ fmap (\i -> (plugKeyToRel inf table ftb $ pluginStatic (snd i) ,i )) $ filter ((== rawName table )  . _pluginTable .snd) (fmap (\(PluginField i ) -> i) $ pluginFKS table)
  let
    srefs :: [Rel Key]
    srefs =  sortRels (M.keys pluginMap <> kvkeys ftb )
    plugmods = first traRepl <$> plmods

  let isSum = rawIsSum table
  LayoutWidget output listBody layout <- if isSum
    then
      anyColumns inf isSum UI.div constr table refs plugmods ftb oldItems srefs
    else  do
      fks <- buildFKS inf isSum UI.div constr table refs plugmods ftb pluginMap  oldItems srefs
      mapM (\(s,(i,_)) -> element (getElement  i) #  sink UI.class_ (facts $ (\i -> "col-xs-" <> show (fst i)) <$> getLayout i)) fks
      listBody <- UI.div # set children (getElement .fst . snd  <$> fks)
      let vertical = (\i -> (min (fst i ) 12,max (snd i) 1)) . foldl1 horizontalL <$> sequenceA(getLayout . fst .snd <$>  fks)
      return $ LayoutWidget (validateRow inf table (filterEmptyPlugs fks)) listBody  vertical
  element listBody
    # set UI.class_ "row"
    # set style [("border","1px"),("border-color",maybe "gray" (('#':).T.unpack) (schemaColor inf)),("border-style","solid"),("margin","1px")]
  body <- UI.div
    # set children (pure listBody)
    # set style [("margin-left","0px"),("border","2px"),("border-color",maybe "gray" (('#':).T.unpack) (schemaColor inf)),("border-style","solid")]
  out <- ui $ calmT output
  return $ LayoutWidget out body layout


loadItems
  :: (Eq (t (TBIndex Showable)),Show (t (KV Key Showable)) , Traversable t) =>
     InformationSchema
     -> Table
     -> KVMeta Key
     -> Tidings (t (TBData CoreKey Showable))
     -> Dynamic (Tidings (t (TBData CoreKey Showable)))
loadItems inf table tbf preoldItems
  = do
     pkOnly <- calmTFilter (fmap (G.getIndex (tableMeta table ))) preoldItems
     joinT =<< mapTidingsDyn
        (fmap sequenceA .  traverse
          (\i -> do
            fmap (justError ("failed getFrom " <> show (tableName table,i))) <$>  (transactionNoLog inf . getItem $ i)
            ) )pkOnly 
  where
    getItem = listenFrom table tbf

crudUITable
   :: InformationSchema
   -> Table
   -> RefTables
   -> ColumnTidings
   -> PluginRef (TBData CoreKey Showable)
   -> KVMeta Key
   -> Tidings (Maybe (TBData CoreKey Showable))
   -> UI (LayoutWidget (Editor (TBIdx CoreKey Showable)))
crudUITable inf table reftb@(_,gist ,_) refs pmods ftb  preoldItems2 = do
  let
    m = tableMeta table

  preoldItems <-  ui $ loadItems inf table ftb  
  -- FIXME : this kvNonEmpty was not necessary before somewhere is leaking empty tables
      =<< mapTidingsDyn (pure . join . traverse kvNonEmpty) preoldItems2

  title <- UI.h5
        # sink text (facts $ maybe "" (attrLine inf  (tableMeta table)) <$> preoldItems)
        # set UI.class_ "header"
  let
    constraints = tableConstraints (m,gist) preoldItems ftb
  -- liftIO $ print ("Table Constraints",fst <$> constraints,_kvuniques (tableMeta table))
  LayoutWidget tablebdiff listBody layout <- eiTableDiff inf  table constraints refs pmods ftb preoldItems
  (panelItems ,e) <- processPanelTable listBody inf reftb tablebdiff table preoldItems

  
  navMeta  <- buttonDivSet  ["Status","Backend Log","Changes","Schema","Indexes"] (pure $ Just "Status") (\i -> UI.button # set UI.text i # set UI.style [("font-size","unset")] # set UI.class_ "buttonSet btn-xs btn-default btn pull-left")
  info <- switchManyLayout (triding navMeta) 
    (M.fromList [
       ("Status", emptyLayout  $ printErrors e)
      ,("Backend Log", emptyLayout $ logConsole inf table)
      ,("Changes", emptyLayout $ debugConsole   preoldItems tablebdiff)
      ,("Indexes", emptyLayout $ tableIndexes reftb table)
      ,("Schema", emptyLayout $ tableSchema table)])
  
  out <- UI.div # set children [title,listBody,panelItems,getElement navMeta,getElement info]
  return $ LayoutWidget tablebdiff out layout

emptyLayout i = (\i -> LayoutWidget (pure Nothing) i (pure (10,10)))  <$> i 

openClose open = do
  let translate True = "expand"
      translate False = "collapse-up"
  nav  <- buttonDivSet [True,False] (fmap Just open)
      (\i -> UI.button
          # set UI.style [("font-size","unset"),("font-weight","bolder")]
          # set UI.class_ ("buttonSet btn-xs btn-default btn pull-left glyphicon glyphicon-" <> translate i))
  return nav

tableIndexes reftb@(_,gist,_) table  = do
  let displayTable  un =
              UI.mkElement "textarea" # sink0 UI.value (facts $ unlines . zipIx . fmap renderIdex .L.sort . idx un<$>  gist )
                  # set UI.style [("max-height","300px"),("width","100%")]
      idx  un gist
        | un == rawPK table =  G.keys . primary $ gist
        | otherwise = G.keys . fromMaybe G.empty . M.lookup un  .secondary $ gist
      uns = _rawIndexes table
      renderIdex (Idex l ) = L.intercalate "," (renderShowable <$> l) ++ " - " ++ show l
      zipIx v = zipWith (\i j -> show i ++ (L.replicate (L.length (show (L.length v)) - L.length (show i)) ' '  ) ++ " " ++  j ) [0..] v
  navMeta  <- buttonDivSet uns (pure (Just $ rawPK table)) 
    (\i -> UI.button # set UI.text (renderRel $ relComp i) # set UI.style [("font-size","unset")] # set UI.class_ "buttonSet btn-xs btn-default btn pull-left")
  info <- switchManyLayout (triding navMeta)  (M.fromList $ (\i -> (i,  emptyLayout $ displayTable  i)) <$> uns)
  element navMeta # set UI.class_ "col-xs-12" 
  element info # set UI.class_ "col-xs-12"  # adjustArea gist # adjustArea (triding navMeta)

  h <- UI.h6 # sink UI.text (renderRel . relComp <$> facts (triding navMeta)) # set UI.class_ "col-xs-10" 
  stat <- UI.span # sink UI.text (facts $ (\f -> show $ L.length f) <$> (idx <$> triding navMeta <*> gist )) # set UI.class_ "col-xs-2"
  UI.div # set UI.class_ "col-xs-12" #  set children [h,stat,getElement navMeta ,getElement info] 
 
adjustArea b e= do
  v <- e
  e # method  "textAreaAdjust(%1)"
  onChanges (facts b) $ \_ -> do 
    e # method  "textAreaAdjust(%1)"
  return v 

tableSchema table  = do
  let displayTable i = 
        [("name", show $ _kvname i)
        ,("indexes", "\n" <>  L.intercalate "\n" (  fmap (prefix . L.intercalate "," . fmap renderRel ) $ _kvuniques i))
        ,("attrs", "\n" <> L.intercalate "\n" (  fmap (prefix . show) $ _kvattrs i))] 
      render = unlines . fmap (\(i,j ) -> i <> ": " <> j  ) 
      prefix i = "\t"  <> i 
  e <- UI.mkElement "textarea" 
     # set UI.value (render $ displayTable (tableMeta table) )
     # set UI.style [("max-height","300px"),("width","100%")]
  element e # method  "textAreaAdjust(%1)"
  return e 
    
dynCrudUITable
   :: InformationSchema
   -> Tidings Bool
   -> ColumnTidings
   -> PluginRef (TBData CoreKey Showable)
   -> Table
   -> Tidings (Maybe (TBData CoreKey Showable))
   -> UI (LayoutWidget (Editor (TBIdx CoreKey Showable)))
dynCrudUITable inf nav refs pmods table preoldItems = do
  switchUILayout (pure Keep) UI.div nav
      (do
        reftb@(_,gist,_) <- ui $ refTables inf table
        i <- crudUITable inf table reftb refs pmods (allFields inf table) preoldItems
        element i # set UI.class_ "col-xs-12"
        return i
      )

mergePatches i j = join $ (liftA2 applyIfChange i j)<|> (createIfChange <$> j) <|> Just i

onDiff f g (Diff i ) = f i
onDiff f g v = g v

filterKey enabled k = void (filterApply (const <$> enabled) k)
containsOneGist table ref = (==1).  L.length . conflictGist  table ref
containsGist table ref = not . L.null .   conflictGist  table ref
conflictGist table ref map = case  G.primaryKeyM (tableMeta table) ref of
              Just i -> G.search i map
              Nothing -> []

catchEd  m  = (Right <$> sequence m) `catchAll` (\ e -> return (Left (show e)))

insertCommand lbox inf table inscrudp inscrud  authorize gist = do
    altI <- onAltI lbox
    let insertEnabled = liftA3 (\i j k -> i && j && k ) 
          (isDiff <$> inscrudp ) 
          (maybe False  (\i -> (isRight .tableCheck m  $ i) || isJust (matchInsert inf (tableMeta table ) i) ) <$>  inscrud) 
          (liftA2 (\j -> maybe True (not. (flip (containsGist table) j))) gist inscrud)
        m = tableMeta table
    insertI <- UI.span # set UI.class_ "glyphicon glyphicon-plus"
    insertB <- UI.button
        # set UI.class_ "btn btn-sm btn-default"
        # set children [insertI]
         # sink UI.style (facts $ (\i j -> noneShowSpan (maybe False (txt "INSERT" `elem`) i && j)) <$>authorize <*> insertEnabled)
    cliIns <- UI.click insertB
    let  crudIns j  =  do
        -- liftIO $ print j
            transaction inf (fullInsert m j)
    diffIns <- ui $ mapEventDyn catchEd $ fmap crudIns <$> facts inscrud <@ unionWith const cliIns (filterKey  (facts insertEnabled) altI )
    return $ (diffIns ,insertB)

editCommand lbox inf table oldItemsi inscrudp inscrud  authorize gist = do
    altU <- onAltU lbox
    let
      m = tableMeta table
      editEnabled = (\i j k l m -> i && j && k && l && m ) <$> (maybe False (\i -> (isRight .tableCheck m  $ i) || isJust (matchUpdate inf (tableMeta table ) i)) <$> inscrud ) <*> (isJust <$> oldItemsi) <*>   liftA2 (\i j -> maybe False (flip (containsOneGist table) j) i ) inscrud gist <*>   liftA2 (\i j -> maybe False (flip (containsGist table) j) i ) oldItemsi gist <*>  (isDiff  <$> inscrudp)
      crudEdi (Just i) (Diff j) =  do
        Just <$> transaction inf $ fullEdit m i j
    editI <- UI.span # set UI.class_ "glyphicon glyphicon-edit"
    editB <- UI.button
        # set UI.class_ "btn btn-sm btn-default"
        # set children [editI]
        # sink UI.style (facts $ (\i j -> noneShowSpan (maybe False (txt "UPDATE" `elem`) i && j)) <$>authorize <*> editEnabled)
    -- Edit when any persistent field has changed
    cliEdit <- UI.click editB
    diffEdi <- ui $ mapEventDyn catchEd $ crudEdi <$> facts oldItemsi <*> facts inscrudp <@ unionWith const cliEdit (filterKey (facts editEnabled)  altU)
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
        # sink UI.style (facts $ (\i j -> noneShowSpan (maybe False (txt "DELETE" `elem`) i && j)) <$>authorize <*> deleteEnabled)

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
        # sink UI.style (facts $ (\i j -> noneShowSpan (maybe False (txt "UPDATE" `elem`) i && j)) <$>authorize <*> mergeEnabled)
    cliMerge <- UI.click mergeB
    diffMerge <- ui $ mapEventDyn catchEd $ liftA2 crudMerge <$> facts inscrud <*> fmap Just (facts gist) <@ cliMerge
    return (diffMerge,mergeB)


logConsole inf table = do 
  t <- ui $ listenLogTable inf table 
  e <- UI.mkElement "textarea" 
          # set UI.class_ "col-xs-12" 
          # sink UI.value (unlines <$> facts t)
          # set UI.style [("max-height","300px"),("width","100%")]
  element e # method  "textAreaAdjust(%1)"
  return e 

debugConsole oldItemsi inscrudp = do
    let
      inscrud = fmap join $ applyIfChange <$> facts oldItemsi <#> inscrudp
      gen (h,s) = do
        header <- UI.h6
                  # set UI.class_ "header"
                  # set UI.text h
                  # set UI.style [("text-align","center")]
        out <- UI.mkElement "textarea"
                  # sink UI.value s
                  # set UI.style [("max-height","300px"),("width","100%")]
        onChanges s (\ _ -> element out # method "textAreaAdjust(%1)")
        element out # method  "textAreaAdjust(%1)"
        UI.div # set children [header,out]
               # set UI.class_ "col-xs-6"
    debugT <- mapM gen
                  [("Last", maybe "" (ident . render) <$> facts oldItemsi),
                  ("Diff", onDiff (ident . render) (const "") <$> facts inscrudp)
                  ,("Undo", maybe "" (onDiff (ident . render) (const "")) <$> (diff <$> facts inscrud <*> facts oldItemsi))]
    UI.div # set children debugT # set UI.class_ "col-xs-12"

processPanelTable
  :: Element
   -> InformationSchema
   -> RefTables
   -> Tidings (Editor (TBIdx CoreKey Showable))
   -> Table
   -> Tidings (Maybe (TBData CoreKey Showable))
   -> UI (Element,Event [String])
processPanelTable lbox inf reftb@(_,trep,_) inscrudp table oldItemsi = do
  let
    inscrud = fmap join $ applyIfChange <$> facts oldItemsi <#> inscrudp
    m = tableMeta table
    authPred =  [(keyRef "grantee",Left ( int $ usernameId inf ,Equals)),(keyRef "schema",Left (int $ schemaId inf  ,Equals))]
  auth <- ui (transactionNoLog (meta inf) $ selectFromTable "authorization" Nothing authPred)
  let authorize =  ((fmap unArray . unSOptional . lookAttr' "authorizations") <=< G.lookup (idex  (meta inf) "authorization"  [("table",int $ tableUnique table),("grantee",int $ usernameId inf)])). primary   <$> collectionTid auth

  let gist = primary <$>  trep
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

compactPlugins  valix plix= fromMaybe Keep .safeHead . compact <$> (F.foldl' (liftA2 (flip (:)))  (pure .const Keep <$> valix)  (snd<$> plix))
compactPlugins'  plix= fromMaybe Keep .safeHead . compact <$> (F.foldl' (liftA2 (flip (:))) (pure []) (snd<$> plix))

dynHandlerPatch
  :: (Compact (Index a1),Patch a1,Eq (Index a1),Show (Index a1),Show a1,Eq a1)
  => (Int -> Tidings (Maybe a1) -> PluginRef a1 -> UI (LayoutWidget (Editor (Index a1))))
  -> (Int -> Tidings (Maybe a1))
  -> (Int -> PluginRef a1)
  -> (a1 -> Bool)
  -> Int
  -> ([LayoutWidget (Editor (Index a1))], Tidings Bool)
  -> UI ([LayoutWidget (Editor (Index a1))], Tidings Bool)
dynHandlerPatch hand val valp check ix (l,old)= do
    valix <- ui $ calmT (val ix)
    plix <- ui $ traverse (traverse calmT) (valp ix)
    oldC <- ui (calmT old)
    let next = hand ix valix plix
    el <- switchUILayout (compactPlugins valix plix) (UI.div # set UI.style [("display","none")]) oldC next
    return (l <> [el], flip (\i j -> maybe False check i && j ) <$> facts old <#> ((\ i j -> join $ applyIfChange i j <|> createIfChange j <|> Just i) <$> valix <*> triding el))


reduceDiffList
  :: Show a => Int -> Int
     -> [(Int, Editor (PathFTB a))]
     -> [Editor (PathFTB a)]
     -> Editor (PathFTB a)
reduceDiffList arraySize o i plugM
   | F.length i  == 0 = Keep
   | F.all isKeep (snd <$> i) = Keep
   | otherwise = patchEditor $  removeOverlap plugl ++ notOverlap ++  removeOverlap plugu ++ reverse (rights diffs)
   where diffs = catMaybes $ (\(ix,v) -> treatA (o+ix)v) <$> i
         treatA a (Diff v) = Just $ Left $ PIdx a  (Just v)
         treatA a Delete =  Just $ Right $ PIdx a Nothing
         treatA _ Keep = Nothing
         plug = filterDiff plugM
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


reduceOptional :: Show a => Editor (PathFTB a) -> Editor (PathFTB a)
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

buildUIDiff 
  :: (Compact (Index b),Eq (Index b),Show (Index b),Show k ,Ord b ,Patch b, Show b) 
  => AtomicUI k b 
  -> (b -> Bool) 
  -> KType k 
  -> PluginRef (FTB b) 
  -> Tidings (Maybe (FTB b)) 
  -> UI (LayoutWidget (Editor (PathFTB (Index b) )))
buildUIDiff f check (Primitive l prim) = go l
  where
    go [] plug tdi = fmap (fmap PAtom) <$> f (fmap (fmap (fmap unAtom)) <$>plug) (fmap unTB1 <$> tdi) prim
    go (i:ti) plug tdi = case i of
         KArray -> mdo
            clearEl <- flabel # set text "clear" # set UI.class_ "label label-default pull-right col-xs-2"
            clearEv <- UI.click clearEl
            ini <- currentValue (facts tdi)
            offsetDiv  <- UI.div
            -- let wheel = fmap negate $ mousewheel offsetDiv
            TrivialWidget offsetT offset <- offsetField (pure 0)  never (facts size)
            let arraySize = 8
                tdi2  = fmap unArray <$> tdi
                index o ix v = flip NonS.atMay (o + ix) <$> v
                unIndexEl ix = fmap join$ index ix <$> offsetT <*> tdi2
                unplugix ix = fmap ((\o -> ((maybe Keep Diff . indexPatchSet (o + ix) )=<<)) <$> offsetT <*>) <$> plug
                first = (\ i j o ->  if o > 0 then  maybe False (isJust  . filterTB1 check) $ (join $ applyIfChange i j <|> createIfChange j  <|> Just i) else True) <$> unIndexEl (-1) <*> compactPlugins' (unplugix (-1)) <*> offsetT
                dyn = dynHandlerPatch  (\ix valix plix ->do
                  wid <- go ti  plix valix
                  let
                    dynShow = do
                      ldelta <- UI.div
                        # sink text  (show <$> facts (triding wid))
                      UI.div # set children [ldelta]
                  lb <- detailsLabel (sink UI.text (show . (+ix) <$> facts offsetT ) . (>>= paintEditDiff valix (triding wid))) dynShow
                  element lb # set UI.style [("width", "5%")]
                  element wid # set UI.style [("width", "95%")]
                  row <- UI.div # set children [lb,getElement wid] # set UI.class_ "col-xs-12"
                    # set UI.style [("display", "inline-flex")]
                  return $ LayoutWidget (triding wid) row (getLayout wid) ) unIndexEl unplugix (isJust  . filterTB1 check )

            element offset # set UI.class_ "label label-default pull-right col-xs-2"
            widgets <- fst <$> foldl' (\i j -> dyn j =<< i ) (return ([],first)) [0..arraySize -1 ]
            let
              widgets2 = Tra.sequenceA (zipWith (\i j -> (i,) <$> j) [0..] ( triding <$> widgets))
              -- [Note] Array diff must be applied in the right order
              --  additions and edits first in ascending order than deletion in descending order
              --  this way the patch index is always preserved
            let bres = (\i k j-> reduceDiffList  arraySize  i j k) <$>facts offsetT <#>   (foldr (liftA2 (:)) (pure [])  ( snd <$>plug)) <*> widgets2
            pini <- currentValue (facts bres)
            element offsetDiv # set children (fmap getElement widgets)
            size <- ui .calmT $  maybe 0 ((+ negate 1).NonS.length .unArray)  . join. fmap (filterTB1 check). join  <$> (applyIfChange <$> tdi <*> bres)
            composed <- UI.span # set children [offset ,clearEl, offsetDiv]
            return  $ LayoutWidget bres composed (F.foldl1 verticalL  <$> (sequenceA $ getLayout <$> widgets))
         KOptional -> do
           let pretdi = join . fmap unSOptional <$> tdi
               plugtdi = fmap (fmap (join . fmap (maybe Delete Diff .unPOpt) ))<$> plug
           tdnew <- go ti  plugtdi pretdi
           -- Delete equals create
           return  (reduceOptional <$> tdnew)
         KSerial -> do
           let pretdi = join . fmap unSOptional <$> tdi
               plugtdi = fmap (fmap (join . fmap (maybe Delete Diff . unPOpt) )) <$> plug
           tdnew <- go ti  plugtdi pretdi
           -- Delete equals create
           return $ LayoutWidget ((\i j -> maybe (head . compact $ [ Diff $ POpt Nothing ,i]) (const i ) j ) <$> (reduceOptional <$> triding tdnew)<*>  tdi ) (getElement tdnew) (getLayout tdnew)
           -- return $ (reduceOptional <$> tdnew)
         KInterval -> do
            let unInterval f (IntervalTB1 i ) = f i
                unInterval _ i = error (show i)
                unfinp (Interval.Finite i) = Just i
                unfinp i = Nothing
                plugtdi i  (PatchSet l ) = PatchSet . Non.fromList <$> nonEmpty ( catMaybes $ Non.toList $ fmap (plugtdi i) l)
                plugtdi i (PInter j l)
                  | i == j  =  unfinp $ fst l
                  | otherwise = Nothing
                plugtdi i j = error (show (i,j))
            composed <-  UI.div
            subcomposed <- UI.div # set UI.children [composed]
            inf <- go ti (fmap ( fmap (join . fmap (maybe Keep Diff .plugtdi True))) <$> plug) (join.fmap (unInterval inf' ) <$> tdi)
            lbd <- checkedWidget (maybe False (unInterval (snd . Interval.lowerBound') ) <$> tdi)

            sup <- go ti (fmap (fmap (join . fmap (maybe Keep Diff . plugtdi False ) ))<$> plug) (join.fmap (unInterval sup')  <$> tdi)
            ubd <- checkedWidget (maybe False (unInterval (snd . Interval.upperBound' ) ) <$> tdi)
            element composed # set UI.style [("display","inline-flex")] # set UI.children [getElement lbd ,getElement  inf,getElement sup,getElement ubd]
            let
              replaceL  Delete   h= Diff $ PInter True (Interval.NegInf,h)
              replaceL   i h =  fmap (PInter True  . (,h). Interval.Finite) i
              replaceU  Delete   h = Diff $ PInter False (Interval.PosInf,h)
              replaceU  i  h =  fmap (PInter False . (,h).Interval.Finite) i
            output <-  ui $ calmT $ (\i j -> reduceDiff [i,j])<$> (replaceL <$>  triding inf <*> triding lbd ) <*> (replaceU <$> triding sup <*> triding ubd)
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
  let tdi = F.foldl' (liftA2 apply) tdi2  (fmap snd plug)
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
             3-> fmap (fmap (\(i,j,k) -> Position i j k )) <$> primEditor (fmap (\(Position i j k ) -> (i,j,k) ) <$> tdip)
             2-> fmap (fmap (\(i,j) -> Position2D i j ))  <$> primEditor (fmap (\(Position2D i j ) -> (i,j) ) <$> tdip)
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
       inp <- oneInput fm i tdi
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
         PDayTime -> oneInput fm i tdi
         PInterval ->oneInput fm i tdi
     PAddress -> do
       let binarySrc = (\(SText i) -> "https://drive.google.com/embeddedfolderview?id=" <> T.unpack i <> "#grid")
       i <- UI.input  # sink UI.value ( maybe "" (\(SText t) -> T.unpack t) <$> facts tdi)
       vci <- UI.valueChange i
       let tdie = unionWith const (Just . SText . T.pack <$> vci ) (rumors tdi)
       vi <- currentValue (facts tdi)
       tdi2 <- ui $ stepperT vi tdie
       let fty = ("iframe",UI.strAttr "src",maybe "" binarySrc ,[("width","100%"),("max-height","300px")])

       f <- pdfFrame fty (facts tdi2) # sink UI.style (noneShow . isJust <$> facts tdi2)
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
           f <- fty (facts tdi2 ) # sink UI.style (noneShow. isJust <$> facts tdi2)
           fd <- UI.div # set UI.style [("display","inline-flex")] # set children [file,clearB]
           res <- UI.div # set children [fd,f]
           valChange <- UI.valueChange f
           tdi3 <- ui $ addEvent  (readPrim  i <$> valChange) tdi2
           return (TrivialWidget tdi3 res)
     PColor -> do
        let f = facts tdi
        v <- currentValue f
        inputUI <- UI.input # set UI.class_ "jscolor" # sink UI.value (maybe "FFFFFF" renderPrim <$> f)# set UI.style [("width","100%")]
        onCE <- UI.onChangeE inputUI
        let pke = unionWith const (readPrim i <$> onCE) (rumors tdi)
        pkt <- ui $ stepperT v  pke
        sp <- UI.div # set UI.children [inputUI ]
        runFunctionDelayed inputUI  $ ffi "new jscolor(%1)" inputUI
        onChanges f (runFunctionDelayed inputUI . ffi "updateColor(%1,%2)" inputUI . maybe "FFFFFF" renderPrim)
        return $ TrivialWidget pkt sp
     z ->
       oneInput fm z tdi


oneInput :: [FieldModifier] -> KPrim -> Tidings (Maybe Showable) ->   UI (TrivialWidget (Maybe Showable))
oneInput fm i tdi = do
    v <- currentValue (facts tdi)
    inputUI <- UI.input # sink UI.value (maybe "" renderPrim <$> facts tdi) # set UI.style [("min-width","30px"),("max-width","250px"),("width","100%")]
    if fm == [FRead] then do
      element inputUI # set UI.enabled False
      return $ TrivialWidget tdi inputUI
    else do
      onCE <- UI.onChangeE inputUI
      let pke = unionWith const  (decode <$> onCE) (Right <$> rumors tdi)
          decode v = maybe (if v == "" then Right Nothing else Left v) (Right . Just) .  readPrim i $ v


      pkt <- ui $ stepperT (Right v) pke
      element inputUI # sink UI.style ((\i -> [("border", either (const "solid red 1.5px") (const "") i)]) <$> facts pkt)
      cpkt <- ui $ calmDiff (either (const Nothing) id <$> pkt)
      return $ TrivialWidget  cpkt inputUI


inlineTableUI
  :: InformationSchemaKV Key Showable
  -> SelTBConstraint
  -> PluginRef (TBData CoreKey Showable)
  -> Tidings (Maybe (TBData CoreKey Showable))
  -> Prim KPrim (Text, Text)
  -> UI (LayoutWidget (Editor (TBIdx CoreKey Showable)))
inlineTableUI inf constr pmods oldItems (RecordPrim na) = do
    let
      tablefields = allFields inf table
      convertConstr (pk,j) 
        = (\rel  -> (relUnComp rel , C.contramap (\v -> kvlist (fmap addDefault' (L.delete (lkTB (relCurrent rel) ) attrs) ++ v)) <$> j )) 
         . unRelAccess <$> pk
        where 
          lkTB i = justError (show (i,i,tablefields)) $ kvLookup i tablefields 
          attrs = unkvlist tablefields
          unRelAccess (RelAccess _ i) = i
      table = lookTable rinf (snd na)
      relCurrent (RelAccess i _  ) = i
      relCurrent i = i
      rinf = fromMaybe inf (HM.lookup (fst na) (depschema inf))
      newConstraints = concat $ convertConstr <$> constr
    -- liftIO $ print ("Constraints",na,fst <$> constr, fst <$> newConstraints)
    eiTableDiff rinf table  newConstraints M.empty pmods tablefields oldItems
  

iUITableDiff
  :: InformationSchema
  -- Plugin Modifications
  -> SelTBConstraint
  -> PluginRef (Column CoreKey Showable)
  -- Selected Item
  -> Tidings (Maybe (Column CoreKey Showable))
  -- Static Information about relation
  -> TBMeta Key
  -> UI (LayoutWidget (Editor (PathAttr CoreKey Showable)))
iUITableDiff inf constr pmods oldItems  (IT na  tb1)
  = fmap (fmap (PInline na)) <$> buildUIDiff (inlineTableUI inf constr) (const True) (keyType na) (fmap (fmap (fmap patchfkt)) <$> pmods) (fmap _fkttable <$> oldItems)

buildPredicate rel o = WherePredicate . AndColl . catMaybes $ prim <$> o
    where
      prim (Attr k v) =  buildPrim <$> unSOptional v <*> L.find ((==k) . _relOrigin) rel
      buildPrim o rel = PrimColl (_relTarget rel,[(_relTarget rel,Left  (o,Flip $ _relOperator rel))])


fkUITablePrim ::
  InformationSchema
  -- Plugin Modifications
  -> ([Rel Key],Table)
  -> SelTBConstraint
  -- Same Table References
  -> ColumnTidings
  -> PluginRef  (TBRef Key Showable)
  -- Relation Event
  -> Tidings (Maybe (TBRef CoreKey Showable))
  -- Static Information about relation
  -> [CorePrim]
  -> UI (LayoutWidget (Editor (PTBRef Key Showable)))
fkUITablePrim inf (rel,targetTable) constr nonInjRefs plmods  oldItems  prim = do
      -- Top Level Widget
      top <- UI.div
      (eSelector,hSelector) <- ui newEvent
      selectT <- ui $ calmT =<< stepperT False  eSelector
      let
        fields = allFields inf targetTable
        reflectRels = filter (isJust. _relOutputs) rel
        matchReflect k = isJust $ L.find (\(Rel i _ _ )-> i == k) reflectRels
        filterReflect :: TBIdx Key Showable -> TBIdx Key Showable 
        filterReflect m = M.filterWithKey  (\k i -> matchReflect k ) m
        filterNotReflect m = kvFilter (not . matchReflect) m
        filterReflectKV m = kvFilter (matchReflect) m
        nonEmptyTBRef v@(TBRef n) = if  snd n  == mempty then Nothing else Just v
        ftdi = F.foldl' (liftA2 apply)  oldItems (snd <$> plmods)
        inipl =  compactPlugins oldItems plmods
      inip <- currentValue (facts inipl)

      (elsel, helsel) <- ui newEvent
      (elselTarget, helselTarget) <- ui newEvent
      (eleditu, heleditu) <- ui newEvent

      let
        evsel = unionWith const elsel (fmap sourcePRef <$> rumors inipl)
        evseltarget = unionWith const elselTarget (fmap targetPRef <$> rumors inipl)
        evtarget = unionWith const eleditu (fmap targetPRefEdit <$> rumors inipl)

      tsource <- ui $ stepperT (sourcePRef <$> inip) evsel
      tseltarget <- ui $ stepperT (targetPRef <$> inip) evseltarget
      ttarget <- ui $ stepperT (targetPRefEdit <$> inip) evtarget

      (elayout, hlayout) <- ui newEvent
      layoutT <- ui $ stepperT (6,1) elayout

      nav <- openClose (pure False) 
      let
        merge :: Editor (TBIdx CoreKey Showable ) -> Editor (TBIdx CoreKey Showable) -> Editor (TBIdx CoreKey Showable) -> Editor (PTBRef CoreKey Showable)
        -- merge i j k | traceShow (i,j ,k ) False = undefined
        merge (Diff i) (Diff j) (Diff k) = if M.null (filterReflect i) && M.null j then Keep else Diff (PTBRef (filterReflect i) j k)
        merge (Diff i) (Diff j) Keep = if M.null (filterReflect i) && M.null j then Keep else Diff (PTBRef (filterReflect i) j mempty)
        merge Keep (Diff i) Keep = Diff $ PTBRef mempty i mempty
        merge _ Keep (Diff i) = Diff $ PTBRef mempty mempty i
        merge Keep  (Diff i) (Diff j) = Diff $ PTBRef mempty  i j
        merge _ Keep Keep = Keep
        merge _ Delete _ = Delete
        merge Delete _ _ = Delete
        merge _ _ Delete = Delete

        tdfk = merge <$> tsource <*> tseltarget <*> ttarget
        refs :: Tidings (Maybe [TB Key Showable])
        refs =  fmap (unkvlist . filterNotReflect . fst . unTBRef) <$> ftdi
        predicate = fmap (buildPredicate rel) <$> refs
        matches  rel tb = case tb of
           Just (TBRef (s,t)) ->  kvSize s == L.length rel && kvSize t > 0
           Nothing -> False
        selector False = do
          ui $ onEventDyn
            (rumors $ (,,) <$> facts tsource <#> oldItems <*> inipl)
            (\(oldsel,initial,tbdiff) -> do
              let newdiff = fmap sourcePRef tbdiff
                  newtbsel = join $ applyIfChange initial tbdiff
                  newsel = join $ applyIfChange (fst .unTBRef <$> initial) (sourcePRef <$> tbdiff)
              when (oldsel /= newdiff) $ do
                when (maybe False ((L.length rel ==) .kvSize) newsel ) .void$
                  do
                    let
                      pred = buildPredicate rel . unkvlist <$> newsel
                    reftb@(_,gist,_) <- refTablesDesc inf targetTable Nothing (fromMaybe mempty pred)
                    flip mapTidingsDyn gist $ \(TableRep (_,s,g)) -> do
                      let out = searchGist rel targetTable  g s =<< newsel
                      when (isJust newsel && isJust out || isNothing newsel) $ 
                        liftIO $ void $ do
                          traverse  helselTarget  (diff (snd .unTBRef<$> initial) out)
                return ())
          pan <- UI.div
            # set UI.class_ "col-xs-11 fixed-label"
            # set UI.style [("border","1px solid gray"),("border-radius","4px"),("height","26px")]
            # sink text (facts $ (\i  -> maybe "" (L.take 50 . L.intercalate "," . fmap renderShowable . allKVRec' inf (tableMeta targetTable). snd .unTBRef)  i) <$>  ((\i j ->  (join $ applyIfChange i j) <|> (join $ createIfChange j) )<$>  facts oldItems <#>  tdfk))
          panClick <- UI.click pan
          ui $ onEventIO panClick (\ _ -> hSelector True)
          (nav,celem,layout) <- edit
          onChanges (facts  layout) (liftIO . hlayout)
          element nav
            # set UI.class_ "col-xs-1"
          return $ [nav,pan] ++ celem
        selector True = do
          pred <- ui $ currentValue (facts predicate)
          reftb@(_,gist,_) <- ui $ refTablesDesc inf targetTable Nothing (fromMaybe mempty pred)
          let newSel = fmap join $ applyIfChange <$> (fmap (fst .unTBRef) <$> facts oldItems) <#> (fmap sourcePRef <$> inipl)
          let  tdi = ((\(TableRep (_,s,g)) v -> searchGist rel targetTable g s =<<  v) <$> gist  <*> newSel)
          cliZone <- jsTimeZone
          metaMap <- mapWidgetMeta inf
          metaAgenda <- eventWidgetMeta inf
          let
            replaceTarget = (\i j ->  let delta = diff i j 
                               in if isNothing delta then Keep else 
                                  (if  isKeep (fromJust delta ) then Keep else patch j))
            hasMap = L.find ((== targetTable).(Le.^._2)) metaMap
            hasAgenda = L.find ((== targetTable).(Le.^._2)) metaAgenda
            add i m =  if i then (m:) else id
            availableModes = add (isJust hasAgenda) "Agenda" $ add (isJust hasMap) "Map" ["List"]
          navMeta  <- buttonDivSet  availableModes (pure $ Just "List") (\i -> UI.button # set UI.text i # set UI.style [("font-size","unset")] # set UI.class_ "buttonSet btn-xs btn-default btn pull-left")
          let navSize =  "col-xs-" ++ (show $ length availableModes - 1)
              selSize =  "col-xs-" ++ (show $ 12 - (length availableModes - 1))
          itemList <- do
              lboxeel <- switchManyLayout
                (triding navMeta)
                (M.fromList
                  [("List" , do
                    itemListEl <- UI.select # set UI.class_ "fixed-label" # set UI.size "21" # set UI.style [("width","100%"),("position","absolute"),("z-index","999"),("left","0px"),("top","22px")]
                    (lbox , l) <- selectListUI inf targetTable itemListEl (pure mempty) reftb constr (recPKDesc inf (tableMeta targetTable) fields) tdi
                    element l # set UI.class_ selSize
                    return (LayoutWidget lbox l (pure (6,1)))),
                  ("Map" ,do
                    let selection = conv $ fromJust hasMap
                        conv (i ,t, j ,l) = (i,t,j ,l)
                    t <- liftIO getCurrentTime
                    TrivialWidget i el <- mapSelector inf (pure mempty ) selection (pure (t,"month")) tdi (never, pure Nothing)
                    element el # set UI.class_ selSize
                    return (LayoutWidget i el (pure (12,1)))),
                  ("Agenda" ,do
                    let selection = conv $ fromJust hasAgenda
                        conv (i ,j ,k,l) = (i,j , k ,l)
                    (sel ,(j,i)) <- calendarSelector
                    el <- traverseUI (\(delta ,time) -> do
                      (e,l) <- calendarView inf mempty cliZone [selection] (pure (S.singleton targetTable )) Basic delta time
                      c <- UI.div # set children e
                      return (TrivialWidget (fmap snd <$> l) c)) $ (,) <$> i <*> j
                    el2 <- UI.div  # sink children (pure . getElement <$> facts el)
                    tsource <- ui $ joinT (triding <$> el)
                    (\i -> LayoutWidget tsource i (pure (12,1))) <$> UI.div # set children [sel,el2] # set UI.class_ selSize)])

              onChanges (facts  (getLayout lboxeel)) (liftIO . hlayout)
              element navMeta # set UI.class_ navSize
              elout <- UI.div # set children [getElement navMeta ,getElement lboxeel]
              esc <- onEsc elout
              loaded <- ui $ loadItems inf targetTable fields (triding lboxeel)
              ui $ onEventIO esc (\ _ ->hSelector False)
              return (TrivialWidget  loaded elout)

          let
            fksel =  fmap TBRef . (\box -> (,) <$>  (reflectFK reflectRels  =<< box ) <*> box ) <$> triding itemList
            output =  replaceTarget <$> facts oldItems <#> fksel
          ui $ onEventIO (rumors output)
            (\i -> do
              when (not (L.null reflectRels)) $ do
                helsel (filterReflect.sourcePRef <$> i)
              helselTarget $ fmap targetPRef i)
          return [getElement itemList]

        edit =  do
          tdi <- ui . calmT $ fmap join $ applyIfChange <$> (fmap (snd.unTBRef) <$>oldItems) <*> tseltarget
          let
            replaceKey :: TB CoreKey a -> TB CoreKey a
            replaceKey = firstTB swapKey
            swapKey k = maybe k (_relOrigin . _relTarget) (L.find ((==k)._relOrigin) rel)
            replaceKeyP :: PathAttr CoreKey Showable  -> PathAttr CoreKey Showable
            replaceKeyP = firstPatchAttr swapKey

            staticold :: ColumnTidings
            staticold = fmap (\(i,j) -> (patch <$>  liftA2 apply  (projectValue j) (projectEdit i),pure Nothing)) . M.mapKeys (fmap swapKey) $ M.filterWithKey (\k _ -> all (\i ->  not (isInlineRel i ) &&  (_relOperator i == Equals)) (relUnComp k)) nonInjRefs
            projectEdit = fmap (fmap replaceKeyP . join . fmap (maybe Keep Diff . unLeftItensP ))
            projectValue = fmap (fmap replaceKey .join . fmap unLeftItens)

          LayoutWidget pretdi celem layout <- dynCrudUITable inf (triding nav) staticold ((fmap (fmap (fmap targetPRef)) <$> plmods)) targetTable tdi
          let
            serialRef = if L.any isSerial (relType <$> rawPK targetTable) then Just (kvlist []) else Nothing
          ui $ onEventIO ((,,,,) <$> facts tsource <*> facts oldItems <*> facts tdi <*> facts ttarget <@> rumors pretdi)
            (\(old,init,selt,olde,i) -> do
            -- Only reflect when
            -- 1. previous target is empty
            -- 2. has something to reflect
            -- 3. new diff is different than current
            let new = (reflectFK reflectRels =<< join (applyIfChange selt i)) <|> serialRef
                s = diff' (fst . unTBRef<$> init) new
            when (isNothing selt && fmap filterReflect old /= fmap filterReflect s && not (L.null reflectRels)) $ {-debugTime "reflectSel" $ -} do
              helsel $ fmap (filterReflect) s
            when (olde /= i) $ {-debugTime ("edit"  <> show (G.getIndex (tableMeta targetTable ) <$> (join (applyIfChange selt i))))$-} do
              heleditu  i)
          return (getElement nav,[celem],max (6,1) <$> layout)

      selEls <- traverseUI selector selectT
      element top
        # sink children (facts selEls)
      -- let lintReflect = (>>= (\(TBRef (i,j)) -> nonEmptyTBRef $ TBRef (filterReflectKV i,j )))
          {-checkOutput i j | traceShow ("checkOutput",i,j ,applyIfChange i j ) False = undefined
          checkOutput old tdfk =
            let oldn =  lintReflect old
            in diff' oldn (lintReflect (join $ applyIfChange  oldn  tdfk)) -}
      out <- ui $ calmT  tdfk
      return $ LayoutWidget  out top layoutT

traceShowIdPrefix s i = traceShow (s,show i) i

fkUITableGen 
  :: InformationSchema
  -> Table
  -> SelTBConstraint
  -> PluginRef  (Column CoreKey Showable)
  -- Same Table References
  -> ColumnTidings
  -- Relation Event
  -> Tidings (Maybe (Column CoreKey Showable))
  -- Static Information about relation
  -> TBMeta Key
  -> UI (LayoutWidget (Editor (PathAttr CoreKey Showable)))
fkUITableGen preinf table constr plmods nonInjRefs oldItems tb@(FKT ifk rel fkref)
  = fmap (join. fmap (maybe Keep Diff . recoverPFK setattr rel )) <$> buildUIDiff 
      (fkUITablePrim inf (liftRelation <$> rel,lookTable inf target) constr nonInjRefs)
      (\((TBRef (i,j))) ->  not $ kvNull j)
      (mergeFKRef  $ keyType . _relOrigin <$>rel)
      (fmap (fmap (fmap liftPFK)) <$> (plmods <> concat replaceNonInj))
      (join .fmap liftFKM<$> foldl' (liftA2 mergeOrCreate) oldItems (snd <$> F.toList nonInjRefs ))
  where
    liftRelation (Rel k (AnyOp i) t) = Rel k i t
    liftRelation o = o
    replaceNonInj = (\(i,j) -> 
      (\v -> (Many [(IProd Nothing (_relOrigin v))],) $ 
        join . fmap ( maybe Keep (\m -> Diff $ PFK rel (kvsingleton m) (patchChange m )).L.find ((== S.singleton (_relOrigin v)) .  relOutputSet . index) .  unkvlistp .  nonRefPatch) <$> fst j )<$> relUnComp i ) <$> M.toList nonInjRefs
      where patchChange (PAttr i k ) = fmap (const mempty) k
    mergeOrCreate (Just i) j = (mergeRef i <$> j) <|> Just i
    mergeOrCreate Nothing j =  mergeRef emptyFKT <$> j
    def KArray  = ArrayTB1 . pure 
    def KOptional = LeftTB1 .Just 
    defKType (Primitive l i ) = foldr (.) TB1 (def <$> l ) $ i
    emptyFKT = FKT  mempty rel (const mempty <$> defKType fkref)
    mergeRef (FKT r rel v) i = FKT (foldl' addAttrO r (nonRefTB i)) rel v
    addAttrO  i v = if isNothing (unSOptional (_tbattr v)) then i else  (addAttr v i)
    (targetSchema,target) = findRefTableKey table rel
    inf = fromMaybe preinf $ HM.lookup targetSchema (depschema preinf)
    setattr = keyAttr <$> unkvlist ifk


reduceTable :: [Editor a] -> Editor [a]
reduceTable l
  | L.any isDelete l = Delete
  | otherwise  = (\i -> if L.null i then Keep else Diff i) . filterDiff $ l

pdfFrame (elem,sr , call,st) pdf = mkElement elem UI.# sink sr (call <$> pdf)  UI.# UI.set style st

metaTable
  :: InformationSchemaKV Key Showable
  -> Text
  -> [(Rel Text, AccessOp Showable)]
  -> UI Element
metaTable inf metaname env =   do
  let modtable = lookTable (meta inf) metaname
  displayTable (meta inf) modtable (fixrel .Le.over _1 (liftRel (meta inf) metaname) <$> env)


displayTable :: InformationSchema -> Table -> [(Rel Key ,[(Rel Key,AccessOp Showable)] )] -> UI Element
displayTable inf table envK = do
  let
    pred = WherePredicate $ AndColl $ PrimColl <$> envK
  reftb@(_,vpt,_) <- ui $ refTables' inf   table Nothing  pred
  tb <- UI.div
  (res,offset) <- paginateList inf table tb (pure $ Just pred) reftb  [] (allFields inf table) (pure Nothing)
  TrivialWidget pretdi cru <- batchUITable inf table reftb M.empty [] (allFields inf table) res
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

instance ToJS Showable where
  render = UI.render . A.toJSON 
instance FromJS Showable where

instance (A.ToJSON a) => ToJS (FTB a ) where
  render = UI.render . A.toJSON 

instance FromJS a => FromJS (FTB a ) where

instance (A.ToJSON a) => ToJS (PathFTB a ) where
  render = UI.render . A.toJSON 

instance FromJS a => FromJS (PathFTB a ) where

testPStream = do 
  (e,h) <- ui newEvent 
  s <- ui $ accumS [] e 
  a <- UI.button  # set text "Add"
  d <- UI.button  # set text "Delete"
  aClick <- (UI.click a )
  dClick <- (UI.click d )
  onEvent aClick $  
    ( \_ -> void $ do 
      e <- UI.div # set text "etewg"
      liftIO $ h ([(0,e)],[]))
  ui $ onEventIO ( psvalue s <@ dClick) $  ( \v ->  do
    void $ liftIO $ h ([] ,[(0, v !! 0)]))
  e <- UI.div # sinkDelta children  s
  UI.div # set children [a,d,e]



