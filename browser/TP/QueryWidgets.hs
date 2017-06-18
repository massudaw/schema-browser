{-# LANGUAGE
    FlexibleInstances
   ,BangPatterns
   ,OverloadedStrings
   ,ScopedTypeVariables
   ,FlexibleContexts
   ,ExistentialQuantification
   ,TupleSections
   ,LambdaCase
   ,RankNTypes
   ,RecordWildCards
   ,DeriveFunctor
   ,NoMonomorphismRestriction
   ,RecursiveDo
 #-}

module TP.QueryWidgets (
    crudUITable,
    refTables,
    refTables',
    offsetField,
    offsetFieldFiltered,
    sorting',
    lookAttr',
    lookAttrs',
    lookAttrM,
    tableIndexA,
    idex,
    metaAllTableIndexA ,
    attrLine,
    viewer,
    ) where

import RuntimeTypes
import TP.View
import Data.Functor.Constant
import Data.Dynamic (fromDynamic)
import Expression
import Control.Monad.Catch
import Data.Tuple
import Data.Semigroup hiding (diff)
import qualified NonEmpty as Non
import NonEmpty (NonEmpty(..))
import Data.Bifunctor
import Text
import SortList
import Data.Functor.Identity
import Control.Monad.Writer hiding((<>))
import TP.MapSelector
import Control.Applicative.Lift
import SchemaQuery
import qualified Data.Binary as B
import qualified Data.Poset as P
import qualified Data.GiST.GiST as G
import Reactive.Threepenny hiding (apply)
import Data.Either
import qualified Graphics.UI.Threepenny as UI
import Graphics.UI.Threepenny.Core hiding (apply,delete)
import Graphics.UI.Threepenny.Internal (ui)
import Data.String
import Data.Ord
import Control.Lens (_1,_2,over,(^?),(&),(%~))
import qualified Control.Lens as Le
import Utils
import Data.Char
import qualified Data.Map as M
import qualified Data.HashMap.Strict as HM
import Data.Map (Map)
import qualified Data.Set as S
import Data.Set (Set)
import qualified Data.Traversable as Tra
import qualified Data.ByteString.Base64 as B64
import Data.Interval (interval)
import qualified Data.ExtendedReal as ER
import qualified Data.Interval as Interval
import qualified Data.List as L
import Text.Read (readMaybe)
import Data.Text (Text)
import Types
import Types.Patch
import qualified Types.Index as G
import Query
import Data.Maybe
import Prelude hiding (head)
import Data.Time
import Data.Functor.Apply
import TP.Widgets
import Schema
import Step.Host
import qualified Data.Foldable as F
import Data.Foldable (foldl')
import Debug.Trace
import Control.Concurrent.STM.TChan
import qualified Data.Text as T
import qualified Data.ByteString.Char8 as BSC
import qualified Data.ByteString.Lazy.Char8 as BSL
import GHC.Stack

type PKConstraint = [Column CoreKey Showable] -> Bool

type TBConstraint = TBData CoreKey Showable -> Bool

type SelPKConstraint = [([Column CoreKey ()],Tidings PKConstraint)]

type SelTBConstraint = [([Column CoreKey ()],Tidings TBConstraint)]

type RefTables = (Tidings (IndexMetadata CoreKey Showable),(Collection CoreKey Showable), Tidings (G.GiST (G.TBIndex  Showable) (TBData CoreKey Showable)),Tidings [SecondaryIndex CoreKey Showable ], TChan [RowPatch KeyUnique Showable] )

--- Plugins Interface Methods
createFresh :: Text -> InformationSchema -> Text -> KType CorePrim -> IO InformationSchema
createFresh  tname inf i ty@(Primitive atom)  =
  case atom of
    AtomicPrim _  -> do
      k <- newKey i ty 0
      return $ inf
          & keyMapL %~ (HM.insert (tname,i) k )
    RecordPrim (s,t) -> do
      k <- newKey i ty 0
      let tableO = lookTable inf tname
          path = Path (S.singleton k) (FKInlineTable $ inlineName ty )
      return $ inf
          & tableMapL . Le.ix tname . rawFKSL %~  S.insert path
          & pkMapL . Le.ix (S.fromList $ rawPK tableO) . rawFKSL Le.%~  S.insert path
          & keyMapL %~ HM.insert (tname,i) k


genAttr :: InformationSchema -> CoreKey -> Column CoreKey ()
genAttr inf k =
  case keyType k of
    Primitive p ->
      case p of
        AtomicPrim l -> Attr k (TB1 ())
        RecordPrim (l,t) ->
          let table =  lookTable inf  t
          in IT k $ TB1 $  unTlabel' $ tableView (tableMap inf) table

pluginUI
    :: InformationSchema
    -> Tidings (Maybe (TBData CoreKey Showable) )
    -> Plugins
    -> UI (Element ,([Access Key],Tidings (Maybe (Index (TBData CoreKey Showable)))))
pluginUI oinf trinp (idp,FPlugins n tname (StatefullPlugin ac)) = do
  let
    fresh :: [([VarDef],[VarDef])]
    fresh = fmap fst ac
  b <- flabel # set UI.text (T.unpack n)
  inf <- liftIO $  foldl' (\i (kn,kty) -> (\m -> createFresh  tname m kn kty) =<< i ) (return  oinf) (concat $ fmap fst fresh <> fmap snd fresh )
  let
      freshKeys :: [([CoreKey],[CoreKey])]
      freshKeys = first (fmap lookK ) . second (fmap lookK) <$> fresh
      lookK = lookKey inf tname . fst
  freshUI <- foldl' (\old (aci ,(inpfresh,outfresh)) -> (old >>= (\(l,unoldItems)-> do
      elemsIn <- mapM (\fresh -> do
        let attrB pre a = do
              wn <-  tbCaseDiff  inf  mempty a mempty  mempty pre
              v <- labelCaseDiff inf False a  wn
              out <- UI.div # set children [getElement v,getElement wn]
              return  $ TrivialWidget (recoverEditChange <$> facts pre <#> triding v) out

        attrB (const Nothing <$> unoldItems)  (genAttr oinf fresh )
           ) inpfresh
      let
        inp :: Tidings (Maybe (TBData CoreKey Showable))
        inp = fmap tblist <$> foldr (liftA2 (liftA2 (:))) (pure (Just [])) (fmap (fmap ( fmap _tb) .  triding) elemsIn )

      (preinp,(_,liftedE )) <- pluginUI  inf (liftA2 mergeTB1 <$>  facts unoldItems <#>  inp) (idp,FPlugins "Enviar" tname aci)

      elemsOut <- mapM (\fresh -> do
        let attrB pre a = do
              wn <-  tbCaseDiff inf  []  a [] [] pre
              TrivialWidget v e <- labelCaseDiff inf False a  wn
              out <- UI.div # set children [getElement e,getElement wn]
              return $ TrivialWidget (recoverEditChange <$> pre <*> v ) out
        attrB (fmap (\v ->  unTB . justError ("no key " <> show fresh <> " in " <>  show v ) . fmap snd . getCompose . unTB . findTB1 ((== [fresh]) . fmap _relOrigin. keyattr ) $ TB1 (create v :: TBData Key Showable) )  <$> liftedE  )  (genAttr oinf fresh )
       ) outfresh

      let styleUI =  set UI.class_ "row"
            . set UI.style [("border","1px"),("border-color","gray"),("border-style","solid"),("margin","1px")]
      j<- UI.div # styleUI  # set children (fmap getElement elemsIn <> [preinp])# sink UI.style (noneShow .isJust <$> facts unoldItems)
      k <- UI.div # styleUI  # set children (fmap getElement elemsOut) # sink UI.style (noneShow .isJust <$> facts liftedE  )
      return  ( l <> [j , k] , (\i j ->  liftA2 apply i j  <|> i <|> fmap create j) <$> facts unoldItems <#>  liftedE  ))
           ) ) (return (([],trinp))) $ zip (fmap snd ac) freshKeys
  el <- UI.div  # set children (b: (fst freshUI))
  let evdiff = fmap join $ liftA2 diff <$>  facts trinp <#> snd freshUI
  return (el , (liftAccessU inf tname  $snd $ pluginStatic' $ snd $ last ac , evdiff ))

pluginUI inf oldItems (idp,p@(FPlugins n t (PurePlugin arrow ))) = do
  let f =second (liftAccessU inf t ). first (liftAccessU  inf t ) $ staticP arrow
      action = pluginAction   p
      pred =  WherePredicate $ AndColl (catMaybes [ genPredicateFullU True (fst f)])
      tdInputPre = join . fmap (\i -> if G.checkPred i pred  then Just i else Nothing) <$>  oldItems
      tdInput = tdInputPre
      table = lookTable inf t
      predOut =  WherePredicate $ AndColl (catMaybes [ genPredicateFullU True (snd f)])
      tdOutput = join . fmap (\i -> if G.checkPred i predOut  then Just i else Nothing) <$> oldItems
  headerP <- UI.button # set UI.class_ "btn btn-sm"# set text (T.unpack n)  # sink UI.enabled (isJust <$> facts tdInput)  # set UI.style [("color","white")] # sink UI.style (liftA2 greenRedBlue  (isJust <$> facts tdInput) (isJust <$> facts tdOutput))
  ini <- currentValue (facts tdInput )
  kk <- ui $ stepper ini (diffEvent (facts tdInput ) (rumors tdInput ))
  pgOut <- ui $mapTEventDyn (\v -> liftIO .fmap ( join .  liftA2 diff v. ( join . fmap (either (const Nothing) Just . typecheck (typeCheckTable (tablePK table)) )) . fmap (liftTable' inf t).  join . eitherToMaybe ). catchPluginException inf (tableUnique table ) idp (M.toList $ getPKM $ justError "ewfew"  v) . action $  fmap (mapKey' keyValue) v)  (tidings kk $diffEvent kk (rumors tdInput ))
  return (headerP, (snd f ,   pgOut ))
pluginUI inf oldItems (idp,p@(FPlugins n t (DiffPurePlugin arrow ))) = do
  let f =second (liftAccessU inf t ). first (liftAccessU  inf t ) $ staticP arrow
      action = pluginActionDiff   p
      pred =  WherePredicate $ AndColl (catMaybes [ genPredicateFullU True (fst f)])
      tdInputPre = join . fmap (\i -> if G.checkPred i pred  then Just i else Nothing) <$>  oldItems
      tdInput = tdInputPre
      predOut =  WherePredicate $ AndColl (catMaybes [ genPredicateFullU True (snd f)])
      tdOutput = join . fmap (\i -> if G.checkPred i predOut  then Just i else Nothing) <$> oldItems
  headerP <- UI.button # set UI.class_ "btn btn-sm"# set text (T.unpack n)  # sink UI.enabled (isJust <$> facts tdInput)  # set UI.style [("color","white")] # sink UI.style (liftA2 greenRedBlue  (isJust <$> facts tdInput) (isJust <$> facts tdOutput))
  ini <- currentValue (facts tdInput )
  kk <- ui $ stepper ini (diffEvent (facts tdInput ) (rumors tdInput ))
  pgOut <- ui $mapTEventDyn (\v -> liftIO .fmap ( fmap (liftPatch inf t).  join . eitherToMaybe ). catchPluginException inf (tableUnique $ lookTable inf t) idp (M.toList $ getPKM $ justError "ewfew"  v) . action $  fmap (mapKey' keyValue) v)  (tidings kk $diffEvent kk (rumors tdInput ))
  return (headerP, (snd f ,   pgOut ))
pluginUI inf oldItems (idp,p@(FPlugins n t (DiffIOPlugin arrow))) = do
  overwrite <- checkedWidget (pure False)
  let f = second (liftAccessU inf t ). first (liftAccessU inf t ) $ staticP arrow
      action = pluginActionDiff p
      pred =  WherePredicate $ AndColl (catMaybes [ genPredicateFullU True (fst f)])
      tdInputPre = join . fmap (\i -> if G.checkPred i pred  then Just i else Nothing) <$>  oldItems
      tdInput = tdInputPre
      predOut =  WherePredicate $ AndColl (catMaybes [ genPredicateFullU True (snd f)])
      tdOutput = join . fmap (\i -> if G.checkPred i predOut  then Just i else Nothing) <$> oldItems
  headerP <- UI.button # set UI.class_ "btn btn-sm"# set text (T.unpack n) # sink UI.enabled (isJust <$> facts tdInput)  #set UI.style [("color","white")] # sink UI.style (liftA2 greenRedBlue  (isJust <$> facts tdInput) (isJust <$> facts tdOutput))
  cliHeader <- UI.click headerP
  let ecv = facts tdInput <@ cliHeader
  vo <- currentValue (facts tdOutput)
  vi <- currentValue (facts tdInput)
  bcv <- ui $ stepper Nothing  ecv
  pgOut  <- ui $mapTEventDyn (\v -> do
    liftIO .fmap ( fmap (liftPatch inf t ). join . eitherToMaybe ) . catchPluginException inf (tableUnique $ lookTable inf t) idp (M.toList $ getPKM $ justError "no Action"  v) $ ( action $ fmap (mapKey' keyValue) v)
                             )  (tidings bcv ecv)
  return (headerP, (snd f ,  pgOut ))

pluginUI inf oldItems (idp,p@(FPlugins n t (BoundedPlugin2 arrow))) = do
  overwrite <- checkedWidget (pure False)
  let f = second (liftAccessU inf t ). first (liftAccessU inf t ) $ staticP arrow
      action = pluginAction p
      pred =  WherePredicate $ AndColl (catMaybes [ genPredicateFullU True (fst f)])
      tdInputPre = join . fmap (\i -> if G.checkPred i pred  then Just i else Nothing) <$>  oldItems
      tdInput = tdInputPre
      predOut =  WherePredicate $ AndColl (catMaybes [ genPredicateFullU True (snd f)])
      tdOutput = join . fmap (\i -> if G.checkPred i predOut  then Just i else Nothing) <$> oldItems
  headerP <- UI.button # set UI.class_ "btn btn-sm"# set text (T.unpack n)  # sink UI.enabled (isJust <$> facts tdInput)  # set UI.style [("color","white")] # sink UI.style (liftA2 greenRedBlue  (isJust <$> facts tdInput) (isJust <$> facts tdOutput))
  cliHeader <- UI.click headerP
  let ecv = facts tdInput <@ cliHeader
  vo <- currentValue (facts tdOutput)
  vi <- currentValue (facts tdInput)
  bcv <- ui $ stepper Nothing ecv
  pgOut  <- ui $mapTEventDyn (\v -> do
    liftIO .fmap (join .  liftA2 diff v .  fmap (liftTable' inf t ). join . eitherToMaybe ) . catchPluginException inf (tableUnique $ lookTable inf t) idp (M.toList $ getPKM $ justError "no Action"  v) . action $ fmap (mapKey' keyValue) v
                             )  (tidings bcv ecv)
  return (headerP, (snd f ,  pgOut ))

indexPluginAttrDiff
  :: Column Key ()
  -> [([Access Key], Tidings (Maybe (Index (TBData Key Showable))))]
  -> [([Access Key], Tidings (Maybe (Index (Column Key Showable))))]
indexPluginAttrDiff a@(Attr i _ )  plugItens =  evs
  where
    match (IProd _ l ) ( IProd _ f) = l == f
    match i ( IProd _ f) = False
    thisPlugs = filter (hasProd (`match` (head $ ( keyRef . _relOrigin <$> keyattri a))) . fst)  plugItens
    evs  = fmap ( fmap ( join . fmap (\(_,_,p) -> L.find (((== S.fromList (keyattri a))  . pattrKey )) p )) ) <$>  thisPlugs
indexPluginAttrDiff  i  plugItens = pfks
  where
    thisPlugs = filter (hasProd (isNested ((fmap (keyRef. _relOrigin) (keyattri i) ))) .  fst) plugItens
    pfks =  first (uNest . justError "No nested Prod FKT" .  findProd (isNested((fmap ( keyRef . _relOrigin ) (keyattri i) )))) . second (fmap (join . fmap ((\(_,_,p) -> L.find (((== S.fromList (keyattri i))  . pattrKey )) p )))) <$> ( thisPlugs)


--- Style and Attribute Size
--
attrSize :: Column CoreKey b -> (Int,Int)
attrSize (FKT  _  _ _ ) = (12,4)
attrSize (IT _ _ ) = (12,4)
attrSize (Attr k _ ) = goAttSize  (keyType k)
attrSize (Fun k _ _ ) = goAttSize  (keyType k)

goAttSize :: KType CorePrim -> (Int,Int)
goAttSize i = case i of
                KOptional l ->  goAttSize l
                KDelayed l ->  goAttSize l
                KSerial l -> goAttSize l
                KArray l -> let (i1,i2) = goAttSize l in (i1+1,i2*8)
                KInterval l -> let (i1,i2) = goAttSize l in (i1*2 ,i2)
                Primitive i ->
                  case (\(AtomicPrim i) -> i) $ i of
                       PInt _-> (3,1)
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

getRelOrigin :: [Column k () ] -> [k ]
getRelOrigin =  fmap _relOrigin . concat . fmap keyattri

labelCaseDiff
  ::  InformationSchema
  -> Bool -> Column CoreKey ()
  -> TrivialWidget (Editor (Index (Column CoreKey Showable)))
  -> UI (TrivialWidget (Editor (Index (Column CoreKey Showable))))
labelCaseDiff inf b a wid = do
    l <- flabel # set text (show $ _relOrigin <$> keyattri a)
    tip <- UI.div
    patch <- UI.div
    hl <- UI.div # set children [l,tip,patch]
    ht <- hoverTip2 l hl
    bh <- ui $ stepper False ht
    element patch
      # sink text (liftA2 (\bh -> if bh then id else const "") bh (facts $ fmap  show $ (triding wid)))
      # sink0 UI.style (noneShow <$> bh)
    element tip
      # set text (show $ fmap showKey  <$> keyattri a)
      # sink0 UI.style (noneShow <$> bh)
    paintEditDiff l (facts (triding wid ))
    return $ TrivialWidget (triding wid) hl

paintEditDiff e  i  = element e # sink0 UI.style ((\ m  -> pure . ("background-color",) $ cond  m  ) <$> i )
  where cond (Delete )  = "purple"
        cond (Keep ) = "blue"
        cond (Diff i) = "yellow"



tbCaseDiff
  :: InformationSchema
  -> SelPKConstraint
  -> Column CoreKey ()
  -> [(Column CoreKey () ,(Tidings (Editor (Index (Column CoreKey Showable))),Tidings (Maybe (Column CoreKey Showable ))))]
  -> PluginRef (Column CoreKey Showable)
  -> Tidings (Maybe (Column CoreKey Showable))
  -> UI (TrivialWidget (Editor (Index (Column CoreKey Showable))))
tbCaseDiff inf constr i@(FKT ifk  rel tb1) wl plugItens preoldItems = do
        let
            oldItems =  preoldItems
            nonInj =  (S.fromList $ _relOrigin   <$> rel) `S.difference` (S.fromList $ getRelOrigin $ fmap unTB $ unkvlist ifk)
            nonInjRefs = filter ((\i -> if S.null i then False else S.isSubsetOf i nonInj ) . S.fromList . fmap fst .  aattri .fst) wl
            relTable = M.fromList $ fmap (\i -> (_relTarget i,_relOrigin i)) rel
            restrictConstraint = filter ((`S.isSubsetOf` (S.fromList $ fmap _relOrigin rel)) . S.fromList . getRelOrigin  .fst) constr
            convertConstr :: SelTBConstraint
            convertConstr = (\(f,j) -> (f,) $ fmap (\constr -> constr . justError "no back fk" .  (\box ->  (\ref -> pure $ FKT (kvlist $ fmap _tb $ ref ) rel (TB1 box) )<$> backFKRef relTable (getRelOrigin f) box ) ) j ) <$>  restrictConstraint
        let
            patchRefs = fmap (\(a,b) -> (flip recoverEditChange ) <$> facts a <#> b ) <$> nonInjRefs
        v <-  fkUITableDiff inf convertConstr plugItens  patchRefs oldItems i
        return $ TrivialWidget  (triding v ) (getElement v)

tbCaseDiff inf constr i@(IT na tb1 ) wl preplugItems preoldItems
    = do
      let restrictConstraint = filter ((`S.isSubsetOf` (S.singleton na) ) . S.fromList . getRelOrigin  .fst) constr
      plugItems <- ui $ traverse (traverse cacheTidings) preplugItems
      oldItems <- ui $ cacheTidings preoldItems
      iUITableDiff inf restrictConstraint plugItems oldItems i
tbCaseDiff inf _ a@(Attr i _ ) wl plugItens preoldItems = do
        let oldItems = maybe preoldItems (\v-> fmap (Just . fromMaybe (Attr i v)) preoldItems  ) ( keyStatic i)
        let tdiv = fmap _tbattr <$> oldItems
        attrUI <- buildUIDiff (keyModifier i) (keyType i) (fmap (fmap (\(PAttr _ v) -> v)) . snd <$> plugItens) tdiv
        let insertT = fmap (PAttr i ) <$> triding attrUI
        return $ TrivialWidget insertT  (getElement attrUI)
tbCaseDiff inf _ a@(Fun i rel ac ) wl plugItens preoldItems = do
  let
    search (IProd _ t) = fmap (fmap _tbattr ). uncurry recoverT .snd <$> L.find ((S.singleton t ==) . S.fromList . fmap _relOrigin . keyattri . fst) wl
    search (Nested t (Many [m]) ) =  fmap (fmap joinFTB . join . fmap (traverse (indexFieldRec m) . _fkttable )). uncurry recoverT . snd <$> L.find ((S.fromList (iprodRef <$> t) ==) . S.fromList . fmap _relOrigin .keyattri . fst) wl
    refs = sequenceA $ catMaybes $ search <$> snd rel
  funinp <- ui$ cacheTidings (fmap _tbattr . preevaluate i (fst rel) funmap (snd rel) <$> refs )
  ev <- buildUIDiff ([FRead])(keyType i) [] funinp
  return $ TrivialWidget (editor <$> preoldItems <*> (fmap (Fun i rel) <$>  funinp)) (getElement ev)

recoverT i j = liftA2 (flip recoverEditChange) i j

emptyRecTable (FKT rel l tb )
    = case tb of
          (LeftTB1 _ ) ->  Just . fromMaybe (FKT (mapKV (mapComp (mapFAttr (const (LeftTB1 Nothing)))) rel) l (LeftTB1 Nothing))
          i -> id
emptyRecTable (IT l tb)
    = case tb of
          (LeftTB1 _) -> Just . fromMaybe (IT l (LeftTB1 Nothing))
          i -> id


tbRecCaseDiff ::  InformationSchema ->  SelPKConstraint  -> Column CoreKey ()
        -> [(Column CoreKey () ,(Tidings (Editor (Index (Column CoreKey Showable))),Tidings (Maybe (Column CoreKey Showable ))))]
        -> PluginRef  (Column CoreKey Showable) -> Tidings (Maybe (Column CoreKey Showable)) -> UI (TrivialWidget (Editor (Index (Column CoreKey Showable))))
tbRecCaseDiff inf constr a wl plugItens preoldItems' = do
      let preoldItems = emptyRecTable  a <$> preoldItems'
      let check = foldl' (liftA2 (\j i ->  liftA2 apply j i <|> j <|> (create <$> i ))) (preoldItems) ( snd <$> plugItens )
      TrivialWidget btr open<- checkedWidget  (isJust <$> check)
      element open
      (ev,h) <- ui $ newEvent
      inipre <- currentValue  (facts preoldItems)
      let fun True = do
              initpre <- currentValue (facts preoldItems)
              initpreOldB <- ui $ stepper initpre (rumors preoldItems)
              TrivialWidget btre bel <- tbCaseDiff inf constr a wl plugItens (tidings initpreOldB (rumors preoldItems) )
              ui $ onEventDyn (rumors btre) (liftIO . h )
              el <- UI.div # set children [bel] # set UI.style [("border","1px solid gray")]
              return el
          fun False = do
            UI.div # set UI.style [("border","1px solid gray")]
      sub <- UI.div # sink items  (pure .fun <$> facts btr )
      out <- UI.div # set children [open,sub]
      binipre <- ui $ stepper  Keep ev
      return (TrivialWidget  (tidings binipre ev) out)

unTBMap :: Show a => TBData k a -> Map (Set (Rel k  )) (Compose Identity (TB Identity ) k a )
unTBMap = _kvvalues . unTB . snd

instance Applicative Editor where
  pure =Diff
  Diff f <*> Diff v = Diff $ f  v
  Keep <*> j = Keep
  j <*> Keep  = Keep
  Delete   <*> j = Delete
  i <*> Keep = Delete

loadPlugins inf =  do
  code <- liftIO$ indexSchema  (rootRef inf) "code"
  (_,(_,evMap )) <- transactionNoLog  code $ selectFromTable "plugin_code" Nothing Nothing [] []
  let
    project e = (i, p)
      where
         i = justError "cant find function field" $ fmap (convertI . _tbattr) $  indexField (liftAccess code "plugin_code" $ keyRef "ref") e
         p = justError "cant find function field" $ join . fmap (convertP . _tbattr) $  indexField (liftAccess code  "plugin_code" $ keyRef "plugin") e
    convertP (TB1 (SHDynamic (HDynamic i))) = fromDynamic i  :: Maybe PrePlugins
    convertI (TB1 (SNumeric i)) = i
  return (project <$> F.toList evMap)


repl :: Ord k =>Access k-> [Access k]
repl (Rec  ix v ) = replaceU ix v v
repl v = [v]
traRepl :: Ord k => [Access k] -> [Access k]
traRepl i = foldMap repl i

eiTableDiff
  :: InformationSchema
     -> SelPKConstraint
     -> [(Column CoreKey () ,Tidings (Maybe (Column CoreKey Showable)))]
     -> PluginRef (TBData CoreKey Showable)
     -> TBData CoreKey ()
     -> Tidings (Maybe (TBData CoreKey Showable))
     -> UI (Element,Tidings (Editor (Index (TBData CoreKey Showable))))
eiTableDiff inf constr refs plmods ftb@(meta,k) preoldItems = do
  oldItems <- ui $ cacheTidings preoldItems
  plugins <- ui $ loadPlugins inf
  let
      table = lookTable inf (_kvname meta)
  res <- mapM (pluginUI inf oldItems) (filter ((== rawName table ) . _bounds . snd) (plugins ))
  let
      resdiff =   fmap ( liftA2 (\i j -> (join .liftA2 (\j i@(_,pk,_)   -> if   pk == G.getIndex j then Just i else Nothing ) i $ j ) ) oldItems   ) .  snd <$> res
      srefs = P.sortBy (P.comparing (RelSort .F.toList . fst) ) . M.toList $ replaceRecRel (unTBMap ftb) (fmap (fmap S.fromList )  <$> _kvrecrels meta)
      plugmods = first traRepl <$> (resdiff <> plmods)
      buildFKS =  foldl' (\jm (l,m)  -> do
                    w <- jm
                    let el = L.any (mAny ((l==) . head ))  (fmap (fmap S.fromList ) <$> ( _kvrecrels meta))
                        plugattr = indexPluginAttrDiff (unTB m) plugmods
                        oldref = (join . fmap (fmap unTB .  (^?  Le.ix l ) . unTBMap ) <$> oldItems)
                        aref = maybe oldref ( snd) (L.find (((keyattr m)==) . keyattri .fst) $  refs)
                    wn <- (if el
                            then tbRecCaseDiff
                            else tbCaseDiff ) inf constr (unTB m)  (fmap (first triding) <$> w) plugattr aref
                    let nref = maybe wn (\(_,a) -> TrivialWidget (liftA3  match (triding wn) a oldref) (getElement wn) ) (L.find (((keyattr m)==) . keyattri .fst) $  refs)
                        match Keep i j = maybe Keep Diff  (join ( liftA2 diff i j <|> fmap (Just .patch) i) )
                        match j _ _  = j
                    lab <- if
                      rawIsSum table
                      then return nref
                      else do
                        v <- labelCaseDiff inf False (unTB m) nref
                        out <- UI.div # set children [getElement v,getElement  nref] #  set UI.class_ ("col-xs-" <> show (fst $  attrSize (unTB m)))
                        return $ TrivialWidget (triding v) out

                    return (w <> [(unTB m,(lab,aref))])
                ) (return [])  (srefs)
  let
      sequenceTable :: [(Column CoreKey () ,(TrivialWidget (Editor (Index (Column CoreKey Showable))), Tidings (Maybe (Column CoreKey Showable))))] -> Tidings (Editor (Index (TBData CoreKey Showable)))
      sequenceTable fks = (\old difs -> (\ i ->  (fmap (tableMeta table , maybe (G.Idex [])G.getIndex old,)   ) i) . reduceTable $ difs) <$> oldItems <*> Tra.sequenceA (triding .fst . snd <$> fks)

  (listBody,output) <- if rawIsSum table
    then do
      fks <-buildFKS
      let
        initialAttr = join . fmap (\(n,  j) ->    safeHead $ catMaybes  $ (unOptionalAttr  . unTB<$> F.toList (_kvvalues (unTB j))))  <$>oldItems
        sumButtom itb =  do
           let i = unTB itb
               (body ,_) = justError ("no sum attr " <> show i) $ M.lookup i (M.fromList fks)
           element =<< labelCaseDiff inf True i body

        marker i = sink  UI.style ((\b -> if not b then [("border","2px gray dotted")] else [("border","2px white solid")] )<$> i)

      chk  <- buttonDivSetO (F.toList (unKV k))  (join . fmap (\i -> M.lookup (S.fromList (keyattri i)) (unKV k)) <$> initialAttr )  marker sumButtom

      element chk # set UI.style [("display","inline-flex")]
      let
          keypattr (PAttr i _) = [Inline i]
          keypattr (PInline i _) = [Inline i]
          keypattr (PFK  l  _ _) = l
          delete (PAttr i _) = PAttr i (POpt Nothing)
          delete (PInline i _) = PInline i (POpt Nothing)
          delete (PFK i j _ ) = PFK i (fmap delete  j ) (POpt Nothing)
          iniValue = (fmap (patch.attrOptional ) <$> initialAttr)
          resei :: Tidings (Editor (Index (TBData CoreKey Showable)))
          resei = (\ini j -> fmap (\(m,i,l)  -> (m,i,L.map (\i -> if (keypattr i == keyattr j) then i else delete i) (maybe l (:l) ini))) ) <$> iniValue <*> triding chk <*> sequenceTable fks
      listBody <- UI.div #  set children (getElement chk : F.toList (getElement .fst .snd <$> fks))
      sequence $ (\(kix,(el,_)) -> element  el # sink0 UI.style (noneShow <$> ((==keyattri kix) .keyattr <$> facts (triding chk) ))) <$> fks
      return (listBody, resei)
    else  do
      fks <- buildFKS
      listBody <- UI.div  #
        set children (F.toList (getElement .fst . snd  <$> fks))
      return (listBody,sequenceTable fks)
  element listBody # set UI.class_ "row" #
      set style [("border","1px"),("border-color",maybe "gray" (('#':).T.unpack) (schemaColor inf)),("border-style","solid"),("margin","1px")]
  plugins <-  if not (L.null (fst <$> res))
    then do
      pure <$> UI.div # set children (fst <$> res)
    else do
      return []
  body <- UI.div
    # set children (plugins  <> pure listBody)
    # set style [("margin-left","0px"),("border","2px"),("border-color",maybe "gray" (('#':).T.unpack) (schemaColor inf)),("border-style","solid")]
  tableName <- flabel # set UI.text (T.unpack $ tableName table)
  tableDiv <- UI.div # set children [tableName,body]
  return (tableDiv , output)

crudUITable
   :: InformationSchema
   -> RefTables
   -> [(TB Identity CoreKey () ,Tidings (Maybe (TB Identity CoreKey Showable)))]
   -> PluginRef (TBData CoreKey Showable)
   -> TBData CoreKey ()
   -> Tidings (Maybe (TBData CoreKey Showable))
   -> UI (Element,Tidings (Maybe (TBData CoreKey Showable)))
crudUITable inf reftb@(_, _ ,gist ,_,tref) refs pmods ftb@(m,_)  preoldItems = do
          out <- UI.div
          let
            table = lookTable inf ( _kvname  m )
            getItem :: TBData CoreKey Showable -> TransactionM (Maybe (TBIdx CoreKey Showable))
            getItem  v =  getFrom table v `catchAll` (\e -> liftIO (putStrLn $ "error getting Item" ++ show (e :: SomeException)) >> return Nothing)
          preoldItens <- currentValue (facts preoldItems)
          loadedItens <-  ui $ join <$> traverse (transactionNoLog inf  . getItem) preoldItens
          (loadedItensEv ) <- mapUIFinalizerT out (ui . fmap join <$> traverse (\i ->  do
            p <-  transactionNoLog inf . getItem $ i
            putPatch tref (fmap PatchRow $ maybeToList p)
            return (fmap PatchRow p  ) )) preoldItems
          let
            deleteCurrentUn un e l =   maybe l (\v -> G.delete v G.indexParam l) $  G.getUnique un <$> e
            tpkConstraint = (fmap unTB $ F.toList $ _kvvalues $ unTB $ snd $ tbPK ftb , (_kvpk m,  gist))
          unConstraints <-  traverse (traverse (traverse (ui . cacheTidings))) $ (\un -> (fmap unTB $ F.toList $ _kvvalues $ unTB $ tbUn (S.fromList un ) (TB1 ftb) , (un, fmap (createUn un . G.toList ) gist))) <$> _kvuniques m
          unDeleted <- traverse (traverse (traverse (ui . cacheTidings))) (fmap (fmap (\(un,o)-> (un,deleteCurrentUn un <$> preoldItems <*> o))) (tpkConstraint:unConstraints))
          let
            dunConstraints (un,o) = flip (checkGist un .tblist' table . fmap _tb) <$> o
            unFinal:: [([Column CoreKey ()], Tidings PKConstraint)]
            unFinal = fmap (fmap dunConstraints) unDeleted
          (listBody,tablebdiff) <- eiTableDiff inf  unFinal  refs pmods ftb preoldItems

          (panelItems,tdiff)<- processPanelTable listBody inf reftb  (diffTidings tablebdiff) table preoldItems
          let
            tableb = recoverEditChange <$> preoldItems <*> tablebdiff

          out <- element out # set children [listBody,panelItems]
          return (out ,tableb)




dynCrudUITable
   :: InformationSchema
   -> Tidings String
   -> RefTables
   -> [(TB Identity CoreKey () ,Tidings (Maybe (TB Identity CoreKey Showable)))]
   -> PluginRef (TBData CoreKey Showable)
   -> TBData CoreKey ()
   -> Tidings (Maybe (TBData CoreKey Showable))
   -> UI ([Element],Tidings (Maybe (TBData CoreKey Showable)))
dynCrudUITable inf open reftb@(_, _ ,gist ,_,tref) refs pmods ftb@(m,_)  preoldItems = do
  (e2,h2) <- ui $ newEvent

  let translate "+" = "plus"
      translate "-" = "minus"
  nav  <- buttonDivSet ["+","-"] (fmap Just open)
      (\i -> UI.button
          # set UI.style [("font-size","smaller"),("font-weight","bolder")]
          # set UI.class_ ("buttonSet btn-xs btn-default btn pull-left glyphicon-" <> translate i))
  element nav # set UI.class_ "pull-left"
  sub <- UI.div
  let table = lookTable inf ( _kvname  m )
  let
      fun "+" =  do
          (out ,tableb)<- crudUITable inf reftb refs pmods ftb preoldItems
          ui $ onEventDyn (filterE (maybe False (isRight.tableCheck)) (rumors tableb))
              (liftIO . h2)
          return out
      fun i = UI.div

  end <- mapUIFinalizerT sub fun (diffTidings $ triding nav)
  element sub # sink children (pure <$> facts end)
  cv <- currentValue (facts preoldItems)
  let evs2 = unionWith const e2  (rumors preoldItems)
  bh2 <- ui $ stepper  cv evs2
  return ([getElement nav,sub], F.foldl' (\i j -> mergePatches <$> i <*> j) (tidings bh2 evs2) (fmap snd pmods))

mergePatches i j = join (liftA2 applyIfChange i j)<|> i  <|> join (createIfChange <$>j)

diffTidings t = tidings (facts t) $ diffEvent (facts t ) (rumors t)

onDiff f g (Diff i ) = f i
onDiff f g _ = g

processPanelTable
   :: Element
   -> InformationSchema
   -> RefTables
   -> Tidings (Editor (TBIdx CoreKey Showable))
   -> Table
   -> Tidings (Maybe (TBData CoreKey Showable))
   -> UI (Element, Event (RowPatch CoreKey Showable) )
processPanelTable lbox inf reftb@(res,_,gist,_,_) inscrudp table oldItemsi = do
  let
      inscrud = recoverEditChange  <$> oldItemsi <*> inscrudp
      containsGistNotEqual old ref map = if isJust refM then (\i -> if L.null i  then True else [G.getIndex old] == L.nub (fmap G.getIndex (F.toList i)))$  (lookGist ix ref map) else False
        where ix = (_kvpk (tableMeta table))
              refM = traverse unSOptional' (getPKM ref)
      containsGist ref map = if isJust refM then not $ L.null $  (lookGist ix ref map) else False
        where ix = (_kvpk (tableMeta table))
              refM = traverse unSOptional' (getPKM ref)
      conflictGist ref map = if isJust refM then lookGist ix ref map else[]
        where ix = (_kvpk (tableMeta table))
              refM = traverse unSOptional' (getPKM ref)


  let
    pred2 =  [(keyRef "schema",Left (int $ schemaId inf  ,Equals))]
    authPred =  [(keyRef "grantee",Left ( int $ fst $ username inf ,Equals))] <> pred2
  auth <- fst <$> ui (transaction (meta inf) $ selectFromTable "authorization" Nothing Nothing [] authPred)
  let authorize =  (\autho -> fmap unArray . unSOptional' . _tbattr .  lookAttr' (meta inf) "authorizations"  =<<  G.lookup (idex  (meta inf) "authorization"  [("schema", int (schemaId inf) ),("table",int $ tableUnique table),("grantee",int $ fst $ username inf)]) autho)  <$> collectionTid auth
  -- Insert when isValid
  let insertEnabled = liftA2 (&&) (liftA2 (||) (onDiff isRight False .  fmap patchCheck <$>  inscrudp) (maybe False (isRight . tableCheck  )  <$> inscrud )) (liftA2 (\i j -> not $ maybe False (flip containsGist j) i  ) inscrud gist)
  insertB <- UI.button
      # set UI.class_ "btn btn-sm"
      # set text "INSERT"
      # set UI.class_ "buttonSet"
      # sink UI.style (noneShowSpan . maybe False (txt "INSERT" `elem`) <$>facts authorize)
      # sinkDiff UI.enabled insertEnabled

  let editEnabled = (\i j k l m -> i && j && k && l && m )<$> ((maybe False (isRight . tableCheck  )  )<$> inscrud ) <*> (isJust <$> oldItemsi) <*>   (liftA2 (\i j -> maybe False (flip containsGist j) i ) oldItemsi gist ) <*> (liftA3 (\i k j -> maybe False (\(a,b) -> containsGistNotEqual b a j) (liftA2 (,) k i) ) inscrud oldItemsi gist ) <*> (isDiff <$> inscrudp)
  editB <- UI.button
      # set UI.class_ "btn btn-sm"
      # set text "EDIT"
      # set UI.class_ "buttonSet"
      # sink UI.style (noneShowSpan . maybe False (txt "UPDATE" `elem`) <$>facts authorize)
  -- Edit when any persistent field has changed
      # sinkDiff UI.enabled editEnabled

  let mergeEnabled = liftA2 (&&) (isJust . fmap tableNonRef' <$> inscrud) (liftA2 (\i j -> not . L.null   $ maybe [] (\e -> filter ((/= tableNonRef' e) .tableNonRef') $  conflictGist e j) i  ) (inscrud) (gist ))
  mergeB <- UI.button# set UI.class_ "btn btn-sm"
      # set text "MERGE"
      # set UI.class_ "buttonSet"
      # sink UI.style (noneShowSpan . maybe False (txt "UPDATE" `elem`) <$>facts authorize)
  -- Edit when any persistent field has changed
      # sinkDiff UI.enabled mergeEnabled

  let deleteEnabled = liftA2 (&&) (isJust . fmap tableNonRef' <$> oldItemsi) (liftA2 (\i j -> maybe False (flip containsGist j) i  ) (oldItemsi ) (gist ))
  deleteB <- UI.button# set UI.class_ "btn btn-sm"
      #   set text "DELETE"
      #   set UI.class_ "buttonSet"
      # sink UI.style (noneShowSpan . maybe False (txt "DELETE" `elem`) <$>facts authorize)
  -- Delete when isValid
      #   sinkDiff UI.enabled deleteEnabled
  let
       filterKey enabled k = const () <$> filterApply (const <$> enabled) (k )
       crudMerge :: Maybe (TBData Key Showable)  ->  G.GiST (TBIndex Showable) (TBData Key Showable )-> Dynamic (Maybe (RowPatch Key Showable))
       crudMerge (Just i) g =
         fmap (tableDiff . fmap ( fixPatchRow inf (tableName table)) )  <$> transaction inf ( do
            let confl = conflictGist i g
            mapM deleteFrom confl
            fullDiffInsert  i)
       crudEdi i j =  fmap (\g -> fmap (PatchRow . fixPatch inf (tableName table) ) $diff i  g) $ transaction inf $ fullDiffEditInsert  i j
       crudIns j   =  fmap (tableDiff . fmap ( fixPatchRow inf (tableName table)) )  <$> transaction inf (fullDiffInsert  j)
       crudDel :: TBData Key Showable  ->  Dynamic (Maybe (RowPatch Key Showable))
       crudDel j  = fmap (tableDiff . fmap ( fixPatchRow inf (tableName table)))<$> transaction inf (deleteFrom j )

  altU <- onAltU lbox
  altI <- onAltI lbox
  cliIns <- UI.click insertB
  cliMerge <- UI.click mergeB
  cliDel <- UI.click deleteB
  cliEdit <- UI.click editB
  diffEdi <- mapEventFin (fmap join . sequence) $ liftA2 crudEdi <$> facts oldItemsi <*> facts inscrud <@ (unionWith const cliEdit (filterKey (facts editEnabled) ( altU)))
  diffDel <- mapEventFin (fmap join . sequence) $ fmap crudDel <$> facts oldItemsi <@ cliDel
  diffMerge <- mapEventFin id $ crudMerge <$> facts inscrud <*> facts gist <@ cliMerge
  diffIns <- mapEventFin (fmap join . sequence) $ fmap crudIns <$> facts inscrud <@ (unionWith const cliIns (filterKey  (facts insertEnabled) altI ))

  conflict <- UI.div # sinkDiff text ((\i j l -> if l then maybe "" (L.intercalate "," .fmap (showFKText ). flip conflictGist  j) i else "")  <$> inscrud <*> gist <*> mergeEnabled) # sinkDiff UI.style (noneShow <$>mergeEnabled)
  debugBox <- checkedWidget (onDiff (const True) False <$> inscrudp)
  transaction <- UI.span
    # set children [insertB,editB,mergeB,deleteB,getElement debugBox]
    -- # set UI.style (noneShowSpan (ReadWrite ==  rawTableType table ))
  debug <- UI.div
  let renderTyped (Pure _ ) i  = ident. renderTable  $ i
      renderTyped (Other (Constant i) ) _ = unlines ("Type check error":  i)
  mapUIFinalizerT debug (\i -> if  i
                    then do
                      let gen (h,s) = do
                            v <- ui $ currentValue s
                            header <- flabel
                                      # set UI.text h
                                      # set UI.class_ "col-xs-4"
                            out <- UI.mkElement "textarea"
                                      # set (UI.strAttr "onkeyup") "textAreaAdjust(this)"
                                      # set UI.value v
                                      # set UI.style [("max-height","300px")]
                                      # set UI.class_ "col-xs-4"
                            onChanges s (\v ->  do
                              element out # set UI.value v # method  "textAreaAdjust(%1)")
                            return (header,out)
                      out <- mapM gen
                          [("Last", maybe "" (ident . renderTable) <$> facts oldItemsi)
                          ,("Diff", onDiff (ident.renderRowPatch ) "" <$> facts inscrudp)
                          ,("New" , maybe "" (\i -> renderTyped (typeCheckTable (_rawSchemaL table,_rawNameL table) i ) i  ) <$> facts inscrud)]

                      element debug # set children (fmap fst out ++ fmap snd out)
                      mapM (\i -> element i# method "textAreaAdjust(%1)")  (snd <$> out)
                      return debug
                    else  element debug # set children [] ) (triding debugBox)
  out <- UI.div # set children [transaction,conflict,debug]
  return (out, fmap head $ unions $ fmap filterJust [diffEdi,diffIns,diffMerge,diffDel] )


method s i = i >>= \e -> runFunctionDelayed e . ffi s $ e

showFKText v = (L.take 50 $ L.intercalate "," $ fmap renderShowable $ allKVRec' $  v)

showFKE v =  UI.div # set text (L.take 50 $ L.intercalate "," $ fmap renderShowable $ allKVRec' $  v) # set UI.class_ "fixed-label"

showFK = (pure ((\v j ->j  # set text (L.take 50 $ L.intercalate "," $ fmap renderShowable $ allKVRec'  v))))



----
-- Fields Array Editing Operations
----

splitArray
  :: Show a => Int  -- Offset
  -> Int  -- Inner Block Size
  -> NonEmpty a  -- FullList
  -> NonEmpty a  -- Inner Block
  -> NonEmpty a
splitArray s o m l
  =  res
  where
    ta = if Non.length l == s then  (fmap Non.fromList $ nonEmpty $Non.drop  (o + s ) m) else Nothing
    pre = (fmap Non.fromList $ nonEmpty $ Non.take o m )
    res = justError "can't be null"  $ pre <> Just l <> ta

takeArray :: (Show b,Applicative f ) => NonEmpty (f (Maybe b)) -> f (Maybe (NonEmpty b))
takeArray a = fmap (Non.fromList) . nonEmpty .fmap (justError "is nothing" ). Non.takeWhile isJust <$> Tra.sequenceA a

dynHandlerPatch hand val ix (l,old)= do
    (ev,h) <- ui $ newEvent
    let valix =  val ix
    let
        --idyn i | traceShow (ix,i) False = undefined
        idyn True  =  do
          tds <- hand ix valix
          ini <- currentValue (facts $ triding tds)
          liftIO $ h ini
          fin <- ui $ onEventDyn (rumors $ triding tds) (liftIO . h)
          return [getElement tds]
        idyn False = do
          return []
        idynDiff [] True= idyn True
        idynDiff [] False=return[]
        idynDiff i False= idyn False
        idynDiff i True= return i
    el <- UI.div
    pretd <- ui $ cacheTidings  old
    els <- mapUIFinalizerT el idyn  pretd
    element el # sink children (facts els)
    bend <- ui $ stepper Keep (unionWith const (const Keep <$> rumors valix) ev)
    let
      -- infer i j | traceShow ("infer",i,j) False = undefined
      infer Delete  _ = False
      infer (Diff _) _ = True
      infer Keep (Just _) = True
      infer Keep Nothing  = False
      evnew = (&&) <$> facts old <@> unionWith const (isJust <$> rumors valix) ( flip infer <$> facts valix <@> ev)

    inivalix <- ui $currentValue (facts valix)
    vout <- ui$ stepper (isJust inivalix) (evnew)
    let evdiff= (diffEvent vout evnew)
    bdifout <- ui $ stepper (isJust inivalix)  evdiff

    return $ (l <> [TrivialWidget (tidings bend ev) el], ( tidings bdifout evdiff))


-- reduceDiffList o i | traceShow (o,i) False = undefined
reduceDiffList o i
   | F.all isKeep (snd <$> i) = Keep
   | otherwise = patchEditor $ lefts diffs ++ reverse (rights diffs)
   where diffs = catMaybes $ (\(ix,v) -> treatA (o+ix)v) <$> i
         treatA a (Diff v) = Just $ Left $ PIdx a  (Just v)
         treatA a Delete =  Just $ Right $ PIdx a Nothing
         treatA _ Keep = Nothing

reduceDiffListFK o i
   -- | traceShow (o,i) False = undefined
   | F.all isKeep (snd <$> i) = Keep
   | otherwise = liftA2 (,) (patchEditor $ fmap fst res )  (patchEditor $ fmap snd res)
   where diffs = catMaybes $ (\(ix,v) -> treatA (o+ix)v) <$> i
         -- treatA  i j | traceShow (i,j) False = undefined
         treatA a (Diff (PFK _ [PAttr k l]  v)) = Just $ Left $  (PIdx a (Just l) ,PIdx a  (Just v))
         treatA a (Diff (PFK _ []  v)) = Nothing
         treatA a Delete =  Just $ Right $ (PIdx a Nothing,PIdx a Nothing)
         treatA _ Keep = Nothing
         treatA a p = errorWithStackTrace ("reduceDiffList " ++ show (a,p))
         res = lefts diffs ++ reverse (rights diffs)




reduceOptional Delete   = Diff $ POpt Nothing
reduceOptional Keep  = Keep
reduceOptional (Diff i )  = Diff (POpt (Just  i))

reduceFKOptional rel att  Delete  = Diff $ PFK rel ((\i -> PAttr i (POpt Nothing)) <$> att) (POpt Nothing)
reduceFKOptional rel att  Keep = Keep
reduceFKOptional rel att  (Diff (PFK _ attn vn))= Diff $ PFK rel ((\(PAttr i j ) -> PAttr (kOptional i )(POpt $ Just j)) <$> attn) (POpt $ Just vn)



maybeEdit v id (Diff i) =  id i
maybeEdit v id _  = v

buildUIDiff:: [FieldModifier] -> KType (Prim KPrim (Text,Text))-> [Tidings (Maybe (Index (FTB Showable)))]-> Tidings (Maybe (FTB Showable)) -> UI (TrivialWidget (Editor (Index (FTB Showable))))
buildUIDiff km i  plug tdi = go i plug tdi
  where
    go :: KType (Prim KPrim (Text,Text))-> [Tidings (Maybe (Index (FTB Showable)))]-> Tidings (Maybe (FTB Showable)) -> UI (TrivialWidget (Editor (Index (FTB Showable))))
    go i plug tdi = case i of
         KArray ti  -> mdo
            offsetDiv  <- UI.div
            -- let wheel = fmap negate $ mousewheel offsetDiv
            TrivialWidget offsetT offset <- offsetField (pure 0)  never (maybe 0 (Non.length .unArray) <$> (recoverEditChange <$> tdi <*> bres))
            let arraySize = 8
                tdi2  = fmap unArray <$> tdi
                index o ix v = flip Non.atMay (o + ix) <$> v
            let unIndexEl ix = fmap join$ index ix <$> offsetT <*> tdi2
                dyn = dynHandlerPatch  (\ix valix ->do
                  let plugix = ((fmap ((\p -> fmap join $ (\ o v ->  (convertPatchSet (o + ix)) <$> v ) <$> offsetT <*>p))) plug)
                  wid <- go ti plugix valix
                  lb <- hlabel ["col-xs-1"] # sink UI.text (show . (+ix) <$> facts offsetT )
                  paintEditDiff lb (facts (triding wid ))
                  element wid # set UI.class_ "col-xs-12"
                  row <- UI.div # set children [lb,getElement wid]
                  return $ TrivialWidget (triding wid) row ) unIndexEl

            element offset # set UI.class_ "label label-default pull-right col-xs-2"
            widgets <- fst <$> foldl' (\i j -> dyn j =<< i ) (return ([],pure True)) [0..arraySize -1 ]
            let
              widgets2 = Tra.sequenceA (zipWith (\i j -> (i,) <$> j) [0..] ( triding <$> widgets) )
              -- [Note] Array diff must be applied in the right order
              --  additions and edits first in ascending order than deletion in descending order
              --  this way the patch index is always preserved
              bres = reduceDiffList  <$> offsetT <*>  widgets2
            element offsetDiv # set children (fmap getElement widgets)
            composed <- UI.span # set children [offset , offsetDiv]
            return  $ TrivialWidget  bres composed
         KOptional ti -> do
           let pretdi = ( join . fmap unSOptional' <$> tdi)
               plugtdi = fmap (join . fmap (\(POpt i ) -> i) )<$> plug
           tdnew <- go ti  plugtdi pretdi
           retUI <- UI.div # set children [getElement tdnew]
           -- Delete equals create

           return $ TrivialWidget ( reduceOptional <$> triding tdnew  ) retUI
         KSerial ti -> do
           let pretdi = ( join . fmap unSSerial <$> tdi)
               plugtdi = fmap (join . fmap (\(POpt i ) -> i) )<$> plug
           tdnew <- go ti  plugtdi pretdi
           retUI <- UI.div # set children [getElement tdnew]
           -- Delete equals create
           let
               test Delete _ = Diff $ POpt Nothing
               test Keep _ = Keep
               test (Diff i ) _ = Diff (POpt (Just  i))

           return $ TrivialWidget ( test <$> triding tdnew <*> tdi) retUI
         KDelayed ti -> do
           let pretdi = ( join . fmap unSDelayed <$> tdi)
               plugtdi = fmap (join . fmap (\(POpt i ) -> i) )<$> plug
           tdnew <-  go ti plugtdi pretdi
           retUI <- UI.div# set children [getElement tdnew]
           let
               test Delete = Delete
               test Keep = Keep
               test (Diff i ) = Diff (POpt (Just  i))

           return $ TrivialWidget (test <$> triding tdnew  ) retUI
         KInterval ti -> do
            let unInterval f (IntervalTB1 i ) = f i
                unInterval _ i = errorWithStackTrace (show i)
                unfinp (Interval.Finite i) = Just i
                unfinp i = Nothing
                plugtdi i (PInter j l)
                  | i == j  =  unfinp $ fst l
                  | otherwise = Nothing
            composed <-  UI.div
            subcomposed <- UI.div # set UI.children [composed]
            inf <- go ti ( fmap (join . fmap (plugtdi True)) <$> plug) (join.fmap (unInterval inf' ) <$> tdi)
            lbd <- checkedWidget (maybe False id . fmap (unInterval (snd . Interval.lowerBound') ) <$> tdi)

            sup <- go ti (fmap (join . fmap (plugtdi False ) )<$> plug) (join.fmap (unInterval sup')  <$> tdi)
            ubd <- checkedWidget (maybe False id .fmap (unInterval (snd . Interval.upperBound' ) ) <$> tdi)
            element composed # set UI.style [("display","inline-flex")] # set UI.children [getElement lbd ,getElement  inf,getElement sup,getElement ubd]
            let
              replaceL  Delete   h= Diff $ PInter True (Interval.NegInf,h)
              replaceL   i h =  fmap (PInter True  . (,h). Interval.Finite) i
              replaceU  Delete   h = Diff $ PInter False (Interval.PosInf,h)
              replaceU  i  h =  fmap (PInter False . (,h).Interval.Finite) i
              output = (\i j -> reduceDiff $ [i,j])<$> (replaceL <$>  triding inf <*> triding lbd ) <*> (replaceU <$> triding sup <*> triding ubd)
            return $ TrivialWidget  output subcomposed
         Primitive (AtomicPrim i) -> do
           let tdi2 = F.foldl' (liftA2 mergePatches) tdi plug
           pinp  <- buildPrim km (fmap unTB1 <$> tdi2) i
           return $ TrivialWidget (fmap (fmap PAtom) $ editor  <$> (fmap unTB1  <$>tdi) <*> ( triding pinp)) (getElement pinp)
         i -> errorWithStackTrace (show i)

reduceDiff :: [Editor (PathFTB a) ] -> Editor (PathFTB a)
reduceDiff i
  | F.all isKeep i = Keep
  | F.all isDelete i = Delete
  | otherwise = patchEditor $ filterDiff i


buildPrim :: [FieldModifier] ->Tidings (Maybe Showable) ->   KPrim -> UI (TrivialWidget (Maybe Showable))
buildPrim fm tdi i = case i of
         PGeom ix g->
           let tdig = fmap (\(SGeo i) -> i) <$> tdi
           in fmap (fmap(fmap SGeo)) $ case g of
             PPosition -> do
               let tdip = fmap (\(SPosition i) -> i) <$> tdig
               fmap (fmap SPosition)<$> case ix of
                 3-> do
                    lon <- buildPrim fm (fmap (\((Position (lon,_,_))) -> SDouble lon ) <$> tdip) PDouble
                    lat <- buildPrim fm (fmap (\((Position (_,lat,_))) -> SDouble lat ) <$> tdip) PDouble
                    alt <- buildPrim fm (fmap (\((Position (_,_,alt))) -> SDouble alt ) <$> tdip) PDouble
                    let res = liftA3 (\(SDouble a)(SDouble b) (SDouble c) -> (Position (a,b,c))) <$> triding lon <*> triding lat <*> triding alt
                    composed <- UI.div # set UI.style [("display","inline-flex")]  # set UI.children (getElement <$> [lon,lat,alt])
                    upper <- UI.div # set children [composed]
                    return $ TrivialWidget res upper
                 2-> do
                    lon <- buildPrim fm (fmap (\((Position2D (lon,_))) -> SDouble lon ) <$> tdip) PDouble
                    lat <- buildPrim fm (fmap (\((Position2D (_,lat))) -> SDouble lat ) <$> tdip) PDouble
                    let res = liftA2 (\(SDouble a)(SDouble b)  -> (Position2D (a,b))) <$> triding lon <*> triding lat
                    composed <- UI.div # set UI.style [("display","inline-flex")] # set UI.children (getElement <$> [lon,lat])
                    upper <- UI.div # set children [composed]
                    return $ TrivialWidget res upper
         PDimensional i (a,b,c,d,e,f,g) -> do
           let mult = zip [a,b,c,d,e,f,g] un
               multP = filter ((>0).fst) mult
               multN = filter ((<0).fst) mult

               un = ["mol","K","A","l","kg","s","m"]
               pols = (L.intercalate "." $ fmap (\(i,j)-> if i == 1 then j else j<> "^" <> show i) multP)
               negs = (L.intercalate "." $ fmap (\(i,j)-> j<> "^" <> show (abs i)) multN)
               build i j
                 | L.length i == 0 && L.length j == 0 = ""
                 | L.length i == 0  = "1/" <> negs
                 | L.length j == 0  = pols
                 | otherwise = pols <> "/" <> negs
               scale i
                 | i == 0 = ""
                 | otherwise = "10^" <> show i  <> "."
           tag <- UI.span # set text  (scale i <> build pols negs)
           out <- oneInput tdi [tag]
           element out # set UI.style [("width","100%")]
           return out
         PBoolean -> do
           res <- checkedWidgetM (fmap (\(SBoolean i) -> i) <$> tdi )
           return (fmap SBoolean <$> res)
         PTime ti -> do
           let  tdip =  tdi
           case ti of
             PTimestamp dbzone -> do
                cliZone <- jsTimeZone
                itime <- liftIO $  getCurrentTime
                let
                  maptime f (STime (STimestamp i)) = STime $ STimestamp (f i)
                  fromLocal = maptime (utcToLocalTime utc .localTimeToUTC cliZone)
                v <- currentValue (facts tdi)

                inputUI <- UI.input
                    # set UI.style [("width","100%")]
                    # set UI.class_ "date"
                    # set (UI.strAttr "data-date-format") "yyyy-mm-dd hh:ii:ss"
                    # set (UI.strAttr "data-provide" ) "datetimepicker"
                    # sinkDiff UI.value (maybe "" (fst . break (=='.') . renderPrim )<$> tdi)

                onCE <- UI.onChangeE inputUI
                let pke = unionWith const (readPrim i <$> onCE ) (rumors tdi)
                pk <- ui $ stepper v  pke
                sp <- UI.div # set children [inputUI ]
                return $ TrivialWidget ((fmap fromLocal) <$> tidings pk pke) sp
             PDate -> do
                cliZone <- jsTimeZone
                itime <- liftIO $  getCurrentTime
                v <- currentValue (facts tdi)

                inputUI <- UI.input
                    # set UI.style [("width","100%")]
                    # set UI.class_ "date"
                    # set (UI.strAttr "data-date-format") "yyyy-mm-dd"
                    # set (UI.strAttr "data-provide" ) "datepicker"
                    # sinkDiff UI.value (maybe "" renderPrim <$> tdi)

                onCE <- UI.onChangeE inputUI
                let pke = unionWith const (readPrim i <$> onCE ) (rumors tdi)
                pk <- ui $ stepper v  pke
                sp <- UI.div # set children [inputUI]
                return $ TrivialWidget(tidings pk pke) sp
             PDayTime -> do
                cliZone <- jsTimeZone
                itime <- liftIO $  getCurrentTime
                oneInput tdi []
             PInterval -> oneInput tdi []
         PSession -> do
           dv <- UI.div # set text "session" # sink UI.style (noneShow . isJust <$> facts tdi)
           return  $ TrivialWidget tdi dv
         PMime "text/plain" -> do
           let fty = ("textarea",UI.value ,maybe "" (\(SBinary i) -> BSC.unpack i) ,[("width","100%"),("height","300px")])
           ini <- currentValue (facts tdi)
           f <- pdfFrame fty (facts tdi) # sink UI.style (noneShow . (\i -> isJust i || elem FWrite fm) <$> facts tdi)
           vcf <- UI.valueChange f
           let ev = if elem FWrite fm then unionWith const (rumors tdi) (Just . SBinary . BSC.pack <$> vcf) else rumors tdi
           step <- ui $ stepper  ini ev
           return (TrivialWidget (tidings step ev) f)
         PMime "video/mp4" -> do
           let binarySrc = (\(SBinary i) -> "data:" <> T.unpack "video/mp4"<> ";base64," <>  (BSC.unpack $ B64.encode i) )
           clearB <- UI.button # set UI.text "clear"
           file <- UI.input # set UI.type_ "file" # set UI.multiple True # set UI.style (noneShow $ elem FWrite fm)
           fchange <- fileChange file
           clearE <- UI.click clearB
           tdi2 <- ui $ addEvent (join . fmap (fmap SBinary . either (const Nothing) Just .   B64.decode .  BSC.drop 7. snd  . BSC.breakSubstring "base64," . BSC.pack ) <$> fchange) =<< addEvent (const Nothing <$> clearE ) tdi

           let fty = ("source",UI.src,maybe "" binarySrc  ,[])
           ini <- currentValue (facts tdi2)
           let f = (\i -> do
                f <- pdfFrame fty  i # set UI.type_ "video/mp4"
                mkElement "video" # set children (pure f) # set (UI.strAttr "width" ) "320" # set (UI.strAttr "height" ) "240" # set (UI.strAttr "controls") ""# set (UI.strAttr "autoplay") ""
                   ) <$> (facts tdi2)
               pdfFrame (elem,sr , call,st) pdf = mkElement (elem ) # set sr (call  pdf)
           v <- UI.div # sink  items(pure <$> f)
           o <- UI.div # set children [file,clearB,v]
           return (TrivialWidget tdi2 o)

         PMime "application/dwg" -> do
           let fty = ("div",UI.value,maybe "" (\(SBinary i) -> BSC.unpack i) ,[("width","100%"),("height","300px")])
           ini <- currentValue (facts tdi)
           f <- pdfFrame fty (facts tdi) # sink UI.style (noneShow . (\i -> isJust i || elem FWrite fm) <$> facts tdi)
           vcf <- UI.valueChange f
           let ev = if elem FWrite fm then unionWith const (rumors tdi) (Just . SBinary . BSC.pack <$> vcf ) else rumors tdi
           step <- ui $ stepper  ini ev
           return (TrivialWidget (tidings step ev) f)
         PAddress -> do
           let binarySrc = (\(SText i) -> "https://drive.google.com/embeddedfolderview?id=" <> T.unpack i <> "#grid")

           i <- UI.input  # sink UI.value ( maybe "" (\(SText t) -> T.unpack t) <$> facts tdi)
           vci <- UI.valueChange i
           let tdie = unionWith const (Just .SText . T.pack <$> vci ) (rumors tdi)
           vi <- currentValue (facts tdi)
           tdib <- ui $ stepper   vi tdie
           let tdi2 = tidings tdib tdie
           let fty = ("iframe",UI.strAttr "src",maybe "" binarySrc ,[("width","100%"),("height","300px")])

           f <- pdfFrame fty (facts tdi2) # sink0 UI.style (noneShow . isJust <$> facts tdi2)
           fd <- UI.div # set UI.style [("display","inline-flex")] # set children [i]
           res <- UI.div # set children [fd,f]
           return (TrivialWidget tdi2 res)
         PMime mime -> do
           let binarySrc = (\(SBinary i) -> "data:" <> T.unpack mime <> ";base64," <>  (BSC.unpack $ B64.encode i) )
           clearB <- UI.button # set UI.text "clear"
           file <- UI.input # set UI.type_ "file" # set UI.multiple True # set UI.style (noneShow $ elem FWrite fm)
           fchange <- fileChange file
           clearE <- UI.click clearB
           cur2 <- ui $currentValue (facts tdi)
           let evi2 = foldl1 (unionWith const) [ rumors tdi,const Nothing <$> clearE,  (trace "fchange" . join . fmap (either (const Nothing) (Just . SBinary).   B64.decode .  BSC.drop 7. snd  . BSC.breakSubstring "base64," . BSC.pack ) <$> fchange)]
           bdi2 <- ui $ stepper cur2  evi2
           let
             tdi2 = tidings bdi2 evi2
             fty = case mime of
               "application/pdf" -> pdfFrame ("iframe" ,UI.strAttr "src",maybe "" binarySrc ,[("width","100%"),("height","300px")])
               "application/x-ofx" ->pdfFrame  ("textarea", UI.value ,maybe "" (\(SBinary i) -> BSC.unpack i) ,[("width","100%"),("height","300px")])
               "text/xml" ->pdfFrame  ("textarea", UI.value ,maybe "" (\(SBinary i) -> BSC.unpack i) ,[("width","100%"),("height","300px")])
               "application/gpx+xml" ->pdfFrame  ("textarea", UI.value ,maybe "" (\(SBinary i) -> BSC.unpack i) ,[("width","100%"),("height","300px")])
               "image/jpg" -> (\i -> pdfFrame ("img" ,UI.strAttr "src",maybe "" binarySrc ,[("max-height","200px")]) i # set UI.class_ "img-responsive")
               "image/png" -> pdfFrame ("img" ,UI.strAttr "src",maybe "" binarySrc ,[("max-height","200px")])
               "image/bmp" -> pdfFrame ("img" ,UI.strAttr "src",maybe "" binarySrc ,[("max-height","200px")])
               "text/html" -> pdfFrame ("iframe" ,UI.strAttr "srcdoc",maybe "" (\(SBinary i) -> BSC.unpack i) ,[("width","100%"),("height","300px")])
           f <- fty bdi2  # sinkDiff UI.style (noneShow. isJust <$> tdi2)
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
            pk <- ui $ stepper v  pke
            let pkt = tidings pk (diffEvent pk pke)
            sp <- UI.div # set UI.children [inputUI ]
            runFunctionDelayed inputUI  $ ffi "new jscolor(%1)" inputUI
            onChanges f (\f -> runFunctionDelayed inputUI  $ ffi "updateColor(%1,%2)" inputUI (maybe "FFFFFF" renderPrim  f))
            return $ TrivialWidget pkt sp
         z -> do
            oneInput tdi []
  where
    oneInput :: Tidings (Maybe Showable) -> [Element] ->  UI (TrivialWidget (Maybe Showable))
    oneInput tdi elem = do
            v <- currentValue (facts tdi)
            inputUI <- UI.input # sinkDiff UI.value (maybe "" renderPrim <$> tdi) # set UI.style [("width","100%")] -- # if [FRead] == fm then (set (UI.strAttr "readonly") "") else id
            onCE <- UI.onChangeE inputUI

            let pke = unionWith const (readPrim i <$> onCE ) (rumors tdi)
            pk <- ui $ stepper v  pke
            sp <- UI.div # set children (inputUI : elem)
            return $ TrivialWidget(tidings pk pke) sp





iUITableDiff
  :: InformationSchema
  -- Plugin Modifications
  -> SelPKConstraint
  -> PluginRef (Column CoreKey (Showable))
  -- Selected Item
  -> Tidings (Maybe (Column CoreKey Showable))
  -- Static Information about relation
  -> Column CoreKey ()
  -> UI (TrivialWidget (Editor (Index (Column CoreKey Showable))))
iUITableDiff inf constr pmods oldItems  (IT na  tb1)
  = fmap (fmap (PInline  na) )<$> go (unConstr <$> constr) (keyType na)   (fmap (fmap (fmap (patchfkt))) <$> pmods) (fmap _fkttable <$> oldItems)
  where
    unConstr (i,j) = (i, (\j -> (\v -> j $ IT na <$> v)) <$> j )
    go constr mt pmods oldItems =  case mt of
      Primitive (RecordPrim tn) ->  do
        coldItems <- ui $ cacheTidings oldItems
        let tdata = allRec' (tableMap inf) table
            convertConstr ([pre],j) =  (\i -> ([i],(\j -> (\v -> j [(TB1 (tblist (fmap addDefault (_tb <$> L.delete i attrs) ++ (_tb <$> v))))])) <$> j )) <$> attrs
              where attrs = fmap unTB $ F.toList $ unKV $ snd $ unTB1 $ _fkttable pre
            table = lookTable rinf (snd tn)
            rinf = fromMaybe inf (HM.lookup (fst tn) (depschema inf))

        (celem,tcrud) <- eiTableDiff inf (concat $ convertConstr <$> constr)
                []
                (fmap (fmap(fmap unAtom))<$> pmods)
                tdata
                (fmap unTB1<$>coldItems)

        let bres =  (fmap ( PAtom )<$> tcrud)
        return $ TrivialWidget bres celem
      KOptional tb1 -> do
        let convertConstr (i,j) = (i,(\j -> (\v -> j $ LeftTB1. Just <$> v)) <$> j)
        tr <- go (convertConstr <$>constr )tb1 ( fmap (fmap (join . fmap (\(POpt i ) -> i)))<$> pmods) (join . fmap unSOptional' <$> oldItems)
        let
          test Delete  _ = Diff $ POpt Nothing
          test Keep _ = Keep
          test (Diff i ) _ = Diff (POpt (Just  i))
        return $ TrivialWidget ( test <$> triding tr <*> oldItems) (getElement tr)

      KArray tb1  -> mdo
        offsetDiv  <- UI.div
        -- let wheel = fmap negate $ mousewheel offsetDiv
        TrivialWidget offsetT offset <- offsetField (pure 0)  never (maybe 0 (Non.length .unArray) <$> (recoverEditChange <$> oldItems <*> bres))
        element offset # set UI.class_ "col-xs-2 pull-right label label-default"
        let arraySize = 8
            tdi2  = fmap unArray <$>oldItems
            index o ix v = flip Non.atMay (o + ix)  <$> v
        let unIndexEl ix = filterT $ index ix <$> offsetT <*> tdi2
            dyn = dynHandlerPatch  (\ix valix ->do
              wid <- go constr tb1 (fmap (fmap ((\p -> filterT $ (\ o v -> convertPatchSet (o + ix) <$> v ) <$> offsetT <*>p))) pmods) valix
              lb <- hlabel ["col-xs-1"] # sink UI.text (show . (+ix) <$> facts offsetT )
              paintEditDiff lb (facts (triding wid ))
              element wid # set UI.class_ "col-xs-12"
              row <- UI.div # set children [lb,getElement wid]
              return $ TrivialWidget (triding wid) row ) unIndexEl

        widgets <- fst <$> foldl' (\i j -> dyn j =<< i ) (return ([],(pure True))) [0..arraySize -1 ]
        let
          widgets2 = Tra.sequenceA (  zipWith (\i j -> (i,) <$> j) [0..] $( triding <$> widgets) )
          bres = reduceDiffList  <$> offsetT <*>  widgets2
        element offsetDiv # set children (fmap getElement widgets)
        composed <- UI.span # set children [offset , offsetDiv]
        return  $ TrivialWidget  bres composed


type PluginRef a = [([Access Key], Tidings (Maybe (Index a)))]

offsetFieldFiltered  initT eve maxes = do
  init <- currentValue (facts initT)
  offset <- UI.span# set (attr "contenteditable") "true" #  set UI.style [("width","50px")]

  lengs  <- mapM (\max -> UI.span # sink text (("/" ++) .show  <$> facts max )) maxes
  offparen <- UI.div # set children (offset : lengs) # set UI.style [("border","2px solid black"),("margin-left","4px") , ("margin-right","4px"),("text-align","center")]

  enter  <- UI.onChangeE offset
  whe <- UI.mousewheel offparen
  let max  = facts $ foldr1 (liftA2 min) maxes
  let offsetE =  filterJust $ (\m i -> if i <m then Just i else Nothing ) <$> max <@> (filterJust $ readMaybe <$> enter)
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



offsetField  initT eve  max = do
  init <- currentValue (facts initT)
  offset <- UI.span# set (attr "contenteditable") "true" #  set UI.style [("width","50px")]
  leng <- UI.span # sink text (("/" ++) .show  <$> facts max )
  offparen <- UI.div # set children [offset,leng] # set UI.style [("margin-left","4px") , ("margin-right","4px"),("text-align","center")]

  offsetEnter <- UI.onChangeE offset
  we <- UI.mousewheel offparen
  let offsetE =  filterJust $ (\m i -> if i <m then Just i else Nothing ) <$> facts max <@> (filterJust $ readMaybe <$> offsetEnter)
  let
      ev = unionWith const (negate <$>  we) eve
      saturate m i j
          | m == 0 = 0
          | i + j < 0  = 0
          | i + j > m - 1  = m - 1
          | otherwise = i + j
      diff o m inc
        | saturate m inc o /= o = Just (saturate m inc )
        | otherwise = Nothing

  (offsetB ,ev2) <- mdo
    let
      filt = ( filterJust $ diff <$> offsetB <*> facts max <@> ev  )
      ev2 = (fmap concatenate $ unions [fmap const offsetE,filt ])
    offsetB <- ui $ accumB 0 (  ev2)
    return (offsetB,ev2)
  element offset # sink UI.text (show <$> offsetB)
  let
     cev = flip ($) <$> offsetB <@> ev2
     offsetT = tidings offsetB cev
  return (TrivialWidget offsetT offparen)


tbrefM i@(FKT _  _ _)  =  unkvlist $_tbref i
tbrefM j = [_tb  j ]


isReadOnly (FKT ifk rel _ ) = L.null (unkvlist ifk ) || all (not . any ((/= FRead)). keyModifier . _relOrigin) rel
isReadOnly (Attr k _ ) =  (not . any ((/= FRead)). keyModifier ) k
isReadOnly (IT k _ ) =   (not . any ((/= FRead)). keyModifier ) k

fkUITableDiff
  ::
  InformationSchema
  -- Plugin Modifications
  -> SelTBConstraint
  -> PluginRef  (Column CoreKey Showable)
  -- Same Table References
  -> [(Column CoreKey () ,Tidings (Maybe (Column CoreKey (Showable))))]
  -- Relation Event
  -> Tidings (Maybe (Column CoreKey Showable))
  -- Static Information about relation
  -> Column CoreKey ()
  -> UI (TrivialWidget(Editor (Index (Column CoreKey Showable))))
fkUITableDiff preinf constr  plmods nonInjRefs   oldItems  tb@(FKT ifk rel tb1@(TB1 tbdata@(m,_)  ) ) =  do
      -- Top Level Widget
      pan <- UI.div #  set UI.class_ "col-xs-5 fixed-label"
      top <- UI.div
      esc <- onEsc top
      panC <- UI.click pan
      let eh  = (unionWith const (const False <$> esc) ((const True <$> panC)  ))
      bh <- ui $ stepper False  eh
      (elsel , helsel ) <- ui newEvent
      (eledit , heledit) <- ui newEvent
      itemDClick <- UI.dblclick top
      let itemDClickE = fmap (const not) itemDClick
      bop <- ui$accumT False itemDClickE
      let evlsel' = unionWith const elsel  (const Keep <$> rumors oldItems)
          relTable = M.fromList $ fmap (\(Rel i _ j ) -> (j,i)) rel
      blsel <- ui $ stepper Keep evlsel'

      let
        selector False = do
          let ftdi = F.foldl' (liftA2 mergePatches) oldItems (snd <$> plmods)
          ui $ (\i -> onEventIO (rumors i) heledit) $ liftA2 editor oldItems ftdi
          return []
        selector True = mdo
          let
            inf = fromMaybe preinf $ HM.lookup (_kvschema m) (depschema preinf)
            table = lookTable inf  (_kvname m)
          reftb@(vpt,_,gist,sgist,_) <- ui $ refTables inf   table
          let ftdi = F.foldl' (liftA2 mergePatches)  oldItems (snd <$>  plmods)
          let
            replaceKey :: TB Identity CoreKey a -> TB Identity CoreKey a
            replaceKey =  firstTB (\k -> maybe k id  $ fmap _relTarget $ L.find ((==k)._relOrigin) $  rel)
            replaceRel a =  (fst $ search (_relOrigin $ head $ (keyattri a  )),  firstTB (\k  -> snd $ search k ) a)
                where  search  k = let v = justError ("no key" <> show k )$ L.find ((==k)._relOrigin)  rel in (_relOperator v , _relTarget v)
            iold2 :: Tidings (Maybe [TB Identity CoreKey Showable])
            iold2 =  fmap (fmap ( uncurry Attr) . concat) . allMaybesEmpty  <$> iold
                where
                  iold :: Tidings [Maybe [(CoreKey,FTB Showable)]]
                  iold  = Tra.sequenceA $ fmap (fmap ( aattr . _tb ) ) . snd <$> nonInjRefs
            ftdi2 :: Tidings (Maybe [TB Identity CoreKey Showable])
            ftdi2 =   fmap (fmap unTB. tbrefM ) <$> ftdi
            applyConstr m l =  filter (foldl' (\l constr ->  liftA2 (&&) l (not <$> constr) ) (pure True)  l) m
            constrT =  Tra.sequenceA $ fmap snd constr
            sortList :: Tidings ([TBData CoreKey Showable] -> [TBData CoreKey Showable])
            sortList =  sorting' <$> pure (fmap ((,True)._relTarget) rel)
          let
            vv :: Tidings (Maybe [TB Identity CoreKey Showable])
            vv =   join .   fmap (\i -> if  L.length i == L.length rel then Just i else Nothing) .fmap L.nub <$>  liftA2 (<>) iold2  ftdi2
          cvres <- currentValue (facts vv)
          filterInp <- UI.input # set UI.class_ "col-xs-3"
          filterInpE <- UI.valueChange filterInp
          filterInpBh <- ui $ stepper "" filterInpE
          iniGist <- currentValue (facts gist)
          iniSgist <- currentValue (facts sgist)
          itemListEl <- UI.select #  set UI.class_ "col-xs-5 fixed-label" # set UI.size "21" # set UI.style ([("position","absolute"),("z-index","999"),("top","22px")] )

          wheel <- fmap negate <$> UI.mousewheel itemListEl
          let
              pageSize = 20
              lengthPage fixmap = (s  `div` pageSize) +  if s `mod` pageSize /= 0 then 1 else 0
                where (s,_) = fromMaybe (sum $ fmap fst $ F.toList fixmap ,M.empty ) $ M.lookup mempty fixmap
              cv = join $ searchGist relTable m iniGist iniSgist <$>cvres

          let
              filterInpT = tidings filterInpBh filterInpE
              filtering i  = T.isInfixOf (T.pack $ toLower <$> i) . T.toLower . T.pack . showFKText
              predicatefk o = (WherePredicate $AndColl $ catMaybes $ fmap ((\(Attr k v) -> PrimColl . (keyRef k, ) . Left . (,Flip $ _relOperator $ justError "no rel" $ L.find (\i ->_relTarget i == k) rel) <$> unSOptional' v). replaceKey)  o)
              preindex = (\i -> maybe id (\i -> filterfixed (lookTable inf (_kvname m))(predicatefk i))i ) <$>iold2 <*>gist
          presort <- ui $ cacheTidings (sortList <*> fmap G.toList  preindex)
          -- Filter and paginate
          (offset,res3)<- do
            let constr = liftA2 applyConstr presort constrT

            res3 <- ui$ cacheTidings (filter .filtering  <$> filterInpT <*> constr)
            element itemListEl # sink UI.size (show . (\i -> if i > 21 then 21 else (i +1 )) . length <$> facts res3)

            offset <- offsetField ((\j i -> maybe 0  (`div`pageSize) $ join $ fmap (\i -> L.elemIndex i j ) i )<$>  (facts res3) <#> (fmap (unTB1._fkttable )<$> ftdi)) wheel  (lengthPage <$> vpt)
            return (offset, res3)
          tdi <- ui $ cacheTidings ((\g s v -> join $ searchGist relTable m  g s  <$> v) <$> gist  <*> sgist <*> vv)
          -- Load offseted items
          ui $onEventDyn (filterE (isJust . fst) $ (,) <$> facts iold2 <@> rumors (triding offset)) $ (\(o,i) ->  traverse (\o -> do
            transactionNoLog inf $ selectFrom (_kvname m) (Just $ i `div` (opsPageSize $ schemaOps inf) `div` pageSize) Nothing  [] (predicatefk  o)) o  )

          ui $onEventDyn (filterE (\(a,b,c)->isJust c && isNothing a ) $ (,,) <$> facts tdi <*> facts (triding offset)<@> diffEvent (facts iold2)(rumors iold2) ) $ (\(v0,i,o) ->  traverse (\o -> do
            transactionNoLog inf $ selectFrom (_kvname m) (Just $ i `div` (opsPageSize $ schemaOps inf) `div` pageSize) Nothing  [] (predicatefk   o)) o  )
          -- Select page
          res4 <- ui$ cacheTidings ((\o -> L.take pageSize . L.drop (o*pageSize) ) <$> triding offset <*> res3)

          metaMap <- mapWidgetMeta inf
          let
              hasMap = L.find ((== (lookTable inf (_kvname m))).(Le.^._2)) metaMap
              add i m =  if i then (m:) else id

          navMeta  <- buttonDivSet (add (isJust hasMap) "M" ["B"]) (fmap Just $pure (maybe "B" (const "M") hasMap )) (\i -> UI.button # set UI.text i # set UI.style [("font-size","smaller")] # set UI.class_ "buttonSet btn-xs btn-default btn pull-right")

          itemList <- do
              (elbox ,helbox) <- ui  newEvent
              lboxeel <- mapUIFinalizerT pan (\(metamap) ->
                          case metamap of
                            "B" -> do
                              lbox <- listBoxEl itemListEl ((Nothing:) . fmap (Just ) <$>    res4 ) (fmap Just <$> tdi) (pure id) ((\i -> maybe id (i$) )<$> showFK )
                              onEvent (rumors $ triding lbox) (liftIO . helbox)
                              return $ itemListEl
                            "M" -> do
                              let selection = (fromJust hasMap)
                              t <- liftIO $ getCurrentTime
                              TrivialWidget i el <- mapSelector inf selection (pure (t,"month")) tdi (never, pure Nothing)
                              onEvent (rumors $ i ) (liftIO . helbox.Just)
                              return el
                                        ) (triding navMeta)

              elembox <- UI.div # sink children (pure <$> facts lboxeel)

              let evbox = (unionWith const (fmap Just <$> rumors tdi) elbox )
              blbox <- ui $ stepper (fmap Just cv) evbox
              let
                lbox = TrivialWidget (tidings blbox  evbox) elembox
                selCh = rumors (triding lbox)

              config <- UI.div # set children [filterInp,getElement offset,getElement navMeta]
              elout <- UI.div # set children [config,elembox]
              return (TrivialWidget  (triding lbox) elout)

          let evsel =  unionWith const (rumors tdi)  (rumors $ join <$> triding itemList)
          prop <- ui $ stepper cv evsel
          let tds = tidings prop evsel
          let
            fksel =  join . fmap (\box ->  (\ref -> FKT (kvlist $ fmap _tb $ ref ) rel (TB1 box) ) <$> backFKRef relTable  (fmap (keyAttr .unTB ) $ unkvlist ifk)   box ) <$>   tds
            diffFK (Just i ) (Just j) = if tbrefM i == tbrefM j then Keep else Diff(patch j)
            diffFK (Just i ) Nothing = Delete
            diffFK Nothing Nothing = Keep
            diffFK Nothing (Just i) = Diff $ patch i
            output = diffFK <$> oldItems <*> fksel
          inioutput <- ui $ currentValue (facts output)
          ui $ onEventIO (rumors output) (liftIO .helsel)
          return [getElement itemList]

        edit =  do
          let
            inf = fromMaybe preinf $ HM.lookup (_kvschema m) (depschema preinf)
            table = lookTable inf  (_kvname m)
          reftb@(vpt,_,gist,sgist,_) <- ui $ refTables inf   table
          let ftdi = flip recoverEditChange <$> tidings blsel evlsel' <*> oldItems -- F.foldl' (liftA2 mergePatches)  oldItems  (snd <$>  plmods)
          let
            replaceKey :: TB Identity CoreKey a -> TB Identity CoreKey a
            replaceKey =  firstTB (\k -> maybe k id  $ fmap _relTarget $ L.find ((==k)._relOrigin) $  rel)
            replaceRel a =  (fst $ search (_relOrigin $ head $ (keyattri a  )),  firstTB (\k  -> snd $ search k ) a)
                where  search  k = let v = justError ("no key" <> show k )$ L.find ((==k)._relOrigin)  rel in (_relOperator v , _relTarget v)
            staticold :: [(TB Identity CoreKey () ,Tidings(Maybe (TB Identity CoreKey (Showable))))]
            staticold  =  second (fmap (fmap replaceKey )) . first replaceKey  <$> filter (all (\i ->  not (isInlineRel i ) &&  ((_relOperator i) == Equals)). keyattri.fst ) nonInjRefs

          (celem,pretdi) <- dynCrudUITable inf (fmap (\i -> if i then "+" else "-")$ bop ) reftb staticold (fmap (fmap (fmap (unAtom. patchfkt))) <$> plmods)  tbdata (fmap (unTB1._fkttable )<$> ftdi )
          let
            fksel =  fmap (\box ->  maybe (FKT (kvlist []) rel (TB1 box) )(\ref -> FKT (kvlist $ fmap _tb $ ref ) rel (TB1 box) ) $ backFKRef relTable  (fmap (keyAttr .unTB ) $ unkvlist ifk)   box ) <$>   pretdi
            -- diffFK i j | traceShow (tableName table,isJust i, isJust j) False  =  undefined
            diffFK (Just i ) (Just j) =  maybe Keep Diff (diff i  j)
            diffFK (Just i ) Nothing = Delete
            diffFK Nothing Nothing = Keep
            diffFK Nothing (Just i) = Diff $ patch i
            output = diffFK <$> oldItems<*>fksel
          inioutput <- ui $ currentValue (facts output)
          ui $ onEventIO (rumors output) (liftIO .heledit)
          return celem

      let
          evsel = unionWith const (unionWith const elsel eledit) (const Keep <$> rumors oldItems)
      blsel <- ui$ stepper Keep evsel
      element pan#  sink text (maybe "" (L.take 50 . L.intercalate "," . fmap renderShowable . allKVRec' . unTB1 . _fkttable )  <$>  (recoverEditChange <$> facts oldItems <*>blsel)) # set UI.style [("border","1px solid gray"),("border-radius","4px"),("height","20px")]
      selEls <- mapUIFinalizerT top selector  (tidings bh  eh)
      subnet <- UI.div  # sink children (facts selEls)
      subnet2 <- edit
      hidden <- UI.div  # set children [subnet,last subnet2] # set UI.class_ "col-xs-12"
      element top # set children [head subnet2,pan,hidden]
      return $ TrivialWidget  (tidings blsel evsel) top
fkUITableDiff inf constr plmods  wl oldItems  tb@(FKT ilk rel  (LeftTB1 (Just tb1 ))) = do
  tr <- fkUITableDiff inf constr (fmap (join . fmap unLeftItensP  <$>) <$> plmods)  (first unLeftKey . second (join . fmap unLeftItens <$>) <$> wl) (join . fmap unLeftItens  <$> oldItems)  (FKT (kvlist $ mapComp (firstTB unKOptional) <$> unkvlist ilk  ) (Le.over relOri unKOptional <$> rel) tb1)
  return $ reduceFKOptional rel (_relOrigin . head . keyattr <$> F.toList (_kvvalues ilk) )<$> tr

fkUITableDiff inf constr preplmods  wl preoldItems  tb@(FKT ifk rel  (ArrayTB1 (tb1:| _)) ) = mdo
     dv <- UI.div
     oldItems <- ui $ cacheTidings preoldItems
     plmods <- ui $ traverse (traverse cacheTidings) preplmods
     let -- wheel = fmap negate $ mousewheel dv
         arraySize = 8
     TrivialWidget offsetT offset <- offsetField (pure 0)  never (maybe 0 (Non.length .unArray. _fkttable ) <$> (recoverEditChange <$> oldItems <*> bres))
     let
         fkst = FKT (mapKV (mapComp (firstTB unKArray)) ifk ) (fmap (Le.over relOri (\i -> if isArray (keyType i) then unKArray i else i )) rel)  tb1
         dyn = dynHandlerPatch  recurse (\ix -> fmap join $ unIndexItens ix <$> offsetT  <*>  oldItems)
         convertPatchSet ix (PatchSet p) = patchSet $ catMaybes $ fmap (convertPatchSet ix ) (F.toList p)
         convertPatchSet ix (PIdx ix2 p)
              | ix == ix2 = p
              | otherwise = Nothing


         recurse ix oix = do
           TrivialWidget tr el<-  fkUITableDiff inf constr (fmap (\i ->  filterT $ (unIndexItensP  ix )<$> offsetT <*> i) <$> plmods) wl oix fkst
           lb <- hlabel ["col-xs-1"] # sink UI.text (show . (+ix) <$> facts offsetT )
           paintEditDiff lb (facts tr)
           element el # set UI.class_ "col-xs-12"
           TrivialWidget tr <$> UI.div # set UI.children [lb,el]
     fks <- fst <$> foldl' (\i j -> dyn j =<< i ) (return ([],(pure True))) [0..arraySize -1 ]

     element dv # set children (getElement <$> fks)
     element offset # set UI.class_ "col-xs-2 pull-right label label-default"

     let
          widgets2 = Tra.sequenceA (  zipWith (\i j -> (i,) <$> j) [0..] $( triding <$> fks) )
          bres0 = reduceDiffListFK <$> offsetT <*>  widgets2
          loadRes (i,j) = PFK rel [PAttr  (_relOrigin $ head $ keyattr $ head $ F.toList $ _kvvalues ifk) i] j
          bres = fmap (head.compact) . reduceTable <$> sequenceA ((fmap loadRes  <$> bres0) : [])
     res <- UI.div # set children [offset ,dv]
     return $  TrivialWidget bres  res

reduceTable l
  | L.any isDelete l = Delete
  | otherwise  = (\i -> if L.null i then Keep else Diff i) . filterDiff $ l

pdfFrame (elem,sr , call,st) pdf = mkElement (elem ) UI.# sink0 sr (call <$> pdf)  UI.# UI.set style (st)


unRels (RelAccess l k) =  unRels k
unRels k = k

unRel :: Show a =>Rel Key -> [Column Key a ] -> Column Key a
unRel (Rel k _ _ ) ilk =  index  ilk
  where
     index = justError "no index" . L.find ((==[Inline k]).  keyattri )
unRel (RelAccess k l)  ilk = unRel l nref
   where
     nref = (fmap unTB . F.toList . unKV . snd . unTB1 . _fkttable . index $  ilk )
     index = justError "no index" . L.find ((==[Inline k]).  keyattri )

data AscDesc a
  = AscW a
  | DescW a
  deriving(Eq)

instance Ord a => Ord (AscDesc a) where
  compare (AscW a ) (AscW b) =  compare a b
  compare (DescW a ) (DescW b) = compare (Down a ) (Down b)

sorting' :: Ord k=> [(k ,Bool)] -> [TBData k Showable]-> [TBData k Showable]
sorting' ss  =  L.sortBy (comparing   (L.sortBy (comparing fst) . fmap (\((ix,i),e) -> (ix,if i then DescW e  else AscW e) ) . F.toList .M.intersectionWith (,) (M.fromList (zipWith (\i (k,v) -> (k ,(i,v))) [0::Int ..] ss)) . M.fromList . concat . fmap aattr  . F.toList . _kvvalues . unTB . snd )  )


rendererShowableUI k  v= renderer (keyValue k) v
  where renderer "modification_data" (SBinary i) = either (\i-> UI.div # set UI.text (show i)) (\(_,_,i ) -> showPatch (i:: PathAttr Text Showable) )  (B.decodeOrFail (BSL.fromStrict i))
        renderer "exception" (SBinary i) = either (\i-> UI.div # set UI.text (show i)) (\(_,_,i ) -> UI.div # set UI.text (T.unpack i))  (B.decodeOrFail (BSL.fromStrict i))
        renderer k i = UI.div # set text (renderPrim i)
        showPatch l = UI.div # set text (show $ fmap renderPrim l)

foldMetaHeader = foldMetaHeader' []

foldMetaHeader' :: [CoreKey] -> UI Element -> (CoreKey -> a -> (UI Element)) -> InformationSchema -> TBData CoreKey a -> [UI Element]
foldMetaHeader' order el rend inf = mapFAttr order (\(Attr k v) -> hideLong (F.toList $ rend  k <$> v ))
    where
          mapFAttr order f (a,kv) = fmap snd. L.sortBy (comparing ((flip L.elemIndex order).  fst) ). concat $ (  fmap (match.unTB ) .  F.toList .  _kvvalues)  $ unTB kv
            where match i@(Attr k v) = [(k,f i)]
                  match i@(FKT l rel t) = ((\k -> (_relOrigin $ head $ keyattr k ,). f . unTB  $ k)<$> unkvlist l )
                  match i@(IT l t) = [( l,hideLong ( concat $ F.toList $ fmap (foldMetaHeader  UI.div rend inf) t))]
          hideLong l = do
            elemD <- el
            if length l > 1
              then do
                hoverFlag  <- hoverTip elemD
                bh <- ui $ stepper False hoverFlag
                element elemD # sink items ((\b -> if not b then take 2  l  <> fmap ( set UI.style (noneShow False)) (drop 2 l) else  l ) <$> bh)
              else return elemD # set items l

hoverTip elemD= do
  ho <- UI.hover elemD
  le <- UI.leave elemD
  return $ unionWith const (const True <$> ho) (const False <$> le )

hoverTip2 elemIn elemOut = do
  ho <- UI.click elemIn
  le <- UI.leave elemOut
  return $ unionWith const (const True <$> ho) (const False <$> le )

tableIndexA inf metaname env =   do
  let modtable = lookTable inf tname
      tname = metaname
  viewer inf modtable env


metaAllTableIndexA inf metaname env =   do
  let modtable = lookTable (meta inf) tname
      tname = metaname
  viewer (meta inf) modtable (Le.over (_1) (liftAccess (meta inf)tname)  <$> env)



sortFilter :: [CoreKey] -> [(CoreKey,Bool)] -> [(CoreKey,(Text,Text))] -> UI Element -> UI Element -> ((CoreKey,Maybe Bool) -> String) -> UI (TrivialWidget [(CoreKey,Maybe Bool,Maybe (String,FTB Showable))])
sortFilter l sel fil liste slote conv = do
    tds <- list liste slote (sortFilterUI conv) ((\i j -> fmap (\e -> (e,,Nothing)  $ fmap snd $  L.find ((==e).fst) j) i ) l sel)
    return $ TrivialWidget (triding tds) (getElement tds)

validOp = ["&&","<@","@>","<",">","=","/=","<=",">="]
readValid = (\v -> if elem v validOp then Just v else Nothing)

sortFilterUI conv ix bh  = do
    let
        step t = case t of
                Just True -> Just False
                Just False -> Nothing
                Nothing -> Just True
    dv <- UI.div # sink text ((\(a,b,_) -> conv (a,b) )<$> bh)
    op <- UI.input # set UI.style [("width","50px")]
    vf <- UI.input # set UI.style [("width","80px")]
    fi <- UI.button # set text "go"
    opE <- UI.valueChange op
    vfE <-  UI.valueChange vf
    opB <- ui $ stepper "" opE
    vfB <- ui $ stepper "" vfE

    dvC <- UI.click dv
    fiC <- UI.click fi
    let
        ev0 = flip (\(l,t,op,vf)-> const (l,step t,op,vf)) <$>  dvC
        ev1 = flip (\(l,t,op,vf) opn -> (l,t,(readValid opn) ,vf)) <$>  opB <@ fiC
        ev2 = flip (\(l,t,op,vf) vfn -> (l,t,op , (readType (keyType l) vfn))) <$>  vfB <@ fiC
    block <- UI.div # set children [dv,op,vf,fi]
    return $ TrivialWidget (tidings bh ((\ini@(l,t,op) f -> (\(l,t,op,v) -> (l , t ,liftA2 (,) op v)) $ f (l,t,fmap fst op , fmap snd op) ) <$> bh <@> (concatenate <$> unions [ev0,ev1,ev2]) )) block




filterT ::  Tidings (Maybe (Maybe a)) -> Tidings (Maybe a)
filterT = fmap join
-- filterT j = tidings (join  <$>  facts j ) (fmap join $ filterE (maybe True isJust ) $  rumors j )

viewer :: InformationSchema -> Table -> [(Access Key ,AccessOp Showable )] -> UI Element
viewer inf table envK = mdo
  let
      filterStatic =filter (not . flip L.elem (concat $ fmap (F.toList . (Le.view Le._1)) envK))
      key = filterStatic $ F.toList $ rawPK table
      sortSet =  filterStatic . F.toList . tableKeys . tableNonRef . TB1 . allRec' (tableMap inf ) $ table
      tableSt2 =   tableViewNR (tableMap inf) table
  itemList <- UI.div
  let pageSize = 20
      iniPg =  M.empty
      iniSort = selSort sortSet ((,True) <$>  key)
  sortList <- sortFilter sortSet ((,True) <$> key) []  UI.tr UI.th conv

  let makeQ slist' (o,i) = do
              let slist = fmap (\(i,j,_) -> (i,j)) slist'
                  ordlist = (fmap (second fromJust) $filter (isJust .snd) slist)
                  paging  = (\o -> fmap (L.take pageSize . L.drop (o*pageSize)) )
                  flist = catMaybes $ fmap (\(i,_,j) -> (\(op,v) -> (keyRef i,Left (v,readBinaryOp $ T.pack op))) <$> j) slist'
              (_,(fixmap,lres)) <- transactionNoLog inf $ selectFrom (tableName table ) (Just o) Nothing  (fmap (\t -> if t then Desc else Asc ) <$> ordlist) (WherePredicate $ AndColl $ fmap PrimColl $envK <> flist)
              let (size,_) = justError ("no fix" <> show (envK ,fixmap)) $ M.lookup (WherePredicate$AndColl $ fmap PrimColl $  envK) fixmap
              return (o,(slist,paging o (size,sorting' ordlist (G.toList lres))))
      nearest' :: M.Map Int (TB2 CoreKey Showable) -> Int -> ((Int,Maybe (Int,TB2 CoreKey Showable)))
      nearest' p o =  (o,) $ safeHead $ filter ((<=0) .(\i -> i -o) .  fst) $ reverse  $ L.sortBy (comparing ((\i -> (i - o)). fst )) (M.toList p)
      ini = nearest' iniPg 0
      addT (c,(s,(cou,td))) = M.insert (c +1)  <$>  (fmap TB1 $ safeHead $reverse td)
  iniQ <- ui $ makeQ iniSort ini
  offset <- offsetField (pure 0 ) (never ) (ceiling . (/pageSize). fromIntegral <$> tidings offsetTotal never )
  let
      event1 , event2 :: Event (Dynamic (Int,([(CoreKey,Maybe Bool)],(Int,[TBData CoreKey Showable]))))
      event1 = (\(j,k) i  -> makeQ i (nearest' j k )) <$> facts ((,) <$> pure iniPg <*> triding offset) <@> rumors (triding sortList)
      event2 = (\(j,i) k  -> makeQ i (nearest' j k )) <$> facts ((,) <$> pg <*> triding sortList) <@> rumors (triding offset)
      evs = (unionWith const event1 event2)
  tdswhere <-  mapEventFin id evs
  offsetTotal <- ui $ stepper (fst $ snd $ snd $ iniQ) (fmap (fst . snd .snd ) tdswhere)
  pg <- ui $ accumT ((fromJust  $addT iniQ ) M.empty ) (unionWith (flip (.)) ((pure (const iniPg ) <@ event1)) (filterJust (addT <$> tdswhere )))

  tdswhereb <- ui $ stepper (snd iniQ) (fmap snd tdswhere)
  let
      tview = unTlabel' . unTB1  $tableSt2
  element itemList # set items ( pure . renderTableNoHeaderSort2   (return $ getElement sortList) inf (tableNonRef' tview) $   fmap (fmap ( tableNonRef')) . (\(slist ,(coun,tb))-> (fmap fst slist,tb))  <$>   tdswhereb )

  UI.div # set children [getElement offset, itemList]




renderTableNoHeaderSort2 header inf modtablei out = do
  let
      body sort o = UI.tr # set UI.class_ "row" #  set items (foldMetaHeader' sort UI.td rendererShowableUI inf $ o)
  header # set UI.class_ "row"
  UI.table # set UI.class_ "table table-bordered table-striped" # sink items ((\(i,l)-> header : fmap (body i) l )<$> out)


attrLine i   = do
  line ( L.intercalate "," (fmap renderShowable .  allKVRec'  $ i))



convertPatchSet ix (PatchSet p) = patchSet $ catMaybes $ fmap (convertPatchSet ix ) (F.toList p)
convertPatchSet ix (PIdx ix2 p)
              | ix == ix2 = p
              | otherwise = Nothing
