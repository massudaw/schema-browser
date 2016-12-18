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
import Control.Lens (_1,over,(^?),(&),(%~))
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

type RefTables = (Tidings (Collection CoreKey Showable),(Collection CoreKey Showable), Tidings (G.GiST (G.TBIndex  Showable) (TBData CoreKey Showable)), TChan [RowPatch KeyUnique Showable] )

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

pluginUI :: InformationSchema
    -> Tidings (Maybe (TBData CoreKey Showable) )
    -> Plugins
    -> UI (Element ,(Access Key,Tidings (Maybe (Index (TBData CoreKey Showable)))))
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
              v <- labelCaseDiff inf a  wn
              return  $ TrivialWidget (recoverEditChange <$> pre <*> triding v) (getElement v)

        attrB (const Nothing <$> trinp)  (genAttr oinf fresh )
           ) inpfresh
      let
        inp :: Tidings (Maybe (TBData CoreKey Showable))
        inp = fmap tblist <$> foldr (liftA2 (liftA2 (:))) (pure (Just [])) (fmap (fmap ( fmap _tb) .  triding) elemsIn )

      (preinp,(_,liftedE )) <- pluginUI  inf (liftA2 mergeTB1 <$>  unoldItems <*>  inp) (idp,FPlugins "Enviar" tname aci)

      elemsOut <- mapM (\fresh -> do
        let attrB pre a = do
              wn <-  tbCaseDiff inf  []  a [] [] pre
              TrivialWidget v e <- labelCaseDiff inf a  wn
              return $ TrivialWidget (recoverEditChange <$> pre <*> v ) e
        attrB (fmap (\v ->  unTB . justError ("no key " <> show fresh <> " in " <>  show v ) . fmap snd . getCompose . unTB . findTB1 ((== [fresh]) . fmap _relOrigin. keyattr ) $ TB1 (create v :: TBData Key Showable) )  <$> liftedE  )  (genAttr oinf fresh )
       ) outfresh

      let styleUI =  set UI.class_ "row"
            . set UI.style [("border","1px"),("border-color","gray"),("border-style","solid"),("margin","1px")]
      j<- UI.div # styleUI  # set children (fmap getElement elemsIn <> [preinp])# sink UI.style (noneShow .isJust <$> facts unoldItems)
      k <- UI.div # styleUI  # set children (fmap getElement elemsOut) # sink UI.style (noneShow .isJust <$> facts liftedE  )
      return  ( l <> [j , k] , liftA2 apply <$> facts unoldItems <#> liftedE  ))
           ) ) (return (([],trinp))) $ zip (fmap snd ac) freshKeys
  el <- UI.div  # set children (b: (fst freshUI))
  return (el , (liftAccess inf tname  $snd $ pluginStatic' $ snd $ last ac ,fmap (fmap patch) $  snd freshUI ))

pluginUI inf oldItems (idp,p@(FPlugins n t (PurePlugin arrow ))) = do
  let f =second (liftAccess inf t ). first (liftAccess  inf t ) $ staticP arrow
      action = pluginAction   p
      pred =  WherePredicate $ AndColl (catMaybes [ genPredicateFull True (fst f)])
      tdInputPre = join . fmap (\i -> if G.checkPred i pred  then Just i else Nothing) <$>  oldItems
      tdInput = tdInputPre
      predOut =  WherePredicate $ AndColl (catMaybes [ genPredicateFull True (snd f)])
      tdOutput = join . fmap (\i -> if G.checkPred i predOut  then Just i else Nothing) <$> oldItems
  headerP <- UI.button # set UI.class_ "btn btn-sm"# set text (T.unpack n)  # sink UI.enabled (isJust <$> facts tdInput)  # set UI.style [("color","white")] # sink UI.style (liftA2 greenRedBlue  (isJust <$> facts tdInput) (isJust <$> facts tdOutput))
  ini <- currentValue (facts tdInput )
  kk <- ui $ stepper ini (diffEvent (facts tdInput ) (rumors tdInput ))
  pgOut <- ui $mapTEventDyn (\v -> liftIO .fmap ( join .  liftA2 diff v . fmap (liftTable' inf t).  join . eitherToMaybe ). catchPluginException inf (_tableUnique $ lookTable inf t) idp (M.toList $ getPKM $ justError "ewfew"  v) . action $  fmap (mapKey' keyValue) v)  (tidings kk $diffEvent kk (rumors tdInput ))
  return (headerP, (snd f ,   pgOut ))
pluginUI inf oldItems (idp,p@(FPlugins n t (DiffPurePlugin arrow ))) = do
  let f =second (liftAccess inf t ). first (liftAccess  inf t ) $ staticP arrow
      action = pluginActionDiff   p
      pred =  WherePredicate $ AndColl (catMaybes [ genPredicateFull True (fst f)])
      tdInputPre = join . fmap (\i -> if G.checkPred i pred  then Just i else Nothing) <$>  oldItems
      tdInput = tdInputPre
      predOut =  WherePredicate $ AndColl (catMaybes [ genPredicateFull True (snd f)])
      tdOutput = join . fmap (\i -> if G.checkPred i predOut  then Just i else Nothing) <$> oldItems
  headerP <- UI.button # set UI.class_ "btn btn-sm"# set text (T.unpack n)  # sink UI.enabled (isJust <$> facts tdInput)  # set UI.style [("color","white")] # sink UI.style (liftA2 greenRedBlue  (isJust <$> facts tdInput) (isJust <$> facts tdOutput))
  ini <- currentValue (facts tdInput )
  kk <- ui $ stepper ini (diffEvent (facts tdInput ) (rumors tdInput ))
  pgOut <- ui $mapTEventDyn (\v -> liftIO .fmap ( fmap (liftPatch inf t).  join . eitherToMaybe ). catchPluginException inf (_tableUnique $ lookTable inf t) idp (M.toList $ getPKM $ justError "ewfew"  v) . action $  fmap (mapKey' keyValue) v)  (tidings kk $diffEvent kk (rumors tdInput ))
  return (headerP, (snd f ,   pgOut ))
pluginUI inf oldItems (idp,p@(FPlugins n t (DiffIOPlugin arrow))) = do
  overwrite <- checkedWidget (pure False)
  let f = second (liftAccess inf t ). first (liftAccess inf t ) $ staticP arrow
      action = pluginActionDiff p
      pred =  WherePredicate $ AndColl (catMaybes [ genPredicateFull True (fst f)])
      tdInputPre = join . fmap (\i -> if G.checkPred i pred  then Just i else Nothing) <$>  oldItems
      tdInput = tdInputPre
      predOut =  WherePredicate $ AndColl (catMaybes [ genPredicateFull True (snd f)])
      tdOutput = join . fmap (\i -> if G.checkPred i predOut  then Just i else Nothing) <$> oldItems
  headerP <- UI.button # set UI.class_ "btn btn-sm"# set text (T.unpack n) # sink UI.enabled (isJust <$> facts tdInput)  #set UI.style [("color","white")] # sink UI.style (liftA2 greenRedBlue  (isJust <$> facts tdInput) (isJust <$> facts tdOutput))
  cliHeader <- UI.click headerP
  let ecv = facts tdInput <@ cliHeader
  vo <- currentValue (facts tdOutput)
  vi <- currentValue (facts tdInput)
  bcv <- ui $ stepper Nothing  ecv
  pgOut  <- ui $mapTEventDyn (\v -> do
    liftIO .fmap ( fmap (liftPatch inf t ). join . eitherToMaybe ) . catchPluginException inf (_tableUnique $ lookTable inf t) idp (M.toList $ getPKM $ justError "no Action"  v) $ ( action $ fmap (mapKey' keyValue) v)
                             )  (tidings bcv ecv)
  return (headerP, (snd f ,  pgOut ))


pluginUI inf oldItems (idp,p@(FPlugins n t (BoundedPlugin2 arrow))) = do
  overwrite <- checkedWidget (pure False)
  let f = second (liftAccess inf t ). first (liftAccess inf t ) $ staticP arrow
      action = pluginAction p
      pred =  WherePredicate $ AndColl (catMaybes [ genPredicateFull True (fst f)])
      tdInputPre = join . fmap (\i -> if G.checkPred i pred  then Just i else Nothing) <$>  oldItems
      tdInput = tdInputPre
      predOut =  WherePredicate $ AndColl (catMaybes [ genPredicateFull True (snd f)])
      tdOutput = join . fmap (\i -> if G.checkPred i predOut  then Just i else Nothing) <$> oldItems
  headerP <- UI.button # set UI.class_ "btn btn-sm"# set text (T.unpack n)  # sink UI.enabled (isJust <$> facts tdInput)  # set UI.style [("color","white")] # sink UI.style (liftA2 greenRedBlue  (isJust <$> facts tdInput) (isJust <$> facts tdOutput))
  cliHeader <- UI.click headerP
  let ecv = facts tdInput <@ cliHeader
  vo <- currentValue (facts tdOutput)
  vi <- currentValue (facts tdInput)
  bcv <- ui $ stepper Nothing ecv
  pgOut  <- ui $mapTEventDyn (\v -> do
    liftIO .fmap (join .  traceShowId .liftA2 diff v . traceShowId . fmap (liftTable' inf t ). join . eitherToMaybe ) . catchPluginException inf (_tableUnique $ lookTable inf t) idp (M.toList $ getPKM $ justError "no Action"  v) . action $ fmap (mapKey' keyValue) v
                             )  (tidings bcv ecv)
  return (headerP, (snd f ,  pgOut ))

indexPluginAttrDiff
  :: Column Key ()
  -> [(Access Key, Tidings (Maybe (Index (TBData Key Showable))))]
  -> [(Access Key, Tidings (Maybe (Index (Column Key Showable))))]
indexPluginAttrDiff a@(Attr i _ )  plugItens =  evs
  where
    match (IProd _ l ) ( IProd _ f) = L.sort l == L.sort f
    match i ( IProd _ f) = False
    thisPlugs = filter (hasProd (`match` (keyRef ( _relOrigin <$> keyattri a))) . fst)  plugItens
    evs  = fmap ( fmap ( join . fmap (\(_,_,p) -> L.find (((== S.fromList (keyattri a))  . pattrKey )) p )) ) <$>  thisPlugs
indexPluginAttrDiff  i  plugItens = pfks
  where
        thisPlugs = filter (hasProd (isNested ((keyRef $ fmap (_relOrigin) (keyattri i) ))) .  fst) plugItens
        pfks =  first (uNest . justError "No nested Prod FKT" .  findProd (isNested((keyRef $ fmap ( _relOrigin ) (keyattri i) )))) . second (fmap (join . fmap ((\(_,_,p) -> L.find (((== S.fromList (keyattri i))  . pattrKey )) p )))) <$> ( thisPlugs)


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
                       PDate -> (3,1)
                       PColor-> (3,1)
                       PTimestamp _ -> (3,1)
                       PDayTime -> (3,1)
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
  -> Column CoreKey ()
  -> TrivialWidget (Editor (Index (Column CoreKey Showable)))
  -> UI (TrivialWidget (Editor (Index (Column CoreKey Showable))))
labelCaseDiff inf a wid = do
    l <- flabel # set text (show $ _relOrigin <$> keyattri a)
    tip <- UI.div
    patch <- UI.div
    hl <- UI.div # set children [l,tip,patch]
    el <- UI.div #
      set children [hl,getElement wid] #
      set UI.class_ ("col-xs-" <> show (fst $  attrSize a))
    {- bh <- stepper False (hoverTip2 l hl)
    element patch #
      sink text (liftA2 (\bh -> if bh then id else const "") bh (facts $ fmap ( show . join) $ liftA2 diff <$> triding wid <*> old)) #
      sink0 UI.style (noneShow <$> bh)
    element tip #
      set text (show $ fmap showKey  <$> keyattri a) #
      sink0 UI.style (noneShow <$> bh)-}
    paintEditDiff l (facts (triding wid ))
    return $ TrivialWidget (triding wid) el

paintEditDiff e  i  = element e # sink0 UI.style ((\ m  -> pure . ("background-color",) $ cond  m  ) <$> i )
  where cond (Delete )  = "purple"
        cond (Keep ) = "blue"
        cond (Diff _) = "yellow"



labelCase
  ::  InformationSchema
  -> Column CoreKey ()
  -> Tidings (Maybe (Column CoreKey Showable))
  -> TrivialWidget (Maybe (Column CoreKey Showable))
  -> UI (TrivialWidget (Maybe (Column CoreKey Showable)))
labelCase inf a old wid = do
    l <- flabel # set text (show $ _relOrigin <$> keyattri a)
    el <- UI.div #
      set children [l,getElement wid] #
      set UI.class_ ("col-xs-" <> show (fst $  attrSize a))
    paintEdit l (triding wid ) (old)
    return $ TrivialWidget (triding wid) el


refTables' inf table page pred = do
        (ref,res)  <-  transactionNoLog inf $ selectFrom (tableName table ) page Nothing  [] pred
        return (liftA2 (,) (idxTid ref) (collectionTid ref),res,collectionTid ref,patchVar $ iniRef ref)


refTables inf table = refTables' inf table Nothing mempty

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
            oldItems =  maybe preoldItems (\v -> if L.null v then preoldItems else fmap (maybe (Just (FKT (kvlist $ fmap  (_tb . uncurry Attr)  v) rel (SerialTB1 Nothing) )) Just ) preoldItems  ) (Tra.traverse (\k -> fmap (k,) . keyStatic $ k ) ( getRelOrigin $ fmap unTB $ unkvlist ifk))
            nonInj =  (S.fromList $ _relOrigin   <$> rel) `S.difference` (S.fromList $ getRelOrigin $ fmap unTB $ unkvlist ifk)
            nonInjRefs = filter ((\i -> if S.null i then False else S.isSubsetOf i nonInj ) . S.fromList . fmap fst .  aattri .fst) wl
            relTable = M.fromList $ fmap (\i -> (_relTarget i,_relOrigin i)) rel
            rinf = fromMaybe inf $ HM.lookup (_kvschema m) (depschema inf)
            table = lookTable rinf  (_kvname m)
            m = (fst $ unTB1 tb1)
            pkset :: S.Set Key
            pkset = S.fromList $ rawPK table
            restrictConstraint = filter ((`S.isSubsetOf` pkset) . S.fromList . getRelOrigin  .fst) constr
            convertConstr :: SelTBConstraint
            convertConstr = (\(f,j) -> (f,) $ fmap (\constr -> constr .  backFKRef relTable (getRelOrigin f)  ) j ) <$>  restrictConstraint
        let
            patchRefs = fmap (\(a,b) -> (flip recoverEditChange ) <$> facts a <#> b ) <$> nonInjRefs
        ref <- ui $ refTables rinf   table
        v <-  fkUITableDiff rinf (convertConstr ) ref plugItens  patchRefs oldItems i
        return $ TrivialWidget  (triding v ) (getElement v)

tbCaseDiff inf _ i@(IT na tb1 ) wl plugItens oldItems
    = iUITableDiff inf plugItens oldItems i
tbCaseDiff inf _ a@(Attr i _ ) wl plugItens preoldItems = do
        let oldItems = maybe preoldItems (\v-> fmap (Just . fromMaybe (Attr i v)) preoldItems  ) ( keyStatic i)
        let tdiv = fmap _tbattr <$> oldItems
        attrUI <- buildUIDiff (keyModifier i) (keyType i) (fmap (fmap (\(PAttr _ v) -> v)) . snd <$> plugItens) tdiv
        let insertT = fmap (PAttr i ) <$> triding attrUI
        return $ TrivialWidget insertT  (getElement attrUI)
tbCaseDiff inf _ a@(Fun i rel ac ) wl plugItens preoldItems = do
  let
    search (IProd _ t) = fmap (fmap _tbattr ). uncurry recoverT .snd <$> L.find ((S.fromList t ==) . S.fromList . fmap _relOrigin . keyattri . fst) wl
    search (Nested (IProd _ t) m ) =  fmap (fmap joinFTB . join . fmap (traverse (indexFieldRec m) . _fkttable )). uncurry recoverT . snd <$> L.find ((S.fromList t ==) . S.fromList . fmap _relOrigin .keyattri . fst) wl
    refs = sequenceA $ catMaybes $ fmap search (snd rel)
  ev <- fmap (fmap (PFun i rel )) <$> buildUIDiff (keyModifier i)(keyType i) [] (fmap _tbattr . preevaluate i (fst rel) funmap (snd rel) <$> refs )
  return $ TrivialWidget (triding ev) (getElement ev)

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
      let check = foldl' (liftA2 (\j i ->  liftA2 apply j i <|> j <|> (create <$> i ))) (join . fmap unLeftItens  <$> preoldItems) (fmap (fmap (join . fmap unLeftItensP) . snd) plugItens )
      TrivialWidget btr bel <- checkedWidget  (isJust <$> check)
      (ev,h) <- ui $ newEvent
      inipre <- currentValue  (facts preoldItems)
      let fun True = do
              initpre <- currentValue (facts preoldItems)
              initpreOldB <- ui $ stepper initpre (rumors preoldItems)
              TrivialWidget btre bel <- tbCaseDiff inf constr a wl plugItens (tidings initpreOldB (rumors preoldItems) )
              ui $ onEventDyn (rumors btre) (liftIO . h )
              el <- UI.div # set children [bel]
              return el
          fun False = do
              UI.div
      sub <- UI.div # sink items  (pure .fun <$> facts btr ) # set UI.class_ "row"
      out <- UI.div # set children [bel,sub]
      binipre <- ui $ stepper  Keep ev
      return (TrivialWidget  (tidings binipre ev) out)

unTBMap :: Show a => TBData k a -> Map (Set (Rel k  )) (Compose Identity (TB Identity ) k a )
unTBMap = _kvvalues . unTB . snd

instance Applicative Editor where
  pure =Diff
  Diff f <*> Diff v = Diff $ f  v

eiTableDiff
  :: InformationSchema
     -> SelPKConstraint
     -> [(Column CoreKey () ,Tidings (Maybe (Column CoreKey Showable)))]
     -> PluginRef (TBData CoreKey Showable)
     -> TBData CoreKey ()
     -> Tidings (Maybe (TBData CoreKey Showable))
     -> UI (Element,Tidings (Editor (Index (TBData CoreKey Showable))))
eiTableDiff inf constr refs plmods ftb@(meta,k) oldItems = do
  let
      table = lookTable inf (_kvname meta)
  res <- mapM (pluginUI inf oldItems) (filter ((== rawName table ) . _bounds .snd ) (plugins inf) )
  let plugmods = first repl <$> (resdiff <> plmods)
      resdiff =   fmap ( liftA2 (\i j -> (join .liftA2 (\j i@(_,pk,_)   -> if  pk == G.getIndex j then Just i else Nothing ) i $ j ) <|> j ) oldItems   ) . snd <$> res
      repl (Rec  ix v ) = replace ix v v
      repl (Many[(Rec  ix v )]) = replace ix v v
      repl v = v
  fks :: [(Column CoreKey () ,(TrivialWidget (Editor (Index (Column CoreKey Showable))),Tidings (Maybe (Column CoreKey Showable))))]  <- foldl' (\jm (l,m)  -> do
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
              else labelCaseDiff inf (unTB m) nref

            return (w <> [(unTB m,(lab,aref))])
        ) (return []) (P.sortBy (P.comparing fst ) . M.toList $ replaceRecRel (unTBMap $ ftb) (fmap (fmap S.fromList )  <$> _kvrecrels meta))
  let
      sequenceTable :: [(Column CoreKey () ,(TrivialWidget (Editor (Index (Column CoreKey Showable))), Tidings (Maybe (Column CoreKey Showable))))] -> Tidings (Editor (Index (TBData CoreKey Showable)))
      sequenceTable fks = (\old difs -> (\ i ->  (fmap (tableMeta table , maybe (G.Idex [])G.getIndex old,)   ) i) . reduceTable $ difs) <$> oldItems <*> Tra.sequenceA (triding .fst . snd <$> fks)
      tableb =  sequenceTable fks

  (listBody,output) <- if rawIsSum table
    then do
      let
        initialSum = join . fmap ((\(n,  j) ->    fmap keyattr $ safeHead $ catMaybes  $ (fmap (_tb . fmap (const ()) ) . unOptionalAttr  . unTB<$> F.toList (_kvvalues (unTB j)))) ) <$>oldItems
        sumButtom itb =  do
           let i = unTB itb
           lab <- labelCaseDiff inf i  (fst $ justError ("no attr" <> show i) $ M.lookup (keyattri i) $ M.mapKeys (keyattri ) $ M.fromList fks)
           element lab #  set UI.class_ "buttonSet btn-xs btn-default"
      chk  <- buttonDivSet (F.toList (_kvvalues $ unTB k))  (join . fmap (\i -> M.lookup (S.fromList i) (_kvvalues (unTB k))) <$> initialSum ) sumButtom
      element chk # set UI.style [("display","inline-flex")]
      sequence $ (\(kix,(el,_)) -> element  el # sink0 UI.style (noneShow <$> ((==keyattri kix) .keyattr <$> facts (triding chk) ))) <$> fks
      let
          keypattr (PAttr i _) = [Inline i]
          keypattr (PInline i _) = [Inline i]
          keypattr (PFK  l  _ _) = l
          resei :: Tidings (Editor (Index (TBData CoreKey Showable)))
          resei = (\j -> fmap (\(m,i,l)  -> (m,i,L.filter ((== keyattr j) . keypattr) l))) <$> triding chk <*> tableb
      listBody <- UI.div #  set children (getElement chk : F.toList (getElement .fst .snd <$> fks))
      return (listBody, resei)
    else  do
      listBody <- UI.div # set UI.class_ "row" #
        set children (F.toList (getElement .fst . snd  <$> fks))
      return (listBody,tableb)
  element listBody # set UI.class_ "row" #
      set style [("border","1px"),("border-color","gray"),("border-style","solid"),("margin","1px")]
  plugins <-  if not (L.null (fst <$> res))
    then do
      pure <$> UI.div # set children (fst <$> res)
    else do
      return []
  body <- UI.div #
     set children (plugins  <> pure listBody) #
     set style [("margin-left","0px"),("border","2px"),("border-color","gray"),("border-style","solid")]
  return (body, output)



crudUITableDiff
   :: InformationSchema
   -> Tidings String
   -> RefTables
   -> [(TB Identity CoreKey () ,Tidings (Maybe (TB Identity CoreKey Showable)))]
   -> PluginRef (TBData CoreKey Showable)
   -> TBData CoreKey ()
   -> Tidings (Maybe (TBData CoreKey Showable))
   -> UI ([Element],Tidings (Editor (Index (TBData CoreKey Showable))))
crudUITableDiff inf open reftb@(bres , _ ,gist ,tref) refs pmods ftb@(m,_)  preoldItems = do
  (e2,h2) <- ui $ newEvent
  nav  <- buttonDivSet ["+","-"] (fmap Just open) (\i -> UI.button # set UI.text i # set UI.style [("font-size","smaller")] # set UI.class_ "buttonSet btn-xs btn-default btn pull-right")
  element nav # set UI.class_ "col-xs-3 pull-right"
  sub <- UI.div
  let table = lookTable inf ( _kvname  m )
  let
      ini = maybe Delete Diff . safeHead . compact  . catMaybes  <$> (Tra.sequenceA $  snd  <$> pmods)
      fun "+" = logTime "crud" $ do
          let
            getItem :: TBData CoreKey Showable -> TransactionM (Maybe (TBIdx CoreKey Showable))
            getItem  v =  getFrom table v `catchAll` (\e -> liftIO (putStrLn $"error getting Item" ++ show (e :: SomeException)) >> return Nothing)
          preoldItens <- currentValue (facts preoldItems)
          loadedItens <-  ui $ join <$> traverse (transactionNoLog inf  . getItem) preoldItens
          (loadedItensEv ) <- mapUIFinalizerT sub (ui . fmap join <$> traverse (\i ->  do
            p <-  transactionNoLog inf . getItem $ i
            putPatch tref (fmap PatchRow $ maybeToList p)
            return (fmap PatchRow p  ))) (preoldItems)
          let
              deleteCurrentUn un e l =   maybe l (\v -> G.delete v (3,6) l) $  G.getUnique un <$> e
              tpkConstraint = (fmap unTB $ F.toList $ _kvvalues $ unTB $ snd $ tbPK ftb , (_kvpk m, ( fmap snd bres)))
          unConstraints <-  traverse (traverse (traverse (ui . mapTEventDyn return ))) $ (\un -> (fmap unTB $ F.toList $ _kvvalues $ unTB $ tbUn (S.fromList un ) (TB1 $ tableNonRef' ftb) , (un, fmap (createUn un . G.toList ) (fmap snd bres)))) <$> (_kvuniques m)
          unDeleted <- traverse (traverse (traverse (ui . mapTEventDyn return))) (fmap (fmap (\(un,o)-> (un,deleteCurrentUn un <$> preoldItems <*> o))) (tpkConstraint:unConstraints))
          let
              dunConstraints (un,o) = flip (\i ->  maybe (const False ) (unConstraint un .tblist' table . fmap _tb ) (traverse (traFAttr unSOptional' ) i ) ) <$> o
              unFinal:: [([Column CoreKey ()], Tidings PKConstraint)]
              unFinal = fmap (fmap dunConstraints) unDeleted
          (listBody,tablebdiff) <- eiTableDiff inf   unFinal  refs pmods ftb preoldItems
          let
            tableb = recoverEditChange <$> preoldItems <*> tablebdiff


          (panelItems,tdiff)<- processPanelTable listBody inf reftb  tablebdiff table preoldItems
          let diff = unionWith const tdiff   (filterJust $ rumors loadedItensEv)

          ui $ onEventDyn diff (putPatch tref . pure)
          ui $ onEventDyn (rumors tablebdiff) (liftIO . h2)
          UI.div # set children [listBody,panelItems]
      fun i = do
        ui $ onEventDyn (rumors ini) (liftIO . h2)
        UI.div

  end <- mapUIFinalizerT sub fun (diffTidings $ triding nav)
  element sub # sink children (pure <$> facts end)
  cv <- currentValue (facts ini)
  bh2 <- ui $ stepper  cv e2
  return ([getElement nav,sub],  tidings bh2 e2   )



crudUITable
   :: InformationSchema
   -> Tidings String
   -> RefTables
   -> [(TB Identity CoreKey () ,Tidings (Maybe (TB Identity CoreKey Showable)))]
   -> PluginRef (TBData CoreKey Showable)
   -> TBData CoreKey ()
   -> Tidings (Maybe (TBData CoreKey Showable))
   -> UI ([Element],Event (TBIdx CoreKey Showable ) ,Tidings (Maybe (TBData CoreKey Showable)))
crudUITable inf open reftb@(bres , _ ,gist ,tref) refs pmods ftb@(m,_)  preoldItems = do
  (e2,h2) <- ui $ newEvent
  (ediff ,hdiff) <- ui $ newEvent
  nav  <- buttonDivSet ["+","-"] (fmap Just open) (\i -> UI.button # set UI.text i # set UI.style [("font-size","smaller")] # set UI.class_ "buttonSet btn-xs btn-default btn pull-right")
  element nav # set UI.class_ "col-xs-3 pull-right"
  sub <- UI.div
  let table = lookTable inf ( _kvname  m )
  let
      fun "+" = logTime "crud" $ do
          let
            getItem :: TBData CoreKey Showable -> TransactionM (Maybe (TBIdx CoreKey Showable))
            getItem  v =  getFrom table v `catchAll` (\e -> liftIO (putStrLn $"error getting Item" ++ show (e :: SomeException)) >> return Nothing)
          preoldItens <- currentValue (facts preoldItems)
          loadedItens <-  ui $ join <$> traverse (transactionNoLog inf  . getItem) preoldItens
          (loadedItensEv ) <- mapUIFinalizerT sub (ui . fmap join <$> traverse (\i ->  do
            p <-  transactionNoLog inf . getItem $ i
            putPatch tref (fmap PatchRow $ maybeToList p)
            return (fmap PatchRow p  ) )) (preoldItems)
          let
              deleteCurrentUn un e l =   maybe l (\v -> G.delete v (3,6) l) $  G.getUnique un <$> e
              tpkConstraint = (fmap unTB $ F.toList $ _kvvalues $ unTB $ snd $ tbPK ftb , (_kvpk m, ( fmap snd bres)))
          unConstraints <-  traverse (traverse (traverse (ui . mapTEventDyn return ))) $ (\un -> (fmap unTB $ F.toList $ _kvvalues $ unTB $ tbUn (S.fromList un ) (TB1 $ tableNonRef' ftb) , (un, fmap (createUn un . G.toList ) (fmap snd bres)))) <$> (_kvuniques m)
          unDeleted <- traverse (traverse (traverse (ui . mapTEventDyn return))) (fmap (fmap (\(un,o)-> (un,deleteCurrentUn un <$> preoldItems <*> o))) (tpkConstraint:unConstraints))
          let
              dunConstraints (un,o) = flip (\i ->  maybe (const False ) (unConstraint un .tblist' table . fmap _tb ) (traverse (traFAttr unSOptional' ) i ) ) <$> o
              unFinal:: [([Column CoreKey ()], Tidings PKConstraint)]
              unFinal = fmap (fmap dunConstraints) unDeleted
          (listBody,tablebdiff) <- eiTableDiff inf   unFinal  refs pmods ftb preoldItems


          (panelItems,tdiff)<- processPanelTable listBody inf reftb  tablebdiff table preoldItems
          let diff = unionWith const tdiff   (filterJust $ rumors loadedItensEv)
              tableb = recoverEditChange <$> preoldItems <*> tablebdiff

          ui $ onEventDyn diff (liftIO . putPatch tref . pure)
          ui $ onEventDyn (filterE (maybe False (isRight.tableCheck)) (rumors tableb))
              (liftIO . h2)
          UI.div # set children [listBody,panelItems]
      fun i = UI.div

  end <- mapUIFinalizerT sub fun (diffTidings $ triding nav)
  element sub # sink children (pure <$> facts end)
  cv <- currentValue (facts preoldItems)
  bh2 <- ui $ stepper  cv (unionWith const e2  (rumors preoldItems))
  return ([getElement nav,sub], ediff ,F.foldl' (\i j -> mergePatches <$> i <*> j) (tidings bh2 (unionWith const e2  (rumors preoldItems))) (fmap snd pmods))

mergePatches i j = join (liftA2 applyIfChange i j)<|> i  <|> join (createIfChange <$>j)

diffTidings t = tidings (facts t) $ diffEvent (facts t ) (rumors t)

unConstraint :: [CoreKey] -> TBData CoreKey Showable -> G.GiST (G.TBIndex Showable) (TBData CoreKey Showable) -> Bool
unConstraint un v m = not . L.null . lookGist un v $ m


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
processPanelTable lbox inf reftb@(res,_,gist,_) inscrudp table oldItemsi = do
  let
      inscrud = recoverEditChange <$> oldItemsi <*> inscrudp
      containsGist ref map = if isJust refM then not $ L.null (lookGist ix ref map) else False
        where ix = (_kvpk (tableMeta table))
              refM = traverse unSOptional' (getPKM ref)
      conflictGist ref map = if isJust refM then lookGist ix ref map else[]
        where ix = (_kvpk (tableMeta table))
              refM = traverse unSOptional' (getPKM ref)


  -- Insert when isValid
  let insertEnabled = liftA2 (&&) (onDiff isRight False . fmap patchCheck <$>  inscrudp ) (liftA2 (\i j -> not $ maybe False (flip containsGist j) i  ) (inscrud ) (gist ))
  insertB <- UI.button# set UI.class_ "btn btn-sm" #
          set text "INSERT" #
          set UI.class_ "buttonSet" #
          set UI.style (noneShowSpan ("INSERT" `elem` rawAuthorization table ))  #
          sinkDiff UI.enabled insertEnabled

  let editEnabled = liftA2 (&& ) (liftA2 (&&) ((maybe False (isRight . tableCheck  )  )<$> inscrud ) (isJust <$> oldItemsi)) $ liftA2 (&&) (liftA2 (\i j -> maybe False (any fst . F.toList  ) $ liftA2 (liftF2 (\l m -> if l  /= m then (True,(l,m)) else (False,(l,m))) )  i j) (fmap (_kvvalues . unTB . snd ). fmap tableNonRef' <$> inscrud) (fmap (_kvvalues . unTB .  snd ). fmap tableNonRef' <$> oldItemsi)) (liftA2 (\i j -> maybe False (flip containsGist j) i  ) (inscrud) (gist) )
  editB <- UI.button# set UI.class_ "btn btn-sm" #
         set text "EDIT" #
         set UI.class_ "buttonSet"#
         set UI.style (noneShowSpan ("UPDATE" `elem` rawAuthorization table )) #
  -- Edit when any persistent field has changed
         sinkDiff UI.enabled editEnabled

  let mergeEnabled = liftA2 (&&) (isJust . fmap tableNonRef' <$> inscrud) (liftA2 (\i j -> not . L.null   $ maybe [] (\e -> filter ((/= tableNonRef' e) .tableNonRef') $  conflictGist e j) i  ) (inscrud) (gist ))
  mergeB <- UI.button# set UI.class_ "btn btn-sm" #
         set text "MERGE" #
         set UI.class_ "buttonSet"#
         set UI.style (noneShowSpan ("UPDATE" `elem` rawAuthorization table )) #
  -- Edit when any persistent field has changed
         sinkDiff UI.enabled mergeEnabled

  let deleteEnabled = liftA2 (&&) (isJust . fmap tableNonRef' <$> oldItemsi) (liftA2 (\i j -> maybe False (flip containsGist j) i  ) (oldItemsi ) (gist ))
  deleteB <- UI.button# set UI.class_ "btn btn-sm" #
         set text "DELETE" #
         set UI.class_ "buttonSet"#
         set UI.style (noneShowSpan ("DELETE" `elem` rawAuthorization table )) #
  -- Delete when isValid
         sinkDiff UI.enabled deleteEnabled
  let
       filterKey enabled k = const () <$> filterApply (const <$> enabled) (k )
       crudMerge :: Maybe (TBData Key Showable)  ->  G.GiST (TBIndex Showable) (TBData Key Showable )-> Dynamic (Maybe (RowPatch Key Showable))
       crudMerge (Just i) g =
          fmap (tableDiff . fmap ( fixPatchRow inf (tableName table)) )  <$> transaction inf ( do
            let confl = conflictGist i g
            mapM deleteFrom (fmap patch confl :: [TBIdx Key Showable])
            fullDiffInsert  i)
       crudEdi (Just i) (Just j) =  fmap (\g -> fmap (PatchRow . fixPatch inf (tableName table) ) $diff i  g) $ transaction inf $ fullDiffEditInsert  i j
       crudIns (Just j)   =  fmap (tableDiff . fmap ( fixPatchRow inf (tableName table)) )  <$> transaction inf (fullDiffInsert  j)
       crudDel :: Maybe (TBData Key Showable)  ->  Dynamic (Maybe (RowPatch Key Showable))
       crudDel (Just j)  = fmap (tableDiff . fmap ( fixPatchRow inf (tableName table)))<$> transaction inf (deleteFrom (patch j :: TBIdx Key Showable))

  altU <- onAltU lbox
  altI <- onAltI lbox
  cliIns <- UI.click insertB
  cliMerge <- UI.click mergeB
  cliDel <- UI.click deleteB
  cliEdit <- UI.click editB
  diffEdi <- mapEventFin id $ crudEdi <$> facts oldItemsi <*> facts inscrud <@ (unionWith const cliEdit (filterKey (facts editEnabled) ( altU)))
  diffDel <- mapEventFin id $ crudDel <$> facts oldItemsi <@ cliDel
  diffMerge <- mapEventFin id $ crudMerge <$> facts inscrud <*> facts gist <@ cliMerge
  diffIns <- mapEventFin id $ crudIns <$> facts inscrud <@ (unionWith const cliIns (filterKey  (facts insertEnabled) altI ))

  conflict <- UI.div # sinkDiff text ((\i j l -> if l then maybe "" (L.intercalate "," .fmap (showFKText ). flip conflictGist  j) i else "")  <$> inscrud <*> gist <*> mergeEnabled) # sinkDiff UI.style (noneShow <$>mergeEnabled)
  transaction <- UI.span #
         set children [insertB,editB,mergeB,deleteB] #
         set UI.style (noneShowSpan (ReadWrite ==  rawTableType table ))
  out <- UI.div # set children [transaction,conflict]
  return (out, fmap head $ unions $ fmap filterJust [diffEdi,diffIns,diffMerge,diffDel] )




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


indexItens
  :: (Show b)
     => Int
     -> TB Identity Key a
     -> Tidings Int
     -> NonEmpty (Tidings (Maybe (TB Identity Key b)))
     -> Tidings (Maybe (TB Identity Key b))
     -> Tidings (Maybe (TB Identity Key b ))
indexItens s tb@(Attr k v) offsetT inner old = fmap constrAttr  <$> bres
  where
    tdcomp = fmap (fmap _tbattr ) <$>  takeArray inner
    tdi = fmap  (unArray. _tbattr) <$> old
    constrAttr = Attr k . ArrayTB1
    bres = attrEditor s <$> offsetT <*>  tdi <*> tdcomp
indexItens s tb@(FKT ifk rel _) offsetT inner old = fmap constFKT  <$> bres
  where
    bres2 = fmap (fmap projFKT )  <$> takeArray  inner
    bres =  attrEditor s <$> offsetT <*> fmap (fmap (fktzip .projFKT)) old <*> bres2
    constFKT a = FKT (mapKV (mapComp (mapFAttr (const (ArrayTB1 ref ))) ) ifk)   rel  (ArrayTB1 tb )
      where (ref,tb) = Non.unzip a
    projFKT (FKT i  _ j ) = (unAttr $ justError ("no array" <> show i)  $ safeHead $  fmap unTB  $ unkvlist i,  j)
    fktzip (ArrayTB1 lc , ArrayTB1 m) =  Non.zip lc m
    fktzip i = errorWithStackTrace  ( show i)
indexItens s tb@(IT na _) offsetT inner old = fmap constIT <$> bres
  where
    bres2 = fmap (fmap _fkttable) <$> takeArray inner
    emptyIT = unArray. _fkttable
    bres =  attrEditor s <$> offsetT <*> (fmap emptyIT <$> old) <*> bres2
    constIT = IT   na . ArrayTB1

attrEditor s o x y = arrayEditor merge create delete x y
  where
    merge = splitArray s o
    create = id
    delete = fmap Non.fromList  . nonEmpty .  Non.take o
    arrayEditor merge create del x y = liftA2 merge  x y <|> fmap create  y <|> join (fmap del x)


dynHandlerPatch hand val ix (l,old)= do
    (ev,h) <- ui $ newEvent
    let valix = val ix
        idyn True  =  do
          tds <- hand ix valix
          ini <- currentValue (facts $ triding tds)
          liftIO $ h ini
          fin <- ui $ onEventDyn (rumors $ triding tds) (liftIO . h)
          return [getElement tds]
        idyn False = do
          liftIO $ h Keep
          return []
    el <- UI.div
    els <- mapUIFinalizerT el idyn (diffTidings $ (||)<$> old<*> fmap isJust valix)
    element el # sink children (facts els)
    bend <- ui $ stepper Keep ev
    let
      -- infer i j | traceShow ("infer",i,j) False = undefined
      infer Keep (Just i) = True
      infer Keep Nothing  = False
      infer Delete (Just i) = False
      infer Delete Nothing = False
      infer (Diff i) _ = True
      inferEv = flip infer <$> valix <*> tidings bend ev

    inferIni <- currentValue (facts inferEv )
    let diffInfer = (diffEvent (facts inferEv) (rumors inferEv))
    inferBh <- ui$ stepper inferIni diffInfer
    return $ (l <> [TrivialWidget (tidings bend ev) el], tidings inferBh diffInfer)


dynHandler hand val ix (l,old)= do
    (ev,h) <- ui $ newEvent
    let valix = val ix
    el <- UI.div
    let idyn True  =  do
          tds <- hand ix valix
          ini <- currentValue (facts $ triding tds)
          liftIO $ h ini
          fin <- ui $ onEventDyn (rumors $ triding tds) (liftIO . h)
          return (getElement tds)
        idyn False = do
          liftIO $ h Nothing
          UI.div
    els <- mapUIFinalizerT el idyn old
    element el # sink children (pure <$>  facts els)
    iniv <- currentValue (facts $ valix)
    bend <- ui $ stepper iniv ev
    let notProp = filterE isNothing $ notdiffEvent bend  (ev)
    bend2 <- ui $ stepper iniv  (diffEvent bend  ev)
    bendn <- ui $ stepper (isJust iniv ) (diffEvent (fmap isJust bend ) (fmap isJust ev))
    bendn2 <- ui $ stepper (isJust iniv ) (diffEvent bendn  (fmap isJust ev))
    return $ (l <> [TrivialWidget (tidings bend2 (diffEvent bend  ev)) el], tidings bendn2  (diffEvent bendn  (fmap isJust ev)))


logTime s f = do
  ini <- liftIO $ getCurrentTime
  r <- f
  out <- liftIO $ getCurrentTime
  return r



-- reduceDiffList o i | traceShow (o,i) False = undefined
reduceDiffList o i
   | F.all isKeep (snd <$> i) = Keep
   | otherwise = patchEditor $ lefts diffs ++ reverse (rights diffs)
   where diffs = catMaybes $ (\(ix,v) -> treatA (o+ix)v) <$> i
         treatA a (Diff v) = Just $ Left $ PIdx a  (Just v)
         treatA a Delete =  Just $ Right $ PIdx a Nothing
         treatA _ Keep = Nothing

reduceDiffListFK o i
   | F.all isKeep (snd <$> i) = Keep
   | otherwise = liftA2 (,) (patchEditor $ fmap fst res )  (patchEditor $ fmap snd res)
   where diffs = catMaybes $ (\(ix,v) -> treatA (o+ix)v) <$> i
         treatA a (Diff (PFK _ [PAttr k l]  v)) = Just $ Left $  (PIdx a (Just l) ,PIdx a  (Just v))
         treatA a Delete =  Just $ Right $ (PIdx a Nothing,PIdx a Nothing)
         treatA _ Keep = Nothing
         res = lefts diffs ++ reverse (rights diffs)




reduceOptional Delete   = Diff $ POpt Nothing
reduceOptional Keep  = Keep
reduceOptional (Diff i )  = Diff (POpt (Just  i))

reduceFKOptional rel att  Delete  = Diff $ PFK rel ((\i -> PAttr i (POpt Nothing)) <$> att) (POpt Nothing)
reduceFKOptional rel att  Keep = Keep
reduceFKOptional rel att  (Diff (PFK _ attn vn))= Diff $ PFK rel ((\(PAttr i j ) -> PAttr i (POpt $ Just j)) <$> attn) (POpt $ Just vn)



maybeEdit v id (Diff i) =  id i
maybeEdit v id _  = v

buildUIDiff:: [FieldModifier] -> KType (Prim KPrim (Text,Text))-> [Tidings (Maybe (Index (FTB Showable)))]-> Tidings (Maybe (FTB Showable)) -> UI (TrivialWidget (Editor (Index (FTB Showable))))
buildUIDiff km i  plug tdi = go i plug tdi
  where
    go :: KType (Prim KPrim (Text,Text))-> [Tidings (Maybe (Index (FTB Showable)))]-> Tidings (Maybe (FTB Showable)) -> UI (TrivialWidget (Editor (Index (FTB Showable))))
    go i plug tdi = case i of
         (KArray ti ) -> mdo
            offsetDiv  <- UI.div
            -- let wheel = fmap negate $ mousewheel offsetDiv
            TrivialWidget offsetT offset <- offsetField (pure 0)  never (maybe 0 (Non.length .unArray) <$> (recoverEditChange <$> tdi <*> bres))
            let arraySize = 8
                tdi2  = fmap unArray <$> tdi
                index o ix v = join $ flip Non.atMay (o + ix) <$> v
            let unIndexEl ix = (index ix <$> offsetT <*> tdi2)
                dyn = dynHandlerPatch  (\ix valix ->do
                    let plugix = ((fmap (((\ o v -> join $ (convertPatchSet (o + ix)) <$> v ) <$> offsetT <*>))) plug)
                    wid <- go ti plugix valix
                    lb <- hlabel ["col-xs-1"] # sink UI.text (show . (+ix) <$> facts offsetT )
                    paintEditDiff lb (facts (triding wid ))
                    element wid # set UI.class_ "col-xs-11"
                    row <- UI.div # set children [lb,getElement wid]
                    return $ TrivialWidget (triding wid) row ) unIndexEl

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
         (KOptional ti) -> do
           let pretdi = ( join . fmap unSOptional' <$> tdi)
               plugtdi = fmap (join . fmap (\(POpt i ) -> i) )<$> plug
           tdnew <- go ti  plugtdi pretdi
           retUI <- UI.div # set children [getElement tdnew]
           -- Delete equals create

           return $ TrivialWidget ( reduceOptional <$> triding tdnew  ) retUI
         (KSerial ti) -> do
           let pretdi = ( join . fmap unSSerial <$> tdi)
               plugtdi = fmap (join . fmap (\(PSerial i ) -> i) )<$> plug
           tdnew <- go ti  plugtdi pretdi
           retUI <- UI.div # set children [getElement tdnew]
           -- Delete equals create
           let
               test Delete _ = Diff $ PSerial Nothing
               -- test Keep Nothing = Diff $ PSerial Nothing
               test Keep _ = Keep
               test (Diff i ) _ = Diff (PSerial (Just  i))

           return $ TrivialWidget ( test <$> triding tdnew <*> tdi) retUI
         (KDelayed ti) -> do
           let pretdi = ( join . fmap unSDelayed <$> tdi)
               plugtdi = fmap (join . fmap (\(PDelayed i ) -> i) )<$> plug
           tdnew <-  go ti plugtdi pretdi
           retUI <- UI.div# set children [getElement tdnew]
           let
               test Delete = Delete
               test Keep = Keep
               test (Diff i ) = Diff (PDelayed (Just  i))

           return $ TrivialWidget (test <$> triding tdnew  ) retUI
         (KInterval ti) -> do
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
         (Primitive (AtomicPrim i)) -> do
           let tdi2 = F.foldl' (liftA2 mergePatches) tdi plug
           pinp <- fmap (fmap TB1) <$> buildPrim km (fmap unTB1 <$> tdi2) i
           return $ TrivialWidget (editor  <$> tdi <*> triding pinp) (getElement pinp)
         i -> errorWithStackTrace (show i)

reduceDiff :: [Editor (PathFTB a) ] -> Editor (PathFTB a)
reduceDiff i
  | F.all isKeep i = Keep
  | F.all isDelete i = Delete
  | otherwise = patchEditor $ filterDiff i


buildPrim :: [FieldModifier] ->Tidings (Maybe Showable) ->   KPrim -> UI (TrivialWidget (Maybe Showable))
buildPrim fm tdi i = case i of
         PGeom g-> fmap (fmap(fmap SGeo)) $do
           let tdig = fmap (\(SGeo i) -> i) <$> tdi
           case g of
             PPosition i -> do
               let tdip = fmap (\(SPosition i) -> i) <$> tdig
               fmap (fmap SPosition)<$> case i of
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
         PBoolean -> do
           res <- checkedWidgetM (fmap (\(SBoolean i) -> i) <$> tdi )
           return (fmap SBoolean <$> res)
         PTimestamp dbzone -> do
            cliZone <- jsTimeZone
            itime <- liftIO $  getCurrentTime
            timeButton <- UI.button # set UI.text "now"
            cliTime <- UI.click timeButton
            evCurr <-  mapEventFin (liftIO . fmap Just) (pure getCurrentTime <@ cliTime )
            let
              newEv = fmap (STimestamp . utcToLocalTime cliZone ) <$> evCurr
              maptime f (STimestamp i) = STimestamp (f i)
              toLocal = maptime  (utcToLocalTime cliZone . localTimeToUTC utc)
              fromLocal = maptime (utcToLocalTime utc .localTimeToUTC cliZone)
            tdi2 <- ui $ addEvent newEv  (fmap toLocal <$> tdi)
            fmap (fmap fromLocal) <$> oneInput tdi2 [timeButton]
         PDate -> do
            cliZone <- jsTimeZone
            itime <- liftIO $  getCurrentTime
            timeButton <- UI.button # set UI.text "now"
            cliTime <- UI.click timeButton
            evCurr <-  ui $ mapEvent (fmap Just) (pure getCurrentTime <@ cliTime )
            let  newEv =  fmap (SDate . localDay . utcToLocalTime cliZone) <$> evCurr
            tdi2 <- ui $ addEvent newEv  tdi
            oneInput tdi2 [timeButton]
         PDayTime -> do
            cliZone <- jsTimeZone
            itime <- liftIO $  getCurrentTime
            timeButton <- UI.button # set UI.text "now"
            cliTime <- UI.click timeButton
            evCurr <-  ui $ mapEvent (fmap Just) (pure getCurrentTime <@ cliTime)
            let  newEv = fmap (SDayTime. localTimeOfDay . utcToLocalTime cliZone) <$> evCurr
            tdi2 <- ui $ addEvent newEv  tdi
            oneInput tdi2 [timeButton]
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
           tdi2 <- ui $ addEvent (join . fmap (fmap SBinary . either (const Nothing) Just .   B64.decode .  BSC.drop 7. snd  . BSC.breakSubstring "base64," . BSC.pack ) <$> fchange) =<< addEvent (const Nothing <$> clearE ) tdi
           let
             fty = case mime of
               "application/pdf" -> pdfFrame ("iframe" ,UI.strAttr "src",maybe "" binarySrc ,[("width","100%"),("height","300px")])
               "application/x-ofx" ->pdfFrame  ("textarea", UI.value ,maybe "" (\(SBinary i) -> BSC.unpack i) ,[("width","100%"),("height","300px")])
               "application/gpx+xml" ->pdfFrame  ("textarea", UI.value ,maybe "" (\(SBinary i) -> BSC.unpack i) ,[("width","100%"),("height","300px")])
               "image/jpg" -> (\i -> pdfFrame ("img" ,UI.strAttr "src",maybe "" binarySrc ,[("max-height","200px")]) i # set UI.class_ "img-responsive")
               "image/png" -> pdfFrame ("img" ,UI.strAttr "src",maybe "" binarySrc ,[("max-height","200px")])
               "image/bmp" -> pdfFrame ("img" ,UI.strAttr "src",maybe "" binarySrc ,[("max-height","200px")])
               "text/html" -> pdfFrame ("iframe" ,UI.strAttr "srcdoc",maybe "" (\(SBinary i) -> BSC.unpack i) ,[("width","100%"),("height","300px")])
           f <- fty (facts tdi2) # sinkDiff UI.style (noneShow. isJust <$> tdi2)
           fd <- UI.div # set UI.style [("display","inline-flex")] # set children [file,clearB]
           res <- UI.div # set children [fd,f]
           return (TrivialWidget tdi2 res)
         PColor -> do
            let f = facts tdi
            v <- currentValue f
            inputUI <- UI.input # set UI.class_ "jscolor" # sink0 UI.value (maybe "FFFFFF" renderPrim <$> f)# set UI.style [("width","100%")]
            onCE <- UI.onChangeE inputUI
            let pke = unionWith const (readPrim i <$> onCE) (rumors tdi)
            pk <- ui $ stepper v  pke
            let pkt = tidings pk (diffEvent pk pke)
            sp <- UI.div # set UI.children [inputUI ]
            runFunction$ ffi "new jscolor(%1)" inputUI
            onChanges f (\f -> runFunction $ ffi "updateColor(%1,%2)" inputUI (maybe "FFFFFF" renderPrim  f))
            return $ TrivialWidget pkt sp
         z -> do
            oneInput tdi []
  where
    oneInput :: Tidings (Maybe Showable) -> [Element] ->  UI (TrivialWidget (Maybe Showable))
    oneInput tdi elem = do
            let f = tdi
            v <- currentValue (facts f)
            inputUI <- UI.input # sinkDiff UI.value (maybe "" renderPrim <$> f) # set UI.style [("width","100%")] # if [FRead] == fm then (set (UI.strAttr "readonly") "") else id
            onCE <- UI.onChangeE inputUI

            let pke = unionWith const (readPrim i <$> onCE ) (rumors tdi)
            pk <- ui $ stepper v  pke
            sp <- UI.div # set children (inputUI : elem)
            return $ TrivialWidget(tidings pk pke) sp

iUITableDiff
  :: InformationSchema
  -- Plugin Modifications
  -> PluginRef (Column CoreKey (Showable))
  -- Selected Item
  -> Tidings (Maybe (Column CoreKey Showable))
  -- Static Information about relation
  -> Column CoreKey ()
  -> UI (TrivialWidget (Editor (Index (Column CoreKey Showable))))
iUITableDiff inf pmods oldItems  (IT na  tb1)
  = fmap (fmap (PInline  na) )<$> go tb1   (fmap (fmap (fmap (patchfkt))) <$> pmods) (fmap _fkttable <$> oldItems)
  where
    go mt pmods oldItems =  case mt of
      (TB1 tdata@(meta,_)) ->  do
        (celem,tcrud) <- eiTableDiff inf []
                []
                (fmap (fmap(fmap unAtom))<$> pmods)
                tdata
                (fmap unTB1<$>oldItems)
        element celem #
            set style [("margin-left","10px")]

        let bres =  (fmap ( PAtom )<$> tcrud)
        return $ TrivialWidget bres celem
      (LeftTB1 (Just tb1)) -> do
        tr <- go tb1 ( fmap (fmap (join . fmap (\(POpt i ) -> i)))<$> pmods) (join . fmap unSOptional' <$> oldItems)
        let
          test Delete  _ = Diff $ POpt Nothing
          -- test Keep Nothing = Diff$ POpt Nothing
          test Keep _ = Keep
          test (Diff i ) _ = Diff (POpt (Just  i))
        return $ TrivialWidget ( test <$> triding tr <*> oldItems) (getElement tr)

      (ArrayTB1 (tb1 :| _)) -> mdo
        offsetDiv  <- UI.div
        -- let wheel = fmap negate $ mousewheel offsetDiv
        TrivialWidget offsetT offset <- offsetField (pure 0)  never (maybe 0 (Non.length .unArray) <$> (recoverEditChange <$> oldItems <*> bres))
        let arraySize = 8
            tdi2  = fmap unArray <$>oldItems
            index o ix v = join $ flip Non.atMay (o + ix) <$> v
        let unIndexEl ix = (index ix <$> offsetT <*> tdi2)
            dyn = dynHandlerPatch  (\ix valix ->do
                    wid <- go tb1 (fmap (fmap (((\ o v -> join $ (convertPatchSet (o + ix)) <$> v ) <$> offsetT <*>))) pmods) valix
                    lb <- hlabel ["col-xs-1"] # sink UI.text (show . (+ix) <$> facts offsetT )
                    paintEditDiff lb (facts (triding wid ))
                    element wid # set UI.class_ "col-xs-11"
                    row <- UI.div # set children [lb,getElement wid]
                    return $ TrivialWidget (triding wid) row ) unIndexEl

        widgets <- fst <$> foldl' (\i j -> dyn j =<< i ) (return ([],pure True)) [0..arraySize -1 ]

        let
          widgets2 = Tra.sequenceA (  zipWith (\i j -> (i,) <$> j) [0..] $( triding <$> widgets) )
          bres = reduceDiffList  <$> offsetT <*>  widgets2
        element offsetDiv # set children (fmap getElement widgets)
        composed <- UI.span # set children [offset , offsetDiv]
        return  $ TrivialWidget  bres composed


type PluginRef a = [(Access Key, Tidings (Maybe (Index a)))]

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
  offparen <- UI.div # set children [offset,leng] # set UI.style [("border","2px solid black"),("margin-left","4px") , ("margin-right","4px"),("text-align","center")]

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
  -> RefTables
  -> PluginRef  (Column CoreKey Showable)
  -- Same Table References
  -> [(Column CoreKey () ,Tidings (Maybe (Column CoreKey (Showable))))]
  -- Relation Event
  -> Tidings (Maybe (Column CoreKey Showable))
  -- Static Information about relation
  -> Column CoreKey ()
  -> UI (TrivialWidget(Editor (Index (Column CoreKey Showable))))
fkUITableDiff inf constr reftb@(vpt,res,gist,tmvard) plmods nonInjRefs   oldItems  tb@(FKT ifk rel tb1@(TB1 tbdata@(m,_)  ) ) = logTime ("fk " <> (show $ keyattri tb)) $ mdo
      let
        relTable = M.fromList $ fmap (\(Rel i _ j ) -> (j,i)) rel
        ftdi = F.foldl' (liftA2 mergePatches)  oldItems (snd <$>  plmods)
        replaceKey :: TB Identity CoreKey a -> TB Identity CoreKey a
        replaceKey =  firstTB (\k -> maybe k id  $ fmap _relTarget $ L.find ((==k)._relOrigin) $  rel)
        replaceRel a =  (fst $ search (_relOrigin $ head $ keyattri a),  firstTB (\k  -> snd $ search k ) a)
            where  search  k = let v = justError ("no key" <> show k )$ L.find ((==k)._relOrigin)  rel in (_relOperator v , _relTarget v)
        staticold :: [(TB Identity CoreKey () ,Tidings(Maybe (TB Identity CoreKey (Showable))))]
        staticold  =  second (fmap (fmap replaceKey )) . first replaceKey  <$> filter (all (\i ->  not (isInlineRel i ) &&  ((_relOperator i) == Equals)). keyattri.fst ) ( nonInjRefs)
        iold2 :: Tidings (Maybe [TB Identity CoreKey Showable])
        iold2 =  fmap (fmap ( uncurry Attr) . concat) . allMaybesEmpty  <$> iold
            where
              iold :: Tidings [Maybe [(CoreKey,FTB Showable)]]
              iold  = Tra.sequenceA $ fmap (fmap ( aattr . _tb ) ) . snd <$> nonInjRefs
        ftdi2 :: Tidings (Maybe [TB Identity CoreKey Showable])
        ftdi2 =   fmap (fmap unTB. tbrefM ) <$> ftdi
        applyConstr m l =  filter (foldl' (\l constr ->  liftA2 (&&) l (not <$> constr) ) (pure (True))  l) m
        constrT =  Tra.sequenceA $ fmap snd constr
        sortList :: Tidings ([TBData CoreKey Showable] -> [TBData CoreKey Showable])
        sortList =  sorting' <$> pure (fmap ((,True)._relTarget) rel)
      let
        vv :: Tidings (Maybe [TB Identity CoreKey Showable])
        vv =   join .   fmap (\i -> if L.length i == L.length rel then Just i else Nothing) .fmap L.nub <$>  liftA2 (<>) iold2  ftdi2
      cvres <- currentValue (facts vv)
      filterInp <- UI.input # set UI.class_ "col-xs-3"
      filterInpE <- UI.valueChange filterInp
      filterInpBh <- ui $ stepper "" filterInpE
      iniGist <- currentValue (facts gist)

      itemListEl <- UI.select #  set UI.class_ "col-xs-5 fixed-label" # set UI.size "21" # set UI.style ([("position","absolute"),("z-index","999"),("top","22px")] <> noneShow False)

      wheel <- fmap negate <$> UI.mousewheel itemListEl
      let
          pageSize = 20
          lengthPage (fixmap,i) = (s  `div` pageSize) +  if s `mod` pageSize /= 0 then 1 else 0
            where (s,_) = fromMaybe (sum $ fmap fst $ F.toList fixmap ,M.empty ) $ M.lookup mempty fixmap
          cv = searchGist relTable m iniGist cvres
          tdi = (\i j -> searchGist relTable m  i j)<$> gist <*> vv
          filterInpT = tidings filterInpBh filterInpE
          filtering i  = T.isInfixOf (T.pack $ toLower <$> i) . T.toLower . T.intercalate "," . fmap (T.pack . renderPrim ) . F.toList . snd
          predicatefk o = (WherePredicate $AndColl $ catMaybes $ fmap ((\(Attr k v) -> PrimColl . (keyRef [k], ) . Left . (,Flip $ _relOperator $ justError "no rel" $ L.find (\i ->_relTarget i == k) rel) <$> unSOptional' v). replaceKey)  o)
          preindex = (\i -> maybe id (\i -> fmap (filterfixed (lookTable inf (_kvname m))(predicatefk i)))i ) <$>iold2 <*>vpt
      presort <- ui $ mapTEventDyn return (fmap  <$> sortList <*> fmap (fmap G.toList ) preindex)
      -- Filter and paginate
      (offset,res3)<- do
        let constr = liftA2 (\ (a,i) j -> (a,applyConstr i j) ) presort constrT

        res3 <- ui$ mapTEventDyn return ((\i -> fmap (filter (filtering i))) <$> filterInpT <*> constr)
        element itemListEl # sink UI.size (show . (\i -> if i > 21 then 21 else (i +1 )) . length .snd <$> facts res3)
        offset <- offsetField ((\j i -> maybe 0  (`div`pageSize) $ join $ fmap (\i -> L.elemIndex i (snd j) ) i )<$> facts res3 <#> (fmap (unTB1._fkttable )<$> oldItems)) wheel  (lengthPage <$> res3)
        return (offset, res3)
      -- Load offseted items
      ui $onEventDyn (filterE (isJust . fst) $ (,) <$> facts iold2 <@> rumors (triding offset)) $ (\(o,i) ->  traverse (\o -> do
        transactionNoLog inf $ selectFrom (_kvname m) (Just $ i `div` (opsPageSize $ schemaOps inf) `div` pageSize) Nothing  [] (predicatefk  o)) o  )

      ui $onEventDyn (filterE (\(a,b,c)->isJust c && isNothing a ) $ (,,) <$> facts tdi <*> facts (triding offset)<@> diffEvent (facts iold2)(rumors iold2) ) $ (\(v0,i,o) ->  traverse (\o -> do
        transactionNoLog inf $ selectFrom (_kvname m) (Just $ i `div` (opsPageSize $ schemaOps inf) `div` pageSize) Nothing  [] (predicatefk   o)) o  )
      -- Select page
      let
        paging  = (\o -> fmap (L.take pageSize . L.drop (o*pageSize)) ) <$> triding offset
      res4 <- ui$ mapTEventDyn  return (paging <*> res3)

      itemList <- if isReadOnly tb
        then
           TrivialWidget (Just  <$> tdi ) <$>
              (UI.div #
                set UI.style [("border","1px solid gray"),("height","20px")] #
                sink items (pure . maybe UI.div showFKE  <$> facts tdi) #  set UI.class_ "col-xs-5 fixed-label" )
        else do
          pan <- UI.div #  set UI.class_ "col-xs-5 fixed-label"
          let isel  = itemListEl
          top <- UI.div
          esc <- onEsc top
          panC <- UI.click pan
          (elbox ,helbox) <- ui  newEvent
          bh <- ui $ stepper False (unionWith const (const False <$> esc) (unionWith const (const True <$> panC) (const False <$> elbox ) ))
          lboxeel <- mapUIFinalizerT pan (\i -> if i
                                    then do
                                        lbox <- listBoxEl itemListEl ((Nothing:) . fmap (Just ) . snd  <$>    res4 ) (tidings (fmap Just <$> st ) (fmap Just <$> sel )) (pure id) ((\i -> maybe id (\l  ->    i  l ) )<$> showFK )
                                        onEvent (rumors $ diffTidings $triding lbox) (liftIO . helbox)
                                        return $ itemListEl

                                    else  UI.div) (tidings bh (unionWith const (const False <$> esc) (unionWith const (const True <$> panC) (const False <$> elbox) )))

          elembox <- UI.div # sink children (pure <$> facts lboxeel)
          let evbox = (unionWith const (fmap Just <$> rumors tdi) elbox )
          blbox <- ui $ stepper (fmap Just cv) evbox
          let
            lbox = TrivialWidget (tidings blbox  evbox) elembox
            selCh = rumors (triding lbox)
          element isel # sink UI.style (noneShow <$> bh)
          element offset # set UI.style (noneShow False)
          element filterInp # set UI.style (noneShow False)
          onChanges bh (\v -> do
              element filterInp # set UI.style (noneShow v)
              element offset # set UI.style (noneShow v)
              if True then runFunction$ ffi "$(%1).focus();" filterInp else return ())

          element pan#  sink text (maybe "" (\v -> (L.take 50 $ L.intercalate "," $ fmap renderShowable $ allKVRec' $  v))<$>  facts (tds )) # set UI.style [("border","1px solid gray"),("height","20px")]
          elsel <-element top # set  children [pan, elembox , filterInp,getElement offset]
          return (TrivialWidget  (triding lbox) elsel)


      let evsel = ( unionWith const (rumors tdi) ) (rumors $ join <$> triding itemList)
      prop <- ui $ stepper cv evsel
      let tds = tidings prop evsel

      itemDClick <- UI.dblclick (getElement itemList)
      let itemDClickE = (fmap (const ((\i -> case i of
                              "-" -> "+"
                              "+" -> "-" ))) itemDClick)
      bop <- ui$accumB ("-")   itemDClickE

      (celem,ediff,pretdi) <-crudUITable inf (tidings bop (flip ($) <$> bop <@> itemDClickE )) reftb staticold (fmap (fmap (fmap (unAtom. patchfkt))) <$> plmods)  tbdata tds
      let
          sel = filterJust $ fmap (safeHead.concat) $ unions $ [(unions  [(rumors $ join <$> triding itemList), rumors tdi])]
      st <- ui $ stepper cv sel
      fk <- if isReadOnly tb
          then
            UI.div # set  children [getElement itemList ,head celem]  # set UI.class_ "row"
          else
            UI.div # set  children [getElement itemList , head celem]  # set UI.class_ "row"
      subnet <- UI.div # set children [fk , last celem] # set UI.class_ "col-xs-12"
      let
        fksel =  fmap (\box ->  FKT (kvlist $ fmap _tb $ backFKRef relTable  (fmap (keyAttr .unTB ) $ unkvlist ifk)   (box)) rel (TB1 box) ) <$>  ((\i -> maybe i Just) <$>  pretdi <*> tidings st sel)
      return $ TrivialWidget (editor <$> oldItems <*> fksel ) subnet
fkUITableDiff inf constr tbrefs plmods  wl oldItems  tb@(FKT ilk rel  (LeftTB1 (Just tb1 ))) = do
  tr <- fkUITableDiff inf constr tbrefs (fmap (join . fmap unLeftItensP  <$>) <$> plmods)  (first unLeftKey . second (join . fmap unLeftItens <$>) <$> wl) (join . fmap unLeftItens  <$> oldItems)  (FKT (mapKV (mapComp (firstTB unKOptional) ) ilk ) (Le.over relOri unKOptional <$> rel) tb1)
  return $ reduceFKOptional rel (_relOrigin . head . keyattr <$> F.toList (_kvvalues ilk) )<$> tr

fkUITableDiff inf constr tbrefs plmods  wl oldItems  tb@(FKT ifk rel  (ArrayTB1 (tb1:| _)) ) = mdo
     dv <- UI.div
     let -- wheel = fmap negate $ mousewheel dv
         arraySize = 8
     TrivialWidget offsetT offset <- offsetField (pure 0)  never (maybe 0 (Non.length .unArray. _fkttable ) <$> (recoverEditChange <$> oldItems <*> bres))
     let
         fkst = FKT (mapKV (mapComp (firstTB unKArray)) ifk ) (fmap (Le.over relOri (\i -> if isArray (keyType i) then unKArray i else i )) rel)  tb1
         dyn = dynHandlerPatch  recurse (\ix -> unIndexItens ix <$> offsetT  <*>  oldItems)
         convertPatchSet ix (PatchSet p) = patchSet $ catMaybes $ fmap (convertPatchSet ix ) (F.toList p)
         convertPatchSet ix (PIdx ix2 p)
              | ix == ix2 = p
              | otherwise = Nothing


         recurse ix oix = do
           TrivialWidget tr el<- fkUITableDiff inf constr tbrefs (fmap ( (\o b -> unIndexItensP  ix o b)<$> offsetT <*> ) <$> plmods) wl oix fkst
           lb <- hlabel ["col-xs-1"] # sink UI.text (show . (+ix) <$> facts offsetT )
           paintEditDiff lb (facts tr)
           element el # set UI.class_ "col-xs-11"
           TrivialWidget tr <$> UI.div # set UI.children [lb,el]
     fks <- fst <$> foldl' (\i j -> dyn j =<< i ) (return ([],pure True)) [0..arraySize -1 ]

     element dv # set children (getElement <$> fks)

     let
          widgets2 = Tra.sequenceA (  zipWith (\i j -> (i,) <$> j) [0..] $( triding <$> fks) )
          bres0 = reduceDiffListFK <$> offsetT <*>  widgets2
          loadRes (i,j)  =  PFK rel [PAttr  (_relOrigin $ head $ keyattr $ head $ F.toList $ _kvvalues ifk) i] j
          bres = fmap (head.compact) . reduceTable <$> sequenceA ((fmap loadRes  <$> bres0) : fmap (fmap (maybe Keep Diff) . snd) plmods)
     res <- UI.div # set children [offset ,dv]
     return $  TrivialWidget bres  res

reduceTable l
  -- | traceShow l False = undefined
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
  ho <- UI.hover elemIn
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
                  flist = catMaybes $ fmap (\(i,_,j) -> (\(op,v) -> (keyRef [i],Left (v,readBinaryOp $ T.pack op))) <$> j) slist'
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


lookAttrM  inf k (i,m) = unTB <$> M.lookup (S.singleton (Inline (lookKey inf (_kvname i) k))) (unKV m)

lookAttrs' inf k (i,m) = unTB $ err $  M.lookup (S.fromList (lookKey inf (_kvname i) <$> k)) ta
    where
      ta = M.mapKeys (S.map _relOrigin) (unKV m)
      err= justError ("no attr " <> show k <> " for table " <> show (_kvname i,M.keys ta ))

lookAttr' inf k (i,m) = unTB $ err $  M.lookup (S.singleton ((lookKey inf (_kvname i) k))) ta
    where
      ta = M.mapKeys (S.map _relOrigin) (unKV m)
      err= justError ("no attr " <> show k <> " for table " <> show (_kvname i,M.keys ta))


attrLine i   = do
  line ( L.intercalate "," (fmap renderShowable .  allKVRec'  $ i))



convertPatchSet ix (PatchSet p) = patchSet $ catMaybes $ fmap (convertPatchSet ix ) (F.toList p)
convertPatchSet ix (PIdx ix2 p)
              | ix == ix2 = p
              | otherwise = Nothing
