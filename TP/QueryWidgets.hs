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
    attrUITable,
    offsetField,
    sorting',
    metaAllTableIndexV ,
    dashBoardAllTable,
    dashBoardAllTableIndex,
    validOp,
    viewer,
    exceptionAllTable,
    exceptionAllTableIndex,
    line,
    strAttr,
    flabel,
    ) where

import RuntimeTypes
import Data.Bifunctor
import Text
import SortList
import Data.Functor.Identity
import Control.Monad.Writer
import Control.Applicative.Lift
import SchemaQuery
import qualified Data.Binary as B
import Control.Concurrent
import qualified Data.Poset as P
import qualified Data.GiST.GiST as G
import Reactive.Threepenny
import Data.Either
import qualified Graphics.UI.Threepenny as UI
import Graphics.UI.Threepenny.Core hiding (delete)
import Data.String
import Data.Bifunctor
import Data.Ord
import Control.Lens ((^?),(&),(%~))
import qualified Control.Lens as Le
import Utils
import Data.Char
import Patch
import qualified Data.Map as M
import Data.Map (Map)
import qualified Data.Set as S
import Data.Set (Set)
import Data.Traversable(traverse)
import qualified Data.Traversable as Tra
import qualified Data.ByteString.Base64 as B64
import Data.Interval (interval)
import qualified Data.ExtendedReal as ER
import qualified Data.Interval as Interval
import qualified Data.List as L
import Text.Read
import Data.Text (Text)
import Types
import Types.Index
import Query
import Data.Maybe
import Prelude hiding (head)
import Data.Time
import Data.Functor.Apply
import TP.Widgets
import Schema
import Step
import qualified Data.Foldable as F
import Data.Foldable (foldl')
import Debug.Trace
import qualified Data.Text as T
import qualified Data.ByteString.Char8 as BSC
import qualified Data.ByteString.Lazy.Char8 as BSL
import GHC.Stack

--- Plugins Interface Methods
createFresh :: Text -> InformationSchema -> Text -> KType (Prim (Text,Text) (Text,Text))-> IO InformationSchema
createFresh  tname inf i ty@(Primitive atom)  =
  case atom of
    AtomicPrim _  -> do
      k <- newKey i ty 0
      return $ inf
          & keyMapL %~ (M.insert (tname,i) k )
    RecordPrim (s,t) -> do
      k <- newKey i ty 0
      let tableO = lookTable inf tname
          path = Path (S.singleton k) (FKInlineTable $ inlineName ty ) S.empty
      return $ inf
          & tableMapL . Le.ix tname . rawFKSL %~  S.insert path
          & pkMapL . Le.ix (S.fromList $ rawPK tableO) . rawFKSL Le.%~  S.insert path
          & keyMapL %~ M.insert (tname,i) k


genAttr :: InformationSchema -> Key -> Column Key ()
genAttr inf k =
  case keyType k of
    Primitive p ->
      case p of
        AtomicPrim l -> Attr k (TB1 ())
        RecordPrim (l,t) ->
          let table =  lookTable inf  t
          in IT (_tb (Attr k (TB1 ()))) $ TB1 $  unTlabel' $ tableView (tableMap inf) table

pluginUI :: InformationSchema
    -> Tidings (Maybe (TBData Key Showable) )
    -> Plugins
    -> UI (Element ,(Access Text,Tidings (Maybe (TBData Key Showable))))
pluginUI oinf trinp (StatefullPlugin n tname ac) = do
  let
      fresh :: [([VarDef],[VarDef])]
      fresh = fmap fst ac
  inf <- liftIO $  foldl' (\i (kn,kty) -> (\m -> createFresh  tname m kn kty) =<< i ) (return  oinf) (concat $ fmap fst fresh <> fmap snd fresh )
  let
      table = lookTable inf  tname
      freshKeys :: [([Key],[Key])]
      freshKeys = first (fmap lookK ) . second (fmap lookK) <$> fresh
      lookK = lookKey inf tname . fst
  freshUI <- foldl' (\old (aci ,(inpfresh,outfresh)) -> (old >>= (\((l,ole),unoldItems)-> do

      elemsIn <- mapM (\fresh -> do
        let attrB pre a = tbCase  inf  []  a [] [] pre
        attrB (const Nothing <$> trinp)  (genAttr oinf fresh )
           ) inpfresh
      let
        inp :: Tidings (Maybe (TBData Key Showable))
        inp = fmap (tbmap . mapFromTBList) . join  . fmap nonEmpty <$> foldr (liftA2 (liftA2 (:) )) (pure (Just [])) (fmap (fmap ( fmap _tb) .  triding) elemsIn )

      (preinp,(_,liftedE )) <- pluginUI  inf (mergeCreate <$>  unoldItems <*>  inp) aci

      elemsOut <- mapM (\fresh -> do
        let attrB pre a = tbCase  inf  []  a [] [] pre
        attrB (fmap (\v ->  unTB . justError ("no key " <> show fresh <> " in " <>  show v ) . fmap snd . getCompose . unTB . findTB1 ((== [fresh]) . fmap _relOrigin. keyattr ) $ TB1 v )  <$> liftedE  )  (genAttr oinf fresh )
       ) outfresh

      let styleUI =  set UI.class_ "row"
            . set UI.style [("border","1px"),("border-color","gray"),("border-style","solid"),("margin","1px")]
      j<- UI.div # styleUI  # set children (fmap getElement elemsIn <> [preinp])# sink UI.style (noneShow .isJust <$> facts unoldItems)
      k <- UI.div # styleUI  # set children (fmap getElement elemsOut) # sink UI.style (noneShow .isJust <$> facts liftedE  )
      return  (( l <> [j , k], ole <> [liftedE] ), mergeCreate <$> unoldItems <*> liftedE  ))
           ) ) (return (([],[]),trinp)) $ zip (fmap snd ac) freshKeys
  el <- UI.div  # set children (fst $ fst freshUI)
  return (el , (snd $ pluginStatic $ snd $ last ac ,last $ snd $ fst freshUI ))

pluginUI inf oldItems p@(PurePlugin n t arrow ) = do
  let f = staticP arrow
      action = pluginAction   p
  let tdInputPre = fmap (checkTable' (fst f)) <$>  oldItems
      tdInput = join . fmap (eitherToMaybe .  runErrors) <$> tdInputPre
      tdOutput = join . fmap (checkTable (snd f)) <$> oldItems
  headerP <- UI.button # set text (T.unpack n) # sink UI.enabled (isJust <$> facts tdInput) # set UI.style [("color","white")] # sink UI.style (liftA2 greenRedBlue  (isJust <$> facts tdInput) (isJust <$> facts tdOutput))
  bh <- stepper False (hoverTip headerP)
  details <-UI.div # sink UI.style (noneShow <$> bh) # sink UI.text (show . fmap (runErrors .fmap (mapValue' (const ()))) <$> facts tdInputPre)
  out <- UI.div # set children [headerP,details]
  ini <- currentValue (facts tdInput )
  kk <- stepper ini (diffEvent (facts tdInput ) (rumors tdInput ))
  (pgOut ,fin) <- mapTEventFin (\v -> fmap (join . eitherToMaybe ). catchPluginException inf t n (getPKM $ justError "ewfew"  v) . action $  fmap (mapKey' keyValue) v)  (tidings kk $diffEvent kk (rumors tdInput ))
  addElemFin out fin
  return (out, (snd f ,   fmap (liftTable' inf t) <$> pgOut ))

pluginUI inf oldItems p@(BoundedPlugin2 n t arrow) = do
  overwrite <- checkedWidget (pure False)
  let f = staticP arrow
      action = pluginAction p
  let tdInputPre = fmap (checkTable' (fst f)) <$>  oldItems
      tdInput = join . fmap (eitherToMaybe .  runErrors) <$> tdInputPre
      tdOutput = join . fmap (checkTable (snd f)) <$> oldItems
  headerP <- UI.button # set text (T.unpack n) {- # sink UI.enabled (isJust <$> facts tdInput) -} # set UI.style [("color","white")] # sink UI.style (liftA2 greenRedBlue  (isJust <$> facts tdInput) (isJust <$> facts tdOutput))
  bh <- stepper False (hoverTip headerP)
  details <-UI.div # sink UI.style (noneShow <$> bh) # sink UI.text (show . fmap (runErrors . fmap (mapValue' (const ())) )<$> facts tdInputPre)
  out <- UI.div # set children [headerP,details]
  let ecv = (facts tdInput <@ UI.click headerP)
  vo <- currentValue (facts tdOutput)
  vi <- currentValue (facts tdInput)
  bcv <- stepper (Nothing {-maybe vi (const Nothing) vo-}) ecv
  (pgOut ,fin) <- mapTEventFin (\v -> fmap (fmap (liftTable' inf t ). join . eitherToMaybe ) . catchPluginException inf t n (getPKM $ justError "ewfew"  v) . action $ fmap (mapKey' keyValue) v)  (tidings bcv ecv)
  addElemFin out fin
  return (out, (snd f ,  pgOut ))

indexPluginAttr
  :: TB Identity (FKey a) ()
     -> [(Access Text, Tidings (Maybe (TBData (FKey a) a1)))]
     -> [(Access Text, Tidings (Maybe (TB Identity (FKey a) a1)))]
indexPluginAttr a@(Attr _ _ )  plugItens =  evs
  where
        thisPlugs = filter (hasProd (== IProd True (keyValue . _relOrigin <$> keyattri a)) . fst)  plugItens
        evs  = fmap ( fmap ( join . fmap ( fmap unTB . fmap snd . getCompose . unTB . findTB1 (((== keyattri a)  . keyattr )) . TB1 )) ) <$>  thisPlugs
indexPluginAttr  i  plugItens = pfks
  where
        thisPlugs = filter (hasProd (isNested ((IProd True $ fmap (keyValue._relOrigin) (keyattri i) ))) .  fst) plugItens
        pfks =  first (uNest . justError "No nested Prod FKT" .  findProd (isNested((IProd True $ fmap (keyValue . _relOrigin ) (keyattri i) )))) . second (fmap (join . fmap (fmap  unTB . fmap snd . getCompose . unTB . findTB1 ((==keyattri i)  . keyattr ) . TB1 ))) <$> ( thisPlugs)



--- Style and Attribute Size
--
attrSize :: TB Identity Key b -> (Int,Int)
attrSize (FKT  _  _ _ ) = (12,4)
attrSize (IT _ _ ) = (12,4)
attrSize (Attr k _ ) = go  (mapKType $ keyType k)
  where
    go i = case i of
                KOptional l ->  go l
                KDelayed l ->  go l
                KSerial l -> go l
                KArray l -> let (i1,i2) = go l in (i1+1,i2*8)
                KInterval l -> let (i1,i2) = go l in (i1*2 ,i2)
                (Primitive i) ->
                  case (\(AtomicPrim i) -> i) $ i of
                       PInt -> (3,1)
                       PText-> (3,1)
                       PDate -> (3,1)
                       PTimestamp _ -> (3,1)
                       PDayTime -> (3,1)
                       PMime m -> case m of
                                    "image/jpg" ->  (4,8)
                                    "application/pdf" ->  (6,8)
                                    "application/x-ofx" ->  (6,8)
                                    "text/plain" ->  (12,8)
                                    "text/html" ->  (12,8)
                                    i  ->  (6,8)
                       i -> (3,1)

getRelOrigin :: [Compose Identity (TB Identity) Key () ] -> [Key]
getRelOrigin =  fmap _relOrigin . concat . fmap keyattr


labelCase
  :: Column Key ()
  -> Tidings (Maybe (Column Key Showable))
  -> TrivialWidget (Maybe (Column Key Showable))
  -> UI (TrivialWidget (Maybe (Column Key Showable)))
labelCase a old wid = do
    l <- flabel # set text (show $ _relOrigin <$> keyattri a)
    bh <- stepper False (hoverTip l)
    tip <- UI.div #
      set text (show $ fmap showKey  <$> keyattri a) #
      sink0 UI.style (noneShow <$> bh)
    patch <- UI.div #
      sink text (facts $ fmap ( show . join) $ liftA2 diff <$> triding wid <*> old) #
      sink0 UI.style (noneShow <$> bh)
    el <- UI.div # set children [l,tip,patch,getElement wid] #
      set UI.class_ ("col-xs-" <> show (fst $ attrSize a))
    paintEdit l (facts (triding wid )) (facts old)
    return $ TrivialWidget (triding wid) el


tbCase
  :: InformationSchema
  -> SelPKConstraint
  -> TB Identity Key ()
  -> [(TB Identity Key () ,TrivialWidget (Maybe (TB Identity Key Showable)))]
  -> [(Access Text,Tidings (Maybe (TB Identity Key Showable)))]
  -> Tidings (Maybe (TB Identity Key Showable))
  -> UI (TrivialWidget (Maybe (TB Identity Key Showable)))
tbCase inf constr i@(FKT ifk  rel tb1) wl plugItens preoldItems = do
        let
            oldItems = maybe preoldItems (\v -> if L.null v then preoldItems else fmap (maybe (Just (FKT (fmap  (_tb . uncurry Attr)  v) rel (DelayedTB1 Nothing) )) Just ) preoldItems  ) (Tra.traverse (\k -> fmap (k,) . keyStatic $ k ) ( getRelOrigin ifk))
            nonInj =  (S.fromList $ _relOrigin   <$> rel) `S.difference` (S.fromList $ getRelOrigin ifk)
            nonInjRefs = filter ((\i -> if S.null i then False else S.isSubsetOf i nonInj ) . S.fromList . fmap fst .  aattri .fst) wl
            nonInjConstr :: SelTBConstraint
            nonInjConstr = first (pure . _tb ) .fmap (fmap (\j ((_,l)) -> maybe True id $ (\ j -> not $ interPointPost rel (nonRefAttr  [_tb  j]) (nonRefAttr  $ F.toList $ _kvvalues $ unTB  l) ) <$> j ).triding) <$>  nonInjRefs
            relTable = M.fromList $ fmap (\(Rel i _ j ) -> (j,i)) rel
            pkset = fmap S.fromList $ allMaybes $  fmap (\ i ->  M.lookup i relTable) ( fmap _relOrigin $ findPK $ tb1 )

            restrictConstraint = filter ((\v -> maybe False  (v `S.isSubsetOf`)   pkset) . S.fromList . getRelOrigin  .fst) constr
            convertConstr :: SelTBConstraint
            convertConstr = (\(f,j) -> (f,) $ fmap (\constr -> constr   .  backFKRef relTable (getRelOrigin f)  .TB1  ) j ) <$>  restrictConstraint
        ftdi <- foldr (\i j -> updateEvent  Just  i =<< j)  (return oldItems) (fmap Just . filterJust . rumors . snd <$>  plugItens )
        fkUITable inf (convertConstr <> nonInjConstr) plugItens wl ftdi i
tbCase inf _ i@(IT na tb1 ) wl plugItens oldItems
    = iUITable inf plugItens oldItems i
tbCase inf _ a@(Attr i _ ) wl plugItens preoldItems = do
        let oldItems = maybe preoldItems (\v-> fmap (Just . fromMaybe (Attr i v)) preoldItems  ) ( keyStatic i)
        attrUITable oldItems (fmap snd plugItens ) a

emptyRecTable (FKT rel l tb )
    = case tb of
          (LeftTB1 _ ) ->  Just . fromMaybe (FKT (fmap (mapComp (mapFAttr (const (LeftTB1 Nothing)))) rel) l (LeftTB1 Nothing))
          i -> id
emptyRecTable (IT l tb)
    = case tb of
          (LeftTB1 _) -> Just . fromMaybe (IT l (LeftTB1 Nothing))
          i -> id

tbRecCase ::  InformationSchema ->  SelPKConstraint  -> TB Identity Key () -> [(TB Identity Key () ,TrivialWidget (Maybe (TB Identity Key Showable)))] -> [(Access Text,Tidings (Maybe (TB Identity Key Showable)))]-> Tidings (Maybe (TB Identity Key Showable)) -> UI (TrivialWidget (Maybe (TB Identity Key Showable)))
tbRecCase inf constr a wl plugItens preoldItems' = do
      let preoldItems = emptyRecTable  a <$> preoldItems'
      check <- foldr (\i j ->  updateTEvent  (fmap Just ) i =<< j) (return $ join . fmap unLeftItens  <$> preoldItems) (fmap (fmap (join . fmap unLeftItens) . snd) plugItens )
      TrivialWidget btr bel <- checkedWidget  (isJust <$> check)
      (ev,h) <- liftIO $ newEvent
      inipre <- currentValue  (facts preoldItems)
      let fun True = do
              initpre <- currentValue (facts preoldItems)
              initpreOldB <- stepper initpre (rumors preoldItems)
              TrivialWidget btre bel <- tbCase inf constr a wl plugItens (tidings initpreOldB (rumors preoldItems) )
              fin <- onEvent (rumors btre) (liftIO . h )
              el <- UI.div # set children [bel]
              liftIO$ addFin  el [fin]
              return el
          fun False = do
              UI.div
      sub <- UI.div # sink items  (pure .fun <$> facts btr ) # set UI.class_ "row"
      out <- UI.div # set children [bel,sub]
      binipre <- stepper  inipre (unionWith const ev (rumors preoldItems))
      return (TrivialWidget  (tidings binipre (unionWith const (rumors preoldItems) ev)) out)


unTBMap :: Show a => TBData Key a -> Map (Set (Rel Key)) (Compose Identity (TB Identity ) Key a )
unTBMap = _kvvalues . unTB . snd


eiTable
  :: InformationSchema
     -> SelPKConstraint
     -> Text
     -> [(TB Identity Key () ,TrivialWidget (Maybe (TB Identity Key Showable)))]
     -> [(Access Text,Tidings (Maybe (TBData Key Showable)))]
     -> TBData Key ()
     -> Tidings (Maybe (TBData Key Showable))
     -> UI (Element,Tidings (Maybe (TBData Key Showable)),Tidings (Maybe (TBData Key Showable)))
eiTable inf constr tname refs plmods ftb@(meta,k) oldItems = do
  let
      Just table = M.lookup tname  (tableMap inf)
  res <- mapM (pluginUI inf oldItems) (filter ((== rawName table ) . _bounds ) (plugins inf) )
  let plugmods = first repl <$> ((snd <$> res) <> plmods)
      repl (Rec  ix v ) = (replace ix v v)
      repl (Many[(Rec  ix v )]) = (replace ix v v)
      repl v = v
  oldItemsPlug <- foldr (\i j ->  updateTEvent  (fmap Just) i =<< j) (return oldItems ) (fmap snd plugmods)
  fks :: [(Column Key () ,TrivialWidget (Maybe (Column Key Showable)))]  <- foldl' (\jm (l,m)  -> do
            w <- jm
            let el =  L.any (mAny ((l==) . head ))  (fmap (fmap S.fromList ) <$> ( _kvrecrels meta))
                plugattr = indexPluginAttr (unTB m) plugmods
                aref = maybe (join . fmap (fmap unTB .  (^?  Le.ix l ) . unTBMap ) <$> oldItems) ( triding . snd) (L.find (((keyattr m)==) . keyattri .fst) $  refs)
            wn <- (if el
                    then tbRecCase
                    else tbCase ) inf constr (unTB m) w plugattr aref
            lab <- if
              rawIsSum table
              then return wn
              else labelCase (unTB m)  (maybe (join . fmap (fmap unTB .  (^?  Le.ix l ) . unTBMap ) <$> oldItems) ( triding . snd) (L.find (((keyattr m)==) . keyattri .fst) $  refs)) wn

            return (w <> [(unTB m,lab)])
        ) (return []) (P.sortBy (P.comparing fst ) . M.toList $ replaceRecRel (unTBMap $ ftb) (fmap (fmap S.fromList )  <$> _kvrecrels meta))
  let
      sequenceTable :: [(Column Key () ,TrivialWidget (Maybe (Column Key Showable)))] -> Tidings (Maybe (TBData Key Showable))
      sequenceTable fks = fmap (tblist' table . fmap _tb) . Tra.sequenceA <$> Tra.sequenceA (triding .snd <$> fks)
      tableb =  sequenceTable fks

      tableIns = sequenceTable $ filter (any (elem FWrite . keyModifier . _relOrigin) . keyattri . fst) fks
  (listBody,output) <- if rawIsSum table
    then do
      let
        initialSum = join . fmap ((\(n,  j) ->    fmap keyattr $ safeHead $ catMaybes  $ (fmap (_tb . fmap (const ()) ) . unOptionalAttr  . unTB<$> F.toList (_kvvalues (unTB j)))) ) <$> oldItemsPlug
        sumButtom itb =  do
           let i = unTB itb
           lab <- labelCase i  (maybe (join . fmap (fmap unTB .  (^?  Le.ix (S.fromList $ keyattri i) ) . unTBMap ) <$> oldItems) ( triding . snd) (L.find (((keyattri i)==) . keyattri .fst) $  refs)) (justError ("no attr" <> show i) $ M.lookup (keyattri i) $ M.mapKeys (keyattri ) $ M.fromList fks)
           element lab #  set UI.class_ "buttonSet btn-xs btn-default"
      chk  <- buttonDivSet (F.toList (_kvvalues $ unTB k))  (join . fmap (\i -> M.lookup (S.fromList i) (_kvvalues (unTB k))) <$> initialSum ) sumButtom
      element chk # set UI.style [("display","inline-flex")]
      sequence $ (\(kix,el) -> element  el # sink0 UI.style (noneShow <$> ((==keyattri kix) .keyattr <$> facts (triding chk) ))) <$> fks
      let
          resei = liftA2 (\c -> fmap (\t@(m, k) -> (m,) . _tb $ KV (M.mapWithKey  (\k v -> if k == S.fromList (keyattr c) then maybe (addDefault (fmap (const ()) v)) (const v) (unOptionalAttr $ unTB  v) else addDefault (fmap (const ()) v)) (_kvvalues $ unTB k)))) (triding chk) tableb
      listBody <- UI.div #  set children (getElement chk : F.toList (getElement .snd <$> fks))
      return (listBody,join . fmap (\m@(_,l) -> if all (isNothing.unOptionalAttr.unTB) (F.toList $ _kvvalues $ unTB l) then Nothing else Just m) <$> resei)
    else do
      listBody <- UI.div # set UI.class_ "row" #
          set children (F.toList (getElement .snd <$> fks))
      return (listBody,tableb)
  element listBody # set UI.class_ "row" #
      set style [("border","1px"),("border-color","gray"),("border-style","solid"),("margin","1px")]
  plugins <-  if not (L.null (fst <$> res))
    then do
      pluginsHeader <- UI.h4 # set UI.text "Plugins"
      pure <$> UI.div # set children (pluginsHeader : (fst <$> res))
    else do
      return []
  body <- UI.div #
     set children (plugins  <> [listBody]) #
     set style [("margin-left","10px"),("border","2px"),("border-color","gray"),("border-style","solid")]
  return (body, output,tableIns)


crudUITable
   :: InformationSchema
   -> Tidings String
   -> Tidings (Collection Key  Showable)
   -> [(TB Identity Key () ,TrivialWidget (Maybe (TB Identity Key Showable)))]
   -> [(Access Text,Tidings (Maybe (TBData Key Showable)))]
   -> TBData Key ()
   -> Tidings (Maybe (TBData Key Showable))
   -> UI ([Element],Event (TBIdx Key Showable ) ,Tidings (Maybe (TBData Key Showable)))
crudUITable inf open bres refs pmods ftb@(m,_)  preoldItems = do
  (e2,h2) <- liftIO $ newEvent
  (ediff ,hdiff) <- liftIO $ newEvent
  (evdiff ,hvdiff) <- liftIO $ newEvent
  nav  <- buttonDivSet ["None","Editor"{-,"Exception","Change"-}] (fmap Just open) (\i -> UI.button # set UI.text i # set UI.style [("font-size","smaller")] # set UI.class_ "buttonSet btn-xs btn-default pull-right")
  element nav # set UI.class_ "col-xs-4 pull-right"
  let table = lookPK inf (S.fromList $ _kvpk  m )
  let fun "Editor" = do
          let
            getItem :: TBData Key Showable -> TransactionM (Maybe (TBIdx Key Showable))
            getItem  =  (getEd $ schemaOps inf) inf table
          preoldItens <- currentValue (facts preoldItems)
          loadedItens <- liftIO$ join <$> traverse (transaction inf  . getItem) preoldItens
          maybe (return ()) (\j -> liftIO  (hvdiff  =<< traverse (\i -> runDBM inf $  applyRecord'  i j ) preoldItens) )  loadedItens
          (loadedItensEv ,fin) <- mapEventFin (fmap join <$> traverse (transaction inf . getItem )) (rumors preoldItems)
          let oldItemsE =  fmap head $ unions [ evdiff, rumors preoldItems  ]
          ini2 <- liftIO $(maybe (return preoldItens) (\j -> traverse (\i -> return $ Patch.apply i j ) preoldItens ) loadedItens)
          oldItemsB <- stepper  ini2 oldItemsE
          let oldItems = tidings oldItemsB oldItemsE
              deleteCurrent e l =  maybe l (flip M.delete l . getPKM) e
              tpkConstraint :: ([Compose Identity (TB Identity) Key ()], Tidings PKConstraint)
              tpkConstraint = (F.toList $ _kvvalues $ unTB $ tbPK (TB1 ftb) , flip pkConstraint  <$> (deleteCurrent  <$> oldItems <*> fmap snd bres))
          unConstraints <-  traverse (traverse (traverse (mapTEvent (return) )) ) $ (\un -> (F.toList $ _kvvalues $ unTB $ tbUn un  (TB1 $ tableNonRef' ftb) , (un, fmap (createUn un ) (fmap snd bres)))) <$> _kvuniques m
          let
              deleteCurrentUn un e l = maybe l ((\v -> G.delete (v, Idex un v) (3,6) l)  ) e
          unDeleted <- traverse (traverse (traverse (mapTEvent return))) (fmap (fmap (\(un,o)-> (un,deleteCurrentUn un <$> oldItems <*> o))) unConstraints)
          let dunConstraints (un,o) = flip (\i -> unConstraint un (tblist i)) <$> o
              unFinal:: [([Compose Identity (TB Identity) Key ()], Tidings PKConstraint)]
              unFinal = fmap (fmap (dunConstraints)) unDeleted
          (listBody,tableb,inscrud) <- eiTable inf   (tpkConstraint: unFinal ) (_kvname m) refs pmods ftb oldItems
          (panelItems,tdiff)<- processPanelTable inf  (facts tableb) (F.toList . snd <$> facts bres) (inscrud) table oldItems
          let diff = unionWith const tdiff   (filterJust loadedItensEv)
          addElemFin panelItems =<<  onEvent diff
              (liftIO . hdiff)
          addElemFin panelItems =<< onEvent ((\i j -> Just $ maybe (create j) (flip Patch.apply j  ) i) <$> facts oldItems <@> diff )
              (liftIO . hvdiff )
          addElemFin panelItems =<< onEvent (rumors tableb)
              (liftIO . h2)
          addElemFin panelItems fin
          UI.div # set children [listBody,panelItems]
      fun "Change" = do
            UI.div # sink0 items (maybe [] (pure . dashBoardAllTableIndex . (inf,table,) . getPKM ) <$> facts preoldItems )
      fun "Exception" = do
            UI.div # sink0 items (maybe [] (pure . exceptionAllTableIndex . (inf,table,). getPKM ) <$> facts preoldItems )
      fun i = UI.div
  sub <- UI.div # sink items (pure . fun <$> facts (triding nav)) # set UI.class_ "row"
  cv <- currentValue (facts preoldItems)
  bh2 <- stepper  cv (unionWith const e2  (rumors preoldItems))
  return ([getElement nav,sub], ediff ,tidings bh2 (unionWith const e2  (rumors preoldItems)))

addElemFin e = liftIO . addFin e .pure


onBin bin p x y = bin (p x) (p y)

type PKConstraint = [Compose Identity (TB Identity ) Key Showable] -> Bool
type TBConstraint = TBData Key Showable -> Bool

type SelPKConstraint = [([Compose Identity (TB Identity) Key ()],Tidings PKConstraint)]
type SelTBConstraint = [([Compose Identity (TB Identity) Key ()],Tidings TBConstraint)]

pkConstraint v  = isJust . M.lookup (concat . fmap aattr $ v)

unConstraint :: Set Key -> TBData Key Showable -> G.GiST TBIndex (TBData Key Showable) -> Bool
unConstraint u v  = isJust . look (Idex u v)
  where look pk  = safeHead . G.search pk

createUn :: Set Key -> Map b (TBData Key Showable) -> G.GiST TBIndex (TBData Key Showable)
createUn un   =  fromList .  F.toList . traceShow "createUn"
  where
    fromList = foldl'  acc G.empty
    acc !m v = G.insert (v,Idex un  ( v) ) (3,6) m




processPanelTable
   :: InformationSchema
   -> Behavior (Maybe (TBData Key Showable))
   -> Behavior [TBData Key Showable]
   -> Tidings (Maybe (TBData Key Showable))
   -> Table
   -> Tidings (Maybe (TBData Key Showable))
   -> UI (Element, Event (TBIdx Key Showable) )
processPanelTable inf attrsB res inscrud table oldItemsi = do
  let
      contains ref table = maybe False (const True) . L.find  (ope ref)  $ table
        where ope = onBin pkOpSet (concat . fmap aattr . F.toList .  _kvvalues . unTB . tbPK. TB1 )
  insertB <- UI.button #
          set text "INSERT" #
          set UI.class_ "buttonSet" #
          set UI.style (noneShowSpan ("INSERT" `elem` rawAuthorization table ))  #
  -- Insert when isValid
          sink UI.enabled (liftA2 (&&) (isJust . fmap (tableNonRef') <$> facts inscrud ) (liftA2 (\i j -> not $ maybe False (flip contains j) i  ) (facts inscrud ) res))
  editB <- UI.button #
         set text "EDIT" #
         set UI.class_ "buttonSet"#
         set UI.style (noneShowSpan ("UPDATE" `elem` rawAuthorization table )) #
  -- Edit when any persistent field has changed
         sink UI.enabled (liftA2 (&&) (liftA2 (\i j -> maybe False (any fst . F.toList  ) $ liftA2 (liftF2 (\l m -> if l  /= m then (True,(l,m)) else (False,(l,m))) )  i j) (fmap (_kvvalues . unTB . snd . tableNonRef' )<$> attrsB) (fmap (_kvvalues . unTB .  snd .tableNonRef' )<$> facts oldItemsi)) (liftA2 (\i j -> maybe False (flip contains j) i  ) attrsB  res))

  deleteB <- UI.button #
         set text "DELETE" #
         set UI.class_ "buttonSet"#
         set UI.style (noneShowSpan ("DELETE" `elem` rawAuthorization table )) #
  -- Delete when isValid
         sink UI.enabled ( liftA2 (&&) (isJust . fmap (tableNonRef') <$> facts oldItemsi) (liftA2 (\i j -> maybe False (flip contains j) i  ) (facts oldItemsi ) res))
  let
         crudEdi (Just (i)) (Just (j)) =  fmap (\g -> fmap (fixPatch inf (tableName table) ) $diff i  g) $ transaction inf $ fullDiffEdit  inf   i j
         crudIns (Just (j))   =  fmap (tableDiff . fmap ( fixPatch inf (tableName table)) )  <$> transaction inf (fullDiffInsert  inf j)
         crudDel (Just (j))  = fmap (tableDiff . fmap ( fixPatch inf (tableName table)))<$> transaction inf (( deleteEd $ schemaOps inf) inf j)
  (diffEdi,ediFin) <- mapEventFin id $ crudEdi <$> facts oldItemsi <*> attrsB <@ UI.click editB
  (diffDel,delFin ) <- mapEventFin id $ crudDel <$> facts (fmap tableNonRef' <$> oldItemsi) <@ UI.click deleteB
  (diffIns,insFin) <- mapEventFin id $ crudIns <$> facts inscrud <@ UI.click insertB
  addElemFin insertB insFin
  addElemFin deleteB delFin
  addElemFin editB   ediFin
  transaction <- UI.span #
         set children [insertB,editB,deleteB] #
         set UI.style (noneShowSpan (ReadWrite ==  rawTableType table ))
  return (transaction , fmap head $ unions $ fmap filterJust [diffEdi,diffIns,diffDel] )




showFKE v =  UI.div # set text (L.take 50 $ L.intercalate "," $ fmap renderShowable $ allKVRec $  v)

showFK = (pure ((\v j ->j  # set text (L.take 50 $ L.intercalate "," $ fmap renderShowable $ allKVRec  $ v))))

tablePKSet  tb1 = S.fromList $ concat $ fmap ( keyattr)  $ F.toList $ _kvvalues $ unTB $ tbPK  tb1

flabel = UI.span # set UI.class_ (L.intercalate " " ["label","label-default"])

splitArray :: Int -> Int -> [a] -> [a] -> [a]
splitArray s o m l = take o m <> l <> drop  (o + s ) m

takeArray :: Applicative f => [f (Maybe b)] -> f (Maybe [b])
takeArray a = allMaybes . L.takeWhile isJust <$> Tra.sequenceA a

indexItens
  :: (Ord k ,Show k) =>
     Int
     -> TB Identity k a
     -> Tidings Int
     -> [Tidings (Maybe (TB Identity k Showable))]
     -> Tidings (Maybe (TB Identity k Showable))
     -> Tidings (Maybe (TB Identity k Showable))
indexItens s tb@(Attr k v) offsetT atdcomp atdi =
            let tdcomp = fmap (fmap _tbattr) <$>  takeArray atdcomp
                tdi = fmap  _tbattr <$> atdi
                emptyAttr = Just . maybe []  unSComposite
                bres = (\o -> liftA2 (\l m  -> ArrayTB1 (splitArray s o m l  ))) <$> offsetT <*> tdcomp <*> (emptyAttr <$> tdi)
            in fmap (Attr k) <$> bres
indexItens s tb@(FKT ifk rel _) offsetT fks oldItems  = bres
  where  bres2 = takeArray (fmap (fmap (\(FKT i  _ j ) -> (head $ fmap (unAttr.unTB) $ i,  j)) )  <$>  fks)
         emptyFKT = Just . maybe (FKT (mapComp (mapFAttr (const (ArrayTB1 [] ))) <$> ifk) rel (ArrayTB1 []) ) id
         bres = (\o -> liftA2 (\l (FKT lc rel (ArrayTB1 m )) -> FKT ( maybe [] (\lc -> mapComp (mapFAttr (const (ArrayTB1 $ splitArray s o  (unSComposite (unAttr $ unTB lc))  (fst <$>  l)))) <$> ifk) (listToMaybe lc) ) rel (ArrayTB1 $ splitArray s o m (snd <$> l)  ))) <$> offsetT <*> bres2 <*> (emptyFKT <$> oldItems)


indexItens s tb@(IT na _) offsetT items oldItems  = bres
   where bres2 = fmap (fmap _fkttable) <$> takeArray items
         emptyIT = Just . maybe [] (unSComposite . _fkttable)
         bres = (\o -> liftA2 (\l m -> IT   na (ArrayTB1 $ splitArray s o m l ))) <$> offsetT <*> bres2 <*> (emptyIT <$> oldItems)


dynHandler hand val ix (l,old)= do
    (ev,h) <- liftIO $ newEvent
    let idyn True  =  do
          tds <- hand ix
          ini <- currentValue (facts $ triding tds)
          liftIO $ h ini
          fin <- onEvent (rumors $ triding tds) (liftIO . h)
          addElemFin (getElement tds) fin
          return (getElement tds)
        idyn False = do
          liftIO $ h Nothing
          UI.div
    el <- UI.div # sink items (pure . idyn  <$> old )
    iniv <- currentValue (facts $ val ix)
    bend <- stepper iniv ev
    let notProp = filterE isNothing $ notdiffEvent bend  (ev)
    bend2 <- stepper iniv  (diffEvent bend  ev)
    bendn <- stepper (isJust iniv ) (diffEvent (fmap isJust bend ) (fmap isJust ev))
    bendn2 <- stepper (isJust iniv ) (diffEvent bendn  (fmap isJust ev))
    return $ (l <> [TrivialWidget (tidings bend2 (bend2 <@ notProp )) el], bendn2  )



attrUITable
  :: Tidings (Maybe (TB Identity Key Showable))
     -> [Tidings (Maybe (TB Identity Key Showable))]
     -> TB Identity Key ()
     -> UI (TrivialWidget (Maybe (TB Identity Key Showable)))
attrUITable tAttr' evs attr@(Attr i@(Key _ _ _ _ _ _ (KOptional _) ) v) = do
      res <- attrUITable (join . fmap unLeftItens <$> tAttr') (fmap (join. fmap unLeftItens ) <$>  evs) (Attr (unKOptional i) v)
      return (leftItens attr <$> res)
attrUITable tAttr' evs attr@(Attr i@(Key _ _ _ _ _ _ (KArray _) ) v) = mdo
          offsetDiv  <- UI.div
          let wheel = fmap negate $ mousewheel offsetDiv
          TrivialWidget offsetT offset <- offsetField 0  wheel (maybe 0 (length . (\(ArrayTB1 l ) -> l) . _tbattr) <$> facts bres)
          let arraySize = 8
          let dyn = dynHandler (\ix -> attrUITable (unIndexItens ix  <$> offsetT <*> tAttr')  ((unIndexItens ix  <$> offsetT <*> ) <$>  evs) (Attr (unKArray i) v  )) (\ix -> unIndexItens ix  <$> offsetT <*> tAttr')
          widgets <- fst <$> foldl' (\i j -> dyn j =<< i ) (return ([],pure True)) [0..arraySize -1 ]
          let
            bres = indexItens arraySize  attr offsetT (triding <$> widgets) tAttr'
          element offsetDiv # set children (fmap getElement widgets)
          paintBorder offsetDiv (facts bres ) (facts tAttr' )
          composed <- UI.span # set children [offset , offsetDiv]
          when (isReadOnly attr )
            $ void (element composed # sink UI.style (noneShow . isJust <$> facts bres))
          return  $ TrivialWidget  bres composed
attrUITable  tAttr' evs attr@(Attr i _ ) = do
      tdi' <- foldr (\i j ->  updateTEvent  (fmap Just) i =<< j) (return tAttr') evs
      let tdi = fmap (\(Attr  _ i )-> i) <$>tdi'
      attrUI <- buildUI (keyModifier i)(mapKType $ keyType i) tdi
      let insertT = fmap (Attr i ) <$> (triding attrUI)
      when (isReadOnly attr )
              $ void (element attrUI # sink UI.style (noneShow . isJust <$> facts insertT ))
      return $ TrivialWidget insertT  (getElement attrUI)

buildUI :: [FieldModifier] -> KType (Prim KPrim (Text,Text))-> Tidings (Maybe (FTB Showable)) -> UI (TrivialWidget (Maybe (FTB Showable)))
buildUI km i  tdi = go i tdi
  where go i tdi = case i of
         (KSerial ti) -> do
           tdnew <- fmap (Just . SerialTB1 ) <$> go ti ( join . fmap unSSerial <$> tdi)
           retUI <- UI.div # set children [getElement tdnew]
           paintBorder retUI (facts $ triding tdnew) (facts tdi)
           return $ TrivialWidget (triding tdnew ) retUI
         (KDelayed ti) -> do
           tdnew <- fmap (maybe Nothing (Just .DelayedTB1 . Just)  ) <$> go ti (join . fmap unSDelayed <$> tdi)
           retUI <- UI.div# set children [getElement tdnew]
           paintBorder retUI (facts $ triding tdnew) (facts tdi)
           return $ TrivialWidget (triding tdnew ) retUI
         (KInterval ti) -> do
            let unInterval f (IntervalTB1 i ) = f i
                unInterval _ i = errorWithStackTrace (show i)
            inf <- fmap (fmap ER.Finite) <$> go ti (fmap (unInterval inf' ) <$> tdi)
            sup <- fmap (fmap ER.Finite) <$> go ti (fmap (unInterval sup')  <$> tdi)
            lbd <- fmap Just <$> checkedWidget (maybe False id . fmap (\(IntervalTB1 i) -> snd . Interval.lowerBound' $i) <$> tdi)
            ubd <- fmap Just <$> checkedWidget (maybe False id .fmap (\(IntervalTB1 i) -> snd . Interval.upperBound' $i) <$> tdi)
            composed <- UI.div # set UI.style [("display","inline-flex")] # set UI.children [getElement lbd ,getElement  inf,getElement sup,getElement ubd]
            subcomposed <- UI.div # set UI.children [composed]
            let td = (\m n -> fmap IntervalTB1 $  join . fmap (\i-> if Interval.null i then Nothing else Just i) $ liftF2 interval m n) <$> (liftA2 (,) <$> triding inf  <*> triding lbd) <*> (liftA2 (,) <$> triding sup <*> triding ubd)
            paintBorder subcomposed (facts td ) (facts tdi)
            return $ TrivialWidget td subcomposed
         (Primitive (AtomicPrim i) ) -> fmap (fmap TB1) <$> buildPrim km (fmap (\(TB1 i )-> i) <$> tdi) i
         i -> errorWithStackTrace (show i)

buildPrim :: [FieldModifier] ->Tidings (Maybe Showable) ->   KPrim -> UI (TrivialWidget (Maybe Showable))
buildPrim fm tdi i = case i of
         {-PPosition -> do
            let addrs = fmap (\(SPosition (Position (lon,lat,_)))-> "http://maps.google.com/?output=embed&q=" <> (urlEncode False $ BSC.pack $show lat  <> "," <>  show lon )) <$>  tdi
            el <- mkElement "iframe" # sink UI.src (maybe "" BSC.unpack <$> facts addrs) # set style [("width","99%"),("height","300px")]
            return $ TrivialWidget tdi el-}
         PBoolean -> do
           res <- checkedWidgetM (fmap (\(SBoolean i) -> i) <$> tdi )
           return (fmap SBoolean <$> res)
         PTimestamp dbzone -> do
            cliZone <- jsTimeZone
            itime <- liftIO $  getCurrentTime
            timeButton <- UI.button # set UI.text "now"
            (evCurr ,fin)<-  mapEventFin (fmap Just) (pure getCurrentTime <@ UI.click timeButton)
            let  newEv = fmap (STimestamp . utcToLocalTime cliZone ) <$> evCurr
                 maptime f (STimestamp i) = STimestamp (f i)
                 toLocal = maptime  (utcToLocalTime cliZone . localTimeToUTC utc)
                 fromLocal = maptime (utcToLocalTime utc .localTimeToUTC cliZone)

            tdi2 <- addEvent newEv  (fmap toLocal <$> tdi)
            fmap (fmap fromLocal) <$> oneInput tdi2 [timeButton]
         PDate -> do
            cliZone <- jsTimeZone
            itime <- liftIO $  getCurrentTime
            timeButton <- UI.button # set UI.text "now"
            evCurr <-  mapEvent (fmap Just) (pure getCurrentTime <@ UI.click timeButton)
            let  newEv =  fmap (SDate . localDay . utcToLocalTime cliZone) <$> evCurr
            tdi2 <- addEvent newEv  tdi
            oneInput tdi2 [timeButton]
         PDayTime -> do
            cliZone <- jsTimeZone
            itime <- liftIO $  getCurrentTime
            timeButton <- UI.button # set UI.text "now"
            evCurr <-  mapEvent (fmap Just) (pure getCurrentTime <@ UI.click timeButton)
            let  newEv = fmap (SDayTime. localTimeOfDay . utcToLocalTime cliZone) <$> evCurr
            tdi2 <- addEvent newEv  tdi
            oneInput tdi2 [timeButton]
         PSession -> do
           dv <- UI.div # set text "session" # sink UI.style (noneShow . isJust <$> facts tdi)
           return  $ TrivialWidget tdi dv
         PMime "text/plain" -> do
           let fty = ("textarea","value",maybe "" (\(SBinary i) -> BSC.unpack i) ,[("width","100%"),("height","300px")])
           ini <- currentValue (facts tdi)
           f <- pdfFrame fty (facts tdi) # sink UI.style (noneShow . (\i -> isJust i || elem FWrite fm) <$> facts tdi)
           let ev = if elem FWrite fm then unionWith const (rumors tdi) (Just . SBinary . BSC.pack <$> UI.valueChange f) else rumors tdi
           step <- stepper  ini ev
           return (TrivialWidget (tidings step ev) f)
         PMime mime -> do
           let binarySrc = (\(SBinary i) -> "data:" <> T.unpack mime <> ";base64," <>  (BSC.unpack $ B64.encode i) )
           clearB <- UI.button # set UI.text "clear"
           file <- UI.input # set UI.type_ "file" # set UI.multiple True # set UI.style (noneShow $ elem FWrite fm)
           runFunction$ ffi "$(%1).on('change',handleFileSelect);" file
           tdi2 <- addEvent (join . fmap (fmap SBinary . either (const Nothing) Just .   B64.decode .  BSC.drop 7. snd  . BSC.breakSubstring "base64," . BSC.pack ) <$> fileChange file ) =<< addEvent (const Nothing <$> UI.click clearB) tdi
           let fty = case mime of
                "application/pdf" -> ("iframe","src",maybe "" binarySrc ,[("width","100%"),("height","300px")])
                "application/x-ofx" -> ("textarea","value",maybe "" (\(SBinary i) -> BSC.unpack i) ,[("width","100%"),("height","300px")])
                "image/jpg" -> ("img","src",maybe "" binarySrc ,[])
                "text/html" -> ("iframe","srcdoc",maybe "" (\(SBinary i) -> BSC.unpack i) ,[("width","100%"),("height","300px")])
           f <- pdfFrame fty (facts tdi2) # sink0 UI.style (noneShow . isJust <$> facts tdi2)
           fd <- UI.div # set UI.style [("display","inline-flex")] # set children [file,clearB]
           res <- UI.div # set children [fd,f]
           paintBorder res (facts tdi2) (facts  tdi)
           return (TrivialWidget tdi2 res)
         z -> do
            oneInput tdi []
  where
    oneInput :: Tidings (Maybe Showable) -> [Element] ->  UI (TrivialWidget (Maybe Showable))
    oneInput tdi elem = do
            let f = facts tdi
            v <- currentValue f
            inputUI <- UI.input # sink0 UI.value (maybe "" renderPrim <$> f)
            let pke = unionWith const (readPrim i <$> UI.valueChange inputUI) (rumors tdi)
            pk <- stepper v  pke
            let pkt = tidings pk (diffEvent pk pke)
            sp <- UI.div # set children (inputUI : elem)
            paintBorder sp (facts pkt) (facts tdi)
            return $ TrivialWidget pkt sp



iUITable
  :: InformationSchema
  -- Plugin Modifications
  -> [(Access Text,Tidings (Maybe (TB Identity Key (Showable))))]
  -- Selected Item
  -> Tidings (Maybe (TB Identity Key Showable))
  -- Static Information about relation
  -> TB Identity Key ()
  -> UI (TrivialWidget(Maybe (TB Identity Key Showable)))
iUITable inf pmods oldItems  tb@(IT na  tb1@(TB1 tdata@(meta,_)) )
    = do
      let tfun = eiTable
      (celem,tcrud,_) <- tfun inf [] (_kvname meta )
              []
              (fmap (fmap (fmap (unTB1 ._fkttable))) <$> pmods)
              tdata
              (fmap (unTB1._fkttable) <$> oldItems)
      element celem #
          set style [("margin-left","10px")]
      let bres =  fmap (fmap (IT  na  ) ) (fmap TB1 <$> tcrud)
      return $ TrivialWidget bres celem
iUITable inf pmods oldItems  tb@(IT na (LeftTB1 (Just tb1))) = do
   tr <- iUITable inf (fmap (join . fmap unLeftItens  <$> ) <$> pmods) (join . fmap unLeftItens <$> oldItems) (IT na tb1)
   return $  leftItens tb <$> tr
iUITable inf plmods oldItems  tb@(IT na (ArrayTB1 [tb1]))
    = mdo
      dv <- UI.div
      let wheel = fmap negate $ mousewheel dv
          arraySize = 8
      (TrivialWidget offsetT offset) <- offsetField 0 wheel (maybe 0 (length . (\(IT _ (ArrayTB1 l) ) -> l)) <$> facts bres )
      let unIndexEl ix = (unIndexItens  ix <$> offsetT <*> )
      let dyn = dynHandler (\ix -> iUITable inf
                (fmap (unIndexEl  ix) <$> plmods)
                (unIndexEl ix oldItems)
                (IT  na tb1)) (flip unIndexEl oldItems)
      items <- fst <$> foldl' (\i j -> dyn j =<< i ) (return ([],pure True)) [0..arraySize -1 ]
      let bres = indexItens arraySize tb offsetT (triding <$>  items ) oldItems
      element dv  # set children (offset : (getElement <$> items))
      return $ TrivialWidget bres  dv

offsetField  init eve  max = do
  offsetL <- UI.span # set text "Offset: "
  offset <- UI.input # set UI.style [("width","50px")]
  leng <- UI.span # sink text (("Size: " ++) .show  <$> max )
  offparen <- UI.div # set children [offsetL,offset,leng]

  let offsetE =  filterJust $ (\m i -> if i <m then Just i else Nothing ) <$> max <@> (filterJust $ readMaybe <$> onEnter offset)
      ev = unionWith const (negate <$> mousewheel offparen) eve
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
      filt = ( filterJust $ diff <$> offsetB <*> max <@> ev  )
      ev2 = (fmap concatenate $ unions [fmap const offsetE,filt ])
    offsetB <- accumB init ev2
    return (offsetB,ev2)
  element offset # sink UI.value (show <$> offsetB)
  let
     cev = flip ($) <$> offsetB <@> ev2
     offsetT = tidings offsetB cev
  return (TrivialWidget offsetT offparen)


tbrefM i@(FKT _  _ _)  =  L.sort $_tbref i
tbrefM j = [_tb  j ]


isReadOnly (FKT ifk rel _ ) = L.null ifk || all (not . any ((/= FRead)). keyModifier . _relOrigin) rel
isReadOnly (Attr k _ ) =  (not . any ((/= FRead)). keyModifier ) k
isReadOnly (IT k _ ) =   (isReadOnly $ unTB k)

fkUITable
  ::
  InformationSchema
  -- Plugin Modifications
  -> SelTBConstraint
  -> [(Access Text,Tidings (Maybe (TB Identity Key Showable)))]
  -- Same Table References
  -> [(TB Identity Key () ,TrivialWidget (Maybe (TB Identity Key (Showable))))]
  -- Relation Event
  -> Tidings (Maybe (TB Identity Key Showable))
  -- Static Information about relation
  -> TB Identity Key ()
  -> UI (TrivialWidget(Maybe (TB Identity Key Showable)))
fkUITable inf constr plmods wl  oldItems  tb@(FKT ifk rel tb1@(TB1 _  ) ) = mdo
      let
          relTable = M.fromList $ fmap (\(Rel i _ j ) -> (j,i)) rel
          rr = tablePKSet tb1
          table = justError "no table found" $ M.lookup (S.map _relOrigin rr) $ pkMap inf

      ((DBVar2 tmvard _ _ vpdiff _ _ ),resi)  <-  (liftIO $ transaction inf $ eventTable inf table (Just 0) Nothing  [] [])
      bres <- accumB resi (flip (foldl' (\ e  p-> fmap (flip Patch.apply p) e)) <$> rumors vpdiff)
      let
          vpt =  tidings bres ((foldl' (\ e  p-> fmap (flip Patch.apply p) e)) <$> bres <@> rumors vpdiff )
          res = fmap TB1 <$> resi
      let
          -- Find non injective part of reference
          ftdi = oldItems
          oldASet :: Set Key
          oldASet = S.fromList (_relOrigin <$> filterNotReflexive rel )
          replaceKey =  firstTB (\k -> maybe k _relTarget $ L.find ((==k)._relOrigin) $ filter (\i -> keyType (_relOrigin i) == keyType (_relTarget i)) rel)
          nonInj =   S.difference (S.fromList $ fmap  _relOrigin   $ rel) (S.fromList $ getRelOrigin ifk)
          nonInjRefs = filter (flip S.isSubsetOf nonInj . S.fromList . fmap _relOrigin . keyattr . _tb .fst) wl
          staticold :: [(TB Identity Key () ,TrivialWidget (Maybe (TB Identity Key (Showable))))]
          staticold  =    second (fmap (fmap replaceKey . join . fmap unLeftItens)) . first (replaceKey .unLeftKey) <$>  nonInjRefs
          iold :: Tidings [Maybe [(Key,FTB Showable)]]
          iold  = Tra.sequenceA $ fmap (fmap ( aattr . _tb ) ) . triding .snd <$> L.filter (\i-> not . S.null $ S.intersection (S.fromList $ fmap _relOrigin $ keyattr . _tb . fst $ i) oldASet) wl
          iold2 :: Tidings (Maybe [TB Identity  Key Showable])
          iold2 =  join . (fmap (traverse ((traFAttr unRSOptional2 ) . firstTB unRKOptional ))) .  fmap (fmap ( uncurry Attr) . concat) . allMaybes <$> iold
          ftdi2 :: Tidings (Maybe [TB Identity  Key Showable])
          ftdi2 =   fmap (fmap unTB. tbrefM ) <$> ftdi
          res3 :: Tidings [TB1 Showable]
          res3 =  foldr (\constr  res2 -> (\el constr -> filter (not. constr. unTB1 ) el)  <$> res2  <*> snd constr ) (tidings (F.toList . snd <$> res2) never) constr
          unRKOptional (Key v a b d n m (KOptional c)) = Key v a b d n m c
          unRKOptional i = i
      let
          search = (\i j -> join $ fmap (\k-> L.find (\(TB1 (kv,l) )->  interPointPost (filter (flip S.member (S.fromList $ _kvpk kv) . _relTarget) rel) k  (concat $ fmap (uncurry Attr) . aattr <$> (F.toList . _kvvalues . unTB $ l)) ) i) $ j )
          vv :: Tidings (Maybe [TB Identity Key Showable])
          vv =   liftA2 (<>) iold2  ftdi2
      cvres <- currentValue (facts vv)
      filterInp <- UI.input
      filterInpBh <- stepper "" (UI.valueChange filterInp)
      let
          cv = search (inisort $ F.toList $ snd res) cvres
          tdi =  search <$> res3 <*> vv
          filterInpT = tidings filterInpBh (UI.valueChange filterInp)
          filtering i  = T.isInfixOf (T.pack $ toLower <$> i) . T.toLower . T.intercalate "," . fmap (T.pack . renderPrim ) . F.toList .    _unTB1
          sortList :: Tidings ([TB1 Showable] -> [TB1 Showable])
          sortList =  sorting  <$> pure (fmap ((,True)._relTarget) rel)
      itemList <- if isReadOnly tb
        then
           TrivialWidget (Just  <$> tdi ) <$>
              (UI.div #
                set UI.style [("border","1px solid gray")] #
                sink items (pure . maybe UI.div showFKE  . fmap _fkttable<$> facts oldItems ))
        else
           listBox ((Nothing:) . reverse <$>  fmap (fmap Just) res3) (tidings (fmap Just <$> st) never) (pure id) ((\i j -> maybe id (\l  ->   (set UI.style (noneShow $ filtering j l  ) ) . i  l ) )<$> showFK <*> filterInpT)

      let evsel = (if isReadOnly tb then id else unionWith const (rumors tdi) ) (rumors $ join <$> triding itemList)
      prop <- stepper cv evsel
      let ptds = tidings prop evsel
      tds <- foldr (\i j ->updateEvent  Just  i =<< j)  (return ptds) (fmap Just . fmap _fkttable.filterJust . rumors . snd <$>  plmods)
      (celem,ediff,pretdi) <-crudUITable inf (pure "None") ( vpt ) staticold (fmap (fmap (fmap (unTB1 . _fkttable))) <$> plmods)  (unTB1 tb1 ) (fmap unTB1 <$> tds)
      (diffUp,fin2) <-  mapEventFin (fmap pure ) $ (\i j -> traverse (fmap TB1 . runDBM inf .  flip applyRecord' j ) i) <$>  facts pretdi <@> ediff
      let
          sel = filterJust $ fmap (safeHead.concat) $ unions $ [(unions  [(rumors $ join <$> triding itemList), if isReadOnly tb then never else rumors tdi]),diffUp]
      st <- stepper cv sel
      inisort <- currentValue (facts sortList)
      res2 <- stepper res  (fmap (fmap TB1) <$> rumors vpt)

      fin <- onEvent (pure <$> ediff) (liftIO .  putMVar tmvard)
      let
        fksel =  fmap (\box ->  FKT (backFKRef  relTable  (fmap (keyAttr .unTB )ifk)   box) rel box ) <$>  ((\i j -> maybe i Just ( j)  ) <$> fmap (fmap TB1) pretdi <*> tidings st sel)
      element itemList # set UI.class_ "col-xs-5"
      element filterInp # set UI.class_ "col-xs-3"
      fk <- if isReadOnly tb
          then
            UI.div # set  children [getElement itemList ,head celem]  # set UI.class_ "row"
          else
            UI.div # set  children [getElement itemList ,filterInp,head celem]  # set UI.class_ "row"
      subnet <- UI.div # set children [fk,last celem] # set UI.class_ "col-xs-12"
      when (isReadOnly tb  ) $
                void $  element subnet # sink0 UI.style (noneShow . isJust <$> facts oldItems )
      addElemFin (getElement subnet) fin
      addElemFin (getElement subnet) fin2
      return $ TrivialWidget (if isReadOnly  tb then oldItems  else fksel ) subnet
fkUITable inf constr plmods  wl oldItems  tb@(FKT ilk rel  (DelayedTB1 (Just tb1 ))) = do
    tr <- fkUITable inf constr  plmods  wl oldItems  (FKT  ilk  rel tb1)
    return $ tr

fkUITable inf constr plmods  wl oldItems  tb@(FKT ilk rel  (LeftTB1 (Just tb1 ))) = do
    tr <- fkUITable inf constr (fmap (join . fmap unLeftItens <$>) <$> plmods)  wl (join . fmap unLeftItens  <$> oldItems)  (FKT (mapComp (firstTB unKOptional) <$> ilk) (Le.over relOrigin unKOptional <$> rel) tb1)
    return $ leftItens tb <$> tr
fkUITable inf constr plmods  wl oldItems  tb@(FKT ifk rel  (ArrayTB1 [tb1]) ) = mdo
     dv <- UI.div
     let wheel = fmap negate $ mousewheel dv
         arraySize = 8
     (TrivialWidget offsetT offset) <- offsetField 0 (wheel) (maybe 0 (length . (\(FKT _  _ (ArrayTB1 l) ) -> l)) <$> facts bres)
     let
         fkst = FKT (mapComp (firstTB unKArray)<$> ifk ) (fmap (Le.over relOrigin (\i -> if isArray (keyType i) then unKArray i else i )) rel)  tb1
     let dyn = dynHandler (\ix-> do
           lb <- UI.div # sink UI.text (show . (+ix) <$> facts offsetT ) # set UI.class_ "col-xs-1"
           TrivialWidget tr el<- fkUITable inf constr (fmap (unIndexItens  ix <$> offsetT <*> ) <$> plmods) wl (unIndexItens ix <$> offsetT  <*>  oldItems) fkst
           element el # set UI.class_ "col-xs-11"
           TrivialWidget tr <$> UI.div # set UI.children [lb,el] ) (\ix -> unIndexItens ix <$> offsetT  <*>  oldItems)
     fks <- fst <$> foldl' (\i j -> dyn j =<< i ) (return ([],pure True)) [0..arraySize -1 ]
     sequence $ zipWith (\e t -> element e # sink0 UI.style (noneShow <$> facts t)) (getElement <$> fks) (pure True : (fmap isJust . triding <$> fks))
     element dv # set children (getElement <$> fks)
     let bres = indexItens arraySize  tb offsetT (triding <$> fks) oldItems
     res <- UI.div # set children [offset ,dv]
     return $  TrivialWidget bres  res


pdfFrame (elem,sr , call,st) pdf = mkElement (elem ) UI.# sink0 (strAttr sr) (call <$> pdf)  UI.# UI.set style (st)

strAttr :: String -> WriteAttr Element String
strAttr name = mkWriteAttr (set' (attr name))


data AscDesc a
  = AscW a
  | DescW a
  deriving(Eq)

instance Ord a => Ord (AscDesc a) where
  compare (AscW a ) (AscW b) =  compare a b
  compare (DescW a ) (DescW b) = compare (Down a ) (Down b)

sorting' :: [(Key,Bool)] -> [TBData Key Showable]-> [TBData Key Showable]
sorting' ss  =  L.sortBy (comparing   (L.sortBy (comparing fst) . fmap (\((ix,i),e) -> (ix,if i then DescW e  else AscW e) ) . F.toList .M.intersectionWith (,) (M.fromList (zipWith (\i (k,v) -> (k ,(i,v))) [0..] ss)) . M.fromList . concat . fmap aattr  . F.toList . _kvvalues . unTB . snd )  )

sorting k = fmap TB1 . sorting' k . fmap unTB1


rendererShowableUI k  v= renderer (keyValue k) v
  where renderer "modification_data" (SBinary i) = either (\i-> UI.div # set UI.text (show i)) (\(_,_,i ) -> showPatch (i:: PathAttr Text Showable) )  (B.decodeOrFail (BSL.fromStrict i))
        renderer k i = UI.div # set text (renderPrim i)
        showPatch l = UI.div # set text (show $ fmap renderPrim l)

foldMetaHeader = foldMetaHeader' []

foldMetaHeader' :: [Key] -> UI Element -> (Key -> a -> (UI Element)) -> InformationSchema -> TBData Key a -> [UI Element]
foldMetaHeader' order el rend inf = mapFAttr order (\(Attr k v) -> hideLong (F.toList $ rend  k <$> v ))
    where
          mapFAttr order f (a,kv) = fmap snd. L.sortBy (comparing ((flip L.elemIndex order).  fst) ). concat $ (  fmap (match.unTB ) .  F.toList .  _kvvalues)  $ unTB kv
            where match i@(Attr k v) = [(k,f i)]
                  match i@(FKT l rel t) = ((\k -> (_relOrigin $ head $ keyattr k ,). f . unTB  $ k)<$> l )
                  match i@(IT l t) = [(_relOrigin $ head $ keyattr l,hideLong ( concat $ F.toList $ fmap (foldMetaHeader  UI.div rend inf) t))]
          hideLong l = do
            elemD <- el
            if length l > 1
              then do
                bh <- stepper False (hoverTip  elemD)
                element elemD # sink items ((\b -> if not b then take 2  l  <> fmap ( set UI.style (noneShow False)) (drop 2 l) else  l ) <$> bh)
              else return elemD # set items l

hoverTip elemD= unionWith const (const True <$> UI.hover elemD ) (const False <$> UI.leave elemD)


metaAllTableIndexV inf metaname env = metaAllTableIndexA inf metaname (fmap (uncurry Attr ) env)
metaAllTableIndexA inf metaname env =   do
  let modtable = lookTable (meta inf) tname
      tname = metaname
      envK :: [(Text,(TB Identity Key Showable))]
      envK = fmap (("=",).liftField (meta inf) tname) env
  viewer (meta inf) modtable (Just envK)

dashBoardAllTable  inf table = metaAllTableIndexV inf "modification_table" [("schema_name",TB1 $ SText (schemaName inf) ),("table_name",TB1 $ SText (tableName table) ) ]
exceptionAllTable inf table = metaAllTableIndexV inf "plugin_exception" [("schema_name",TB1 $ SText (schemaName inf) ),("table_name",TB1 $ SText (tableName table) ) ]


sortFilter :: [Key] -> [(Key,Bool)] -> [(Key,(Text,Text))] -> UI Element -> UI Element -> ((Key,Maybe Bool) -> String) -> UI (TrivialWidget [(Key,Maybe Bool,Maybe (String,FTB Showable))])
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
  let opE = UI.valueChange op
      vfE =  UI.valueChange vf
  opB <- stepper "" opE
  vfB <- stepper "" vfE
  let
      ev0 = flip (\(l,t,op,vf)-> const (l,step t,op,vf)) <$>  UI.click dv
      ev1 = flip (\(l,t,op,vf) opn -> (l,t,(readValid opn) ,vf)) <$>  opB <@ UI.click fi
      ev2 = flip (\(l,t,op,vf) vfn -> (l,t,op , (readType (mapKType $ keyType l) vfn))) <$>  vfB <@ UI.click fi
  block <- UI.div # set children [dv,op,vf,fi]
  return $ TrivialWidget (tidings bh ((\ini@(l,t,op) f -> (\(l,t,op,v) -> (l , t ,liftA2 (,) op v)) $ f (l,t,fmap fst op , fmap snd op) ) <$> bh <@> (concatenate <$> unions [ev0,ev1,ev2]) )) block



viewer :: InformationSchema -> Table -> Maybe [(Text ,Column Key Showable)] -> UI Element
viewer inf table env = mdo
  let
      envK = concat $ maybeToList env
      filterStatic =filter (not . flip L.elem (fmap (_relOrigin . head . keyattri  . snd) envK))
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
                  flist = catMaybes $ fmap (\(i,_,j) -> second (Attr i) . first T.pack <$> j) slist'
              (_,(fixmap,lres)) <- liftIO $ transaction inf $ eventTable  inf table  (Just o) Nothing  (fmap (\t -> if t then Desc else Asc ) <$> ordlist) (traceShowId $ envK <> flist)
              let (size,_) = justError ("no fix" <> show (envK ,fixmap)) $ M.lookup (L.sort $ fmap snd envK) fixmap
              return (o,(slist,paging o (size,sorting' ordlist (F.toList lres))))
      nearest' :: M.Map Int (TB2 Key Showable) -> Int -> ((Int,Maybe (Int,TB2 Key Showable)))
      nearest' p o =  (o,) $ safeHead $ filter ((<=0) .(\i -> i -o) .  fst) $ reverse  $ L.sortBy (comparing ((\i -> (i - o)). fst )) (M.toList p)
      ini = nearest' iniPg 0
      addT (c,(s,(cou,td))) = M.insert (c +1)  <$>  (fmap TB1 $ safeHead $reverse td)
  iniQ <- liftIO$ makeQ iniSort ini
  offset <- offsetField 0 (never ) (ceiling . (/pageSize). fromIntegral <$> offsetTotal)
  let
      event1 , event2 :: Event (IO (Int,([(Key,Maybe Bool)],(Int,[TBData Key Showable]))))
      event1 = (\(j,k) i  -> makeQ i (nearest' j k )) <$> facts ((,) <$> pure iniPg <*> triding offset) <@> rumors (triding sortList)
      event2 = (\(j,i) k  -> makeQ i (nearest' j k )) <$> facts ((,) <$> pg <*> triding sortList) <@> rumors (triding offset)
      evs = (unionWith const event1 event2)
  tdswhere <- mapEvent id evs
  offsetTotal <- stepper (fst $ snd $ snd $ iniQ) (fmap (fst . snd .snd ) tdswhere)
  pg <- accumT ((fromJust  $addT iniQ ) M.empty ) (unionWith (flip (.)) ((pure (const iniPg ) <@ event1)) (filterJust (addT <$> tdswhere )))

  tdswhereb <- stepper (snd iniQ) (fmap snd tdswhere)
  let
      tview = unTlabel' . unTB1  $tableSt2
  element itemList # set items ( pure . renderTableNoHeaderSort2   (return $ getElement sortList) inf (tableNonRef' tview) $   fmap (fmap (filterRec' (fmap (_relOrigin . head .keyattri . snd ) $ concat $ maybeToList env) . tableNonRef')) . (\(slist ,(coun,tb))-> (fmap fst slist,tb))  <$>   tdswhereb )

  UI.div # set children [getElement offset, itemList]


exceptionAllTableIndex e@(inf,table,index) =   metaAllTableIndexA inf "plugin_exception" envA
  where
        envA = [Attr "schema_name" (TB1 $ SText (schemaName inf))
              , Attr "table_name" (TB1 $ SText (tableName table))
              , IT (_tb $ Attr "data_index2" (TB1 () ) ) (ArrayTB1 $  fmap ((\(i,j) -> TB1 $tblist $ fmap _tb [Attr "key" (TB1 $ SText i) ,Attr "val" (TB1 (SDynamic j))]). first keyValue)index) ]


dashBoardAllTableIndex e@(inf,table,index) =   metaAllTableIndexA inf "modification_table" envA
  where
        envA = [Attr "schema_name" (TB1 $ SText (schemaName inf))
              , Attr "table_name" (TB1 $ SText (tableName table))
              , IT (_tb $ Attr "data_index2" (TB1 () ) ) (ArrayTB1 $  fmap ((\(i,j) -> TB1 $tblist $ fmap _tb [Attr "key" (TB1 $ SText i) ,Attr "val" (TB1 (SDynamic j))]). first keyValue)index) ]


filterRec' envK = filterTB1' (not . (`S.isSubsetOf`  (S.fromList envK )) . S.fromList . fmap _relOrigin.  keyattr )

renderTableNoHeaderSort2 header inf modtablei out = do
  let
      body sort o = UI.tr # set UI.class_ "row" #  set items (foldMetaHeader' sort UI.td rendererShowableUI inf $ o)
  header # set UI.class_ "row"
  UI.table # set UI.class_ "table table-bordered table-striped" # sink items ((\(i,l)-> header : fmap (body i) l )<$> out)

