{-# LANGUAGE BangPatterns,FlexibleInstances,OverloadedStrings,ScopedTypeVariables,FlexibleContexts,ExistentialQuantification,TupleSections,LambdaCase,RankNTypes,RecordWildCards,DeriveFunctor,NoMonomorphismRestriction,RecursiveDo #-}
module TP.QueryWidgets where

import RuntimeTypes
import SortList
import Data.Functor.Identity
import Control.Monad.Writer
import Control.Monad
import qualified Data.Binary as B
import Control.Concurrent
import qualified Data.Poset as P
import Reactive.Threepenny
import Data.Either
import qualified Graphics.UI.Threepenny as UI
import Graphics.UI.Threepenny.Core hiding (delete)
import Data.String
import Data.Bifunctor
import Data.Ord
import Control.Lens ((^?))
import qualified Control.Lens as Le
import Utils
import Data.Char
import Patch
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Set (Set)
import Data.Traversable(Traversable,traverse)
import qualified Data.Traversable as Tra
import qualified Data.ByteString.Base64 as B64
import Data.Monoid
import Safe
import Data.Interval (interval)
import qualified Data.ExtendedReal as ER
import qualified Data.Interval as Interval
import qualified Data.List as L
import Text.Read
import Data.Text.Lazy (Text)
import Types
import Query
import Postgresql
import PostgresQuery
import Data.Maybe
import Data.Time
import qualified Data.Vector as V
import Data.Functor.Apply
import TP.Widgets
import Schema
import Step
import qualified Data.Foldable as F
import Data.Foldable (foldl')
import Data.Tuple
import Database.PostgreSQL.Simple
import Control.Exception
import Debug.Trace
import qualified Data.Text.Lazy as T
import qualified Data.ByteString.Char8 as BSC
import qualified Data.ByteString.Lazy.Char8 as BSL
import GHC.Stack



generateFresh = do
  (e,h) <- liftIO $ newEvent
  b <- stepper Nothing e
  return $ (h,tidings b e)



createFresh n tname pmap i ty  =  do
  k <- newKey i ty 0
  return $ M.insert (n,tname,i) k pmap

testTable i =  (\t ->  checkTable  t i)


pluginUI oinf initItems (StatefullPlugin n tname tf fresh (WrappedCall init ac ) ) = do
  window <- askWindow
  let tdInput = isJust . join . fmap (flip testTable  (fst $ head tf ))  <$>   initItems
  headerP <- UI.button # set text (T.unpack n) # sink UI.enabled (facts tdInput)
  trinp <- cutEvent (UI.click headerP) initItems
  m <- liftIO $  foldl' (\i (kn,kty) -> (\m -> createFresh  n tname m kn kty) =<< i ) (return $ pluginsMap oinf) (concat fresh)
  let inf = oinf {pluginsMap = m}
      freshKeys :: [[Key]]
      freshKeys = fmap (lookFresh  inf n tname . fst ) <$> fresh
  freshUI <- Tra.sequence $   zipWith (\(input,output) freshs -> do
      (h,t :: Tidings (Maybe (TB1 Showable)) ) <- liftIO $ generateFresh
      elems <- mapM (\fresh -> do
        let hasF l = hasProd (== IProd True [ keyValue fresh] ) l
        case  (hasF input , hasF output)  of
             (True,False)-> Right <$> attrUITable (const Nothing <$> trinp) [] (Attr fresh (TB1 ()) )
             (False,True)->  Left <$> attrUITable (fmap (\v ->  runIdentity . getCompose . justError ("no key " <> show fresh <> " in " <>  show v ) . fmap snd . getCompose . runIdentity . getCompose . findTB1 ((== [fresh]) . fmap _relOrigin. keyattr ) $ v ) <$> t) [] (Attr (fresh) (TB1 ()) )
             (True,True)-> errorWithStackTrace $ "circular reference " <> show fresh
             (False,False)-> errorWithStackTrace $ "unreferenced variable "<> show fresh
           ) freshs
      let
        inp :: Tidings (Maybe (TB1 Showable))
        inp = fmap (tbmap . mapFromTBList) <$> foldr (liftA2 (liftA2 (:) )) (pure (Just [])) (fmap (fmap ( fmap (Compose .Identity )) . triding) (rights elems) )
      ei <- if not $ any (\fresh -> hasProd (== IProd True [keyValue fresh]) input)  freshs
         then
          TrivialWidget trinp <$> UI.div
         else do
          inpPost <- UI.button # set UI.text "Submit"
          trinp <- cutEvent (UI.click inpPost) inp
          ei <- UI.div # set UI.children ((fmap getElement $ rights elems ) <> [inpPost])
          return $ TrivialWidget trinp ei
      return (h,(output,t),(lefts elems) ,ei )
           ) tf freshKeys
  el <- UI.div # set UI.children (headerP : (concat $ fmap (\(_,_,o,i)-> concat $ [fmap getElement o ,[getElement i]]) freshUI ))
  liftIO $ forkIO  $ fmap (const ()) $ init $ foldl' (\unoldM (f,((h,htidings,loui,inp),action))  -> unoldM >>= (\unoldItems -> do
      let oldItems = liftA2 (flip mergeTB1) <$>  facts initItems <#> triding inp
      liftEvent (rumors oldItems) (\i -> action inf  i  (liftIO . h) )
      return  oldItems ))  (return trinp) ( zip tf $ zip freshUI ac)
  element el # sink UI.style (noneShow <$> facts tdInput)
  return (el ,  (  ((\(_,o,_,_) -> fmap rumors o)$ last freshUI ) ))


pluginUI inf oldItems (BoundedPlugin2 n t f action) = do
  overwrite <- checkedWidget (pure False)
  let tdInput = join . fmap (flip testTable  (fst f)) <$>  oldItems
      tdOutput = join . fmap (flip testTable (snd f)) <$> oldItems
  v <- currentValue (facts oldItems)
  headerP <- UI.button # set text (T.unpack n) # sink UI.enabled (isJust <$> facts tdInput) # set UI.style [("color","white")] # sink UI.style (liftA2 greenRedBlue  (isJust <$> facts tdInput) (isJust <$> facts tdOutput))
  bh <- stepper False (unionWith const (const True <$> UI.hover headerP ) (const False <$> UI.leave headerP))
  details <-UI.div # sink UI.style (noneShow <$> bh) # sink UI.text (show . fmap (mapValue (const ())) <$> facts tdInput)
  out <- UI.div # set children [headerP,details]
  let ecv = (facts oldItems <@ UI.click headerP)
  pgOut <- mapEvent (\v -> catchPluginException inf n t (getPK $ justError "ewfew"  v) . action inf $ v)  ecv
  return (out, (snd f ,   pgOut ))



attrSize (FKT  _  _ _ ) = (12,4)
attrSize (IT _ _ ) = (12,4)
attrSize (Attr k _ ) = go  (keyType k)
  where
    go i = case i of
                KOptional l ->  go l
                KDelayed l ->  go l
                KSerial l -> go l
                KArray l -> let (i1,i2) = go l in (i1+1,i2*8)
                KInterval l -> let (i1,i2) = go l in (i1*2,i2)
                (Primitive i) ->
                  case textToPrim i of
                       PInt -> (2,1)
                       PText-> (3,1)
                       PDate -> (3,1)
                       PTimestamp -> (3,1)
                       PDayTime -> (3,1)
                       PMime m -> case m of
                                    "image/jpg" ->  (4,8)
                                    "application/pdf" ->  (6,8)
                                    "application/x-ofx" ->  (6,8)
                       i -> (3,1)




getRelOrigin =  fmap _relOrigin . concat . fmap keyattr

tbCase :: InformationSchema -> [Plugins] -> SelPKConstraint  -> TB Identity Key () -> [(TB Identity Key () ,TrivialWidget (Maybe (TB Identity Key Showable)))] -> [(Access Text,Event (Maybe (TB1 Showable)))]-> Tidings (Maybe (TB Identity Key Showable)) -> UI (TrivialWidget (Maybe (TB Identity Key Showable)))
tbCase inf pgs constr i@(FKT ifk  rel tb1) wl plugItens preoldItems = do
        l <- flabel # set text (show $ _relOrigin <$> rel )
        let
            oldItems = maybe preoldItems (\v -> if L.null v then preoldItems else fmap (maybe (Just (FKT (fmap  (Compose . Identity . uncurry Attr)  v) rel (DelayedTB1 Nothing) )) Just ) preoldItems  ) (Tra.traverse (\k -> fmap (k,) . keyStatic $ k ) ( getRelOrigin ifk))
            nonInj =  (S.fromList $ _relOrigin   <$> rel) `S.difference` (S.fromList $ getRelOrigin ifk)
            nonInjRefs = filter ((\i -> if S.null i then False else S.isSubsetOf i nonInj ) . S.fromList . fmap fst .  aattr .Compose . Identity .fst) wl
            nonInjConstr :: SelTBConstraint
            nonInjConstr = first (pure . Compose . Identity ) .fmap (fmap (\j (TB1 (_,l)) -> maybe True id $ (\ j -> not $ interPoint rel ( nonRefAttr $ fmap (Compose . Identity)  [j]) (nonRefAttr  $ F.toList $ _kvvalues $ unTB  l) ) <$> j ).triding) <$>  nonInjRefs
            tbi = fmap (Compose . Identity)  <$> oldItems
            thisPlugs = filter (hasProd (isNested ((IProd True $ fmap (keyValue._relOrigin) (keyattri i) ))) .  fst) plugItens
            pfks =  first (uNest . justError "No nested Prod IT" .  findProd (isNested((IProd True $ fmap (keyValue . _relOrigin ) (keyattri i) )))) . second (fmap (join . fmap (fmap  unTB . fmap snd . getCompose . runIdentity . getCompose . findTB1 ((==keyattr (_tb i))  . keyattr )))) <$> ( thisPlugs)
            relTable = M.fromList $ fmap (\(Rel i _ j ) -> (j,i)) rel
            pkset = fmap S.fromList $ allMaybes $  fmap (\ i ->  M.lookup i relTable) ( fmap _relOrigin $ findPK $ tb1 )

            restrictConstraint = filter ((\v -> maybe False  (v `S.isSubsetOf`)   pkset) . S.fromList . getRelOrigin  .fst) constr
            convertConstr :: SelTBConstraint
            convertConstr = (\(f,j) -> (f,) $ fmap (\constr -> constr   .  backFKRef relTable (getRelOrigin f)  ) j ) <$>  restrictConstraint
        ftdi <- foldr (\i j -> updateEvent  Just  i =<< j)  (return (fmap (runIdentity . getCompose ) <$>  tbi)) (fmap Just . filterJust . snd <$>  pfks )
        tds <- fkUITable inf pgs (convertConstr <> nonInjConstr ) pfks wl (ftdi ) i
        dv <- UI.div #  set UI.class_ "col-xs-12"# set children [l,getElement tds]
        paintEdit l (fmap tbrefM <$> facts (triding tds)) (fmap tbrefM  <$> facts oldItems)
        return $ TrivialWidget (triding tds) dv
tbCase inf pgs constr i@(IT na tb1 ) wl plugItens oldItems  = do
        l <- flabel # set text (show $ keyAttr .unTB $ na )
        let tbi = fmap (Compose . Identity ) <$> oldItems
            thisPlugs = filter (hasProd (isNested (IProd True (keyValue . _relOrigin <$> keyattr na ))) . fst) $  plugItens
            pfks =  first (uNest . justError "No nested Prod IT" . (findProd (isNested (IProd True (keyValue . _relOrigin <$> keyattr na))))) . second ( fmap ( join .  fmap (fmap (runIdentity . getCompose) . fmap snd . getCompose . runIdentity . getCompose . findTB1 ((== keyattr na).keyattr)))) <$> thisPlugs
        tds <- iUITable inf pgs pfks (fmap (runIdentity . getCompose ) <$>  tbi) i
        dv <- UI.div #  set UI.class_ "col-xs-12" # set children [l,getElement tds]
        paintEdit l (facts (triding tds)) (facts oldItems)
        return $ TrivialWidget (triding tds) dv
tbCase inf pgs constr a@(Attr i _ ) wl plugItens preoldItems = do
        l<- flabel # set text (show i)
        let oldItems = maybe (preoldItems) (\v-> fmap (maybe (Just (Attr i v )) Just ) preoldItems  ) (keyStatic i)
        let thisPlugs = filter (hasProd (== IProd True (keyValue . _relOrigin <$> keyattri a)) . fst)  plugItens
            tbi = oldItems
            evs  = ( fmap ( join . fmap ( fmap (runIdentity .  getCompose ) . fmap snd . getCompose . runIdentity . getCompose  . findTB1 (((== [i])  . fmap _relOrigin . keyattr )))) <$>  (fmap snd thisPlugs))
        tds <- attrUITable tbi evs a
        dv <- UI.div # set UI.style [("margin-bottom","3px")] # set UI.class_ ("col-xs-" <> show ( fst $ attrSize a) )# set children [l,getElement tds]
        paintEdit l (facts (triding tds)) (facts oldItems)
        return $ TrivialWidget (triding tds) dv



hasProd p (Many i) = any p i
hasProd p i = False

findProd p (Many i) = L.find p i
findProd p i = Nothing

isNested p (Nested pn i) =  p == pn
isNested p i =  False

uNest (Nested pn i) = i

unTBMap = _kvvalues . unTB . _unTB1

eiTable
  ::
     InformationSchema
     -> [Plugins]
     -> SelPKConstraint
     -> Text
     -> [(TB Identity Key () ,TrivialWidget (Maybe (TB Identity Key Showable)))]
     -> [(Access Text,Event (Maybe (TB1 Showable)))]
     -> TB1 ()
     -> Tidings (Maybe (TB1 Showable))
     -> UI (Element,Tidings (Maybe (TB1 Showable)))
eiTable inf pgs constr tname refs plmods ftb@(TB1 (m,k) ) oldItems = do
  let
      Just table = M.lookup tname  (tableMap inf)
  res <- mapM (pluginUI inf oldItems) (filter ((== rawName table ) . _bounds ) pgs)
  let plugmods = (snd <$> res) <> plmods
  fks <- foldl' (\jm (l,m)  -> do
            w <- jm
            wn <- (tbCase inf pgs  constr (unTB m) w plugmods ) $ maybe (join . fmap (fmap unTB .  (^?  Le.ix l ) . unTBMap ) <$> oldItems) ( triding . snd) (L.find (((keyattr m)==) . keyattr . Compose . Identity .fst) refs)
            return (w <> [(unTB m,wn)])
        ) (return []) (P.sortBy (P.comparing fst ) . M.toList . unTBMap $ ftb)
  let
      tableb :: Tidings (Maybe (TB1 Showable))
      tableb  = fmap (TB1 . (tableMeta table,) . Compose . Identity . KV . mapFromTBList . fmap _tb) . Tra.sequenceA <$> Tra.sequenceA (triding .snd <$> fks)
      initialSum = (join . fmap (\(TB1 (n,  j) ) ->    safeHead $ catMaybes  (fmap (Compose . Identity. fmap (const ()) ) . unOptionalAttr  . unTB<$> F.toList (_kvvalues (unTB j)) ))<$>   oldItems)
  chk  <- buttonDivSet (F.toList (_kvvalues $ unTB k))  initialSum (show . fmap _relOrigin.keyattr ) (\i -> UI.button # set text (L.intercalate "," $ fmap (show._relOrigin) $ keyattr $ i) )
  sequence $ (\(ix,el) -> element  el # sink0 UI.style (noneShow <$> ((==keyattri ix) .keyattr <$> facts (triding chk) ))) <$> fks
  let
      resei = liftA2 (\c -> fmap (\t@(TB1 (m, k)) -> TB1 . (m,) . Compose $ Identity $ KV (M.mapWithKey  (\k v -> if k == S.fromList (keyattr c) then maybe (addDefault (fmap (const ()) v)) (const v) (unOptionalAttr $ unTB  v) else addDefault (fmap (const ()) v)) (_kvvalues $ unTB k)))) (triding chk) tableb

  listBody <- UI.div # set UI.class_ "row"
    # set children (getElement chk : F.toList (getElement .snd <$> fks))
    # set style [("border","1px"),("border-color","gray"),("border-style","solid"),("margin","1px")]
  plugins <-  if not (L.null (fst <$> res))
    then do
      pluginsHeader <- UI.div # set UI.text "Plugins"
      pure <$> UI.div # set children (pluginsHeader : (fst <$> res))
    else do
      return []
  body <- UI.div
    # set children (plugins  <> [listBody])
    # set style [("margin-left","10px"),("border","2px"),("border-color","gray"),("border-style","solid")]
  return (body, resei)



uiTable
  ::
     InformationSchema
     -> [Plugins]
     -> SelPKConstraint
     -> Text
     -> [(TB Identity Key () ,TrivialWidget (Maybe (TB Identity Key Showable)))]
     -> [(Access Text,Event (Maybe (TB1 Showable)))]
     -> TB1 ()
     -> Tidings (Maybe (TB1 Showable))
     -> UI (Element,Tidings (Maybe (TB1 Showable)))
uiTable inf pgs constr tname refs plmods ftb@(TB1 (m,k) ) oldItems = do
  let
      Just table = M.lookup tname  (tableMap inf)

  res <- mapM (pluginUI inf oldItems) (filter ((== rawName table ) . _bounds ) pgs)
  let plugmods = (snd <$> res) <> plmods

  fks <- foldl' (\jm (l,m)  -> do
            w <- jm
            wn <- (tbCase inf pgs  constr (unTB m) w plugmods ) $ maybe (join . fmap (fmap unTB .  (^?  Le.ix l ) . unTBMap ) <$> oldItems) ( triding . snd) (L.find (((keyattr m)==) . keyattr . Compose . Identity .fst) $  refs)
            return (w <> [(unTB m,wn)])
        ) (return []) (P.sortBy (P.comparing fst ) . M.toList . unTBMap $ ftb)
  let
      tableb :: Tidings (Maybe (TB1 Showable))
      tableb  = fmap (TB1 .(tableMeta table,) . Compose . Identity . KV . mapFromTBList . fmap _tb) . Tra.sequenceA <$> Tra.sequenceA (triding .snd <$> fks)
  listBody <- UI.div # set UI.class_ "row"
    # set children (F.toList (getElement .snd <$> fks))
    # set style [("border","1px"),("border-color","gray"),("border-style","solid"),("margin","1px")]
  plugins <-  if not (L.null (fst <$> res))
    then do
      pluginsHeader <- UI.div # set UI.text "Plugins"
      pure <$> UI.div # set children (pluginsHeader : (fst <$> res))
    else do
      return []
  body <- UI.div
    # set children (plugins  <> [listBody])
    # set style [("margin-left","10px"),("border","2px"),("border-color","gray"),("border-style","solid")]
  return (body, tableb )

unLeftTB  = join . fmap  un
  where
      un (LeftTB1 i) = i
      un i = errorWithStackTrace ("unleft " <> show i )

brow = UI.div # set UI.class_ "row"
bfield s = UI.div # set UI.class_ ("col-lg-" <> show s)

lookPK inf pk =
            case  M.lookup pk  (pkMap inf) of
                 Just table -> table
                 i -> errorWithStackTrace (show pk)
crudUITable
  ::
     InformationSchema
     -> [Plugins]
     -> Tidings String
     -> Tidings [TB1 Showable]
     -> [(TB Identity Key () ,TrivialWidget (Maybe (TB Identity Key Showable)))]
     -> [(Access Text,Event (Maybe (TB1 Showable)))]
     -> TB1 ()
     -> Tidings (Maybe (TB1 Showable))
     -> UI ([Element],Event (PathFTB (TBIdx Key Showable) ) ,Tidings (Maybe (TB1 Showable)))
crudUITable inf pgs open bres refs pmods ftb@(TB1 (m,_) ) preoldItems = do
  (e2,h2) <- liftIO $ newEvent
  (ediff ,hdiff) <- liftIO $ newEvent
  (evdiff ,hvdiff) <- liftIO $ newEvent
  nav  <- buttonSetUI open ["None","Exception","Editor","Change"] (\i -> set UI.text i . set UI.class_ "buttonSet btn-xs btn-default pull-right")
  element nav # set UI.class_ "col-xs-4 pull-right"
  let table = lookPK inf (S.fromList $ fmap _relOrigin $ findPK $ ftb)
  let fun "Editor"= do
          preoldItens <- currentValue (facts preoldItems)
          loadedItens <- liftIO$ join <$> traverse (loadDelayed inf (unTB1 ftb) . unTB1 ) preoldItens
          maybe (return ()) (\j -> liftIO  (hvdiff  =<< traverse (\i -> runDBM inf $ applyTB1'  i (PAtom j) ) preoldItens) )  loadedItens
          loadedItensEv <- mapEvent (fmap join <$> traverse (loadDelayed inf (unTB1 ftb) . unTB1 )) (rumors preoldItems)
          let oldItemsE =  fmap head $ unions [ evdiff, rumors preoldItems  ]
          ini2 <- liftIO $(maybe (return preoldItens) (\j -> traverse (\i -> runDBM inf $ applyTB1' i (PAtom j) ) preoldItens ) loadedItens)
          oldItemsB <- stepper  ini2 oldItemsE
          let oldItems = tidings oldItemsB oldItemsE
              deleteCurrent e l =  maybe l (flip (L.deleteBy (onBin pkOpSet (concat . fmap aattr . F.toList .  _kvvalues . unTB . tbPK ))) l) e
              tpkConstraint :: ([Compose Identity (TB Identity) Key ()], Tidings PKConstraint)
              tpkConstraint = (F.toList $ _kvvalues $ unTB $ tbPK ftb , flip pkConstraint  <$> (deleteCurrent  <$> oldItems <*>bres))
              unConstraints :: [([Compose Identity (TB Identity) Key ()], Tidings PKConstraint)]
              unConstraints = (\un -> (F.toList $ _kvvalues $ unTB $ tbUn un  (tableNonRef ftb) , flip (unConstraint un) <$> (deleteCurrent <$> oldItems <*>bres))) <$> _kvuniques m
          (listBody,tableb) <- uiTable inf pgs ( (tpkConstraint: unConstraints)) (_kvname m) refs pmods ftb oldItems
          (panelItems,tdiff)<- processPanelTable inf  (facts tableb) (facts bres) table oldItems
          let diff =unionWith const tdiff   (filterJust loadedItensEv)
          onEvent (PAtom <$> diff)
              (liftIO . hdiff)
          onEvent (unsafeMapIO (fmap Just) $ (\i j -> runDBM inf $ maybe (fmap  TB1$  createTB1' j) (flip applyTB1' (PAtom j)  ) i) <$> facts oldItems <@> diff )
              (liftIO . hvdiff )
          onEvent (rumors tableb)
              (liftIO . h2)
          UI.div # set children [listBody,panelItems]
      fun "Change" = do
            UI.div # sink0 items (maybe [] (pure . dashBoardAllTableIndex . (inf,table,) . getPK )   <$> facts preoldItems )
      fun "Exception" = do
            UI.div # sink0 items (maybe [] (pure . exceptionAllTableIndex . (inf,table,). getPK )   <$> facts preoldItems )
      fun i = UI.div
  sub <- UI.div # sink items  (pure .fun <$> facts (triding nav)) # set UI.class_ "row"
  cv <- currentValue (facts preoldItems)
  bh2 <- stepper  cv (unionWith const e2  (rumors preoldItems))
  return ([getElement nav,sub], ediff ,tidings bh2 (unionWith const e2  (rumors preoldItems)))


tb1Diff f (TB1 (_,k1) ) (TB1 (_,k2)) =  liftF2 f k1 k2

onBin bin p x y = bin (p x) (p y)

type PKConstraint = [Compose Identity (TB Identity ) Key Showable] -> Bool
type TBConstraint = TB1 Showable -> Bool

type SelPKConstraint = [([Compose Identity (TB Identity) Key ()],Tidings PKConstraint)]
type SelTBConstraint = [([Compose Identity (TB Identity) Key ()],Tidings TBConstraint)]

pkConstraint v  = isJust . L.find (pkOpSet (concat . fmap aattr $ v ) . (concat . fmap aattr . F.toList .  _kvvalues . unTB . tbPK ))
unConstraint u v  = isJust . L.find (pkOpSet (concat . fmap aattr $ v ) . (concat . fmap aattr . F.toList .  _kvvalues . unTB . tbUn u .tableNonRef))


processPanelTable
   :: InformationSchema
   -> Behavior (Maybe (TB1 Showable))
   -> Behavior [TB1 Showable]
   -> Table
   -> Tidings (Maybe (TB1 Showable))
   -> UI (Element, Event (TBIdx Key Showable) )
processPanelTable inf attrsB res table oldItemsi = do
  let
      contains v  = maybe False (const True) . L.find (onBin (pkOpSet) (concat . fmap aattr . F.toList .  _kvvalues . unTB . tbPK ) v )
  insertB <- UI.button # set UI.class_ "buttonSet" # set text "INSERT" # set UI.style (noneShowSpan ("INSERT" `elem` rawAuthorization table )) #
  -- Insert when isValid
         sink UI.enabled (liftA2 (&&) (isJust . fmap tableNonRef <$> attrsB ) (liftA2 (\i j -> not $ maybe False (flip contains j) i  ) attrsB  res))
  editB <- UI.button #
         set text "EDIT" #
         set UI.class_ "buttonSet"#
         set UI.style (noneShowSpan ("UPDATE" `elem` rawAuthorization table )) #
  -- Edit when any persistent field has changed
         sink UI.enabled (liftA2 (&&) (liftA2 (\i j -> maybe False (any fst . F.toList  ) $ liftA2 (liftF2 (\l m -> if l  /= m then (True,(l,m)) else (False,(l,m))) )  i j) (fmap (_kvvalues . unTB . _unTB1 .  tableNonRef)<$> attrsB) (fmap (_kvvalues . unTB . _unTB1 . tableNonRef )<$> facts oldItemsi)) (liftA2 (\i j -> maybe False (flip contains j) i  ) attrsB  res))

  deleteB <- UI.button #
         set text "DELETE" #
         set UI.class_ "buttonSet"#
         set UI.style (noneShowSpan ("DELETE" `elem` rawAuthorization table )) #
  -- Delete when isValid
         sink UI.enabled ( liftA2 (&&) (isJust . fmap tableNonRef <$> facts oldItemsi) (liftA2 (\i j -> maybe False (flip contains j) i  ) (facts oldItemsi ) res))
  let
         crudEdi (Just (TB1 i)) (Just (TB1 j)) =  fmap (\g -> fmap (fixPatch inf (tableName table) ) $difftable i  g) $ transaction inf $ fullDiffEdit inf   i j
         crudIns  (Just (TB1 j))   =  fmap (tableDiff . fmap ( fixPatch inf (tableName table)) )  <$> insertMod inf j table
         crudDel (Just (TB1 j))  = fmap (tableDiff . fmap ( fixPatch inf (tableName table)))<$> deleteMod inf j table


  diffEdi <- mapEvent id $ crudEdi <$> facts oldItemsi <*> attrsB <@ UI.click editB
  diffDel <- mapEvent id $ crudDel <$> facts (fmap tableNonRef <$> oldItemsi) <@ UI.click deleteB
  diffIns <- mapEvent id $ crudIns <$>  attrsB <@ UI.click insertB
  transaction <- UI.span# set children [insertB,editB,deleteB]
  return (transaction , fmap head $ unions $ fmap filterJust [diffEdi,diffIns,diffDel] )




showFKE v =  UI.div # set text (L.take 50 $ L.intercalate "," $ fmap renderShowable $ allKVRec $  v)

showFKE' v =  UI.div # set text (L.take 100 $ L.intercalate "," $ F.toList $ _unTB1 $ mapValue renderPrim $   v)

showFK = (pure ((\v j ->j  # set text (L.take 50 $ L.intercalate "," $ fmap renderShowable $ allKVRec  $ v))))

tablePKSet  tb1 = S.fromList $ concat $ fmap ( keyattr)  $ F.toList $ _kvvalues $ unTB $ tbPK  tb1

flabel = UI.span # set UI.class_ (L.intercalate " " ["label","label-default"])


splitArray s o m l = take o m <> l <> drop  (o + s ) m

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
         emptyFKT = Just . maybe [] (unSComposite . _fkttable)
         bres = (\o -> liftA2 (\l m -> IT   na (ArrayTB1 $ splitArray s o m l ))) <$> offsetT <*> bres2 <*> (emptyFKT <$> oldItems)

attrUITable
  :: Tidings (Maybe (TB Identity Key Showable))
     -> [Event (Maybe (TB Identity Key Showable))]
     -> TB Identity Key ()
     -> UI (TrivialWidget (Maybe (TB Identity Key Showable)))
attrUITable tAttr' evs attr@(Attr i@(Key _ _ _ _ _ (KOptional _) ) v) = do
      res <- attrUITable (join . fmap unLeftItens <$> tAttr') (fmap (join. fmap unLeftItens ) <$>  evs) (Attr (unKOptional i) v)
      return (leftItens attr <$> res)
attrUITable tAttr' evs attr@(Attr i@(Key _ _ _ _ _ (KArray _) ) v) = mdo
            offsetDiv  <- UI.div
            let wheel = fmap negate $ mousewheel offsetDiv
            TrivialWidget offsetT offset <- offsetField 0  wheel (maybe 0 (length . (\(ArrayTB1 l ) -> l) . _tbattr) <$> facts bres)
            let arraySize = 8
            widgets <- mapM (\ix  -> attrUITable (unIndexItens ix  <$> offsetT <*> tAttr' ) ((unIndexItens ix  <$> facts offsetT <@> ) <$>  evs) (Attr (unKArray i) v  ) ) [0..arraySize -1 ]

            sequence $ zipWith (\e t -> element e # sink0 UI.style (noneShow . isJust <$> facts t)) (tail $ getElement <$> widgets) (triding <$> widgets)
            let
              bres = indexItens arraySize  attr offsetT (triding <$> widgets) tAttr'
            element offsetDiv # set children (fmap getElement widgets)
            paintBorder offsetDiv (facts bres ) (facts tAttr' )
            composed <- UI.span # set children [offset , offsetDiv]
            return  $ TrivialWidget  bres composed
attrUITable  tAttr' evs (Attr i _ ) = do
      tdi' <- foldr (\i j ->  updateEvent  Just i =<< j) (return tAttr') evs
      let tdi = fmap (\(Attr  _ i )-> i) <$>tdi'
      attrUI <- buildUI (textToPrim <$> keyType i) tdi
      let insertT = fmap (Attr i ) <$> (triding attrUI)
      return $ TrivialWidget insertT  (getElement attrUI)

buildUI :: KType KPrim -> Tidings (Maybe (FTB Showable)) -> UI (TrivialWidget (Maybe (FTB Showable)))
buildUI i  tdi = case i of
         (KSerial ti) -> do
           tdnew <- fmap (Just . SerialTB1 ) <$> buildUI ti ( join . fmap unSSerial <$> tdi)
           retUI <- UI.div # set children [getElement tdnew]
           paintBorder retUI (facts $ triding tdnew) (facts tdi)
           return $ TrivialWidget (triding tdnew ) retUI
         (KDelayed ti) -> do
           tdnew <- fmap (maybe Nothing (Just .DelayedTB1 . Just)  ) <$> buildUI ti (join . fmap unSDelayed <$> tdi)
           retUI <- UI.div# set children [getElement tdnew]
           paintBorder retUI (facts $ triding tdnew) (facts tdi)
           return $ TrivialWidget (triding tdnew ) retUI
         (KInterval ti) -> do
            let unInterval f (IntervalTB1 i ) = f i
                unInterval _ i = errorWithStackTrace (show i)
            inf <- fmap (fmap ER.Finite) <$> buildUI ti (fmap (unInterval inf' ) <$> tdi)
            sup <- fmap (fmap ER.Finite) <$> buildUI ti (fmap (unInterval sup')  <$> tdi)
            lbd <- fmap Just <$> checkedWidget (maybe False id . fmap (\(IntervalTB1 i) -> snd . Interval.lowerBound' $i) <$> tdi)
            ubd <- fmap Just <$> checkedWidget (maybe False id .fmap (\(IntervalTB1 i) -> snd . Interval.upperBound' $i) <$> tdi)
            composed <- UI.div # set UI.style [("display","inline-flex")] # set UI.children [getElement lbd ,getElement  inf,getElement sup,getElement ubd]
            subcomposed <- UI.div # set UI.children [composed]
            let td = (\m n -> fmap IntervalTB1 $  join . fmap (\i-> if Interval.null i then Nothing else Just i) $ liftF2 interval m n) <$> (liftA2 (,) <$> triding inf  <*> triding lbd) <*> (liftA2 (,) <$> triding sup <*> triding ubd)
            paintBorder subcomposed (facts td ) (facts tdi)
            return $ TrivialWidget td subcomposed
         (Primitive i ) -> fmap (fmap TB1) <$> buildPrim (fmap (\(TB1 i )-> i) <$> tdi) i

buildPrim :: Tidings (Maybe Showable) -> KPrim -> UI (TrivialWidget (Maybe Showable))
buildPrim tdi i = case i of
         {-(Position) -> do
            let addrs = (\(SPosition (Position (lon,lat,_)))-> "http://maps.google.com/?output=embed&q=" <> (HTTP.urlEncode $ show lat  <> "," <>  show lon )) <$>  tdi
            mkElement "iframe" # sink UI.src (maybe "" id <$> facts addrs) # set style [("width","99%"),("height","300px")]-}
         PBoolean -> do
           res <- checkedWidgetM (fmap (\(SBoolean i) -> i) <$> tdi )
           return (fmap SBoolean <$> res)
         PTimestamp -> do
            itime <- liftIO $  getCurrentTime
            timeButton <- UI.button # set UI.text "now"
            evCurr <-  mapEvent (fmap Just) (pure getCurrentTime <@ UI.click timeButton)
            let  newEv = fmap (STimestamp . utcToLocalTime utc) <$> evCurr
            tdi2 <- addEvent newEv  tdi
            oneInput tdi2 [timeButton]
         PDate -> do
            itime <- liftIO $  getCurrentTime
            timeButton <- UI.button # set UI.text "now"
            evCurr <-  mapEvent (fmap Just) (pure getCurrentTime <@ UI.click timeButton)
            let  newEv =  fmap (SDate . localDay . utcToLocalTime utc) <$> evCurr
            tdi2 <- addEvent newEv  tdi
            oneInput tdi2 [timeButton]
         PDayTime -> do
            itime <- liftIO $  getCurrentTime
            timeButton <- UI.button # set UI.text "now"
            evCurr <-  mapEvent (fmap Just) (pure getCurrentTime <@ UI.click timeButton)
            let  newEv = fmap (SDayTime. localTimeOfDay . utcToLocalTime utc) <$> evCurr
            tdi2 <- addEvent newEv  tdi
            oneInput tdi2 [timeButton]
         PMime mime -> do
           let binarySrc = (\(SBinary i) -> "data:" <> T.unpack mime <> ";base64," <>  (BSC.unpack $ B64.encode i) )
           clearB <- UI.button # set UI.text "clear"
           file <- UI.input # set UI.class_ "file_client" # set UI.type_ "file" # set UI.multiple True
           UI.div # sink0 UI.html (pure "<script> $(\".file_client\").on('change',handleFileSelect); </script>")
           tdi2 <- addEvent (join . fmap (fmap SBinary . either (const Nothing) Just .   B64.decode .  BSC.drop 7. snd  . BSC.breakSubstring "base64," . BSC.pack ) <$> fileChange file ) =<< addEvent (const Nothing <$> UI.click clearB) tdi
           let fty = case mime of
                "application/pdf" -> ("iframe","src",maybe "" binarySrc ,[("width","100%"),("height","300px")])
                "application/x-ofx" -> ("textarea","value",maybe "" (\(SBinary i) -> BSC.unpack i) ,[("width","100%"),("height","300px")])
                "image/jpg" -> ("img","src",maybe "" binarySrc ,[])
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
            let pke = unionWith const  (rumors tdi) (readPrim i <$> UI.valueChange inputUI)
            pk <- stepper v  pke
            let pkt = tidings pk pke
            sp <- UI.div # set children (inputUI : elem)
            paintBorder sp (facts pkt) (facts tdi)
            return $ TrivialWidget pkt sp



iUITable
  :: InformationSchema
  -> [Plugins]
  -- Plugin Modifications
  -> [(Access Text,Event (Maybe (TB Identity Key (Showable))))]
  -- Selected Item
  -> Tidings (Maybe (TB Identity Key Showable))
  -- Static Information about relation
  -> TB Identity Key ()
  -> UI (TrivialWidget(Maybe (TB Identity Key Showable)))
iUITable inf pgs pmods oldItems  tb@(IT na  tb1@(TB1 (meta,_)) )
    = do
      let tfun = if isKEither (keyType $ _relOrigin$  head $ keyattr $  na) then eiTable else uiTable
      (celem,tcrud) <- tfun inf pgs [] (_kvname meta )
              []
              (fmap (fmap (fmap _fkttable)) <$> pmods)
              tb1
              (fmap _fkttable <$> oldItems)
      element celem #
          set style [("margin-left","10px")]
      let bres =  fmap (fmap (IT  na  ) ) (tcrud)
      return $ TrivialWidget bres celem
iUITable inf pgs pmods oldItems  tb@(IT na (LeftTB1 (Just tb1))) = do
   tr <- iUITable inf pgs (fmap (join . fmap unLeftItens  <$> ) <$> pmods) (join . fmap unLeftItens <$> oldItems) (IT na tb1)
   return $  leftItens tb <$> tr
iUITable inf pgs plmods oldItems  tb@(IT na (ArrayTB1 [tb1]))
    = mdo
      dv <- UI.div
      let wheel = fmap negate $ mousewheel dv
          arraySize = 8
      (TrivialWidget offsetT offset) <- offsetField 0 wheel (maybe 0 (length . (\(IT _ (ArrayTB1 l) ) -> l)) <$> facts bres )
      items <- mapM (\ix -> iUITable inf pgs
                (fmap (unIndexItens  ix <$> facts offsetT <@> ) <$> plmods)
                (unIndexItens ix <$> offsetT <*>   oldItems)
                (IT  na tb1)) [0..arraySize -1 ]
      let tds = triding <$> items
          es = getElement <$> items
      sequence $ zipWith (\e t -> element e # sink0 UI.style (noneShow <$> facts t)) es  (pure True : (fmap isJust <$>  tds ))
      let bres = indexItens arraySize tb offsetT (triding <$>  items ) oldItems
      element dv  # set children (offset : (getElement <$> items))
      return $ TrivialWidget bres dv

offsetField  init eve  max = mdo
  offsetL <- UI.span # set text "Offset: "
  offset <- UI.input # set UI.style [("width","50px")] # sink UI.value (show <$> offsetB)
  leng <- UI.span # sink text (("Size: " ++) .show  <$> max )
  offparen <- UI.div # set children [offsetL,offset,leng]

  let offsetE =  filterJust $ (\m i -> if i <m then Just i else Nothing ) <$> max <@> (filterJust $ readMaybe <$> onEnter offset)
      ev = unionWith const (negate <$> mousewheel offparen) eve
      saturate m i j
          | m == 0 = 0
          | i + j < 0  = 0
          | i + j > m -1  = m -1
          | otherwise = i + j
      diff o m inc
        | saturate m inc o /= o = Just (saturate m inc )
        | otherwise = Nothing

  let
      filt = ( filterJust $ diff <$> offsetB <*> max <@> ev  )
      ev2 = (fmap concatenate $ unions [fmap const offsetE,filt ])
  offsetB <- accumB init ev2
  let
     cev = flip ($) <$> offsetB <@> ev2
     offsetT = tidings offsetB cev
  return (TrivialWidget offsetT offparen)


backFKRef
  :: (Show (f Key ),Show a, Functor f) =>
     M.Map Key Key
     -> f Key
     -> TB2 Key a
     -> f (Compose Identity (TB f1) Key a)
backFKRef relTable ifk = fmap (_tb . uncurry Attr). reorderPK .  concat . fmap aattr . F.toList .  _kvvalues . unTB . _unTB1
  where
        reorderPK l = fmap (\i -> justError (show ("reorder wrong", ifk ,relTable , l,i))  $ L.find ((== i).fst) (catMaybes (fmap lookFKsel l) ) )  ifk
        lookFKsel (ko,v)=  (\kn -> (kn ,transformKey (textToPrim <$> keyType ko ) (textToPrim <$> keyType kn) v)) <$> knm
          where knm =  M.lookup ko relTable


tbrefM i@(FKT _  _ _)  =  _tbref i
tbrefM j = [Compose $ Identity $ j ]



fkUITable
  ::
  InformationSchema
  -> [Plugins]
  -- Plugin Modifications
  -> SelTBConstraint
  -> [(Access Text,Event  (Maybe (TB Identity Key Showable)))]
  -- Same Table References
  -> [(TB Identity Key () ,TrivialWidget (Maybe (TB Identity Key (Showable))))]
  -- Relation Event
  -> Tidings (Maybe (TB Identity Key Showable))
  -- Static Information about relation
  -> TB Identity Key ()
  -> UI (TrivialWidget(Maybe (TB Identity Key Showable)))
fkUITable inf pgs constr plmods wl  oldItems  tb@(FKT ifk rel tb1@(TB1 _  ) ) = mdo
      let
          relTable = M.fromList $ fmap (\(Rel i _ j ) -> (j,i)) rel
          rr = tablePKSet tb1
          table = justError "no table found" $ M.lookup (S.map _relOrigin rr) $ pkMap inf
      (tmvar,vpt)  <- liftIO $ eventTable inf table
      res <- currentValue (facts vpt)
      let
          -- Find non injective part of reference
          ftdi = oldItems
          oldASet :: Set Key
          oldASet = S.fromList (_relOrigin <$> filterNotReflexive rel )
          replaceKey =  firstTB (\k -> maybe k _relTarget $ L.find ((==k)._relOrigin) $ filter (\i -> keyType (_relOrigin i) == keyType (_relTarget i)) rel)
          nonInj =   S.difference (S.fromList $ fmap  _relOrigin   $ rel) (S.fromList $ getRelOrigin ifk)
          nonInjRefs = filter (flip S.isSubsetOf nonInj . S.fromList . fmap _relOrigin . keyattr .Compose . Identity .fst) wl
          staticold :: [(TB Identity Key () ,TrivialWidget (Maybe (TB Identity Key (Showable))))]
          staticold  =    second (fmap (fmap replaceKey . join . fmap unLeftItens)) . first (replaceKey .unLeftKey) <$>  nonInjRefs
          iold :: Tidings [Maybe [(Key,FTB Showable)]]
          iold  = Tra.sequenceA $ fmap (fmap ( aattr . _tb ) ) . triding .snd <$> L.filter (\i-> not . S.null $ S.intersection (S.fromList $ fmap _relOrigin $ keyattr . _tb . fst $ i) oldASet) wl
          iold2 :: Tidings (Maybe [TB Identity  Key Showable])
          iold2 =  join . (fmap (traverse ((traFAttr unRSOptional2 ) . firstTB unRKOptional ))) .  fmap (fmap ( uncurry Attr) . concat) . allMaybes <$> iold
          ftdi2 :: Tidings (Maybe [TB Identity  Key Showable])
          ftdi2 =   fmap (fmap unTB. tbrefM ) <$> ftdi
          res3 :: Tidings [TB1 Showable]
          res3 =  foldr (\constr  res2 -> (\el constr -> filter (not. constr) el)  <$> res2  <*> snd constr ) (tidings res2 never) constr
          unRKOptional (Key a b d n m (KOptional c)) = Key a b d n m c
          unRKOptional (Key a b d n m c) = Key a b d n m c
      let
          search = (\i j -> join $ fmap (\k-> L.find (\(TB1 (kv,l) )->  interPoint (filter (flip S.member (_kvpk kv) . _relTarget) rel) k  (concat $ fmap (uncurry Attr) . aattr <$> (F.toList . _kvvalues . unTB $ l)) ) i) $ j )
          vv :: Tidings (Maybe [TB Identity Key Showable])
          vv =   liftA2 (<>) iold2  ftdi2
      cvres <- currentValue (facts vv)
      filterInp <- UI.input
      filterInpBh <- stepper "" (UI.valueChange filterInp)
      let
          cv = search res cvres
          tdi =  search <$> res3 <*> vv
          filterInpT = tidings filterInpBh (UI.valueChange filterInp)
          filtering i  = T.isInfixOf (T.pack $ toLower <$> i) . T.toLower . T.intercalate "," . fmap (T.pack . renderPrim ) . F.toList .    _unTB1
          sortList :: Tidings ([TB1 Showable] -> [TB1 Showable])
          sortList =  sorting  <$> pure (fmap ((,True)._relTarget) rel)
      itemList <- listBox ((Nothing:) <$>  fmap (fmap Just) res3) (tidings (fmap Just <$> st) never) (pure id) ((\i j -> maybe id (\l  ->   (set UI.style (noneShow $ filtering j l  ) ) . i  l ) )<$> showFK <*> filterInpT)

      let evsel = unionWith const (rumors tdi) (rumors $ join <$> userSelection itemList)
      prop <- stepper cv evsel
      let ptds = tidings prop evsel
      tds <- foldr (\i j ->updateEvent  Just  i =<< j)  (return ptds) (fmap Just . fmap _fkttable.filterJust . snd <$>  plmods)
      (celem,ediff,pretdi) <-crudUITable inf pgs  (pure "None") res3 staticold (fmap (fmap (fmap _fkttable)) <$> plmods)  tb1  tds
      diffUp <-  mapEvent (fmap pure) $ (\i j -> traverse (runDBM inf .  flip applyTB1' j ) i) <$> facts pretdi <@> ediff
      let
          sel = filterJust $ fmap (safeHead.concat) $ unions $ [(unions  [(rumors $ join <$> userSelection itemList), rumors tdi]),diffUp]
      st <- stepper cv sel
      inisort <- currentValue (facts sortList)
      res2  <-  accumB (inisort res ) (fmap concatenate $ unions $ [fmap const (($) <$> facts sortList <@> rumors vpt) , rumors sortList])
      onEvent ((\i j -> foldl' applyTable i (expandPSet j)) <$> res2 <@> ediff)  (liftIO .  putMVar tmvar  . fmap unTB1 )
      let
        fksel =  fmap (\box ->  FKT (backFKRef  relTable  (fmap (keyAttr .unTB )ifk)   box) rel box ) <$>  ((\i j -> maybe i Just ( j)  ) <$> pretdi <*> tidings st sel)
      element itemList # set UI.class_ "col-xs-5"
      element filterInp # set UI.class_ "col-xs-3"
      fk <- UI.div # set  children [getElement itemList ,filterInp,head celem]  # set UI.class_ "row"
      subnet <- UI.div # set children [fk,last celem] # set UI.class_ "col-xs-12"
      return $ TrivialWidget fksel subnet
fkUITable inf pgs constr plmods  wl oldItems  tb@(FKT ilk rel  (DelayedTB1 (Just tb1 ))) = do
    tr <- fkUITable inf pgs constr  plmods  wl oldItems  (FKT  ilk  rel tb1)
    return $ tr

fkUITable inf pgs constr plmods  wl oldItems  tb@(FKT ilk rel  (LeftTB1 (Just tb1 ))) = do
    tr <- fkUITable inf pgs constr (fmap (join . fmap unLeftItens <$>) <$> plmods)  wl (join . fmap unLeftItens  <$> oldItems)  (FKT (mapComp (firstTB unKOptional) <$> ilk) (Le.over relOrigin unKOptional <$> rel) tb1)
    return $ leftItens tb <$> tr
fkUITable inf pgs constr plmods  wl oldItems  tb@(FKT ifk rel  (ArrayTB1 [tb1]) ) = mdo
     dv <- UI.div
     let wheel = fmap negate $ mousewheel dv
         arraySize = 8
     (TrivialWidget offsetT offset) <- offsetField 0 (wheel) (maybe 0 (length . (\(FKT _  _ (ArrayTB1 l) ) -> l)) <$> facts bres)
     let
         fkst = FKT (mapComp (firstTB unKArray)<$> ifk ) (fmap (Le.over relOrigin (\i -> if isArray (keyType i) then unKArray i else i )) rel)  tb1
     fks <- traverse (\ix-> do
         lb <- UI.div # sink UI.text (show . (+ix) <$> facts offsetT ) # set UI.class_ "col-xs-1"
         TrivialWidget tr el<- fkUITable inf pgs constr (fmap (unIndexItens  ix <$> facts offsetT <@> ) <$> plmods) wl (unIndexItens ix <$> offsetT  <*>  oldItems) fkst
         element el # set UI.class_ "col-xs-11"
         TrivialWidget tr <$> UI.div # set UI.children [lb,el] ) [0..arraySize -1 ]
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

deleteMod :: InformationSchema ->  TBData Key Showable -> Table -> IO (Maybe (TableModification (TBIdx Key Showable)))
deleteMod inf j@(meta,_) table = do
  let patch =  (tableMeta table, getPKM j,[])
  deletePatch (conn inf)  patch table
  Just <$> logTableModification inf (TableModification Nothing table patch)

--
--  MultiTransaction Postgresql insertOperation
--

type TransactionM = WriterT [TableModification (TBIdx Key Showable)] IO

fullInsert inf = Tra.traverse (fullInsert' inf )

fullInsert' :: InformationSchema -> TBData Key Showable -> TransactionM  (TBData Key Showable)
fullInsert' inf ((k1,v1) )  = do
   let proj = _kvvalues . unTB
   ret <-  (k1,) . Compose . Identity . KV <$>  Tra.traverse (\j -> Compose <$>  tbInsertEdit inf   (unTB j) )  (proj v1)
   (m,t) <- liftIO $ eventTable inf (lookTable inf (_kvname k1))
   l <- currentValue (facts t)
   if  isJust $ L.find ((==tbPK (tableNonRef (TB1 ret))). tbPK . tableNonRef ) l
      then do
        return ret
      else do
        i@(Just (TableModification _ _ tb))  <- liftIO $ insertMod inf ret (lookTable inf (_kvname k1))
        tell (maybeToList i)
        return $ createTB1 tb


noInsert inf = Tra.traverse (noInsert' inf)

noInsert' :: InformationSchema -> TBData Key Showable -> TransactionM  (TBData Key Showable)
noInsert' inf (k1,v1)   = do
   let proj = _kvvalues . unTB
   (k1,) . Compose . Identity . KV <$>  Tra.sequence (fmap (\j -> Compose <$>  tbInsertEdit inf   (unTB j) )  (proj v1))


insertMod :: InformationSchema ->  TBData Key Showable -> Table -> IO (Maybe (TableModification (TBIdx Key Showable)))
insertMod inf j  table = do
  let patch = patchTB1 j
  kvn <- insertPatch fromRecord (conn  inf) patch table
  let mod =  TableModification Nothing table kvn
  Just <$> logTableModification inf mod


transaction :: InformationSchema -> TransactionM a -> IO a
transaction inf log = withTransaction (conn inf) $ do
  (md,mods)  <- runWriterT log
  let aggr = foldr (\(TableModification id t f) m -> M.insertWith mappend t [f] m) M.empty mods
  Tra.traverse (\(k,v) -> do
    (m,t) <- eventTable inf k
    l <- currentValue (facts t)
    let lf = foldl' (\i p -> applyTable  i (PAtom p)) l v
    putMVar m (fmap unTB1 lf)
    ) (M.toList aggr)
  return md

fullDiffEdit :: InformationSchema -> TBData Key Showable -> TBData Key Showable -> TransactionM  (TBData Key Showable)
fullDiffEdit inf old@((k1,v1) ) (k2,v2) = do
   let proj = _kvvalues . unTB
   edn <- (k2,) . Compose . Identity . KV <$>  Tra.sequence (M.intersectionWith (\i j -> Compose <$>  tbDiffEdit inf  (unTB i) (unTB j) ) (proj v1 ) (proj v2))
   mod <- liftIO $ updateModAttr inf edn old (lookTable inf (_kvname k2))
   tell (maybeToList mod)
   return edn

updateModAttr :: InformationSchema -> TBData Key Showable -> TBData Key Showable -> Table -> IO (Maybe (TableModification (TBIdx Key Showable)))
updateModAttr inf kv old table = do
  patch <- updatePatch (conn  inf) kv  old  table
  let mod =  TableModification Nothing table patch
  Just <$> logTableModification inf mod


tbDiffEdit :: InformationSchema -> TB Identity Key Showable -> TB Identity Key Showable -> TransactionM (Identity (TB Identity Key  Showable))
tbDiffEdit inf i j
  | i == j =  return (Identity j)
  | otherwise = tbInsertEdit inf  j

tbInsertEdit inf  j@(Attr k1 k2) = return $ Identity  (Attr k1 k2)
tbInsertEdit inf  (IT k2 t2) = Identity . IT k2 <$> noInsert inf t2
tbInsertEdit inf  f@(FKT pk rel2  t2) =
   case t2 of
        t@(TB1 (_,l)) -> do
           let relTable = M.fromList $ fmap (\(Rel i _ j ) -> (j,i)) rel2
           Identity . (\tb -> FKT ( backFKRef relTable  (keyAttr .unTB <$> pk) tb) rel2 tb ) <$> fullInsert inf t
        LeftTB1 i ->
           maybe (return (Identity f) ) (fmap (fmap attrOptional) . tbInsertEdit inf) (unLeftItens f)
        ArrayTB1 l ->
           fmap (fmap (attrArray f)) $ fmap Tra.sequenceA $ Tra.traverse (\ix ->   tbInsertEdit inf $ justError ("cant find " <> show (ix,f)) $ unIndex ix f  )  [0.. length l - 1 ]

rendererHeaderUI k v = const (renderer k) v
  where renderer k = UI.div # set items [UI.div # set text (T.unpack $ keyValue k ) , UI.div # set text (T.unpack $ showTy id (keyType k)) ]

rendererShowableUI k  v= renderer (keyValue k) v
  where renderer "modification_data" (SBinary i) = either (\i-> UI.div # set UI.text (show i)) (\(_,_,i ) -> showPatch (i:: PathAttr Text Showable) )  (B.decodeOrFail (BSL.fromStrict i))
        renderer "data_index" (SBinary i) = either (\i-> UI.div # set UI.text (show i)) (\(_,_,i ) -> UI.div # set items (showIndex <$> (i:: [((Text ,FTB Showable) )])))  (B.decodeOrFail (BSL.fromStrict i))
        renderer k i = UI.div # set text (renderPrim i)
        showPatch l = UI.div # set text (show $ fmap renderPrim l)
        showIndex l = UI.div # set text (show $ renderShowable <$> l)

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
                bh <- stepper False (unionWith const (const True <$> UI.hover elemD ) (const False <$> UI.leave elemD))
                element elemD # sink items ((\b -> if not b then take 2  l  <> fmap ( set UI.style (noneShow False)) (drop 2 l) else  l ) <$> bh)
              else return elemD # set items l


testUI e = startGUI (defaultConfig { tpStatic = Just "static", tpCustomHTML = Just "index.html" })  $ \w ->  do
              els <- e
              getBody w #+ [els]
              return ()

metaAllTableIndexV inf metaname env =   do
  let modtable = lookTable (meta inf) tname
      tname = metaname
      modtablei = tableView (tableMap $ meta inf) modtable
      envK = fmap (first (lookKey (meta inf) tname)) env
  viewer (meta inf) modtable (Just envK)

dashBoardAllTable  inf table = metaAllTableIndexV inf "modification_table" [("schema_name",TB1 $ SText (schemaName inf) ),("table_name",TB1 $ SText (tableName table) ) ]
exceptionAllTable inf table = metaAllTableIndexV inf "plugin_exception" [("schema_name",TB1 $ SText (schemaName inf) ),("table_name",TB1 $ SText (tableName table) ) ]

dashBoardAll inf = metaAllTableIndexV inf "modification_table" [("schema_name",TB1 $ SText (schemaName inf) ) ]

exceptionAll inf = metaAllTableIndexV inf "plugin_exception" [("schema_name",TB1 $ SText (schemaName inf) ) ]



viewer inf table env = do
  let
      envK = concat $ maybeToList env
      filterStatic =filter (not . flip L.elem (fmap fst envK))
      key = filterStatic $ F.toList $ rawPK table
      sortSet =  filterStatic . F.toList . tableKeys . tableNonRef . allRec' (tableMap inf ) $ table
      tableSt2 =   tableViewNR (tableMap inf) table
  itemList <- UI.div
  let pageSize = 20
      iniPg =  M.empty
      iniSort = selSort sortSet ((,True) <$>  key)
  offset <- offsetField 0 (negate <$> mousewheel (getElement itemList)) (pure $ maybe 100 (ceiling . (/pageSize). fromIntegral) $ M.lookup table (tableSize inf ) )
  sortList <- selectUI sortSet ((,True) <$> key) UI.tr UI.th conv
  let makeQ slist (o,i) = fmap ((o,).(slist,)) $ paginate (conn inf) (unTB1 tableSt2)  (fmap dir2 <$> (filterOrd slist))  ((*pageSize) $ maybe o ((o-) . fst) kold ) pageSize (snd <$> kold) env
          where kold = join $ fmap (traverse (allMaybes . fmap (traverse unSOptional') . L.filter (flip elem (fmap fst (filterOrd slist)).fst) . getAttr'  )) i
      dir2 True  = Desc
      dir2 False = Asc
      nearest' :: M.Map Int (TB2 Key Showable) -> Int -> ((Int,Maybe (Int,TB2 Key Showable)))
      nearest' p o =  (o,) $ safeHead $ filter ((<=0) .(\i -> i -o) .  fst) $ reverse  $ L.sortBy (comparing ((\i -> (i - o)). fst )) (M.toList p)
      ini = nearest' iniPg 0
      addT (c,(s,td)) = M.insert (c +1)  <$>  (fmap TB1 $ safeHead $reverse td)
  iniQ <- liftIO$ makeQ iniSort ini
  do
    rec
      let
          event1 , event2 :: Event (IO (Int,([(Key,Maybe Bool)],[TBData Key Showable])))
          event1 = (\(j,k) i  -> makeQ i (nearest' j k )) <$> facts ((,) <$> pure iniPg <*> triding offset) <@> rumors (triding sortList)
          event2 = (\(j,i) k  -> makeQ i (nearest' j k )) <$> facts ((,) <$> pg <*> triding sortList) <@> rumors (triding offset)
      tdswhere <- mapEvent id (unionWith const event1 event2)
      pg <- accumT iniPg (unionWith (flip (.)) ((pure (const iniPg ) <@ event1)) (filterJust (addT <$> tdswhere )))
    tdswhereb <- stepper (snd iniQ) (fmap snd tdswhere)
    let
        tview = unTlabel' . unTB1  $tableSt2
        ordtoBool Asc = False
        ordtoBool Desc = True
    element itemList # sink items ((\(slist ,tb)-> pure . renderTableNoHeaderSort  (fmap fst slist) (return $ getElement sortList) inf (tableNonRef' tview) .  fmap tableNonRef' . fmap ((filterRec (concat $ maybeToList env))) $ tb )  <$>   tdswhereb )
    UI.div # set children [getElement offset, itemList]



exceptionAllTableIndex e@(inf,table,index) =   metaAllTableIndexV inf "plugin_exception" [("schema_name",TB1 $ SText (schemaName inf) ),("table_name",TB1 $ SText (tableName table) ),("data_index",TB1 $ SBinary $ BSL.toStrict $ B.encode $ fmap (first keyValue)index) ]

dashBoardAllTableIndex e@(inf,table,index) =   metaAllTableIndexV inf "modification_table" [("schema_name",TB1 $ SText (schemaName inf) ),("table_name",TB1 $ SText (tableName table) ),("data_index",TB1 $ SBinary $ BSL.toStrict $ B.encode $ fmap (first keyValue)index) ]


filterRec envK = filterTB1' ( not . (`S.isSubsetOf`  (S.fromList (fst <$> envK ))) . S.fromList . fmap _relOrigin.  keyattr )

renderTableNoHeader' header inf modtablei out = do
  let
      body o = UI.tr # set UI.class_ "row" #  set items (foldMetaHeader UI.td rendererShowableUI inf $ o)
  header # set UI.class_ "row"
  UI.table # set UI.class_ "table table-bordered table-striped" # sink items ( ( (header :) . fmap body <$> out))

renderTableNoHeaderSort sort header inf modtablei out = do
  let
      body o = UI.tr # set UI.class_ "row" #  set items (foldMetaHeader' sort UI.td rendererShowableUI inf $ o)
  header # set UI.class_ "row"
  UI.table # set UI.class_ "table table-bordered table-striped" # set items (header :(body <$> out))


renderTableNoHeader header inf modtablei out = do
  let
      body o = UI.tr # set UI.class_ "row" #  set items (foldMetaHeader UI.td rendererShowableUI inf $ o)
  header # set UI.class_ "row"
  UI.table # set UI.class_ "table table-bordered table-striped" # set items (header :(body <$> out))

renderTable'  inf modtablei out =  do
  let
      header = UI.tr # set UI.class_ "row" # set items (foldMetaHeader UI.th rendererHeaderUI inf $ modtablei)
  renderTableNoHeader' header inf modtablei out

renderTable  inf modtablei out =  do
  let
      header = UI.tr # set UI.class_ "row" # set items (foldMetaHeader UI.th rendererHeaderUI inf $ modtablei)
  renderTableNoHeader  header inf modtablei out



panel t els = UI.div # set items ( UI.h2 # set text (T.unpack t  ) : [UI.div # set items (F.toList els)])
showModDiv i =  set UI.style [("display","flex")] . set items (showMod i)
showMod i  = [UI.div # line (show i) ]
line n =   set  text n
