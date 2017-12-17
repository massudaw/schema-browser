{-# LANGUAGE
    OverloadedStrings
   ,FlexibleContexts
   ,RecursiveDo
 #-}

module TP.QueryWidgets (
    crudUITable,
    refTables,
    refTables',
    idex,
    metaAllTableIndexA ,
    viewer,
    ) where

import Control.Applicative.Lift
import Control.Concurrent.STM.TChan
import Control.Lens ((%~), (&), (^?), _1, _2, over)
import qualified Control.Lens as Le
import Serializer (decodeT)
import Control.Monad.Catch
import Control.Monad.Writer hiding ((<>))
import Data.Bifunctor
import qualified Data.Binary as B
import qualified Data.ByteString.Base64 as B64
import qualified Data.ByteString.Char8 as BSC
import qualified Data.ByteString.Lazy.Char8 as BSL
import Data.Char
import Data.Dynamic (fromDynamic)
import Data.Either
import qualified Data.ExtendedReal as ER
import qualified Data.Foldable as F
import Data.Foldable (foldl')
import Data.Functor.Apply
import Data.Functor.Constant
import qualified Data.GiST.GiST as G
import qualified Data.HashMap.Strict as HM
import Data.Interval (interval)
import qualified Data.Interval as Interval
import qualified Data.List as L
import qualified Data.Map as M
import Data.Map (Map)
import Data.Maybe
import Data.Ord
import qualified Data.Poset as P
import Data.Semigroup hiding (diff)
import qualified Data.Set as S
import Data.Set (Set)
import Data.String
import Data.Text (Text)
import qualified Data.Text as T
import Data.Time
import qualified Data.Traversable as Tra
import Data.Tuple
import Debug.Trace
import Default
import Expression
import GHC.Stack
import qualified Graphics.UI.Threepenny as UI
import Graphics.UI.Threepenny.Core hiding (apply, delete)
import Graphics.UI.Threepenny.Internal (ui)
import qualified NonEmpty as Non
import NonEmpty (NonEmpty(..))
import Prelude hiding (head)
import Query
import Reactive.Threepenny hiding (apply)
import RuntimeTypes
import Schema
import SchemaQuery
import SortList
import Step.Host
import TP.AgendaSelector
import TP.MapSelector
import TP.Selector
import TP.View
import TP.Widgets
import Text
import Text.Read (readMaybe)
import Types
import qualified Types.Index as G
import Types.Patch
import Utils

type ColumnTidings = Map (S.Set (Rel CoreKey ))(Tidings (Maybe (Column CoreKey Showable)))

--- Plugins Interface Methods
createFresh :: Text -> InformationSchema -> Text -> KType CorePrim -> IO InformationSchema
createFresh  tname inf i ty@(Primitive l  atom)  =
  case atom of
    AtomicPrim _  -> do
      k <- newKey i ty 0
      return $ inf
          & keyMapL %~ (HM.insert (tname,i) k )
    RecordPrim (s,t) -> do
      k <- newKey i ty 0
      let tableO = lookTable inf tname
          path =  (FKInlineTable k $ inlineName ty )
      return $ inf
          & tableMapL . Le.ix tname . rawFKSL %~  (:) path
          & pkMapL . Le.ix (S.fromList$ rawPK tableO) . rawFKSL Le.%~  (:) path
          & keyMapL %~ HM.insert (tname,i) k


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

execute :: InformationSchema -> Text -> Plugins -> Maybe (TBData Key Showable) -> IO (Maybe (TBIdx Key Showable))
execute inf t (idp,p) = fmap join . traverse (\v -> fmap (join . fmap (diff v . apply v . liftPatch inf t). join . eitherToMaybe ). catchPluginException inf (tableUnique table) idp ( getPKM (tableMeta table) v) . action $  (mapKey' keyValue) v)
  where
    action :: TBData Text Showable -> IO (Maybe (TBIdx Text Showable))
    action = pluginActionDiff p
    table = lookTable inf t

executeT inf t (idp,p) = fmap join . traverse (\v -> liftIO .fmap (join .  fmap (diff v ).  fmap (liftTable' inf t ). join . eitherToMaybe ) . catchPluginException inf (tableUnique table ) idp ( getPKM (tableMeta table)   v) . action $ (mapKey' keyValue) v)
  where
    table = lookTable inf t
    action = pluginAction p

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
      elemsIn <- mapM (\fresh -> do
        let attrB pre a = do
              wn <-  tbCaseDiff  inf  (lookTable oinf tname) mempty a mempty  mempty pre
              v <- labelCaseDiff inf a  wn
              out <- UI.div # set children [getElement v,getElement wn]
              return  $ TrivialWidget (recoverEditChange <$> facts pre <#> triding v) out

        attrB (const Nothing <$> unoldItems)  (genAttr oinf fresh )
           ) inpfresh
      let
        inp :: Tidings (Maybe (TBData CoreKey Showable))
        inp = fmap tblist <$> foldr (liftA2 (liftA2 (:))) (pure (Just [])) (fmap triding elemsIn)

      (preinp,(_,liftedE )) <- pluginUI  inf (liftA2 mergeTB1 <$>  facts unoldItems <#>  inp) (idp,FPlugins "Enviar" tname aci)

      elemsOut <- mapM (\fresh -> do
        let
          attrB pre a = do
              wn <-  tbCaseDiff inf (lookTable oinf tname) []  a [] [] pre
              TrivialWidget v e <- labelCaseDiff inf a  wn
              out <- UI.div # set children [getElement e,getElement wn]
              return $ TrivialWidget (recoverEditChange <$> pre <*> v ) out
        attrB (fmap (\v ->  justError ("no key " <> show fresh <> " in " <>  show v ) .fmap snd . findTB1 ((== [fresh]) . fmap _relOrigin. keyattr ) $ TB1 (create v :: TBData Key Showable) )  <$> liftedE  )  (genAttr oinf fresh )
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

pluginUI inf oldItems pl@(idp,p@(FPlugins n t (PurePlugin arrow ))) = do
  let
      (tdInput, tdOutput,out) = checkAccessFull inf t arrow oldItems
  headerP <- UI.button # set UI.class_ "btn btn-sm"# set text (T.unpack n)  # sink UI.enabled (isJust <$> facts tdInput)  # set UI.style [("color","white")] # sink UI.style (liftA2 greenRedBlue  (isJust <$> facts tdInput) (isJust <$> facts tdOutput))
  ini <- currentValue (facts tdInput )
  kk <- ui $ stepper ini (diffEvent (facts tdInput ) (rumors tdInput ))
  pgOut <- ui $mapTEventDyn (liftIO . executeT inf t pl)  (tidings kk $diffEvent kk (rumors tdInput ))
  return (headerP, (out ,   pgOut ))
pluginUI inf oldItems pl@(idp,p@(FPlugins n t (DiffPurePlugin arrow ))) = do
  let
      (tdInput, tdOutput,out) = checkAccessFull inf t arrow  oldItems
  headerP <- UI.button # set UI.class_ "btn btn-sm"# set text (T.unpack n)  # sink UI.enabled (isJust <$> facts tdInput)  # set UI.style [("color","white")] # sink UI.style (liftA2 greenRedBlue  (isJust <$> facts tdInput) (isJust <$> facts tdOutput))
  ini <- currentValue (facts tdInput )
  kk <- ui $ stepper ini (diffEvent (facts tdInput ) (rumors tdInput ))
  pgOut <- ui $mapTEventDyn (liftIO . execute inf t pl) (tidings kk $diffEvent kk (rumors tdInput ))
  return (headerP, (out,   pgOut ))
pluginUI inf oldItems pl@(idp,p@(FPlugins n t (DiffIOPlugin arrow))) = do
  overwrite <- checkedWidget (pure False)
  let
      (tdInput, tdOutput,out) = checkAccessFull inf t arrow oldItems
  headerP <- UI.button # set UI.class_ "btn btn-sm"# set text (T.unpack n) # sink UI.enabled (isJust <$> facts tdInput)  #set UI.style [("color","white")] # sink UI.style (liftA2 greenRedBlue  (isJust <$> facts tdInput) (isJust <$> facts tdOutput))
  cliHeader <- UI.click headerP
  let ecv = facts tdInput <@ cliHeader
  bcv <- ui $ stepper Nothing  ecv
  pgOut  <- ui $mapTEventDyn (liftIO . execute inf t pl)  (tidings bcv ecv)
  return (headerP, (out,  pgOut ))

pluginUI inf oldItems pl@(idp,p@(FPlugins n t (IOPlugin arrow))) = do
  overwrite <- checkedWidget (pure False)
  let
      (tdInput, tdOutput,out) = checkAccessFull inf t arrow  oldItems
  headerP <- UI.button # set UI.class_ "btn btn-sm"# set text (T.unpack n)  # sink UI.enabled (isJust <$> facts tdInput)  # set UI.style [("color","white")] # sink UI.style (liftA2 greenRedBlue  (isJust <$> facts tdInput) (isJust <$> facts tdOutput))
  cliHeader <- UI.click headerP
  let ecv = facts tdInput <@ cliHeader
  bcv <- ui $ stepper Nothing ecv
  pgOut  <- ui $mapTEventDyn (liftIO . executeT inf t pl)   (tidings bcv ecv)
  return (headerP, (out ,  pgOut ))



checkAccessFull
  :: Functor f =>
     InformationSchema
     -> Text
     -> Parser t (Union (Access Text)) t2 t3
     -> f (Maybe (TBData Key Showable))
     -> (f (Maybe (TBData Key Showable)),
         f (Maybe (TBData Key Showable)),
         (Union (Access Key)))
checkAccessFull inf  t arrow oldItems = (tdInput,tdOutput,out)
    where
      (inp,out) = second (liftAccessU inf t ). first (liftAccessU  inf t ) $ staticP arrow
      pred =  WherePredicate <$> genPredicateFullU True inp
      tdInput = join . fmap (checkPredFull pred) <$> oldItems
      predOut =  WherePredicate <$> genPredicateFullU True out
      tdOutput = join . fmap (checkPredFull predOut)  <$> oldItems
      checkPredFull pred i
          =  if maybe False (G.checkPred i) pred then  Just i else Nothing


indexPluginAttrDiff
  :: Column Key ()
  -> [(Union (Access Key), Tidings (Maybe (Index (TBData Key Showable))))]
  -> [(Union (Access Key), Tidings (Maybe (Index (Column Key Showable))))]
indexPluginAttrDiff a@(Attr i _ )  plugItens =  evs
  where
    match (IProd _ l) ( IProd _ f) = l == f
    match i f = False
    thisPlugs = filter (hasProd (`match` (head (keyRef . _relOrigin <$> keyattri a))) . fst)  plugItens
    evs  = fmap (fmap (join . fmap (F.find ((== keyattrs a)  . pattrKey )  ))) <$>  thisPlugs
indexPluginAttrDiff  i  plugItens = pfks
  where
    thisPlugs = filter (hasProd (isNested ((fmap (keyRef. _relOrigin) (keyattri i) ))) .  fst) plugItens
    pfks =  first (uNest . justError "No nested Prod FKT" .  findProd (isNested((fmap ( keyRef . _relOrigin ) (keyattri i) )))) . second (fmap (join . fmap ((\p -> F.find (((==  keyattrs i)  . pattrKey )) p )))) <$>  thisPlugs


--- Style and Attribute Size
--
attrSize :: Column CoreKey b -> (Int,Int)
attrSize (FKT  _  _ _ ) = (12,4)
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
      KDelayed  ->  go l
      KSerial  -> go l
      KArray  -> let (i1,i2) = go l in (i1+1,i2*8)
      KInterval  -> let (i1,i2) = go l in (i1*2 ,i2)

getRelOrigin :: [Column k () ] -> [k ]
getRelOrigin =  fmap _relOrigin . concat . fmap keyattri

attributeLabel :: Column CoreKey () -> String
attributeLabel (Fun k rel _ ) = show k ++  " = " ++ renderFun rel
attributeLabel (IT k v ) = show k
attributeLabel (Attr k v ) = show k
attributeLabel (FKT ifk rel v ) =  if L.null constr then   stotal else L.intercalate "," (show <$>  constr ) ++ " => " ++ stotal
  where total = concat $ fmap _relOrigin . keyattr <$> _kvvalues ifk
        stotal = if L.null total then "()" else L.intercalate "," (show <$> total)
        constr = (_relOrigin <$> rel) L.\\ total

labelCaseDiff
  ::  InformationSchema
  -> Column CoreKey ()
  -> TrivialWidget (Editor (Index (Column CoreKey Showable)))
  -> UI (TrivialWidget (Editor (Index (Column CoreKey Showable))))
labelCaseDiff inf a wid = do
    let dynShow = do
          patch <- UI.div
              # sink text  (facts $ show <$> triding wid)
          tip <- UI.div
              # set text (show $ keyattri  a)
          UI.div # set children [tip,patch]
    hl <- detailsLabel (set UI.text (attributeLabel a) . (>>= (flip paintEditDiff $  (triding wid )))) dynShow
    return $ TrivialWidget (triding wid) hl

paintEditDiff e  i  = element e # sinkDiff UI.style ((\ m  -> pure . ("background-color",) $ cond  m  ) <$> i )
  where cond Delete = "purple"
        cond Keep = "blue"
        cond (Diff i) = "yellow"


tbCaseDiff
  :: InformationSchema
  -> Table
  -> SelPKConstraint
  -> Column CoreKey ()
  -> [(S.Set (Rel Key) ,(Tidings (Editor (Index (Column CoreKey Showable))),Tidings (Maybe (Column CoreKey Showable ))))]
  -> PluginRef (Column CoreKey Showable)
  -> Tidings (Maybe (Column CoreKey Showable))
  -> UI (TrivialWidget (Editor (Index (Column CoreKey Showable))))
tbCaseDiff inf table constr i@(FKT ifk  rel tb1) wl plugItens oldItems= do
    let
      nonInj =  (S.fromList $ _relOrigin   <$> rel) `S.difference` (S.fromList $ getRelOrigin $ unkvlist ifk)
      nonInjRefs = filter ((\i -> if S.null i then False else S.isSubsetOf i nonInj ) . S.map _relOrigin .fst) wl
      relTable = M.fromList $ fmap (\i -> (_relTarget i,_relOrigin i)) rel
      restrictConstraint = filter ((`S.isSubsetOf` (S.fromList $ fmap _relOrigin rel)) . S.fromList . getRelOrigin  .fst) constr
      reflectFK f rel box = (\ref -> pure $ FKT (kvlist $ ref ) rel (TB1 box) )<$> backFKRef relTable (getRelOrigin f) box
      convertConstr (f,j) = (f, fmap (\constr -> maybe False constr  .  reflectFK f rel ) j)
      patchRefs = M.fromList $ fmap (\(a,b) -> flip recoverEditChange  <$> a <*> b ) <$> nonInjRefs
    fkUITableGen inf table (convertConstr <$>  restrictConstraint) plugItens  patchRefs oldItems  i

tbCaseDiff inf table constr i@(IT na tb1 ) wl plugItems oldItems = do
    let restrictConstraint = filter ((`S.isSubsetOf` (S.singleton na) ) . S.fromList . getRelOrigin  .fst) constr
    iUITableDiff inf restrictConstraint plugItems oldItems i
tbCaseDiff inf table _ a@(Attr i _ ) wl plugItens preoldItems = do
    let oldItems = maybe preoldItems (\v-> fmap (Just . fromMaybe (Attr i v)) preoldItems  ) ( keyStatic i)
    let tdiv = fmap _tbattr <$> oldItems
    attrUI <- buildUIDiff (buildPrimitive (keyModifier i)) (keyType i) (fmap (fmap (fmap (\(PAttr _ v) -> v))) <$> plugItens) tdiv
    let insertT = fmap (PAttr i ) <$> triding attrUI
    return $ TrivialWidget insertT  (getElement attrUI)
tbCaseDiff inf table _ a@(Fun i rel ac ) wl plugItens preoldItems = do
  let
    search (IProd _ t) = fmap (fmap _tbattr ). uncurry recoverT .snd <$> L.find ((S.singleton t ==) .  S.map _relOrigin . fst) wl
    search (Nested t (Many [One m])) =  fmap (fmap joinFTB . join . fmap (traverse (indexFieldRec m) . _fkttable )). uncurry recoverT . snd <$> L.find ((S.fromList (iprodRef <$> t) ==) .  S.map _relOrigin . fst) wl
    refs = sequenceA $ catMaybes $ search <$> snd rel

  funinp <- traverseUI ( traverse (liftIO. evaluateFFI (rootconn inf) (fst rel) funmap (buildAccess <$> snd rel)). allMaybes ) refs
  ev <- buildUIDiff (buildPrimitive [FRead]) (keyType i) [] funinp
  return $ TrivialWidget (editor <$> preoldItems <*> (fmap (Fun i rel) <$>  funinp)) (getElement ev)

recoverT i j = liftA2 (flip recoverEditChange) i j

emptyRecTable (FKT rel l tb )
    = case tb of
          (LeftTB1 _ ) ->  Just . fromMaybe (FKT (mapKV ((mapFAttr (const (LeftTB1 Nothing)))) rel) l (LeftTB1 Nothing))
          i -> id
emptyRecTable (IT l tb)
    = case tb of
          (LeftTB1 _) -> Just . fromMaybe (IT l (LeftTB1 Nothing))
          i -> id


tbRecCaseDiff ::  InformationSchema ->  Table -> SelPKConstraint  -> Column CoreKey ()
        -> [(S.Set (Rel CoreKey ) ,(Tidings (Editor (Index (Column CoreKey Showable))),Tidings (Maybe (Column CoreKey Showable ))))]
        -> PluginRef  (Column CoreKey Showable) -> Tidings (Maybe (Column CoreKey Showable)) -> UI (TrivialWidget (Editor (Index (Column CoreKey Showable))))
tbRecCaseDiff inf table constr a wl plugItens preoldItems' = do
      let preoldItems = emptyRecTable  a <$> preoldItems'
      let check = F.foldl' (liftA2 (\j i ->  liftA2 apply j i <|> j <|> (create <$> i ))) preoldItems (snd <$> plugItens )
      TrivialWidget btr open<- checkedWidget  (isJust <$> check)
      element open
      (ev,h) <- ui $ newEvent
      inipre <- currentValue  (facts preoldItems)
      let fun True = do
              initpre <- currentValue (facts preoldItems)
              initpreOldB <- ui $ stepper initpre (rumors preoldItems)
              TrivialWidget btre bel <- tbCaseDiff inf table constr a wl plugItens (tidings initpreOldB (rumors preoldItems) )
              ui $ onEventIO (rumors btre) h
              el <- UI.div # set children [bel] # set UI.style [("border","1px solid gray")]
              return el
          fun False = do
            UI.div # set UI.style [("border","1px solid gray")]
      els <- traverseUI  fun btr
      sub <- UI.div # sink children (pure <$> facts els)
      out <- UI.div # set children [open,sub]
      binipre <- ui $ stepper  Keep ev
      return (TrivialWidget  (tidings binipre ev) out)

unTBMap :: Show a => TBData k a -> Map (Set (Rel k  )) (TB k a )
unTBMap = _kvvalues

instance Applicative Editor where
  pure =Diff
  Diff f <*> Diff v = Diff $ f  v
  Keep <*> j = Keep
  j <*> Keep  = Keep
  Delete   <*> j = Delete
  i <*> Delete = Delete

select table  = do
  (_,(_,evMap )) <- selectFromTable table Nothing Nothing [] []
  return (decodeT . mapKey' keyValue <$> evMap)

loadPlugins :: InformationSchema -> Dynamic [Plugins]
loadPlugins inf =  do
  code <- liftIO$ indexSchema  (rootRef inf) "code"
  F.toList <$> transactionNoLog  code (select "plugin_code")


traRepl :: Ord k => Union (Access k) -> Union (Access k)
traRepl i = foldMap repl i
  where
    repl :: Ord k =>Access k-> Union (Access k)
    repl (Rec  ix v ) = replaceU ix v v
    repl v = One v

buildFKS :: InformationSchema
     -> SelPKConstraint
     -> Table
     -> ColumnTidings
     -> PluginRef (TBData CoreKey Showable)
     -> TBData CoreKey ()
     -> Tidings (Maybe (TBData CoreKey Showable))
     -> [(Set (Rel Key),TB Key ())]
     -> UI [(Set (Rel Key), (TrivialWidget  (Editor (PathAttr CoreKey Showable)),
                             Tidings (Maybe (Column CoreKey Showable))))]
buildFKS inf constr table refs plugmods  ftb@(k) oldItems srefs =  F.foldl'  run (return [])  srefs
  where
        meta = tableMeta table
        run jm (l,m) = do
            w <- jm
            let el = L.any (mAny ((l==) . head ))  (fmap (fmap S.fromList ) <$> ( _kvrecrels meta))
                plugattr = indexPluginAttrDiff m plugmods
                oldref = (join . fmap ((^?  Le.ix l ) . unTBMap ) <$> oldItems)
                aref = fromMaybe oldref  (M.lookup (keyattrs m) refs)
            wn <- (if el
                    then tbRecCaseDiff
                    else tbCaseDiff ) inf table constr m  (fmap (first triding) <$> w) plugattr aref
            let nref = maybe wn (\a -> TrivialWidget (liftA3  match (triding wn) a oldref) (getElement wn) ) (M.lookup (keyattrs m) refs)
                match Keep i j = maybe Keep Diff  (join ( liftA2 diff i j <|> fmap (Just .patch) i) )
                match j _ _  = j
            lab <- if
              rawIsSum table
              then return nref
              else do
                v <- labelCaseDiff inf (m) nref
                out <- UI.div # set children [getElement v,getElement  nref] #  set UI.class_ ("col-xs-" <> show (fst $  attrSize m))
                return $ TrivialWidget (triding v) out
            return (w <> [( keyattrs m,(lab,aref))] )


eiTableDiff
  :: InformationSchema
     -> Table
     -> SelPKConstraint
     -> ColumnTidings
     -> PluginRef (TBData CoreKey Showable)
     -> TBData CoreKey ()
     -> Tidings (Maybe (TBData CoreKey Showable))
     -> UI (Element,Tidings (Editor (TBIdx CoreKey Showable)))
eiTableDiff inf table constr refs plmods ftb@(k) preOldItems = do
  oldItems <- ui $ cacheTidings preOldItems
  plugins <- ui $ loadPlugins inf
  let
    meta = tableMeta table
  res <- mapM (pluginUI inf oldItems) (filter ((== rawName table ) . _bounds .  snd) (plugins ))
  let
      resdiff =   snd <$> res
      srefs :: [(Set (Rel Key),
                        TB Key ())]
      srefs = P.sortBy (P.comparing (RelSort .F.toList . fst) ) . M.toList $ replaceRecRel (unTBMap ftb) (fmap (fmap S.fromList )  <$> _kvrecrels meta)
      plugmods = first traRepl <$> (resdiff <> plmods)
  let
      sequenceTable :: [(S.Set (Rel CoreKey ) ,(TrivialWidget (Editor (PathAttr CoreKey Showable)), Tidings (Maybe (Column CoreKey Showable))))] -> Tidings (Editor (TBIdx CoreKey Showable))
      sequenceTable fks = (\old difs -> reduceTable difs) <$> oldItems <*> Tra.sequenceA (triding .fst . snd <$> fks)

  (listBody,output) <- if rawIsSum table
    then do
      fks <- buildFKS inf constr table refs plugmods ftb oldItems srefs
      let
        initialAttr = join . fmap (\ j -> safeHead $ catMaybes  $ unOptionalAttr  <$> F.toList (_kvvalues j))  <$>oldItems
        sumButtom itb =  do
           let i = itb
           case  M.lookup i (M.fromList fks) of
             Just (body ,_) ->  element =<< labelCaseDiff inf (fromJust $ M.lookup i (unKV k)) body
             Nothing -> UI.div
        marker i = sink  UI.style ((\b -> if not b then [("border","1.0px gray solid"),("background","gray"),("border-top-right-radius","0.25em"),("border-top-left-radius","0.25em")] else [("border","1.5px white solid"),("background","white")] )<$> i)

      chk  <- buttonDivSetO (M.keys (unKV k))  (fmap keyattrs <$> initialAttr )  marker sumButtom
      element chk # set UI.style [("display","inline-flex")]
      let
          keypattr (PAttr i _) = [Inline i]
          keypattr (PInline i _) = [Inline i]
          keypattr (PFK  l  _ _) = l
          delete (PAttr i _) = PAttr i (POpt Nothing)
          delete (PInline i _) = PInline i (POpt Nothing)
          delete (PFK i j _ ) = PFK i (fmap delete  j ) (POpt Nothing)
          iniValue = fmap (patch.attrOptional) <$> initialAttr
          resei :: Tidings (Editor (TBIdx CoreKey Showable))
          resei = (\ini j -> fmap (\l  -> (L.map (\i -> if (S.fromList (keypattr i) == j) then i else delete i) (maybe l (:l) ini))) ) <$> iniValue <*> triding chk <*> sequenceTable fks
      listBody <- UI.div #  set children (getElement chk : F.toList (getElement .fst .snd <$> fks))
      sequence $ (\(kix,(el,_)) -> element  el # set UI.style [("border","1.5px gray solid")] # sink0 UI.style (noneShow <$> ((==kix) <$> facts (triding chk) ))) <$> fks
      return (listBody, resei)
    else  do
      fks <- buildFKS inf constr table refs plugmods ftb oldItems srefs
      listBody <- UI.div  #
        set children (F.toList (getElement .fst . snd  <$> fks))
      return (listBody,sequenceTable fks)
  element listBody # set UI.class_ "row" #
      set style [("border","1px"),("border-color",maybe "gray" (('#':).T.unpack) (schemaColor inf)),("border-style","solid"),("margin","1px")]
  plugins <-  do
    pure <$> UI.div # set children (fst <$> res)
  body <- UI.div
    # set children (plugins  <> pure listBody)
    # set style [("margin-left","0px"),("border","2px"),("border-color",maybe "gray" (('#':).T.unpack) (schemaColor inf)),("border-style","solid")]
  tableName <- detailsLabel (set UI.text (T.unpack $ tableName table)) (UI.div  # set text (show table))
  tableDiv <- UI.div # set children [tableName,body]
  out <- ui . calmT $ (\i j -> maybe i ((\b -> if b then i else Keep ). isRight . tableCheck (tableMeta table)) (recoverEditChange j i))  <$> output <*> oldItems
  return (tableDiv , out)


crudUITable
   :: InformationSchema
   -> Table
   -> RefTables
   -> ColumnTidings
   -> PluginRef (TBData CoreKey Showable)
   -> TBData CoreKey ()
   -> Tidings (Maybe (TBData CoreKey Showable))
   -> UI (Element,Tidings (Maybe (TBData CoreKey Showable)))
crudUITable inf table reftb@(_, _ ,gist ,_,tref) refs pmods ftb@(_)  preoldItems = do
      let
        m = tableMeta table
        getItem :: TBData CoreKey Showable -> TransactionM (Maybe (TBIdx CoreKey Showable))
        getItem  v =  getFrom table v `catchAll` (\e -> liftIO (putStrLn $ "error getting Item" ++ show (e :: SomeException)) >> return Nothing)
      preoldItens <- currentValue (facts preoldItems)
      loadedItens <-  ui $ join <$> traverse (transactionNoLog inf  . getItem) preoldItens
      loadedItensEv <- ui $ mapTEventDyn (fmap join <$> traverse (\i ->  do
        p <-  transactionNoLog inf . getItem $ i
        traverse (putPatch tref .pure .PatchRow .(G.getIndex m i,)) p
        return (fmap (PatchRow.(G.getIndex m i,)) p  ) )) preoldItems
      let
        deleteCurrentUn un e l =   maybe l (\v -> G.delete v G.indexParam l) $  G.getUnique un <$> e
        tpkConstraint = (F.toList $ _kvvalues $ tbPK m ftb , (_kvpk m,  gist))
      unConstraints <-  traverse (traverse (traverse (ui . cacheTidings))) $ (\un -> (F.toList $ _kvvalues $ tbUn (S.fromList un ) (TB1 ftb) , (un, fmap (createUn un . G.toList ) gist))) <$> _kvuniques m
      unDeleted <- traverse (traverse (traverse (ui . cacheTidings))) (fmap (fmap (\(un,o)-> (un,deleteCurrentUn un <$> preoldItems <*> o))) (tpkConstraint:unConstraints))
      let
        dunConstraints (un,o) = flip (checkGist un .tblist' ) <$> o
        unFinal:: [([Column CoreKey ()], Tidings PKConstraint)]
        unFinal = fmap (fmap dunConstraints) unDeleted
      (listBody,tablebdiff) <- eiTableDiff inf  table unFinal  refs pmods ftb preoldItems

      (panelItems,tdiff)<- processPanelTable listBody inf reftb  tablebdiff table preoldItems
      let
        tableb = recoverEditChange <$> preoldItems <*> tablebdiff
      out <- UI.div # set children [listBody,panelItems]
      return (out ,tableb)



dynCrudUITable
   :: InformationSchema
   -> Tidings Bool
   -> ColumnTidings
   -> PluginRef (TBData CoreKey Showable)
   -> Table
   -> Tidings (Maybe (TBData CoreKey Showable))
   -> UI ([Element],Tidings (Maybe (TBData CoreKey Showable)))
dynCrudUITable inf open  refs pmods table preoldItems = do
  (e2,h2) <- ui $ newEvent

  let translate True = "plus"
      translate False = "minus"
  nav  <- buttonDivSet [True,False] (fmap Just open)
      (\i -> UI.button
          # set UI.style [("font-size","smaller"),("font-weight","bolder")]
          # set UI.class_ ("buttonSet btn-xs btn-default btn pull-left glyphicon-" <> translate i))
  element nav # set UI.class_ "pull-left"
  sub <- UI.div
  let
      fun True =  do
          reftb@(vpt,_,gist,sgist,_) <- ui $ refTables inf   table
          (out ,tableb)<- crudUITable inf table reftb refs pmods (allRec' (tableMap inf ) table) preoldItems
          ui $ onEventIO (filterE (maybe False (isRight.tableCheck (tableMeta table))) (rumors tableb))
              h2
          return out
      fun i = UI.div

  end <- traverseUI fun ( triding nav)
  element sub # sink children (pure <$> facts end)
  cv <- currentValue (facts preoldItems)
  let evs2 = unionWith const e2  (rumors preoldItems)
  bh2 <- ui $ stepper  cv evs2
  return ([getElement nav,sub], F.foldl' (\i j -> mergePatches <$> i <*> j) (tidings bh2 evs2) (fmap snd pmods))

mergePatches i j = join (liftA2 applyIfChange i j)<|> i  <|> join (createIfChange <$>j)

onDiff f g (Diff i ) = f i
onDiff f g v = g v

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
      inscrud = recoverEditChange <$> oldItemsi <*> inscrudp
      m = tableMeta table
      containsGistNotEqual old ref map = if isJust refM then (\i -> if L.null i  then True else [G.getIndex m old] == L.nub (fmap (G.getIndex m)(F.toList i)))$  (lookGist ix ref map) else False
        where ix = (_kvpk (tableMeta table))
              refM = traverse unSOptional' (getPKM (tableMeta table)ref)
      containsGist ref map = if isJust refM then not $ L.null $  (lookGist ix ref map) else False
        where ix = (_kvpk (tableMeta table))
              refM = traverse unSOptional' (getPKM (tableMeta table)ref)
      conflictGist ref map = if isJust refM then lookGist ix ref map else[]
        where ix = (_kvpk (tableMeta table))
              refM = traverse unSOptional' (getPKM (tableMeta table)ref)
  let
    pred2 =  [(keyRef "schema",Left (int $ schemaId inf  ,Equals))]
    authPred =  [(keyRef "grantee",Left ( int $ fst $ username inf ,Equals))] <> pred2
  auth <- fst <$> ui (transactionNoLog (meta inf) $ selectFromTable "authorization" Nothing Nothing [] authPred)
  let authorize =  (\autho -> fmap unArray . unSOptional' . lookAttr' "authorizations"  =<<  G.lookup (idex  (meta inf) "authorization"  [("schema", int (schemaId inf) ),("table",int $ tableUnique table),("grantee",int $ fst $ username inf)]) autho)  <$> collectionTid auth
  -- Insert when isValid
  let insertEnabled = liftA2 (&&) (liftA2 (||) (onDiff isRight (const False ).  fmap (patchCheckInf inf m)<$>  inscrudp) (maybe False (isRight . tableCheck  m)  <$> inscrud )) (liftA2 (\i j -> not $ maybe False (flip containsGist j) i  ) inscrud gist)
  insertB <- UI.button
      # set UI.class_ "btn btn-sm"
      # set text "INSERT"
      # set UI.class_ "buttonSet"
      # sinkDiff UI.style ((\i j -> noneShowSpan (maybe False (txt "INSERT" `elem`) i && j)) <$>authorize <*> insertEnabled)

  let editEnabled = (\i j k l m -> i && j && k && l && m )<$> ((maybe False (isRight . tableCheck  m)  )<$> inscrud ) <*> (isJust <$> oldItemsi) <*>   (liftA2 (\i j -> maybe False (flip containsGist j) i ) oldItemsi gist ) <*> (liftA3 (\i k j -> maybe False (\(a,b) -> containsGistNotEqual b a j) (liftA2 (,) k i) ) inscrud oldItemsi gist ) <*> (isDiff <$> inscrudp)
  editB <- UI.button
      # set UI.class_ "btn btn-sm"
      # set text "EDIT"
      # set UI.class_ "buttonSet"
      # sinkDiff UI.style ((\i j -> noneShowSpan (maybe False (txt "UPDATE" `elem`) i && j)) <$>authorize <*> editEnabled)
  -- Edit when any persistent field has changed

  let mergeEnabled = liftA2 (&&) (isJust . fmap tableNonRef' <$> inscrud) (liftA2 (\i j -> not . L.null   $ maybe [] (\e -> filter ((/= tableNonRef' e) .tableNonRef') $  conflictGist e j) i  ) inscrud (gist ))
  mergeB <- UI.button# set UI.class_ "btn btn-sm"
      # set text "MERGE"
      # set UI.class_ "buttonSet"
      # sinkDiff UI.style ((\i j -> noneShowSpan (maybe False (txt "UPDATE" `elem`) i && j)) <$>authorize <*> mergeEnabled)

  let deleteEnabled = liftA2 (&&) (isJust . fmap tableNonRef' <$> oldItemsi) (liftA2 (\i j -> maybe False (flip containsGist j) i  ) (oldItemsi ) (gist ))
  deleteB <- UI.button# set UI.class_ "btn btn-sm"
      #   set text "DELETE"
      #   set UI.class_ "buttonSet"
      # sinkDiff UI.style ((\i j -> noneShowSpan (maybe False (txt "DELETE" `elem`) i && j)) <$>authorize <*> deleteEnabled)
  let
       filterKey enabled k = const () <$> filterApply (const <$> enabled) (k )
       crudMerge :: Maybe (TBData Key Showable)  ->  G.GiST (TBIndex Showable) (TBData Key Showable )-> Dynamic (Maybe (RowPatch Key Showable))
       crudMerge (Just i) g =
         fmap (tableDiff . fmap ( fixPatchRow inf (tableName table)) )  <$> transaction inf ( do
            let confl = conflictGist i g
            mapM (deleteFrom m) confl
            fullDiffInsert  m i)
       crudEdi i j =  fmap (fmap (PatchRow .(G.getIndex m j,). fixPatch inf (tableName table )))$ transaction inf $ fullDiffEditInsert  m i j
       crudIns j   =  fmap (tableDiff . fmap ( fixPatchRow inf (tableName table)))  <$> transaction inf (fullDiffInsert m j)
       crudDel :: TBData Key Showable  ->  Dynamic (Maybe (RowPatch Key Showable))
       crudDel j  = fmap (tableDiff . fmap ( fixPatchRow inf (tableName table)))<$> transaction inf (deleteFrom m j )

  altD <- onAltO lbox
  altU <- onAltU lbox
  altI <- onAltI lbox
  cliIns <- UI.click insertB
  cliMerge <- UI.click mergeB
  cliDel <- UI.click deleteB
  cliEdit <- UI.click editB
  diffEdi <- mapEventFin (fmap join . sequence) $ liftA2 crudEdi <$> facts oldItemsi <*> facts inscrud <@ unionWith const cliEdit (filterKey (facts editEnabled)  altU)
  diffDel <- mapEventFin (fmap join . sequence) $ fmap crudDel <$> facts oldItemsi <@ unionWith const cliDel (filterKey (facts deleteEnabled) altD)
  diffMerge <- mapEventFin id $ crudMerge <$> facts inscrud <*> facts gist <@ cliMerge
  diffIns <- mapEventFin (fmap join . sequence) $ fmap crudIns <$> facts inscrud <@ (unionWith const cliIns (filterKey  (facts insertEnabled) altI ))

  conflict <- UI.div # sinkDiff text ((\i j l -> if l then maybe "" (L.intercalate "," .fmap (showFKText inf m) . flip conflictGist  j) i else "")  <$> inscrud <*> gist <*> mergeEnabled) # sinkDiff UI.style (noneShow <$>mergeEnabled)
  debugBox <- checkedWidget (pure False )--onDiff (const True) False <$> inscrudp)
  transaction <- UI.span
    # set children [insertB,editB,mergeB,deleteB,getElement debugBox]
  debug <- UI.div
  let renderTyped (Pure _ ) i  = ident. renderTable  $ i
      renderTyped (Other (Constant i) ) _ = unlines ("Type check error":  i)
  traverseUI (\i -> if  i
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
                          ,("Diff", onDiff (ident . renderRowPatch) (const "") <$> facts inscrudp)
                          ,("New" , maybe "" (\i -> renderTyped (typeCheckTable (_rawSchemaL table,_rawNameL table) i ) i) <$> facts inscrud)]

                      element debug # set children (fmap fst out ++ fmap snd out)
                      mapM (\i -> element i# method "textAreaAdjust(%1)")  (snd <$> out)
                      return debug
                    else  element debug # set children [] ) (triding debugBox)
  out <- UI.div # set children [transaction,conflict,debug]
  return (out, fmap head $ unions $ fmap filterJust [diffEdi,diffIns,diffMerge,diffDel] )



dynHandlerPatch
  :: Eq a1 => (t -> Tidings (Maybe a1) -> UI (TrivialWidget (Editor a)))
     -> (t -> Tidings (Maybe a1))
     -> t
     -> ([TrivialWidget (Editor a)], Tidings Bool)
     -> UI ([TrivialWidget (Editor a)], Tidings Bool)
dynHandlerPatch hand val ix (l,old)= do
    (ev,h) <- ui $ newEvent
    let
        valix = val ix
        idyn True  =  do
          tds <- hand ix valix
          ini <- currentValue (facts $ triding tds)
          liftIO $ h ini
          ui $ onEventIO (rumors $ triding tds) h
          return [getElement tds]
        idyn False = do
          return []
    els <- traverseUI idyn old
    el <- UI.div # sink children (facts els)
    bend <- ui $ stepper Keep  ev
    let
      -- infer i j | traceShow ("infer",i,j) False = undefined
      infer Delete  _ = False
      infer (Diff _) _ = True
      infer Keep (Just _) = True
      infer Keep Nothing  = False
      evnew = (&&) <$> facts old <@> unionWith (&&) (isJust <$> rumors valix) ( flip infer <$> facts valix <@> ev)

    inivalix <- ui $ currentValue (facts valix)
    vout <- ui$ stepper (isJust inivalix) evnew
    let evdiff= diffEvent vout evnew
    bdifout <- ui $ stepper (isJust inivalix)  evdiff
    let out = tidings bdifout evdiff
    return $ (l <> [TrivialWidget (tidings bend ev) el], out )


reduceDiffList o i plug
   | F.all isKeep (snd <$> i) = Keep
   | otherwise = patchEditor $ removeOverlap ++ notOverlap ++  reverse (rights diffs)
   where diffs = catMaybes $ (\(ix,v) -> treatA (o+ix)v) <$> i
         treatA a (Diff v) = Just $ Left $ PIdx a  (Just v)
         treatA a Delete =  Just $ Right $ PIdx a Nothing
         treatA _ Keep = Nothing
         plugl = F.concat $ fmap unPatchSet $ catMaybes plug
           where
             unPatchSet (PatchSet l ) = F.toList l
             unPatchSet i = [i]
         removeOverlap = catMaybes $ fmap (\(PIdx ix a ) -> if (not $ ( ix - o) `elem`  (fst <$> i)) then  Just (PIdx ix a)  else (unDiff ix $ snd $  i !! (ix -  o)) ) plugl
         notOverlap = filter (\(PIdx i o ) ->  not $ L.elem i ((\(PIdx i a ) -> i) <$> plugl )) (lefts diffs)
         unDiff o (Diff v) = Just $  PIdx o (Just v)
         unDiff o i = Nothing


reduceOptional Delete   = Diff $ POpt Nothing
reduceOptional Keep  = Keep
reduceOptional (Diff i )  = Diff (POpt (Just  i))

maybeEdit v id (Diff i) =  id i
maybeEdit v id _  = v

unPOpt (POpt i ) = i


type AtomicUI k b = PluginRef b ->  Tidings (Maybe b) ->  k -> UI (TrivialWidget (Editor (Index b)))

buildUIDiff:: (Eq (Index b),Show (Index b),Show k ,Ord b ,Patch b, Show b) => AtomicUI k b -> KType k -> PluginRef (FTB b) -> Tidings (Maybe (FTB b)) -> UI (TrivialWidget (Editor (PathFTB (Index b) )))
buildUIDiff f (Primitive l prim)  plug tdi = go l plug tdi
  where
    go [] plug tdi = fmap (fmap PAtom) <$> f (fmap (fmap (fmap unAtom )) <$>plug) (fmap unTB1 <$> tdi) prim
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
            let unIndexEl ix = fmap join$ index ix <$> offsetT <*> tdi2
                unplugix ix = fmap ((\p -> fmap join $ (\o ->  fmap (convertPatchSet (o + ix) )) <$> offsetT <*>p)) <$> cplug
                dyn = dynHandlerPatch  (\ix valix ->do
                  let pl = unplugix ix
                  wid <- go ti  pl valix
                  lb <- hlabel ["col-xs-1"] # sink UI.text (show . (+ix) <$> facts offsetT )
                  paintEditDiff lb (triding wid )
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
              bres = reduceDiffList  <$> offsetT <*>  widgets2 <*> foldr (liftA2 (:)) (pure [])  (snd <$>cplug)
            pini <- currentValue (facts bres)
            bres' <- ui $ calmT =<< accumT pini (unionWith (.) ((\_ -> const Delete)<$> clearEv ) (const <$> rumors bres))
            element offsetDiv # set children (fmap getElement widgets)
            size <- ui $ calmT (maybe 0 (Non.length .unArray)  <$> (recoverEditChange <$> ctdi' <*> bres))
            composed <- UI.span # set children [offset ,clearEl, offsetDiv]
            return  $ TrivialWidget  bres' composed
         KOptional -> do
           let pretdi = join . fmap unSOptional' <$> tdi
               plugtdi = fmap (fmap (join . fmap unPOpt ))<$> plug
           tdnew <- go ti  plugtdi pretdi
           -- Delete equals create
           return  (reduceOptional <$> tdnew)
         KSerial -> do
           let pretdi = join . fmap unSOptional' <$> tdi
               plugtdi = fmap (fmap (join . fmap unPOpt )) <$> plug
           tdnew <- go ti  plugtdi pretdi
           -- Delete equals create
           return $ (reduceOptional <$> tdnew )
         KDelayed -> do
           let pretdi =  join . fmap unSOptional' <$> tdi
               plugtdi = fmap (fmap (join . fmap unPOpt )) <$> plug
           tdnew <-  go ti plugtdi pretdi
           let
               test Delete = Delete
               test Keep = Keep
               test (Diff i ) = Diff (POpt (Just  i))
           return (test <$> tdnew)
         KInterval -> do
            let unInterval f (IntervalTB1 i ) = f i
                unInterval _ i = errorWithStackTrace (show i)
                unfinp (Interval.Finite i) = Just i
                unfinp i = Nothing
                plugtdi i (PInter j l)
                  | i == j  =  unfinp $ fst l
                  | otherwise = Nothing
            composed <-  UI.div
            subcomposed <- UI.div # set UI.children [composed]
            inf <- go ti (fmap ( fmap (join . fmap (plugtdi True))) <$> plug) (join.fmap (unInterval inf' ) <$> tdi)
            lbd <- checkedWidget (maybe False id . fmap (unInterval (snd . Interval.lowerBound') ) <$> tdi)

            sup <- go ti (fmap (fmap (join . fmap (plugtdi False ) ))<$> plug) (join.fmap (unInterval sup')  <$> tdi)
            ubd <- checkedWidget (maybe False id .fmap (unInterval (snd . Interval.upperBound' ) ) <$> tdi)
            element composed # set UI.style [("display","inline-flex")] # set UI.children [getElement lbd ,getElement  inf,getElement sup,getElement ubd]
            let
              replaceL  Delete   h= Diff $ PInter True (Interval.NegInf,h)
              replaceL   i h =  fmap (PInter True  . (,h). Interval.Finite) i
              replaceU  Delete   h = Diff $ PInter False (Interval.PosInf,h)
              replaceU  i  h =  fmap (PInter False . (,h).Interval.Finite) i
              output = (\i j -> reduceDiff $ [i,j])<$> (replaceL <$>  triding inf <*> triding lbd ) <*> (replaceU <$> triding sup <*> triding ubd)
            return $ TrivialWidget  output subcomposed
         i -> errorWithStackTrace (show i)


reduceDiff :: [Editor (PathFTB a) ] -> Editor (PathFTB a)
reduceDiff i
  | F.all isKeep i = Keep
  | F.all isDelete i = Delete
  | otherwise = patchEditor $ filterDiff i

horizontal l = UI.div # set UI.style [("display","inline-flex")]  # set UI.children l
vertical l = UI.div # set UI.children l

class PrimEditor a where
  primEditor :: Tidings (Maybe a) -> UI (TrivialWidget (Maybe a))

instance (PrimEditor a,PrimEditor b,PrimEditor c) => PrimEditor (a,b,c) where
  primEditor i = do
    f <- primEditor (fmap (Le.view Le._1)<$> i)
    s <- primEditor (fmap (Le.view Le._2)<$> i)
    t <- primEditor (fmap (Le.view Le._3)<$> i)
    TrivialWidget (liftA3 (,,)<$> triding f <*> triding s <*> triding t) <$> horizontal [getElement f,getElement s,getElement t]

instance (PrimEditor a,PrimEditor b) => PrimEditor (a,b) where
  primEditor i = do
    f <- primEditor (fmap fst <$> i)
    s <- primEditor (fmap snd <$> i)
    TrivialWidget (liftA2 (,)<$> triding f <*> triding s) <$> horizontal [getElement f,getElement s]

instance PrimEditor Bool where
  primEditor  = checkedWidgetM

instance PrimEditor Double where
  primEditor i = fmap (fmap (\(SDouble i) -> i)) <$> buildPrim  [] (fmap SDouble <$> i)  PDouble

buildPrimitive :: [FieldModifier] -> PluginRef Showable ->  Tidings (Maybe Showable) ->  Prim KPrim (Text, Text)-> UI (TrivialWidget (Editor Showable))
buildPrimitive fm plug tdi2 (AtomicPrim i) = do
  let tdi = F.foldl' (liftA2 mergePatches) tdi2  (fmap snd plug)
  pinp <- buildPrim fm  tdi i
  return $ TrivialWidget ( editor  <$> tdi2 <*> triding pinp) (getElement pinp)

buildPrim fm tdi i = case i of
         PGeom ix g->
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
                 | L.length i == 0 && L.length j == 0 = ""
                 | L.length i == 0  = "1/" <> negs
                 | L.length j == 0  = pols
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
           res <- primEditor (fmap (\(SBoolean i) -> i) <$> tdi )
           return (fmap SBoolean <$> res)
         PTime ti -> do
           let  tdip =  tdi
           case ti of
             PTimestamp dbzone -> do
                cliZone <- jsTimeZone
                itime <- liftIO $  getCurrentTime
                let
                  maptime f (STime (STimestamp i)) = STime $ STimestamp (f i)
                  fromLocal = maptime (localTimeToUTC cliZone. utcToLocalTime utc)
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
                oneInput i tdi
             PInterval -> oneInput i tdi
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
         PMime mime ->
           case mime of
            "text/plain" -> do
               let fty = ("textarea",UI.value ,maybe "" (\(SBinary i) -> BSC.unpack i) ,[("width","100%"),("height","300px")])
               ini <- currentValue (facts tdi)
               f <- pdfFrame fty (facts tdi) # sink UI.style (noneShow . (\i -> isJust i || elem FWrite fm) <$> facts tdi)
               vcf <- UI.valueChange f
               let ev = if elem FWrite fm then unionWith const (rumors tdi) (Just . SBinary . BSC.pack <$> vcf) else rumors tdi
               step <- ui $ stepper  ini ev
               return (TrivialWidget (tidings step ev) f)
            "application/dwg" -> do
               let fty = ("div",UI.value,maybe "" (\(SBinary i) -> BSC.unpack i) ,[("width","100%"),("height","300px")])
               ini <- currentValue (facts tdi)
               f <- pdfFrame fty (facts tdi) # sink UI.style (noneShow . (\i -> isJust i || elem FWrite fm) <$> facts tdi)
               vcf <- UI.valueChange f
               let ev = if elem FWrite fm then unionWith const (rumors tdi) (Just . SBinary . BSC.pack <$> vcf ) else rumors tdi
               step <- ui $ stepper  ini ev
               return (TrivialWidget (tidings step ev) f)
            "video/mp4" -> do
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
                   pdfFrame (elem,sr , call,st) pdf = mkElement elem  # set sr (call  pdf)
               v <- UI.div # sink items(pure <$> f)
               o <- UI.div # set children [file,clearB,v]
               return (TrivialWidget tdi2 o)
            otherwise -> do
               let binarySrc = (\(SBinary i) -> "data:" <> T.unpack mime <> ";base64," <>  (BSC.unpack $ B64.encode i) )
               clearB <- UI.button # set UI.text "clear"
               file <- UI.input # set UI.type_ "file" # set UI.multiple True # set UI.style (noneShow $ elem FWrite fm)
               fchange <- fileChange file
               clearE <- UI.click clearB
               cur2 <- ui $currentValue (facts tdi)
               let evi2 = foldl1 (unionWith const) [ rumors tdi,const Nothing <$> clearE,  ( join . fmap (either (const Nothing) (Just . SBinary).   B64.decode .  BSC.drop 7. snd  . BSC.breakSubstring "base64," . BSC.pack ) <$> fchange)]
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
           oneInput z tdi

oneInput :: KPrim -> Tidings (Maybe Showable) ->   UI (TrivialWidget (Maybe Showable))
oneInput i tdi = do
    v <- currentValue (facts tdi)
    inputUI <- UI.input # sinkDiff UI.value (maybe "" renderPrim <$> tdi) # set UI.style [("width","100%")]
    onCE <- UI.onChangeE inputUI
    let pke = unionWith const (readPrim i <$> onCE ) (rumors tdi)
    pk <- ui $ stepper v  pke
    return $ TrivialWidget (tidings pk pke) inputUI


renderInlineTable inf constr pmods oldItems (RecordPrim na) = do
    let
        convertConstr ([pre],j) =  (\i -> ([i],(\j -> (\v -> j [(TB1 (tblist (fmap addDefault (L.delete i attrs) ++ (v))))])) <$> j )) <$> attrs
          where attrs = F.toList $ unKV $ unTB1 $ _fkttable pre
        table = lookTable rinf (snd na)
        rinf = fromMaybe inf (HM.lookup (fst na) (depschema inf))
    uncurry (flip TrivialWidget) <$>
      eiTableDiff inf table (concat $ convertConstr <$> constr) M.empty pmods (allRec' (tableMap inf) table) oldItems




iUITableDiff
  :: InformationSchema
  -- Plugin Modifications
  -> SelPKConstraint
  -> PluginRef (Column CoreKey (Showable))
  -- Selected Item
  -> Tidings (Maybe (Column CoreKey Showable))
  -- Static Information about relation
  -> Column CoreKey ()
  -> UI (TrivialWidget (Editor (PathAttr CoreKey Showable)))
iUITableDiff inf constr pmods oldItems  (IT na  tb1)
  = fmap (fmap (PInline  na) )<$> buildUIDiff (renderInlineTable inf (fmap unConstr <$> constr)) (keyType na)   (fmap (fmap (fmap patchfkt)) <$> pmods) (fmap _fkttable <$> oldItems)
  where
    unConstr  =  fmap (\j -> (j . fmap (IT na) ))



isReadOnly (FKT ifk rel _ ) = L.null (unkvlist ifk ) || all (not . any ((/= FRead)). keyModifier . _relOrigin) rel
isReadOnly (Attr k _ ) =  (not . any ((/= FRead)). keyModifier ) k
isReadOnly (IT k _ ) =   (not . any ((/= FRead)). keyModifier ) k


liftPFK :: (Show k,Show b,Ord k) => PathAttr k b-> PathFTB (Map k (FTB b) ,TBIdx k b)
liftPFK (PFK rel l i ) =first (fmap TB1 ) <$> liftPRel l  rel i


liftPRel :: (Show b,Show k ,Ord k) => [PathAttr k b] -> [Rel k] -> PathFTB c -> PathFTB (Map k b ,c)
liftPRel  l rel f = liftA2 (,) (M.fromList  <$> F.foldl' (flip mergePFK) (PAtom []) rels) f
  where rels = catMaybes $ findPRel l <$> rel

recoverRel :: Eq k => PathFTB ([b] ,TBIdx k b) -> ([PathFTB b],PathFTB (TBIdx k b))
recoverRel i = (getZipList $ sequenceA $ ZipList . fst <$>   i , snd <$> i)

mergePFK :: Show a => PathFTB a -> PathFTB [a] -> PathFTB [a]
mergePFK (POpt i ) (POpt j) = POpt $ mergePFK  <$> i <*> j
mergePFK (PatchSet i) (PatchSet j) =PatchSet $ Non.zipWith mergePFK i j
mergePFK (PIdx ixi i ) (PIdx ixj j)
    | ixi == ixj = PIdx ixi $ mergePFK  <$> i <*> j
    | otherwise = error ("wrong idx: " ++ show (ixi,ixj))
mergePFK (POpt i ) j = POpt $ flip mergePFK  j <$> i
mergePFK j (POpt i ) = POpt $ mergePFK  j  <$> i
mergePFK (PatchSet j) i =  PatchSet $ flip mergePFK i <$> j
mergePFK i (PatchSet j) =  PatchSet $ mergePFK i <$> j
mergePFK (PIdx ix i ) (PAtom l) = PIdx ix (flip mergePFK (PAtom l)  <$>  i)
mergePFK (PAtom i ) (PAtom l) = PAtom (i : l)
mergePFK i  j = errorWithStackTrace (show (i,j))
findPRel l (Rel k op j) =  do
  PAttr k v <- L.find (\(PAttr i v) -> i == k ) l
  return $ fmap (k,) v
recoverPFK :: [Key] -> [Rel Key]-> PathFTB (Map Key (FTB Showable),TBIdx Key Showable) -> PathAttr Key Showable
recoverPFK ori rel i =
  PFK rel ((catMaybes $ defaultAttrs <$> ori ) ++  (fmap (\(i,j) -> PAttr i (join $ fmap patch j)) $  zip  (L.sort ori ). getZipList . sequenceA $ fmap ( ZipList . F.toList. fst) i))   (fmap snd i)

attrToTuple  (Attr k v ) = (k,v)


fkUITablePrim ::
  InformationSchema
  -- Plugin Modifications
  -> ([Rel Key],Table,[CoreKey])
  -> SelTBConstraint
  -- Same Table References
  -> ColumnTidings
  -> PluginRef  (TBRef  Key Showable)
  -- Relation Event
  -> Tidings (Maybe (TBRef CoreKey Showable))
  -- Static Information about relation
  -> [(Rel Key,CorePrim)]
  -> UI (TrivialWidget(Editor (PTBRef Key Showable)))
fkUITablePrim inf (rel,targetTable,ifk) constr  nonInjRefs   plmods  oldItems  prim = do
      -- Top Level Widget
      pan <- UI.div #  set UI.class_ "col-xs-5 fixed-label"
      top <- UI.div
      esc <- onEsc top
      panC <- UI.click pan
      let eh  = (unionWith const (const False <$> esc) ((const True <$> panC)  ))
      bh <- ui $ stepper False  eh

      (elsel , helsel ) <- ui newEvent
      (eledit , heledit) <- ui newEvent
      (eleditu , heleditu) <- ui newEvent

      let
          relTable = M.fromList $ fmap (\(Rel i _ j ) -> (j,i)) rel
          relType = M.fromList $ fmap (\(Rel i _ j,t) -> (j,t)) prim
          ftdi = F.foldl' (liftA2 mergePatches)  oldItems (snd <$>  plmods)
      inipl <- mapM (ui . currentValue . facts) (snd <$>  plmods)
      let inip = maybe Keep (Diff .head) $ nonEmpty $ catMaybes inipl

      blsel <- ui $ stepper (fst <$> inip) (unionWith const elsel  (const Keep <$> rumors oldItems))
      bledit <- ui $ stepper (snd <$> inip) eledit
      bleditall <- ui  $ stepper  (snd <$> inip) eleditu

      let
        selector False = do
          let sel = liftA2 editor oldItems ftdi
          reftb@(vpt,_,gist,sgist,_) <- ui $ refTables inf   targetTable
          ui $ onEventIO
            ((,,,,) <$> facts gist <*> facts sgist <*> facts oldItems <*> blsel <@> rumors sel)
            (\(g,s,old,oldsel,i) ->
              when (oldsel /= fmap (fst) i) $ do
                helsel $ fmap (fst) i
                onDiff  (heledit .  editor (snd <$> old) .  (searchGist relTable targetTable  g s. M.toList . fst ) ) (\i -> heledit $snd <$> i) i
              )
          return []
        selector True = do
          reftb@(vpt,_,gist,sgist,_) <- ui $ refTables inf   targetTable
          let
            iold2 :: Tidings (Maybe (Map Key (FTB Showable)))
            iold2 =  fmap (M.fromList . concat) . allMaybesEmpty <$> iold
                where
                  iold :: Tidings [Maybe [(CoreKey,FTB Showable)]]
                  iold  = Tra.sequenceA $ fmap (join . fmap ( traverse (traverse unSOptional')) . fmap aattr  ) <$> F.toList nonInjRefs
            ftdi2 :: Tidings (Maybe (Map Key (FTB Showable)))
            ftdi2 =   fmap (M.fromList . zip (L.sort $ _relOrigin <$> rel). getZipList . (ZipList . F.toList . fst) )  <$> ftdi
          let
            vv :: Tidings (Maybe (Map CoreKey (FTB Showable)))
            vv =   join .   fmap (\i -> if  M.size i == L.length rel then Just i else Nothing) <$>  liftA2 (<>) iold2  ftdi2
          tdi <- ui $ cacheTidings ((\g s v -> join $ searchGist relTable targetTable  g s  .M.toList <$> v) <$> gist  <*> sgist <*> vv)
          cv <- currentValue (facts tdi)
          metaMap <- mapWidgetMeta inf

          cliZone <- jsTimeZone
          metaAgenda <- eventWidgetMeta inf  cliZone
          let
              hasMap = L.find ((== targetTable).(Le.^._2)) metaMap
              hasAgenda = L.find ((== targetTable).(Le.^._2)) metaAgenda
              add i m =  if i then (m:) else id

          navMeta  <- buttonDivSet (add (isJust hasAgenda) "Agenda" $ add (isJust hasMap) "Map" ["List"]) (pure $ Just "List"  ) (\i -> UI.button # set UI.text i # set UI.style [("font-size","smaller")] # set UI.class_ "buttonSet btn-xs btn-default btn pull-right")

          itemList <- do
              (elbox ,helbox) <- ui  newEvent
              lboxeel <- traverseUI (\metamap ->
                  case metamap of
                    "List" -> do
                      let predicatefk o = WherePredicate $AndColl $ catMaybes $ fmap (\(k, v) ->  join $ (\ o ->  fmap (\ rel -> PrimColl (keyRef (_relTarget rel),   Left  (o,Flip $ _relOperator rel) )) $  L.find ((==k) . _relOrigin ) rel) <$> unSOptional' v) $ M.toList o
                          predicate = fmap predicatefk <$> iold2
                      itemListEl <- UI.select #  set UI.class_ "row fixed-label" # set UI.size "21" # set UI.style [("width","100%"),("position","absolute"),("z-index","999"),("top","22px")]
                      (lbox , l) <- selectListUI inf targetTable itemListEl predicate reftb constr tdi
                      ui $ onEventIO (rumors lbox) helbox
                      return l
                    "Map" -> do
                      let selection = fromJust hasMap
                      let predicatefk o = WherePredicate $AndColl $ catMaybes $ fmap (\(k, v) ->  join $ (\ o ->  fmap (\ rel -> PrimColl (keyRef (_relTarget rel),   Left  (o,Flip $ _relOperator rel) )) $  L.find ((==k) . _relOrigin ) rel) <$> unSOptional' v) $ M.toList o
                          predicate = fmap predicatefk <$> iold2
                      t <- liftIO $ getCurrentTime
                      TrivialWidget i el <- mapSelector inf predicate selection (pure (t,"month")) tdi (never, pure Nothing)
                      ui $ onEventIO (rumors i ) (helbox.Just)
                      return [el]
                    "Agenda" -> do
                      let predicatefk o = WherePredicate $AndColl $ catMaybes $ fmap (\(k, v) ->  join $ (\ o ->  fmap (\ rel -> PrimColl (keyRef (_relTarget rel),   Left  (o,Flip $ _relOperator rel) )) $  L.find ((==k) . _relOrigin ) rel) <$> unSOptional' v) $ M.toList o
                          predicate = fmap predicatefk <$> iold2
                      let selection = fromJust hasAgenda
                      now <- liftIO getCurrentTime
                      (sel ,(j,i)) <- calendarSelector
                      el <- traverseUI id $ (\delta time predicate -> do
                        (e,l) <- calendarView inf predicate cliZone [selection] (pure (S.singleton targetTable )) Basic delta time
                        ui $ onEventIO (rumors l) (helbox .Just)
                        return e) <$> i <*> j <*> predicate
                      el2 <- UI.div  # sink children (facts el)
                      return [sel,el2]
                ) (triding navMeta)

              elembox <- UI.div # sink children (facts lboxeel)

              let evbox =  elbox
              blbox <- ui $ stepper (fmap Just cv) evbox
              let
                lbox = TrivialWidget (tidings blbox  evbox) elembox
                selCh = rumors (triding lbox)

              elout <- UI.div # set children [getElement navMeta ,elembox]
              return (TrivialWidget  (triding lbox) elout)

          let evsel =  unionWith const (rumors tdi)  (rumors $ join <$> triding itemList)
          prop <- ui $ stepper cv evsel
          let tds = tidings prop evsel
          let
            fksel =  join . fmap (\box ->  (\ref -> (M.fromList $ attrToTuple <$> ref ,box) ) <$> backFKRefType relTable relType ifk box ) <$>   tds
            diffFK (Just i ) (Just j) = if fst i == fst j then Keep else Diff(patch j)
            diffFK (Just i ) Nothing = Delete
            diffFK Nothing Nothing = Keep
            diffFK Nothing (Just i) = Diff $ patch i
            output = diffFK <$> oldItems <*> fksel
          inioutput <- ui $ currentValue (facts output)
          ui $ onEventIO (rumors output) (\i -> do
            helsel $ fmap (fst ) i
            heledit $ fmap (snd )i)
          return [getElement itemList]

        edit =  do
          let
            tdi =  flip recoverEditChange <$>   tidings bledit eledit <*> (fmap (snd )<$>oldItems)
            replaceKey :: TB CoreKey a -> TB CoreKey a
            replaceKey =  firstTB swapKey
            swapKey k = maybe k id  $ fmap _relTarget $ L.find ((==k)._relOrigin) $  rel
            staticold :: ColumnTidings
            staticold  =  fmap (fmap (fmap replaceKey )) . M.mapKeys (S.map (fmap swapKey)) $ M.filterWithKey (\k _ -> all (\i ->  not (isInlineRel i ) &&  ((_relOperator i) == Equals))k) nonInjRefs

          itemDClick <- UI.dblclick top
          let itemDClickE = fmap (const not) itemDClick
          bop <- ui $ accumT False itemDClickE
          (celem,pretdi) <- dynCrudUITable inf  bop  staticold (fmap (fmap (fmap snd)) <$> plmods) targetTable  tdi
          let
            fksel = fmap (\box -> maybe ((M.empty,box) )(\ref -> ( M.fromList $ attrToTuple <$> ref ,box) ) $ backFKRefType relTable relType ifk box) <$>   pretdi
            diffFK (Just i ) (Just j) =   maybe Keep Diff  (diff i  j)
            diffFK (Just i ) Nothing = Delete
            diffFK Nothing Nothing = Keep
            diffFK Nothing (Just i) = Diff $ patch i
            output = diffFK <$> oldItems <*> fksel
          inioutput <- ui $ currentValue (facts output)
          ui $ onEventIO ((,,) <$> blsel <*> bleditall <@> rumors output) (\(old,olde,i) -> do
            when (old /= fmap (fst) i) $
              helsel $ fmap (fst) i
            when (olde /= fmap (snd)i)$
              heleditu $ fmap (snd) i
            return ()
            )
          return celem

      let
        tdfk = liftA2 (,) <$> tidings blsel elsel <*> tidings bleditall eleditu
      element pan
          # set UI.style [("border","1px solid gray"),("border-radius","4px"),("height","20px")]
          # sink  text (maybe "" (L.take 50 . L.intercalate "," . fmap renderShowable . allKVRec' inf (tableMeta targetTable). snd )  <$>  facts (recoverEditChange <$> oldItems <*> tdfk ))
      selEls <- traverseUI selector  (tidings bh  eh)
      subnet <- UI.div  # sink children (facts selEls)
      subnet2 <- edit
      hidden <- UI.div  # set children [subnet,last subnet2] # set UI.class_ "col-xs-12"
      element top # set children [head subnet2,pan,hidden]
      return $ TrivialWidget   tdfk top


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
  -> UI (TrivialWidget(Editor (PathAttr CoreKey Showable )))
fkUITableGen preinf table constr plmods nonInjRefs oldItems tb@(FKT ifk rel _)
  = fmap (fmap (recoverPFK  setattr rel)) <$> buildUIDiff (fkUITablePrim inf (rel,lookTable inf target,setattr) constr nonInjRefs) (fmap (zip rel) $ mergeFKRef  $ keyType . _relOrigin <$>rel) (fmap (fmap (fmap liftPFK)) <$> plmods) (fmap liftFK <$>oldItems)
    where (targetSchema,target) = findRefTableKey preinf table rel
          inf = fromMaybe preinf $ HM.lookup targetSchema (depschema preinf)
          setattr = keyAttr <$> unkvlist ifk


reduceTable l
  | L.any isDelete l = Delete
  | otherwise  = (\i -> if L.null i then Keep else Diff i) . filterDiff $ l

pdfFrame (elem,sr , call,st) pdf = mkElement (elem ) UI.# sink0 sr (call <$> pdf)  UI.# UI.set style (st)

metaAllTableIndexA inf metaname env =   do
  let modtable = lookTable (meta inf) metaname
  viewer (meta inf) modtable (Le.over (_1) (liftAccess (meta inf) metaname)  <$> env)


viewer :: InformationSchema -> Table -> [(Access Key ,AccessOp Showable )] -> UI Element
viewer inf table envK = do

  let
    filterStatic =filter (not . flip L.elem (concat $ fmap (F.toList . (Le.view Le._1)) envK))
    key = filterStatic $ F.toList $ rawPK table
    sortSet =  filterStatic . F.toList . tableKeys . tableNonRef . TB1 . allRec' (tableMap inf ) $ table
  let
    iniSort = selSort sortSet ((,True) <$>  key)
    flist = catMaybes $ fmap (\(i,_,j) -> (\(op,v) -> (keyRef i,Left (v,readBinaryOp $ T.pack op))) <$> j) iniSort
    pred = WherePredicate $ AndColl $ fmap PrimColl $envK <> flist
  reftb@(_,_,vpt,_,_) <- ui $ refTables' inf   table Nothing  pred
  itemList <- selector inf table reftb (pure Nothing) (pure Nothing)
  tds <-  mdo
    let
      updatedValue = (\i j -> const . join $ flip G.lookup j  . G.getIndex  (tableMeta table)<$> i )<$> facts tds <@> rumors vpt
      selection = const <$> rumors (triding itemList)
    tds <- ui $ accumT  Nothing  (unionWith (.) selection  updatedValue)
    ui $ cacheTidings tds

  (cru,pretdi) <- crudUITable inf table reftb M.empty [] (allRec' (tableMap inf) table) tds
  UI.div # set UI.children [getElement itemList,cru]


convertPatchSet ix (PatchSet p) = patchSet $ catMaybes $ fmap (convertPatchSet ix ) (F.toList p)
convertPatchSet ix (PIdx ix2 p)
              | ix == ix2 = p
              | otherwise = Nothing
