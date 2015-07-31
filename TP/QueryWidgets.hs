{-# LANGUAGE FlexibleInstances,OverloadedStrings,ScopedTypeVariables,FlexibleContexts,ExistentialQuantification,TupleSections,LambdaCase,RankNTypes,RecordWildCards,DeriveFunctor,NoMonomorphismRestriction,RecursiveDo #-}
module TP.QueryWidgets where

import RuntimeTypes
import Data.Functor.Identity
import Control.Monad
import Control.Concurrent
import Reactive.Threepenny
import Data.Either
import qualified Data.Poset as P
import qualified Graphics.UI.Threepenny as UI
import Graphics.UI.Threepenny.Core hiding (delete)
import Data.String
import Data.Bifunctor
import Data.Ord
import Control.Lens ((^?))
import qualified Control.Lens as Le
import Utils
import Data.Char
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
import Data.Maybe
import Data.Time
import qualified Data.Vector as V
import Data.Functor.Apply
import TP.Widgets
import Schema
import Step
import qualified Data.Foldable as F
import Data.Tuple
import Database.PostgreSQL.Simple
import Control.Exception
import Debug.Trace
import qualified Data.Text.Lazy as T
import qualified Data.ByteString.Char8 as BSC
import GHC.Stack

containKV f = (\i ->   S.member ( S.fromList $ fmap keyValue $  kattr (Compose . Identity $ fst i)) (S.fromList $ fmap (S.fromList .head) $ fmap snd $ f))

-- [Note] Smooth Plugins
-- Just update when input change
-- Don't overwrite when wont change output
-- Hide when output is already filled
-- Let overwrite output with user command

-- modifyTB :: (Traversable f ,Ord a) => f a -> Modification a b ->  Maybe ( f (a,b)) -> Maybe (f (a,b))
modifyTB  (InsertTB m) =  (Just m)
modifyTB  (DeleteTB m ) =  Nothing
modifyTB  (EditTB m n ) =  fmap ( mapTB1 (\i -> maybe i (snd) $ getCompose . runIdentity . getCompose $ findTB1  (\k -> keyattr k == keyattr i) m ) ) (Just n)

generateFresh = do
  (e,h) <- liftIO $ newEvent
  b <- stepper Nothing e
  return $ (h,tidings b e)



createFresh n tname pmap i ty  =  do
  k <- newKey i ty
  return $ M.insert (n,tname,i) k pmap

testTable i =  (\t ->  fmap  F.toList  $  (checkTable  t) i)



pluginUI oinf initItems (StatefullPlugin n tname tf fresh (WrappedCall init ac ) ) = do
  window <- askWindow
  let tdInput = isJust . join . fmap (flip testTable  (fst $ head tf ))  <$>   initItems
      table = lookTable oinf tname
  headerP <- UI.button # set text (T.unpack n) # sink UI.enabled (facts tdInput)
  m <- liftIO $  foldl (\i (kn,kty) -> (\m -> createFresh  n tname m kn kty) =<< i ) (return $ pluginsMap oinf) (concat fresh)
  let inf = oinf {pluginsMap = m}
      freshKeys :: [[Key]]
      freshKeys = fmap (lookFresh  inf n tname . fst ) <$> fresh
  freshUI <- Tra.sequence $   zipWith  (\(input,output) freshs -> do
      (h,t :: Tidings (Maybe (TB1 Showable)) ) <- liftIO $ generateFresh
      elems <- mapM (\fresh -> do
        let hasF l = hasProd (== IProd True [ keyValue fresh] ) l
        case  (hasF input , hasF output)  of
             (True,False)-> Right <$> attrUITable (const Nothing <$> initItems) [] (Attr fresh () )
             (False,True)->  Left <$> attrUITable (fmap (\v ->  runIdentity . getCompose . justError ("no key " <> show fresh <> " in " <>  show v ) . fmap snd . getCompose . runIdentity . getCompose . findTB1 ((== [fresh]) . keyattr ) $ v ) <$> t) [] (Attr (fresh) () )
             (True,True)-> errorWithStackTrace $ "circular reference " <> show fresh
             (False,False)-> errorWithStackTrace $ "unreferenced variable "<> show fresh
           ) freshs
      let
        inp :: Tidings (Maybe (TB1 Showable))
        inp = fmap (tbmap . mapFromTBList) <$> foldr (liftA2 (liftA2 (:) )) (pure (Just [])) (fmap (fmap ( fmap (Compose .Identity )) . triding) (rights elems) )
      ei <- if not $ any (\fresh -> hasProd ( == IProd True [keyValue fresh]) input)  freshs
         then
          TrivialWidget (pure (Just  $ tbmap $ M.empty) ) <$> UI.div
         else do
          inpPost <- UI.button # set UI.text "Submit"
          trinp <- cutEvent (UI.click inpPost) inp
          ei <- UI.div # set UI.children ((fmap getElement $ rights elems ) <> [inpPost])
          return $ TrivialWidget trinp ei
      return (h,(output,t),(lefts elems) ,ei )
           ) tf freshKeys
  el <- UI.div # set UI.children (headerP : (concat $ fmap (\(_,_,o,i)-> concat $ [fmap getElement o ,[getElement i]]) freshUI ))
  liftIO $ forkIO  $ fmap (const ()) $ init $ foldl (\ unoldM (f,((h,htidings,loui,inp),action))  -> unoldM >>= (\unoldItems -> do
      let oldItems = foldl1 (liftA2 (liftA2 mergeTB1)) (triding inp: unoldItems)
      liftEvent (rumors oldItems) (\i -> action inf  i  (liftIO . h) )
      return  [oldItems]  ))  (return [initItems] ) ( zip tf $ zip freshUI ac)
  element el # sink UI.style (noneShow <$> facts tdInput)
  return (el ,  (  ((\(_,o,_,_) -> fmap rumors o)$ last freshUI ) ))


pluginUI inf oldItems (BoundedPlugin2 n t f action) = do
  overwrite <- checkedWidget (pure False)
  let tdInput = isJust . join . fmap (flip testTable  (fst f)) <$>  oldItems
      -- tdOutput1 = (\i -> maybe True (const False) $ allMaybes $ fmap (\f -> (if not(fst f ) then join . fmap unRSOptional' else id ) $ fmap snd $ join $ fmap (indexTable  $ snd f) i) (snd f) ) <$>  outputItems
      -- tdOutput= liftA2 (\i j -> if i then True else j) (triding overwrite)  tdOutput1
  -- let ovev =((\ j i  -> if i then j else Nothing) <$>   oldItems <*> tdOutput1)
  v <- currentValue (facts oldItems)
  headerP <- UI.button # set text (T.unpack n) # sink UI.enabled (facts tdInput)
  let ecv = (facts oldItems<@ UI.click headerP)
  bcv <- stepper v (facts oldItems <@ UI.click headerP)
  pgOut <- mapEvent (catchPluginException inf n t . action inf) (ecv)
  return (headerP, (snd f ,   pgOut ))


plugTags inf oldItems (StatefullPlugin n t f action _) = UI.div
plugTags inf bres (BoundedPlugin2 n t f action) = do
  let tdInput = filter (isJust .  (flip testTable  (fst f))) <$>  bres
      tdOutput = filter (not . isJust . (flip testTable (snd f))) <$> tdInput
  headerP <- UI.button # set text (T.unpack n)
  let ecv = tdOutput <@ UI.click headerP
  -- pgOut <- mapEvent (mapM (\inp -> catchPluginException inf n t . maybe (return Nothing )  (\i -> updateModAttr inf i inp (lookTable inf t)) =<< action inf (Just  inp))  ) ecv

  el <- UI.div # sink UI.text ((\i o t-> T.unpack n <> " (" <>  show (length o) <> "/" <> show (length i) <> "/" <> show (length t) <> ")" ) <$> tdInput <*> tdOutput <*> bres)
  UI.div # set children [headerP,el]


lorder lo lref = allMaybes $ fmap (\k -> L.find (\i-> fst i == k ) lref) lo

attrSize (TBEither n l _ ) = maximum $ fmap (attrSize . runIdentity . getCompose) l
attrSize (FKT  _ _ _ _ ) = (12,4)
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

attrUITable
  :: Tidings (Maybe (TB Identity Key Showable))
     -> [Event (Maybe (TB Identity Key Showable))]
     -> TB Identity Key ()
     -> UI (TrivialWidget (Maybe (TB Identity Key Showable)))
attrUITable  tAttr' evs (Attr i _ ) = do
      tdi' <- foldr (\i j ->  updateEvent  (fmap (Tra.traverse ( diffOptional ))) i =<< j) (return tAttr') evs
      let tdi = fmap (\(Attr  _ i )-> i) <$>tdi'
      attrUI <- buildUI (textToPrim <$> keyType i) tdi
      let insertT = fmap (Attr i ) <$> (triding attrUI)
      return $ TrivialWidget insertT  (getElement attrUI)
buildUI i  tdi = case i of
         (KOptional ti) -> do
           tdnew <- fmap (Just. SOptional) <$> buildUI ti (join . fmap unSOptional  <$> tdi)
           retUI <- UI.div# set children [getElement tdnew]
           paintBorder retUI (facts $ triding tdnew) (facts tdi)
           return $ TrivialWidget (triding tdnew ) retUI
         (KSerial ti) -> do
           tdnew <- fmap (Just . SSerial) <$> buildUI ti ( join . fmap unSSerial <$> tdi)
           retUI <- UI.div # set children [getElement tdnew]
           paintBorder retUI (facts $ triding tdnew) (facts tdi)
           return $ TrivialWidget (triding tdnew ) retUI
         (KDelayed ti) -> do
           tdnew <- fmap (maybe Nothing (Just .SDelayed. Just)  ) <$> buildUI ti (join . fmap unSDelayed <$> tdi)
           retUI <- UI.div# set children [getElement tdnew]
           paintBorder retUI (facts $ triding tdnew) (facts tdi)
           return $ TrivialWidget (triding tdnew ) retUI
         (KArray ti) -> do
            TrivialWidget offsetT offset <- offsetField 0
            let arraySize = 8
            widgets <- mapM (\i-> buildUI ti ((\o -> join . fmap (\a-> unSComposite a V.!? (i + o) )) <$> offsetT <*> tdi )) [0..arraySize]
            let tdcomp =  fmap (V.fromList) .  allMaybes .  L.takeWhile isJust  <$> (Tra.sequenceA $ triding <$> widgets)
            sequence $ zipWith (\e t -> element e # sink0 UI.style (noneShow . isJust <$> facts t)) (tail $ getElement <$> widgets) (triding <$> widgets)
            let
                emptyAttr = Just . maybe (SComposite  (V.fromList []) ) id
                bres = (\o -> liftA2 (\l (SComposite m ) -> SComposite (V.take o m <> l <> V.drop  (o + 9 ) m ))) <$> offsetT <*> tdcomp <*> (emptyAttr <$> tdi)
            offsetDiv <- UI.div # set children (fmap getElement widgets)
            paintBorder offsetDiv (facts bres) (facts tdi)
            leng <- UI.span # sink text (("Size: " ++) .show .maybe 0 (V.length . (\(SComposite l ) -> l)) <$> facts bres)
            fk <- UI.div # set UI.style [("display","inline-flex")]  # set  children [offset,  leng ]
            composed <- UI.span # set children [fk , offsetDiv]
            return  $ TrivialWidget bres composed
         (KInterval ti) -> do
            inf <- fmap (fmap ER.Finite) <$> buildUI ti (fmap (\(SInterval i) -> inf' i) <$> tdi)
            sup <- fmap (fmap ER.Finite) <$> buildUI ti (fmap (\(SInterval i) -> sup' i) <$> tdi)
            lbd <- fmap Just <$> checkedWidget (maybe False id . fmap (\(SInterval i) -> snd . Interval.lowerBound' $i) <$> tdi)
            ubd <- fmap Just <$> checkedWidget (maybe False id .fmap (\(SInterval i) -> snd . Interval.upperBound' $i) <$> tdi)
            composed <- UI.div # set UI.style [("display","inline-flex")] # set UI.children [getElement lbd ,getElement  inf,getElement sup,getElement ubd]
            subcomposed <- UI.div # set UI.children [composed]
            let td = (\m n -> fmap SInterval $  join . fmap (\i-> if Interval.null i then Nothing else Just i) $ liftF2 interval m n) <$> (liftA2 (,) <$> triding inf  <*> triding lbd) <*> (liftA2 (,) <$> triding sup <*> triding ubd)
            paintBorder subcomposed (facts td ) (facts tdi)
            return $ TrivialWidget td subcomposed
         {-(Primitive Position) -> do
            let addrs = (\(SPosition (Position (lon,lat,_)))-> "http://maps.google.com/?output=embed&q=" <> (HTTP.urlEncode $ show lat  <> "," <>  show lon )) <$>  tdi
            mkElement "iframe" # sink UI.src (maybe "" id <$> facts addrs) # set style [("width","99%"),("height","300px")]-}
         (Primitive PTimestamp) -> do
            itime <- liftIO $  getCurrentTime
            timeButton <- UI.button # set UI.text "now"
            evCurr <-  mapEvent (fmap Just) (pure getCurrentTime <@ UI.click timeButton)
            let  newEv = fmap (STimestamp . utcToLocalTime utc) <$> evCurr
            tdi2 <- addEvent newEv  tdi
            oneInput tdi2 [timeButton]
         (Primitive PDate) -> do
            itime <- liftIO $  getCurrentTime
            timeButton <- UI.button # set UI.text "now"
            evCurr <-  mapEvent (fmap Just) (pure getCurrentTime <@ UI.click timeButton)
            let  newEv =  fmap (SDate . localDay . utcToLocalTime utc) <$> evCurr
            tdi2 <- addEvent newEv  tdi
            oneInput tdi2 [timeButton]
         (Primitive PDayTime) -> do
            itime <- liftIO $  getCurrentTime
            timeButton <- UI.button # set UI.text "now"
            evCurr <-  mapEvent (fmap Just) (pure getCurrentTime <@ UI.click timeButton)
            let  newEv = fmap (SDayTime. localTimeOfDay . utcToLocalTime utc) <$> evCurr
            tdi2 <- addEvent newEv  tdi
            oneInput tdi2 [timeButton]

         (Primitive (PMime mime)) -> do
           let binarySrc = (\(SBinary i) -> "data:" <> T.unpack mime <> ";base64," <>  (BSC.unpack $ B64.encode i) )
           clearB <- UI.button # set UI.text "clear"
           file <- UI.input # set UI.class_ "file_client" # set UI.type_ "file" # set UI.multiple True
           UI.div # sink0 UI.html (pure "<script> $(\".file_client\").on('change',handleFileSelect); </script>")
           tdi2 <- addEvent (join . fmap (fmap SBinary . either (const Nothing) Just .   B64.decode .  BSC.drop 7. snd  . BSC.breakSubstring "base64," . BSC.pack ) <$> fileChange file ) =<< addEvent (const Nothing <$> UI.click clearB) tdi
           let fty = case mime of
                "application/pdf" -> ("iframe","src",maybe "" binarySrc ,[("width","100%"),("height","300px")])
                "application/x-ofx" -> ("textarea","value",maybe "" (\(SBinary i) -> BSC.unpack i) ,[("width","100%"),("height","300px")])
                "image/jpg" -> ("img","src",maybe "" binarySrc ,[])
           f <- pdfFrame fty (facts tdi2) # sink UI.style (noneShow . isJust <$> facts tdi2)
           fd <- UI.div # set UI.style [("display","inline-flex")] # set children [file,clearB]
           res <- UI.div # set children [fd,f]
           paintBorder res (facts tdi2) (facts  tdi)
           return (TrivialWidget tdi2 res)

         z -> do
            oneInput tdi []
  where
    justCase i j@(Just _) = j
    justCase i Nothing = i
    oneInput tdi elem = do
            let f = facts tdi
            v <- currentValue f
            inputUI <- UI.input # sink0 UI.value ((forceDefaultType  <$> f))
            let pke = foldl1 (unionWith const ) [rumors tdi,readType i <$> UI.valueChange inputUI]
            pk <- stepper v  pke
            let pkt = tidings pk pke
            sp <- UI.div # set children (inputUI : elem)
            paintBorder sp (facts pkt) (facts tdi)
            return $ TrivialWidget pkt sp


forceDefaultType (Just i ) = renderShowable i
forceDefaultType Nothing = ""

diffOptional (SOptional i) = fmap (SOptional .Just)  . join $   unRSOptional' <$> i
diffOptional (SSerial i )  = fmap (SSerial .Just) . join $  unRSOptional' <$>i
diffOptional i   = Just i


tbCase :: InformationSchema -> [Plugins] -> SelPKConstraint  -> TB Identity Key () -> [(TB Identity Key () ,TrivialWidget (Maybe (TB Identity Key Showable)))] -> [(Access Text,Event (Maybe (TB1 Showable)))]-> Tidings (Maybe (TB Identity Key Showable)) -> UI (TrivialWidget (Maybe (TB Identity Key Showable)))
tbCase inf pgs constr i@(FKT ifk _ rel tb1 ) wl plugItens oldItems  = do
        l <- flabel # set text (show $ _relOrigin <$> rel )
        let
            tbi = fmap (Compose . Identity)  <$> oldItems
            thisPlugs = filter (hasProd (isNested ((IProd True $ concat $ fmap (fmap keyValue.keyattr) ifk)) ) . fst) $  plugItens
            pfks =  first ( uNest . justError "No nested Prod IT" .  findProd (isNested((IProd True $ concat $ fmap (fmap keyValue.keyattr) ifk)))) . second (fmap (join . fmap (fmap  unTB . fmap snd . getCompose . runIdentity . getCompose . findTB1 ((==keyattr (_tb i))  . keyattr )))) <$> thisPlugs
            restrictConstraint = filter ((== (fmap keyattr ifk)) . fmap keyattr  .fst) constr

            relTable = M.fromList $ fmap (\(Rel i _ j ) -> (j,i)) rel
            convertConstr :: SelTBConstraint
            convertConstr = fmap ((\td constr  -> (\i -> (\el -> constr  el && fmap _tbref td /= Just el )  $ (justError "no backref" . backFKRef relTable ifk . Just) i)  ) <$> oldItems <*>  )<$>  restrictConstraint
        tds <- fkUITable inf pgs convertConstr pfks (filter (isReflexive .fst) wl) (fmap (runIdentity . getCompose ) <$>  tbi) i
        dv <- UI.div #  set UI.class_ "col-xs-12"# set children [l,getElement tds]
        paintEdit l (facts (fmap _tbref <$> triding tds)) (fmap _tbref <$> facts oldItems)
        return $ TrivialWidget (triding tds) dv

tbCase inf pgs constr i@(IT na tb1 ) wl plugItens oldItems  = do
        l <- flabel # set text (show $ keyAttr .unTB $ na )
        let tbi = fmap (Compose . Identity ) <$> oldItems
            thisPlugs = filter (hasProd (isNested (IProd True (keyValue <$> keyattr na ))) . fst) $  plugItens
            pfks =  first ( uNest . justError "No nested Prod IT" . (findProd (isNested (IProd True (keyValue <$> keyattr na))))) . second ( fmap ( join .  fmap (fmap (runIdentity . getCompose) . fmap snd . getCompose . runIdentity . getCompose . findTB1 ((== keyattr na).keyattr)))) <$> thisPlugs
        tds <- iUITable inf pgs pfks (fmap (runIdentity . getCompose ) <$>  tbi) i
        dv <- UI.div #  set UI.class_ "col-xs-12" # set children [l,getElement tds]
        paintEdit l (facts (triding tds)) (facts oldItems)
        return $ TrivialWidget (triding tds) dv

tbCase inf pgs constr a@(Attr i _ ) wl plugItens oldItems = do
        l<- flabel # set text (show i)
        let thisPlugs = filter (hasProd (== IProd True [keyValue i]) . fst)  plugItens
            tbi = oldItems
            evs  = ( fmap ( join . fmap ( fmap (runIdentity .  getCompose ) . fmap snd . getCompose . runIdentity . getCompose  . findTB1 (((== [i])  . keyattr )))) <$>  (fmap snd thisPlugs))
        tds <- attrUITable tbi evs a
        dv <- UI.div #  set UI.class_ ("col-xs-" <> show ( fst $ attrSize a) )# set children [l,getElement tds]
        paintEdit l (facts (triding tds)) (facts oldItems)
        return $ TrivialWidget (triding tds) dv

tbCase inf pgs constr a@(TBEither n ls  _ ) wl plugItens oldItems = mdo
        l <- flabel # set text (show  n )
        ws <- mapM (\l -> do
            let  tbl = fmap (runIdentity.getCompose) . join . fmap (\(TBEither n _  j) -> join $ fmap (\i -> if (fmap (const ()) i == l) then j else Nothing) j) <$> oldItems
                 lu = runIdentity $ getCompose l
            lw <- tbCase inf pgs constr lu wl plugItens tbl
            return lw ) ls
        chk  <- buttonDivSet (zip [0..(length ls - 1)] ls)  ((join . fmap (\(TBEither n _ j ) ->   join $ (\e -> fmap (,e) . (flip L.elemIndex ls) $ e ) <$> ((fmap (const ())<$> j)))<$>   oldItems)) (show .keyattr . snd) (\i -> UI.button # set text (show $ keyattr $ snd i) )
        sequence $ zipWith (\el ix-> element  el # sink0 UI.style (noneShow <$> ((==ix) .fst <$> facts (triding chk) ))) ws  [0..]
        let teitherl = foldr (liftA2 (:)) (pure []) (triding <$> ws)
            res = liftA2 (\c j -> fmap (TBEither n ls . fmap (Compose . Identity) ) $ atMay j (fst c)) (triding chk) teitherl
        paintEdit l (facts res) (facts oldItems)
        lid <- UI.div #  set UI.class_ ("col-xs-" <> show ( fst $ attrSize a ) )# set children (l:getElement chk : (getElement <$> ws))
        return $ TrivialWidget  res  lid


hasProd p (Many i) = any p i
hasProd p i = False

findProd p (Many i) = L.find p i
findProd p i = Nothing

isNested p (Nested pn i)  =  p == pn
isNested p i   =  False -- p == pn
uNest (Nested pn i) = i

unTBMap = _kvvalues . unTB . _unTB1


uiTable
  ::
     InformationSchema
     -> [Plugins]
     -> SelPKConstraint
     -> Text
     -> [(Access Text,Event (Maybe (TB1 Showable)))]
     -> TB1 ()
     -> Tidings (Maybe (TB1 Showable))
     -> UI (Element,Tidings (Maybe (TB1 Showable)))
uiTable inf pgs constr tname plmods ftb@(TB1 m k ) oldItems = do
  let
      Just table = M.lookup tname  (tableMap inf)

  res <- mapM (pluginUI inf oldItems) (filter ((== rawName table ) . _bounds ) pgs)
  let plugmods = (snd <$> res ) <> plmods

  fks <- foldl (\jm (l,m)  -> do
            w <- jm
            wn <- tbCase inf pgs  constr (unTB m) w plugmods (fmap (unTB . justError "FKT" . (^?  Le.ix l ) . unTBMap ) <$> oldItems)
            return (w <> [(unTB m,wn)])
        ) (return []) (P.sortBy (P.comparing fst ) . M.toList . unTBMap $ ftb)
  let
      tableb :: Tidings (Maybe (TB1 Showable))
      tableb  = fmap (TB1 (tableMeta table) . Compose . Identity . KV . mapFromTBList . fmap _tb) . Tra.sequenceA <$> Tra.sequenceA (triding .snd <$> fks)
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
    # set children (listBody : plugins )
    # set style [("margin-left","10px"),("border","2px"),("border-color","gray"),("border-style","solid")]
  return (body, tableb )


instance P.Poset (FKey (KType Text))where
  compare  = (\i j -> case compare (i) (j) of
                      EQ -> P.EQ
                      LT -> P.LT
                      GT -> P.GT )

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
     -> Tidings Bool
     -> Tidings [TB1 Showable]
     -> [(Access Text,Event (Maybe (TB1 Showable)))]
     -> TB1 ()
     -> Tidings (Maybe (TB1 Showable))
     -> UI ([Element],Event [Modification Key Showable])
crudUITable inf pgs open bres pmods ftb@(TB1 m _ ) preoldItems = do
  chw <- checkedWidget open
  (h,e) <- liftIO $ newEvent
  let fun True = do
          let
            table = lookPK inf ( S.fromList $ findPK ftb)
          preoldItens <- currentValue (facts preoldItems)
          loadedItens <- liftIO$ join <$> traverse (loadDelayed inf ftb)   preoldItens
          maybe (return ()) (liftIO. e. pure)  loadedItens
          loadedItensEv <- mapEvent (fmap join <$> traverse (loadDelayed inf ftb )) (rumors preoldItems)
          let oldItemsE = (\i -> maybe i modifyTB ) <$> facts preoldItems <@> loadedItensEv
          oldItemsB <- stepper (maybe preoldItens modifyTB loadedItens) oldItemsE
          let oldItems = tidings oldItemsB oldItemsE
              tpkConstraint :: ([Compose Identity (TB Identity) Key ()], Tidings PKConstraint)
              tpkConstraint = (F.toList $ _kvvalues $ unTB $ tbPK ftb , flip pkConstraint  <$> bres )
          (listBody,tableb) <- uiTable inf pgs [tpkConstraint] (tableName table) pmods ftb oldItems
          (panelItems,evsa)<- processPanelTable inf  (facts tableb) (facts bres) table oldItems
          let evs =  unions (filterJust loadedItensEv : evsa)
          onEvent evs (\i ->  liftIO $ e i )
          UI.div # set children [listBody,panelItems]
      fun False  = UI.div
  sub <- UI.div # sink items  (pure .fun <$> facts (triding chw))
  return ([getElement chw ,  sub],h )

unTB1 (LeftTB1 (Just i) ) = unTB1 i
unTB1 (ArrayTB1 [i] ) = unTB1 i
unTB1 (TB1 _ i)  = i

tb1Diff f (TB1 _ k1 ) (TB1 _ k2) =  liftF2 f k1 k2

onBin bin p x y = bin (p x) (p y)

type PKConstraint = [Compose Identity (TB Identity ) Key Showable] -> Bool
type TBConstraint = TB1 Showable -> Bool

type SelPKConstraint = [([Compose Identity (TB Identity) Key ()],Tidings PKConstraint)]
type SelTBConstraint = [([Compose Identity (TB Identity) Key ()],Tidings TBConstraint)]
pkConstraint v  = maybe False (const True) . L.find (pkOpSet (concat . fmap aattr $ v ) . (concat . fmap aattr . F.toList .  _kvvalues . unTB . tbPK ))


processPanelTable
   :: InformationSchema
   -> Behavior (Maybe (TB1 Showable))
   -> Behavior [TB1 Showable]
   -> Table
   -> Tidings (Maybe (TB1 Showable))
   -> UI (Element,[Event (Modification Key Showable)])
processPanelTable inf attrsB res table oldItemsi = do
  let
      contains v  = maybe False (const True) . L.find (onBin (pkOpSet) (concat . fmap aattr . F.toList .  _kvvalues . unTB . tbPK ) v )
  insertB <- UI.button # set UI.class_ "buttonSet" # set text "INSERT" # set UI.style (noneShowSpan ("INSERT" `elem` rawAuthorization table ))
  -- Insert when isValid
        # sink UI.enabled (liftA2 (&&) (isJust . fmap tableNonRef <$> attrsB ) (liftA2 (\i j -> not $ maybe False (flip contains j) i  ) attrsB  res))
  editB <- UI.button # set text "EDIT" # set UI.class_ "buttonSet"# set UI.style (noneShowSpan ("UPDATE" `elem` rawAuthorization table ))

  -- Edit when any persistent field has changed
        # sink UI.enabled (liftA2 (&&) (liftA2 (\i j -> maybe False (any fst . F.toList  ) $ liftA2 (liftF2 (\l m -> if l  /= m then {-traceShow (l,m)-} (True,(l,m)) else (False,(l,m))) )  i j) (fmap (_kvvalues . unTB . _unTB1 .  tableNonRef)<$> attrsB) (fmap (_kvvalues . unTB . _unTB1 . tableNonRef )<$> facts oldItemsi)) (liftA2 (\i j -> maybe False (flip contains j) i  ) attrsB  res))

  deleteB <- UI.button # set text "DELETE" # set UI.class_ "buttonSet"# set UI.style (noneShowSpan ("DELETE" `elem` rawAuthorization table ))
  -- Delete when isValid
        # sink UI.enabled ( liftA2 (&&) (isJust . fmap tableNonRef <$> facts oldItemsi) (liftA2 (\i j -> maybe False (flip contains j) i  ) (facts oldItemsi ) res))
  let
      deleteAction ki =  do
        res <- liftIO $ catch (Right <$> delete (conn inf) ki table) (\e -> return $ Left (show $ traceShowId  (e :: SomeException) ))
        return $ const (DeleteTB ki ) <$> res
      editAction :: Maybe (TB1 Showable) -> Maybe (TB1 Showable ) -> IO (Either String (Modification Key Showable))
      editAction attr old = do
        let
            isM' :: Maybe (TB1 Showable)
            isM' =  join $ fmap (TB1  (tableMeta table). Compose . Identity  . KV ) . allMaybesMap <$> (liftA2 (liftF2 (\i j -> if i == j then traceShow i Nothing else   traceShow (i,j) $ Just i))) (traceShowId . _kvvalues. unTB . _unTB1 <$> attr) (traceShowId . _kvvalues. unTB . _unTB1  <$> old)
        res <- liftIO $ catch (maybe (return (Left "no attribute changed check edit restriction")) (\l-> Right <$> updateAttr (conn inf) l (justError "unold" old) table) attr ) (\e -> return $ Left (show $ traceShowId (e :: SomeException) ))
        return $ fmap (const (EditTB (justError "unism'" isM') (justError "unold" old) )) res

      insertAction ip = do
          res <- catch (Right <$> insertAttr (fromAttr )  (conn inf) ip table) (\e -> return $ Left (show $ traceShowId (e :: SomeException) ))
          return $ InsertTB  <$> res

  let    spMap = fmap split . mapEvent id
  (evid,evir) <- spMap $ filterJust $ (fmap insertAction  <$> attrsB ) <@ (UI.click insertB)
  (evdd,evdr) <- spMap $ filterJust $ (fmap deleteAction <$> facts oldItemsi) <@ UI.click deleteB
  (eved,ever) <- spMap $ (editAction  <$> attrsB <*> (facts oldItemsi) ) <@ UI.click editB
  bd <- stepper [] (unions [evid,evdd,eved])
  errorOut <- UI.span # sink UI.text (L.intercalate "," <$> bd)
  transaction <- UI.span# set children [insertB,editB,deleteB,errorOut]
  onEvent (fmap head $ unions [evir,ever,evdr]) ( liftIO . logTableModification inf . TableModification Nothing table )
  return (transaction ,[evir,ever,evdr])


-- lookup pk from attribute list
editedMod :: (Traversable f ,Ord a) => f a ->  Maybe [(a,b)] -> Maybe (f (a,b))
editedMod  i  m=  join $ fmap (\mn-> look mn i ) m
  where look mn k = allMaybes $ fmap (\ki -> fmap (ki,) $  M.lookup ki (M.fromList mn) ) k

showFKE v =  UI.div # set text (L.take 50 $ L.intercalate "," $ fmap renderShowable $ allKVRec $  v)

showFKE' v =  UI.div # set text (L.take 100 $ L.intercalate "," $ F.toList $ fmap renderShowable $   v)

showFK = (pure ((\v j ->j  # set text (L.take 50 $ L.intercalate "," $ fmap renderShowable $ allKVRec  $ v))))

tablePKSet  tb1 = S.fromList $ concat $ fmap ( keyattr)  $ F.toList $ _kvvalues $ unTB $ tbPK  tb1

flabel = UI.span # set UI.class_ (L.intercalate " " ["label","label-default"])

unIndexItens :: Int -> Int -> Maybe (TB Identity  Key Showable) -> Maybe (TB Identity  Key Showable)
unIndexItens ix o=  join . fmap (unIndex o)
  where
    unIndex o (IT  na  (ArrayTB1 j))
      =  IT  na <$>  atMay j (ix + o)
    unIndex o (FKT els refl rel (ArrayTB1 m)  )
      = (\li mi ->  FKT  (nonl <> [mapComp (firstTB unKArray) li]) refl (Le.over relOrigin (\i -> if isArray (keyType i) then unKArray i else i ) <$> rel) mi )
            <$> join (traverse (indexArray (ix + o) ) <$> l)
            <*> atMay m (ix + o)
      where
        l = L.find (all (isArray.keyType) . keyattr)  els
        nonl = L.filter (not .all (isArray.keyType) . keyattr) els
    unIndex o i = errorWithStackTrace (show (o,i))

    indexArray ix s =  atMay (unArray s) ix

unLeftKey (IT na (LeftTB1 (Just tb1))) = IT na tb1
unLeftKey (FKT ilk refl rel  (LeftTB1 (Just tb1 ))) = (FKT (fmap unKOptional<$> ilk) refl (Le.over relOrigin unKOptional <$> rel) tb1)

unLeftItens  :: Maybe (TB Identity  Key Showable) -> Maybe (TB Identity  Key Showable)
unLeftItens = join . fmap unLeftTB
  where

    unLeftTB (IT na (LeftTB1 l))
      = IT na <$>  l
    unLeftTB (FKT ifk refl rel  (LeftTB1 tb))
      = (\ik -> FKT ik  refl (Le.over relOrigin unKOptional <$> rel))
          <$> traverse ( traverse unSOptional . mapComp (firstTB unKOptional )  ) ifk
          <*>  tb
    unLeftTB i = errorWithStackTrace (show i)

tbOptional = mapComp (firstTB kOptional) . fmap (SOptional . Just)

leftItens tb@(IT na _ ) tr =   Just . maybe  emptyIT (\(IT na j) -> IT  na (LeftTB1 (Just j)))  <$> tr
  where emptyIT = IT  na  (LeftTB1 Nothing)
leftItens tb@(FKT ilk refl rel _) tr  = Just . maybe  emptyFKT (\(FKT ifk refl rel  tb)-> FKT (tbOptional <$> ifk) refl (Le.over relOrigin kOptional <$> rel) (LeftTB1 (Just tb))) <$> tr
  where emptyFKT = FKT (fmap (const (SOptional Nothing)) <$> ilk) refl rel (LeftTB1 Nothing)

indexItens tb@(FKT ifk refl rel _) offsetT fks oldItems  = bres
  where  bres2 =    allMaybes .  L.takeWhile isJust  <$> Tra.sequenceA (fmap (fmap (\(FKT i _ _ j ) -> (head $ fmap (unAttr.unTB) $ i,  j)) )  . triding <$> fks)
         emptyFKT = Just . maybe (FKT (fmap (const (SComposite (V.empty))) <$> ifk) refl rel (ArrayTB1 []) ) id
         bres = (\o -> liftA2 (\l (FKT [lc] refl rel (ArrayTB1 m )) -> FKT (fmap (const (SComposite $ V.fromList $  ((L.take o $ F.toList $ unSComposite $(unAttr $ runIdentity $ getCompose lc)  )<> fmap fst l <> (L.drop (o + 9 )  $ F.toList $ unSComposite $(unAttr $ runIdentity $ getCompose lc)  )))) <$> ifk) refl rel (ArrayTB1 $ L.take o m <> fmap snd l <> L.drop  (o + 9 ) m ))) <$> offsetT <*> bres2 <*> (emptyFKT <$> oldItems)

indexItens tb@(IT na _) offsetT items oldItems  = bres
   where bres2 = fmap (fmap (\(IT na j ) -> j)) . allMaybes . L.takeWhile isJust <$> Tra.sequenceA (triding <$> items)
         emptyFKT = Just . maybe (IT  (na) (ArrayTB1 []) ) id
         bres = (\o -> liftA2 (\l (IT ns (ArrayTB1 m )) -> IT   ns (ArrayTB1 $ L.take o m <> l <> L.drop  (o + 9 ) m ))) <$> offsetT <*> bres2 <*> (emptyFKT <$> oldItems)


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
iUITable inf pgs pmods oldItems  tb@(IT na  tb1@(TB1 meta _) )
    = do
      (celem,tcrud) <- uiTable inf pgs [] (_kvname meta )
              (fmap (fmap (fmap _fkttable)) <$> pmods)
              tb1
              (fmap _fkttable <$> oldItems)
      element celem
          # set style [("margin-left","10px")]
      let bres =  fmap (fmap (IT  na  ) ) (tcrud)
      return $ TrivialWidget bres celem
iUITable inf pgs pmods oldItems  tb@(IT na (LeftTB1 (Just tb1))) = do
   tr <- iUITable inf pgs (fmap (unLeftItens  <$> ) <$> pmods) (unLeftItens <$> oldItems) (IT na tb1)
   return $  leftItens tb tr
iUITable inf pgs plmods oldItems  tb@(IT na (ArrayTB1 [tb1]))
    = do
      (TrivialWidget offsetT offset) <- offsetField 0
      items <- mapM (\ix ->
            iUITable inf pgs
                (fmap (unIndexItens  ix <$> (facts offsetT) <@> ) <$> plmods)
                (unIndexItens ix <$> offsetT <*>   oldItems)
                (IT  na tb1)) [0..8]
      let tds = triding <$> items
          es = getElement <$> items
      sequence $ zipWith (\e t -> element e # sink0 UI.style (noneShow . isJust <$> facts t)) (tail es ) ( tds )
      let bres = indexItens tb offsetT items oldItems
      leng <- UI.span # sink text (("Size: " ++) . show .maybe 0 (length . (\(IT _ (ArrayTB1 l) ) -> l)) <$> facts bres )
      fk <- UI.div # set UI.style [("display","inline-flex")]  # set  children [offset,  leng ]
      res <- UI.div # set children (fk: (getElement <$> items))
      return $ TrivialWidget bres res

offsetField  init = do
  offsetL <- UI.span # set text "Offset: "
  offset <- UI.input # set UI.style [("width","50px")] # set UI.value (show init)
  let offsetE =  (filterJust $ readMaybe <$> onEnter offset)
  offsetB <- stepper init offsetE
  let
     offsetT = tidings offsetB offsetE
  offparen <- UI.div # set children [offsetL,offset]
  return (TrivialWidget offsetT offparen)

backFKRef2 relTable ifk box = fmap (\ibox -> (fmap (\ i -> _tb $ Attr (fst i ) (snd i) ). reorderPK . fmap lookFKsel $ ibox) ) .  join . fmap findPKM $ box
  where
        reorderPK l = fmap (\i -> justError "reorder wrong" $ L.find ((== i).fst) l )  (keyAttr . unTB <$> ifk)
        lookFKsel (ko,v)=  (kn ,transformKey (textToPrim <$> keyType ko ) (textToPrim <$> keyType kn) v)
          where kn = justError "relTable" $ M.lookup ko relTable

backFKRef relTable ifk box = fmap (\ibox -> (fmap (\ i -> _tb $ Attr (fst i ) (snd i) ). reorderPK . fmap lookFKsel $ ibox) ) .  join . fmap findPKM $ box
  where
        reorderPK l = fmap (\i -> justError "reorder wrong" $ L.find ((== i).fst) l )  (keyAttr . unTB <$> ifk)
        lookFKsel (ko,v)=  (kn ,transformKey (textToPrim <$> keyType ko ) (textToPrim <$> keyType kn) v)
          where kn = justError "relTable" $ M.lookup ko relTable
nonRefAttr l = concat $  fmap (uncurry Attr) . aattr <$> ( l )

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
fkUITable inf pgs constr plmods wl  oldItems  tb@(FKT ifk refl rel tb1@(TB1 _ _ ) )
    | not refl = do
        nonInjectiveSelection inf pgs wl tb  oldItems
    | otherwise = mdo
      cvres <- currentValue (fmap (fmap unTB . _tbref) <$> facts oldItems)

      let
          cv = search res cvres
          relTable = M.fromList $ fmap (\(Rel i _ j ) -> (j,i)) rel
          rr = tablePKSet tb1
          table = justError "no table found" $ M.lookup rr $ pkMap inf
      res <- liftIO$ addTable inf table

      ftdi <- foldr (\i j -> updateEvent  Just  i =<< j)  (return oldItems) (fmap Just . filterJust . snd <$> plmods)
      let
          res3 :: Tidings [TB1 Showable]
          res3 =  foldr (\constr  res2 -> (\el constr td -> filter (not. constr  )  el )  <$> res2  <*> snd constr <*> (fmap ( _tbref )<$> ftdi)) (tidings res2 never ) constr
      let
          search = (\i j -> join $ fmap (\k-> L.find (\(TB1 _ l )-> interPoint rel k  (concat $ fmap (uncurry Attr) . aattr <$> (F.toList . _kvvalues . unTB $ l)) ) i) $ j )
          tdi =  search <$> res3 <*> (fmap (fmap unTB. _tbref )<$> ftdi)
      filterInp <- UI.input
      filterInpBh <- stepper "" (UI.valueChange filterInp)
      let
          filterInpT = tidings filterInpBh (UI.valueChange filterInp)
          filtering i  = T.isInfixOf (T.pack $ toLower <$> i) . T.toLower . T.intercalate "," . fmap (T.pack . renderShowable) . F.toList
          sortList :: Tidings ([TB1 Showable] -> [TB1 Showable])
          sortList =  sorting  <$> pure True <*> pure (fmap (Le.view relTarget) rel)
      itemList <- listBox (((Nothing:) <$>  fmap (fmap Just) res3) ) (tidings bselection  never) (pure id) ((\i j -> maybe id (\l  ->   (set UI.style (noneShow $ filtering j l  ) ) . i  l ) )<$> showFK <*> filterInpT)

      let evsel = unionWith const (rumors $ join <$> userSelection itemList) (rumors tdi)
      prop <- stepper cv evsel
      let tds = tidings prop evsel
      (celem,evs) <- crudUITable inf pgs  (pure False) res3 (fmap (fmap (fmap _fkttable)) <$> plmods)  tb1  tds
      let
          bselection = fmap Just <$> st
          sel = filterJust $ fmap (safeHead.concat) $ unions $ [(unions  [(rumors $ join <$> userSelection itemList), rumors tdi]),(fmap modifyTB <$> evs)]
      st <- stepper cv sel
      inisort <- currentValue (facts sortList)
      res2  <-  accumB (inisort res ) (fmap concatenate $ unions $ [rumors sortList , (flip (foldr addToList ) <$> evs)])
      let
        reorderPK l = fmap (\i -> justError "reorder wrong" $ L.find ((== i).fst) l )  (keyAttr . unTB <$> ifk)
        lookFKsel (ko,v)=  (kn ,transformKey (textToPrim <$> keyType ko ) (textToPrim <$> keyType kn) v)
          where kn = justError "relTable" $ M.lookup ko relTable
        box = TrivialWidget (tidings st sel) (getElement itemList)
        fksel =  (\box -> fmap (\ibox -> FKT (fmap (\ i -> _tb $ Attr (fst i ) (snd i) ). reorderPK . fmap lookFKsel $ ibox) refl rel (fromJust box) ) .  join . fmap findPKM $ box ) <$>  ( triding box)
      fk <- UI.div # set  children ([getElement box,filterInp] <> celem)
      return $ TrivialWidget fksel fk



fkUITable inf pgs constr plmods  wl oldItems  tb@(FKT ilk refl rel  (LeftTB1 (Just tb1 ))) = do
    tr <- fkUITable inf pgs constr (fmap (unLeftItens <$> ) <$> plmods)  wl (unLeftItens  <$> oldItems)  (FKT (mapComp (firstTB unKOptional) <$> ilk) refl (Le.over relOrigin unKOptional <$> rel) tb1)
    return $ leftItens tb tr
fkUITable inf pgs constr plmods  wl oldItems  tb@(FKT ifk refl rel  (ArrayTB1 [tb1]) ) = do
     (TrivialWidget offsetT offset) <- offsetField 0
     let
         nonInj = fmap  _relOrigin   (filterNotReflexive rel )
         arrayK = mapComp (firstTB unKArray) <$> filter (all (isArray .keyType ) . keyattr)  ifk
         nonInjConstr :: SelTBConstraint
         nonInjConstr = first (pure . Compose . Identity ) .fmap ( fmap (\j (TB1 _ l) -> not $ interPoint rel ( nonRefAttr $ fmap (Compose . Identity) $ maybeToList j) (nonRefAttr  $ F.toList $ _kvvalues $ unTB  l  ) ).  triding) <$> filter (flip S.isSubsetOf (S.fromList   nonInj) . S.fromList . keyattr .Compose . Identity .fst) wl
         fkst = FKT arrayK refl (fmap (Le.over relOrigin (\i -> if isArray (keyType i) then unKArray i else i )) rel)  tb1
     fks <- mapM (\ix-> fkUITable inf pgs (constr <> nonInjConstr ) (fmap (unIndexItens  ix <$> facts offsetT <@> ) <$> plmods ) [] (unIndexItens ix <$> offsetT  <*>  oldItems) fkst) [0..8]
     sequence $ zipWith (\e t -> element e # sink0 UI.style (noneShow . isJust <$> facts t)) (getElement <$> tail fks) (triding <$> fks)
     dv <- UI.div # set children (getElement <$> fks)
     let bres = indexItens tb offsetT fks oldItems
     leng <- UI.span # sink text (("Size: " ++) .show .maybe 0 (length . (\(FKT _ _ _ (ArrayTB1 l) ) -> l)) <$> facts bres)
     fksE <- UI.div # set UI.style [("display","inline-flex")] # set children [offset , leng ]
     res <- UI.div # set children [fksE ,dv]
     -- paintEdit (getElement l) (facts bres) (facts oldItems )
     return $  TrivialWidget bres  res

interPoint
  :: [Rel (FKey (KType Text))]
     -> [TB Identity (FKey (KType Text)) Showable]
     -> [TB Identity (FKey (KType Text)) Showable]
     -> Bool
interPoint ks i j = all id $  catMaybes $ fmap (\(Rel l op  m) -> {-justError "interPoint wrong fields" $-} liftA2 (intersectPredTuple  op) (L.find ((==l).keyAttr ) i )   (L.find ((==m).keyAttr ) j)) ks

intersectPredTuple  op = (\i j-> intersectPred (textToPrim <$> keyType (keyAttr i)) op  (textToPrim <$> keyType (keyAttr j)) (unAttr i) (unAttr j))

unArray (SComposite s) =  V.toList s
unArray o  = errorWithStackTrace $ "unArray no pattern " <> show o

-- Create non
nonInjectiveSelection
  :: InformationSchema
  -> [Plugins]
  -> [(TB Identity Key (),TrivialWidget (Maybe (TB Identity Key Showable)))]
  -> TB Identity Key ()
  -> Tidings (Maybe (TB Identity Key Showable))
  -> UI (TrivialWidget (Maybe (TB Identity Key Showable )))
nonInjectiveSelection inf pgs wl  attr@(FKT fkattr refl ksjoin tbfk ) selks = do
      let
          fkattr' = unTB <$> fkattr
          oldASet :: Set Key
          oldASet = S.fromList (keyAttr <$> fkattr')
          iold :: Tidings ([Maybe [(Key,Showable)]])
          iold  =    (Tra.sequenceA $ fmap (fmap ( aattr . _tb ) ) . triding .snd <$> L.filter (\i-> not . S.null $ S.intersection (S.fromList $ keyattr $ _tb $ fst $ i) oldASet) wl)
          sel = fmap (\i->  (Just . unAttr .unTB<$> _tbref i) ) <$> selks
      (vv ,ct, els) <- inner tbfk sel  fkattr' iold
      o <- UI.div # set children (els)
      let bres = liftA2 (liftA2 (\i j-> FKT (fmap (\i -> _tb $ Attr (fst i) (snd i) ) i)  refl ksjoin j)) vv ct
      return $ TrivialWidget bres o
  where inner tbfk sel fkattr' iold = mdo
            let
                table = justError "no table found" $ M.lookup rr $ pkMap inf
                rr =  tablePKSet tbfk
            res <- liftIO $ addTable inf table
            let
                unRKOptional (Key a b d (KOptional c)  ) = Key a b d c
                unRKOptional (Key a b d c  ) = Key a b d c
                vv =  join . (fmap (traverse (traverse unRSOptional2 . first unRKOptional ))) . join . fmap (lorder $ keyAttr <$> fkattr' ) . fmap concat . allMaybes  <$> iold
                tb = (\i j -> join $ fmap (\k-> L.find ((\(TB1 _  l)-> interPoint ksjoin (uncurry Attr <$> k)  (concat $ fmap (uncurry Attr) . aattr <$> (F.toList $ _kvvalues $ unTB $ l))) ) i) j ) <$> pure res <*> vv
            li <- wrapListBox res2 tb (pure id) showFK
            (ce,evs) <- crudUITable inf pgs (pure False) res2 [] tbfk  tb
            let eres = flip (foldr addToList)  <$>  evs
            res2  <-  accumTds (pure res) eres
            return (vv,tb, (getElement li: ce))

pdfFrame (elem,sr , call,st) pdf = mkElement (elem ) UI.# sink0 (strAttr sr) (call <$> pdf)  UI.# UI.set style (st)

strAttr :: String -> WriteAttr Element String
strAttr name = mkWriteAttr (set' (attr name))

allNonEmpty [] = Nothing
allNonEmpty l = Just  l

sorting :: Bool -> [Key] -> [TB1 Showable]-> [TB1 Showable]
sorting b ss  =  L.sortBy (ifApply b flip (comparing (filterTB1 (not . S.null . (`S.intersection` (S.fromList ss) ). S.fromList .keyattr ))  ))
  where ifApply True i =  i
        ifApply False _ = id



deleteMod :: InformationSchema ->  TB1 Showable -> Table -> IO (Maybe (TableModification Showable))
deleteMod inf kv table = do
  delete (conn inf)  kv table
  Just <$> logTableModification inf (TableModification Nothing table (DeleteTB kv))

updateModAttr :: InformationSchema -> TB1 Showable -> TB1 Showable -> Table -> IO (Maybe (TableModification Showable))
updateModAttr inf kv old table = join <$> traverse (\df -> do
  updateAttr (conn  inf) kv old table
  let mod =  TableModification Nothing table (EditTB  kv old)
  Just <$> logTableModification inf mod) (diffUpdateAttr kv old)


insertMod :: InformationSchema ->  TB1 Showable -> Table -> IO (Maybe (TableModification Showable))
insertMod inf kv table = do
  kvn <- insertAttr fromAttr (conn  inf) kv table
  let mod =  TableModification Nothing table (InsertTB  kvn)
  Just <$> logTableModification inf mod


