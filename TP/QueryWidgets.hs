{-# LANGUAGE OverloadedStrings,ScopedTypeVariables,FlexibleContexts,ExistentialQuantification,TupleSections,LambdaCase,RankNTypes,RecordWildCards,DeriveFunctor,NoMonomorphismRestriction,RecursiveDo #-}
module TP.QueryWidgets where

import RuntimeTypes
import Data.Functor.Compose
import Data.Functor.Identity
import Control.Monad
import Control.Concurrent
import Reactive.Threepenny
import Data.Either
import qualified Graphics.UI.Threepenny as UI
import Graphics.UI.Threepenny.Core hiding (delete)
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
modifyTB  (EditTB (TB1 m) n ) =  fmap ( mapTB1 (\i -> maybe i id $ L.find (\k -> (tbAttr $ fmap fst $ runIdentity $ getCompose k) == (tbAttr $ fmap fst $ runIdentity $ getCompose i) ) ls ) ) (Just n)
    where ls = F.toList m

generateFresh = do
  (e,h) <- liftIO $ newEvent
  b <- stepper Nothing e
  return $ (h,tidings b e)

addAttr (TB1 (KV pk a)) e =  TB1 (KV pk (a <> e))

mergeTB1 (TB1 k) (TB1 k2) = TB1 (k <> k2)


createFresh n tname pmap i ty  =  do
  k <- newKey i ty
  return $ M.insert (n,tname,i) k pmap

testTable i =  (\t -> join . fmap (allMaybes . F.toList . fmap (unRSOptional' .snd)) $  (checkTable  t) i)

instance Monoid (KV a) where
  mempty = KV (PK [] []) []
  mappend (KV (PK i j ) l) (KV ( PK m n ) o)  =  (KV (PK (i <> m) ( j <> n)) (l <> o))

pluginUI oinf initItems (StatefullPlugin n tname tf fresh (WrappedCall init ac ) ) = do
  window <- askWindow
  let tdInput = isJust . join . fmap (flip testTable  (fst $ head tf ))  <$>   initItems
  headerP <- UI.button # set text (T.unpack n) # sink0 UI.enabled (facts tdInput)
  m <- liftIO $  foldl (\i (kn,kty) -> (\m -> createFresh  n tname m kn kty) =<< i ) (return $ pluginsMap oinf) (concat fresh)
  let inf = oinf {pluginsMap = m}
      freshKeys :: [[Key]]
      freshKeys = fmap (lookFresh  inf n tname . fst ) <$> fresh
  freshUI <- Tra.sequence $   zipWith  (\(input,output) freshs -> do
      (h,t :: Tidings (Maybe (TB1 (Key,Showable))) ) <- liftIO $ generateFresh
      elems <- mapM (\fresh -> do
        let hasF l = hasProd (== IProd [ keyValue fresh] ) l
        case  (hasF input , hasF output)  of
             (True,False)-> Right <$> attrUITable (const Nothing <$> initItems) [] (Attr (fresh) fresh)
             (False,True)->  Left <$> attrUITable (fmap (\v -> (\i -> Attr (fst i ) i). justError ("no key " <> show fresh <> " in " <>  show v ) . L.find ((== fresh) .fst) . F.toList $ v ) <$> t) [] (Attr (fresh) fresh)
             (True,True)-> errorWithStackTrace $ "circular reference " <> show fresh
             (False,False)-> errorWithStackTrace $ "unreferenced variable "<> show fresh
           ) freshs
      let inp = fmap (TB1 . KV (PK [] [])) <$> foldr (liftA2 (liftA2 (:) )) (pure (Just [])) (fmap (fmap ( fmap (Compose .Identity )) . triding) (rights elems) )
      ei <- if not $ any (\fresh -> hasProd ( == IProd [keyValue fresh]) input)  freshs
         then
          TrivialWidget (pure (Just  $ TB1 mempty) ) <$> UI.div
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
  element el # sink0 UI.style (noneShow <$> facts tdInput)
  return (el ,  (  ((\(_,o,_,_) -> o)$ last freshUI ) ))


pluginUI inf oldItems (BoundedPlugin2 n t f action) = do
  overwrite <- checkedWidget (pure False)
  let tdInput = isJust . join . fmap (flip testTable  (fst f)) <$>  oldItems
      -- tdOutput1 = (\i -> maybe True (const False) $ allMaybes $ fmap (\f -> (if not(fst f ) then join . fmap unRSOptional' else id ) $ fmap snd $ join $ fmap (indexTable  $ snd f) i) (snd f) ) <$>  outputItems
      -- tdOutput= liftA2 (\i j -> if i then True else j) (triding overwrite)  tdOutput1
  -- let ovev =((\ j i  -> if i then j else Nothing) <$>   oldItems <*> tdOutput1)
  v <- currentValue (facts oldItems)
  headerP <- UI.button # set text (T.unpack n) # sink0 UI.enabled (facts tdInput)
  let ecv = (facts oldItems<@ UI.click headerP)
  bcv <- stepper v (facts oldItems <@ UI.click headerP)
  pgOut <- mapTEvent (action inf) (tidings bcv ecv)
  return (headerP, (snd f ,   pgOut ))


intersectPredTuple  = (\i j -> intersectPred (textToPrim <$> keyType (fst i)) (textToPrim <$> keyType (fst j)) (snd i) (snd j))


lorder lo lref = allMaybes $ fmap (\k -> L.find (\i-> fst i == k ) lref) lo

attrSize (TBEither n l _ ) = maximum $ fmap (attrSize . runIdentity . getCompose) l
attrSize (FKT  _ _ _ _ ) = (12,4)
attrSize (IT _ _ ) = (12,4)
attrSize (Attr _ k) = go  (keyType k)
  where
    go i = case i of
                KOptional l ->  go l
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
                       PMime _ -> (4,8)
                       i -> (3,1)


attrUITable
  :: Tidings (Maybe (TB Identity Key (Key,Showable)))
     -> [Event (Maybe (TB Identity Key (Key,Showable)))]
     -> TB Identity Key Key
     -> UI (TrivialWidget (Maybe (TB Identity Key (Key, Showable))))
attrUITable  tAttr' evs (Attr _ i) = do
      tdi' <- foldr (\i j ->  updateEvent  (fmap (Tra.traverse (Tra.traverse diffOptional ))) i =<< j) (return tAttr') evs
      let tdi = fmap (\(Attr _ i)-> snd i) <$>tdi'
      attrUI <- buildUI (textToPrim <$> keyType i) tdi
      let insertT = fmap (Attr i .(i,)) <$> (triding attrUI)
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
            let  newEv = (unionWith const (rumors tdi) $ fmap (STimestamp . utcToLocalTime utc) <$> evCurr)
            tdi2 <- addEvent newEv  tdi
            oneInput tdi2 [timeButton]
         (Primitive PDate) -> do
            itime <- liftIO $  getCurrentTime
            timeButton <- UI.button # set UI.text "now"
            evCurr <-  mapEvent (fmap Just) (pure getCurrentTime <@ UI.click timeButton)
            let  newEv = (unionWith const (rumors tdi) $ fmap (SDate . localDay . utcToLocalTime utc) <$> evCurr)
            tdi2 <- addEvent newEv  tdi
            oneInput tdi2 [timeButton]
         (Primitive PDayTime) -> do
            itime <- liftIO $  getCurrentTime
            timeButton <- UI.button # set UI.text "now"
            evCurr <-  mapEvent (fmap Just) (pure getCurrentTime <@ UI.click timeButton)
            let  newEv = (unionWith const (rumors tdi) $ fmap (SDayTime. localTimeOfDay . utcToLocalTime utc) <$> evCurr)
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
            inputUI <- UI.input # sink0 UI.value ((forceDefaultType  <$> f))
            let pke = foldl1 (unionWith justCase ) [readType i <$> UI.valueChange inputUI,rumors  tdi]
            pk <- stepper (defaultType i)  pke
            let pkt = tidings pk pke
            sp <- UI.div # set children (inputUI : elem)
            paintBorder sp (facts pkt) (facts tdi)
            return $ TrivialWidget pkt sp


forceDefaultType (Just i ) = renderShowable i
forceDefaultType Nothing = ""

diffOptional (SOptional i) = fmap (SOptional .Just)  . join $   unRSOptional' <$> i
diffOptional (SSerial i )  = fmap (SSerial .Just) . join $  unRSOptional' <$>i
diffOptional i   = Just i


tbCase :: InformationSchema -> [Plugins]   -> TB Identity Key Key -> [(TB Identity Key Key,TrivialWidget (Maybe (TB Identity Key (Key,Showable))))] -> [(Access Text,Tidings (Maybe (TB1 (Key,Showable))))]-> Tidings (Maybe (TB Identity Key (Key,Showable))) -> UI (TrivialWidget (Maybe (TB Identity Key (Key,Showable))))
tbCase inf pgs i@(FKT ifk _ _ tb1 ) wl plugItens oldItems  = do
        l <- flabel # set text (show $ unAttr .unTB <$> ifk)
        let
            rr =  tablePKSet tb1
            table = justError "no table found" $ M.lookup rr $ pkMap inf
            tbi = fmap (Compose . Identity)  <$> oldItems
            thisPlugs = filter (hasProd (isNested ((IProd $ fmap (keyValue.unAttr.runIdentity.getCompose) ifk)) ) . fst) $  plugItens
            pfks =  (first ( uNest . justError "No nested Prod IT" . findProd (isNested((IProd $ fmap (keyValue.unAttr.runIdentity.getCompose) ifk)) ))  . second ( fmap ( join .  fmap (fmap  (runIdentity . getCompose ) . findTB1 ((== ifk ) . tbAttr . fmap (fst )   . runIdentity . getCompose  )))  ) <$> thisPlugs)
        res <- liftIO $ addTable inf table
        tds <- fkUITable inf pgs res pfks (filter (isReflexive .fst) wl) (fmap (runIdentity . getCompose ) <$>  tbi) i
        dv <- UI.li #  set UI.class_ "col-xs-12"# set children [l,getElement tds]
        paintEdit l (facts (triding tds)) (facts oldItems)
        return $ TrivialWidget (triding tds) dv

tbCase inf pgs i@(IT na tb1 ) wl plugItens oldItems  = do
        l <- flabel # set text (show  na )
        let tbi = fmap (Compose . Identity ) <$> oldItems
            thisPlugs = filter (hasProd (isNested (IProd [keyValue na ])) . fst) $  plugItens
            pfks =  first ( uNest . justError "No nested Prod IT" . (findProd (isNested (IProd [keyValue na]))))  . second ( fmap ( join .  fmap (fmap (runIdentity . getCompose) . findTB1 ((== [na]) . keyattr )))  ) <$> thisPlugs
        tds <- iUITable inf pgs pfks (fmap (runIdentity . getCompose ) <$>  tbi) i
        dv <- UI.div #  set UI.class_ "col-xs-12" # set children [l,getElement tds]
        paintEdit l (facts (triding tds)) (facts oldItems)
        return $ TrivialWidget (triding tds) dv
tbCase inf pgs a@(Attr _ i) wl plugItens oldItems = do
        l<- flabel # set text (show i)
        let thisPlugs = filter (hasProd (== IProd [keyValue i]) . fst) $  (fmap (fmap (fmap F.toList) ) <$> plugItens)
            tbi = oldItems
            evs  = (rumors . fmap ( join . fmap ( fmap (\i -> Attr (fst i) i). L.find ((== i).fst )) )   <$>  (fmap snd thisPlugs))
        tds <- attrUITable tbi evs a
        dv <- UI.div #  set UI.class_ ("col-xs-" <> show ( fst $ attrSize a) )# set children [l,getElement tds]
        paintEdit l (facts (triding tds)) (facts oldItems)
        return $ TrivialWidget (triding tds) dv
tbCase inf pgs a@(TBEither n ls  _ ) wl plugItens oldItems = mdo
        ws <- mapM (\l -> do
            let  tbl = fmap (runIdentity.getCompose) . join . fmap (\(TBEither n _  j) -> join $ fmap (\i -> if (fmap fst i == l) then j else Nothing) j) <$> oldItems
                 lu = runIdentity $ getCompose l
            lw <- tbCase inf pgs lu wl plugItens tbl
            return lw ) ls
        chk  <- buttonDivSet (zip [0..(length ls - 1)] ls)  ((join . fmap (\(TBEither n _ j ) ->   join $ (\e -> fmap (,e) . (flip L.elemIndex ls) $ e ) <$> ((fmap fst <$> j)))<$>   oldItems)) (show .keyattr . snd) (\i -> UI.button # set text (show $ keyattr $ snd i) )
        sequence $ zipWith (\el ix-> element  el # sink0 UI.style (noneShow <$> ((==ix) .fst <$> facts (triding chk) ))) ws  [0..]
        let teitherl = foldr (liftA2 (:)) (pure []) (triding <$> ws)
            res = liftA2 (\c j -> fmap (TBEither n ls . fmap (Compose . Identity) ) $ atMay j (fst c)) (triding chk) teitherl
        lid <- UI.div #  set UI.class_ ("col-xs-" <> show ( fst $ attrSize a ) )# set children (getElement chk : (getElement <$> ws))
        return $ TrivialWidget  res  lid


hasProd p (Many i) = any p i
hasProd p i = False

findProd p (Many i) = L.find p i
findProd p i = Nothing

isNested p (Nested pn i)  =  p == pn
isNested p i   =  False -- p == pn
uNest (Nested pn i) = i

uiTable
  ::
     InformationSchema
     -> [Plugins]
     -- Plugin Modifications
     -> Text
     -> [(Access Text,Tidings (Maybe (TB1 (Key,Showable))))]
     -> TB1 Key
     -> Tidings (Maybe (TB1 (Key,Showable)))
     -> UI (Element,Tidings (Maybe (TB1 (Key,Showable))))
uiTable inf pgs tname plmods ftb@(TB1 (KV (PK k d) a)) oldItems = do
  let
      Just table = M.lookup tname  (tableMap inf)

  res <- mapM (pluginUI inf oldItems) (filter ((== rawName table ) . _bounds ) pgs)
  let plugmods = (snd <$> res ) <> plmods
  let
    mapMI f td  = foldl (\jm (l,m)  -> do
                w <- jm
                wn <- f  (unTB m) w plugmods (fmap (\v ->  unTB . justError "FKT" . (^?  td . Le.ix l ) . _unTB1  $ v) <$> oldItems)
                return (w <> [(unTB m,wn)])
              ) (return []) . zip [0..]
  fks <- do
      i <- mapMI (tbCase inf pgs) (kvKey.pkKey) k
      j <- mapMI (tbCase inf pgs) (kvKey.pkDescription) d
      k <- mapMI (tbCase inf pgs) kvAttr a
      return $  KV (PK i j ) k
  let
      tableb :: Tidings (Maybe (TB1 (Key,Showable)))
      tableb  = fmap (TB1 . fmap _tb) . Tra.sequenceA <$> Tra.sequenceA (triding .snd <$> fks)
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
    # set style [("border","2px"),("border-color","gray"),("border-style","solid")]
  return (body, tableb )


unLeftTB  = join . fmap  un
  where
      un (LeftTB1 i) = i
      un i = errorWithStackTrace ("unleft " <> show i )

brow = UI.div # set UI.class_ "row"
bfield s = UI.div # set UI.class_ ("col-lg-" <> show s)

crudUITable
  ::
     InformationSchema
     -> [Plugins]
     -> Behavior [TB1 (Key,Showable)]
     -> [(Access Text,Tidings (Maybe (TB1 (Key,Showable))))]
     -> TB1 Key
     -> Tidings (Maybe (TB1 (Key,Showable)))
     -> UI (Element,[Event (Modification Key Showable)])
crudUITable inf pgs bres pmods ftb@(TB1 (KV (PK k d) a)) oldItems = do
  let
      Just table = M.lookup (S.fromList $ findPK ftb) (pkMap inf)
  (listBody,tableb) <- uiTable inf pgs (tableName table) pmods ftb oldItems
  (panelItems,evsa)<- processPanelTable inf  (facts tableb) bres table oldItems
  body <- UI.div
    # set children (listBody : panelItems : [])
    # set style [("border","2px"),("border-color","gray"),("border-style","solid")]
  return (body,evsa)

tbAttr (IT  i _ ) = [Compose . Identity $Attr i i]
tbAttr (TBEither  _ _   j  ) = (maybeToList j )
tbAttr (FKT i _ _ _ ) = i
tbAttr a@(Attr _ i ) = [Compose . Identity $ a]

filterTB1 f = TB1 . filterKV f . _unTB1
findTB1 f =  findKV f . _unTB1
mapTB1 f = TB1 . mapKV f . _unTB1

unTB1 (LeftTB1 (Just i) ) = unTB1 i
unTB1 (ArrayTB1 [i] ) = unTB1 i
unTB1 (TB1 i)  = i

tb1Diff f (TB1 k1 ) (TB1 k2) =  liftF2 f k1 k2

onBin bin p x y = bin (p x) (p y)

processPanelTable
   :: InformationSchema
   -> Behavior (Maybe (TB1 (Key, Showable)))
   -> Behavior [TB1 (Key,Showable)]
   -> Table
   -> Tidings (Maybe (TB1 (Key, Showable)))
   -> UI (Element,[Event (Modification Key Showable)])
processPanelTable inf attrsB res table oldItemsi = do
  let
      contains v  = maybe True (const False) . L.find (onBin (==) (_pkKey._kvKey . _unTB1) v )
  insertB <- UI.button # set UI.class_ "buttonSet" # set text "INSERT" # set UI.style (noneShowSpan ("INSERT" `elem` rawAuthorization table ))
  -- Insert when isValid
        # sink UI.enabled (liftA2 (&&) (isJust . fmap tableNonRef <$> attrsB ) (liftA2 (\i j -> maybe False (flip contains j) i  ) attrsB  res))
  editB <- UI.button # set text "EDIT" # set UI.class_ "buttonSet"# set UI.style (noneShowSpan ("UPDATE" `elem` rawAuthorization table ))

  -- Edit when any persistent field has changed
        # sink UI.enabled (liftA2 (\i j -> maybe False (any fst . F.toList  ) $ liftA2 (tb1Diff (\l m -> if l  /= m then traceShow (l,m) (True,(l,m)) else (False,(l,m))) )  i j) (fmap tableNonRef <$> attrsB) (fmap tableNonRef <$> facts oldItemsi))
  deleteB <- UI.button # set text "DELETE" # set UI.class_ "buttonSet"# set UI.style (noneShowSpan ("DELETE" `elem` rawAuthorization table ))
  -- Delete when isValid
        # sink UI.enabled ( liftA2 (&&) (isJust . fmap tableNonRef <$> facts oldItemsi) (liftA2 (\i j -> maybe False (not . flip contains j) i  ) attrsB res))
  let
      deleteAction ki =  do
        res <- liftIO $ catch (Right <$> delete (conn inf) ki table) (\e -> return $ Left (show $ traceShowId  (e :: SomeException) ))
        return $ const (DeleteTB ki ) <$> res
      editAction attr old = do
        let
            isM :: Maybe (TB1 (Key,Showable))
            isM =  join $ fmap TB1 . allMaybes . filterKV (isJust ) <$> (liftA2 (liftF2 (\i j -> if i == j then Nothing else  traceShow (i,j) $ Just i))) (_unTB1 . tableNonRef  <$> attr) (_unTB1 . tableNonRef <$> old)
        res <- liftIO $ catch (maybe (return (Left "no attribute changed check edit restriction")) (\l-> Right <$> updateAttr (conn inf) l (fromJust old) table) isM ) (\e -> return $ Left (show $ traceShowId (e :: SomeException) ))
        return $ fmap (const (EditTB (fromJust isM) (fromJust old) )) res

      insertAction ip = do
          res <- catch (Right <$> insertAttr (fromAttr )  (conn inf) ip table) (\e -> return $ Left (show $ traceShowId (e :: SomeException) ))
          return $ InsertTB  <$> res

  let    spMap = fmap split . mapEvent id
  (evid,evir) <- spMap $ filterJust $ (fmap insertAction  <$> attrsB ) <@ (UI.click insertB)
  (evdd,evdr) <- spMap $ filterJust $ (fmap deleteAction <$> facts oldItemsi) <@ UI.click deleteB
  (eved,ever) <- spMap $ (editAction  <$> attrsB <*> (facts oldItemsi) ) <@ UI.click editB
  bd <- stepper [] (unions [evid,evdd,eved])
  errorOut <- UI.div # sink UI.text (L.intercalate "," <$> bd)
  transaction <- UI.div # set children [insertB,editB,deleteB,errorOut]
  onEvent (fmap head $ unions [evir,ever,evdr]) ( liftIO . logTableModification inf . TableModification Nothing table )
  return (transaction ,[evir,ever,evdr])

logTableModification inf (TableModification Nothing table i) = do
  time <- getCurrentTime
  let ltime =  utcToLocalTime utc $ time
  [id] <- liftIO $ query (rootconn inf) "INSERT INTO metadata.modification_table (modification_time,table_name,modification_data,schema_name) VALUES (?,?,?,?) returning modification_id "  (ltime,rawName table,show i , schemaName inf)
  return (TableModification (unOnly id) table i )


addToList  (InsertTB m) =  (m:)
addToList  (DeleteTB m ) =  L.delete m
addToList  (EditTB (TB1 m) n ) = (map (\e-> if  (e ==  n) then  mapTB1 (\i -> maybe i id $ L.find (\k -> (tbAttr $ fmap fst $ runIdentity $ getCompose k) == (tbAttr $ fmap fst $ runIdentity $ getCompose i) ) ls ) e  else e ))
    where ls = F.toList m

-- lookup pk from attribute list
editedMod :: (Traversable f ,Ord a) => f a ->  Maybe [(a,b)] -> Maybe (f (a,b))
editedMod  i  m=  join $ fmap (\mn-> look mn i ) m
  where look mn k = allMaybes $ fmap (\ki -> fmap (ki,) $  M.lookup ki (M.fromList mn) ) k

eitherDescPK (PK i j )
  |not ( L.null j) =  j
  |  otherwise = i

showFKE v =  UI.div # set text (L.take 50 $ L.intercalate "," $ fmap renderShowable $ F.toList $ eitherDescPK $  _kvKey $ allKVRec $  snd <$> v)

showFK = (pure ((\v j ->j  # set text (L.take 50 $ L.intercalate "," $ fmap renderShowable $ F.toList $  eitherDescPK $ _kvKey $ allKVRec $  snd <$> v))))

tablePKSet  tb1 = S.fromList $ fmap (unAttr . runIdentity . getCompose ) $ _pkKey $ _kvKey $ unTB1 $ tableNonRef tb1

flabel = UI.span # set UI.class_ (L.intercalate " " ["label","label-default"])

unIndexItens offsetT  ix tdi = (\o -> join . fmap (unIndex o) )  <$> offsetT <*> tdi
  where
    unIndex o (IT  na  (ArrayTB1 j))
      =  IT  na <$>  atMay j (ix + o)
    unIndex o (FKT [l] refl rel (ArrayTB1 m)  )
      = (\li mi ->  FKT  [li] refl (fmap (first unKArray) rel) mi )
            <$> traverse (indexArray (ix + o) )   l
            <*> atMay (L.drop o m) ix

    indexArray ix s =  atMay (unArray s) ix

unLeftKey (IT na (LeftTB1 (Just tb1))) = IT na tb1
unLeftKey (FKT ilk refl rel  (LeftTB1 (Just tb1 ))) = (FKT (fmap unKOptional<$> ilk) refl (first unKOptional <$> rel) tb1)

unLeftItens tds = join . fmap unLeftTB <$> tds
  where
    unLeftTB (IT na (LeftTB1 l))
      = IT na <$>  l
    unLeftTB (FKT ifk refl rel  (LeftTB1 tb))
      = (\ik -> FKT ik  refl (first unKOptional <$> rel))
          <$> traverse (traverse unKeyOptional ) ifk
          <*>  tb

leftItens tb@(IT na _ ) tr =   Just . maybe  emptyIT (\(IT na j) -> IT  na (LeftTB1 (Just j)))  <$> tr
  where emptyIT = IT  (na)  (LeftTB1 Nothing)
leftItens tb@(FKT ilk refl rel _) tr  = Just . maybe  emptyFKT (\(FKT ifk refl rel  tb)-> FKT (fmap keyOptional <$> ifk) refl rel (LeftTB1 (Just tb))) <$> tr
  where emptyFKT = FKT (fmap (,SOptional Nothing)  <$> ilk) refl rel (LeftTB1 Nothing)

indexItens tb@(FKT ifk refl rel _) offsetT fks oldItems  = bres
  where  bres2 =    allMaybes .  L.takeWhile isJust  <$> Tra.sequenceA (fmap (fmap (\(FKT i _ _ j ) -> (head $ fmap (snd.unAttr.unTB) $ i,  j)) )  . triding <$> fks)
         emptyFKT = Just . maybe (FKT (fmap (,SComposite (V.empty)) <$> ifk) refl rel (ArrayTB1 []) ) id
         bres = (\o -> liftA2 (\l (FKT [lc] refl rel (ArrayTB1 m )) -> FKT ( fmap  ( (,SComposite $ V.fromList $  ((L.take o $ F.toList $ unSComposite $snd $ (unAttr $ runIdentity $ getCompose lc)  )<> fmap fst l <> (L.drop (o + 9 )  $ F.toList $ unSComposite $snd $ (unAttr $ runIdentity $ getCompose lc)  )))) <$> ifk) refl rel (ArrayTB1 $ L.take o m <> fmap snd l <> L.drop  (o + 9 ) m ))) <$> offsetT <*> bres2 <*> (emptyFKT <$> oldItems)

indexItens tb@(IT na _) offsetT items oldItems  = bres
   where bres2 = fmap (fmap (\(IT na j ) -> j)) . allMaybes . L.takeWhile isJust <$> Tra.sequenceA (triding <$> items)
         emptyFKT = Just . maybe (IT  (na) (ArrayTB1 []) ) id
         bres = (\o -> liftA2 (\l (IT ns (ArrayTB1 m )) -> IT   ns (ArrayTB1 $ L.take o m <> l <> L.drop  (o + 9 ) m ))) <$> offsetT <*> bres2 <*> (emptyFKT <$> oldItems)


iUITable
  :: InformationSchema
  -> [Plugins]
  -- Plugin Modifications
  -> [(Access Text,Tidings (Maybe (TB Identity Key (Key,Showable))))]
  -- Selected Item
  -> Tidings (Maybe (TB Identity Key (Key,Showable)))
  -- Static Information about relation
  -> TB Identity Key Key
  -> UI (TrivialWidget(Maybe (TB Identity Key (Key, Showable))))
iUITable inf pgs pmods oldItems  tb@(IT na  tb1@(TB1 _) )
    = do
      (celem,tcrud) <- uiTable inf pgs (inlineName $ keyType na)
              (fmap (fmap (fmap _fkttable)) <$> pmods)
              tb1
              (fmap _fkttable <$> oldItems)
      element celem
          # set style [("padding-left","10px")]
      let bres =  fmap (fmap (IT  na  ) ) (tcrud)
      return $ TrivialWidget bres celem
iUITable inf pgs pmods oldItems  tb@(IT na (LeftTB1 (Just tb1))) = do
   tr <- iUITable inf pgs (fmap unLeftItens  <$> pmods) (unLeftItens oldItems) (IT na tb1)
   return $  leftItens tb tr
iUITable inf pgs plmods oldItems  tb@(IT na (ArrayTB1 [tb1]))
    = do
      (TrivialWidget offsetT offset) <- offsetField 0
      items <- mapM (\ix ->
            iUITable inf pgs
                (fmap (unIndexItens offsetT ix ) <$> plmods)
                (unIndexItens offsetT ix oldItems)
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

pruneTidings chw tds =   tidings chkBH chkAll
  where
    chkEvent = fmap Just $ filterJust $ (\b e -> if b then e else Nothing ) <$> facts chw <@> rumors tds
    chkBehaviour = fmap Just $ filterJust $ (\e b -> if b then e else Nothing ) <$>  facts tds <@> rumors chw
    chkAll = unionWith const chkEvent chkBehaviour
    chkBH = (\b e -> if b then e else Nothing ) <$> facts chw <*> facts tds


sink0 attr uiv ui =  do
  v <- currentValue uiv
  ui # set attr v # sink attr uiv

fkUITable
  ::
  InformationSchema
  -> [Plugins]
  -- Table Data
  -> [TB1 (Key,Showable)]
  -- Plugin Modifications
  -> [(Access Text,Tidings (Maybe (TB Identity Key (Key,Showable))))]
  -- Same Table References
  -> [(TB Identity Key Key,TrivialWidget (Maybe (TB Identity Key (Key,Showable))))]
  -- Relation Event
  -> Tidings (Maybe (TB Identity Key (Key,Showable)))
  -- Static Information about relation
  -> TB Identity Key Key
  -> UI (TrivialWidget(Maybe (TB Identity Key (Key, Showable))))
fkUITable inf pgs res plmods wl  oldItems  tb@(FKT ifk refl rel tb1@(TB1 _ ) )
    | not refl = do
        nonInjectiveSelection inf pgs wl tb (pure res) oldItems
    | otherwise = mdo
      let
          relTable = M.fromList $ fmap swap rel
      ftdi <- foldr (\i j -> updateEvent  Just  i =<< j)  (return oldItems) (fmap Just . filterJust . rumors . snd <$> plmods)
      let
          search = (\i j -> join $ fmap (\k-> L.find (\(TB1 (KV (PK  l _ ) _ ))-> interPoint rel k  (concat $ kattr . Compose . Identity . unTB <$> l) ) i) $ j )
          tdi =  search <$> res2 <#> (fmap (concat . fmap kattr . _tbref )<$> ftdi)
      filterInp <- UI.input
      filterInpBh <- stepper "" (UI.valueChange filterInp)
      let
          filterInpT = tidings filterInpBh (UI.valueChange filterInp)
          filtering i  = T.isInfixOf (T.pack $ toLower <$> i) . T.toLower . T.intercalate "," . fmap (T.pack . renderShowable) . F.toList . fmap snd
          sortList :: Tidings ([(TB1 (Key,Showable))] -> [(TB1 (Key,Showable))])
          sortList =  sorting  <$> pure True <*> pure (fmap snd rel )
      ol <- listBox (tidings ((Nothing:) <$>  fmap (fmap Just) res2) never) (tidings bselection  never) (pure id) ((\i j -> maybe id (\l  ->   (set UI.style (noneShow $ filtering j l  ) ) . i  l ) )<$> showFK <*> filterInpT)

      let evsel = unionWith const (rumors $ join <$> userSelection ol) (rumors tdi)
      prop <- stepper Nothing evsel
      let tds = tidings prop evsel
      chw <- checkedWidget (pure False)
      (celem,evs) <- crudUITable inf pgs  res2 (fmap (fmap (fmap _fkttable)) <$> plmods)  tb1  (pruneTidings (triding chw) tds )
      let
          bselection = fmap Just <$> st
          sel = fmap head $ unions $ [(rumors $ join <$> userSelection ol), rumors tdi] <> (fmap modifyTB <$> evs)
      st <- stepper Nothing sel
      inisort <- currentValue (facts sortList)
      res2  <-  accumB (inisort res ) (fmap concatenate $ unions $ (rumors sortList : (fmap addToList <$> evs)))
      let
        reorderPK l = fmap (\i -> justError "reorder wrong" $ L.find ((== i).fst) l )  (unAttr . unTB <$> ifk)
        lookFKsel (ko,v)=  (kn ,transformKey (textToPrim <$> keyType ko ) (textToPrim <$> keyType kn) v)
          where kn = justError "relTable" $ M.lookup ko relTable
        box = TrivialWidget (tidings st sel) (getElement ol)
        fksel =  (\box -> fmap (\ibox -> FKT (fmap (\ i -> _tb $ Attr (fst i ) i ). reorderPK . fmap lookFKsel $ ibox) refl rel (fromJust box) ) .  join . fmap findPKM $ box ) <$>  ( triding box)
      element celem
          # set UI.style (noneShow False)
          # sink0 UI.style (noneShow <$> (facts $ triding chw))
          # set style [("padding-left","10px")]
      element celem
      fk <- UI.div # set  children [getElement box,filterInp,getElement chw,celem]
      return $ TrivialWidget fksel fk



fkUITable inf pgs res plmods  wl oldItems  tb@(FKT ilk refl rel  (LeftTB1 (Just tb1 ))) = do
    tr <- fkUITable inf pgs res (fmap (unLeftItens ) <$> plmods)  wl (unLeftItens  oldItems)  (FKT (fmap unKOptional<$> ilk) refl (first unKOptional <$> rel) tb1)
    return $ leftItens tb tr
fkUITable inf pgs res2 plmods  wl oldItems  tb@(FKT ifk@[_] refl rel  (ArrayTB1 [tb1]) ) = do
     (TrivialWidget offsetT offset) <- offsetField 0
     let
         fkst = FKT (fmap (fmap unKArray ) ifk) refl (fmap (first (unKArray)) rel)  tb1
         rr = tablePKSet tb1
     res <- liftIO$ addTable inf (fromJust $ M.lookup rr $ pkMap inf )
     fks <- mapM (\ix-> fkUITable inf pgs res (fmap (unIndexItens offsetT ix) <$> plmods ) [] (unIndexItens offsetT ix oldItems )  fkst) [0..8]
     sequence $ zipWith (\e t -> element e # sink0 UI.style (noneShow . isJust <$> facts t)) (getElement <$> tail fks) (triding <$> fks)
     dv <- UI.div # set children (getElement <$> fks)
     let bres = indexItens tb offsetT fks oldItems
     leng <- UI.span # sink text (("Size: " ++) .show .maybe 0 (length . (\(FKT _ _ _ (ArrayTB1 l) ) -> l)) <$> facts bres)
     fksE <- UI.div # set UI.style [("display","inline-flex")] # set children [offset , leng ]
     res <- UI.div # set children [fksE ,dv]
     -- paintEdit (getElement l) (facts bres) (facts oldItems )
     return $  TrivialWidget bres  res

interPoint ks i j = all (\(l,m) -> justError "interPoint wrong fields" $ liftA2 intersectPredTuple  (L.find ((==l).fst) i ) (L.find ((==m).fst) j)) ks



unArray (k,SComposite s) = (unKArray k,) <$> V.toList s
unArray o  = errorWithStackTrace $ "unArray no pattern " <> show o

-- Create non
nonInjectiveSelection
  :: InformationSchema
  -> [Plugins]
  -> [(TB Identity Key Key,TrivialWidget (Maybe (TB Identity Key (Key,Showable))))]
  -> TB Identity Key Key
  -> Tidings [TB1 (Key,Showable)]
  -> Tidings (Maybe (TB Identity Key (Key,Showable)))
  -> UI (TrivialWidget (Maybe (TB Identity Key (Key,Showable ))))
nonInjectiveSelection inf pgs wl  attr@(FKT fkattr refl ksjoin tbfk ) lks selks = do
      let
          fkattr' = unTB <$> fkattr
          oldASet :: Set Key
          oldASet = S.fromList (unAttr <$> fkattr')
          iold :: Tidings ([Maybe [(Key,Showable)]])
          iold  =    (Tra.sequenceA $ fmap (fmap ( kattr . _tb ) ) . triding .snd <$> L.filter (\i-> not . S.null $ S.intersection (S.fromList $ kattr $ _tb $ fst $ i) oldASet) wl)
          sel = fmap (\i->  (Just . unAttr .unTB<$> _tbref i) ) . fmap (fmap snd) <$> selks
      (vv ,ct, els) <- inner tbfk sel  fkattr' iold
      o <- UI.div # set children (els)
      let bres = liftA2 (liftA2 (\i j-> FKT (fmap (\i -> _tb $ Attr (fst i) i ) i)  refl ksjoin j)) vv ct
      return $ TrivialWidget bres o
  where inner tbfk sel fkattr' iold = mdo
            let
                unRKOptional (Key a b d (KOptional c)  ) = Key a b d c
                unRKOptional (Key a b d c  ) = Key a b d c
                vv =  join . (fmap (traverse (traverse unRSOptional2. first unRKOptional ))) . join . fmap (lorder $ unAttr <$> fkattr' ) . fmap concat . allMaybes  <$> iold
                tb = (\i j -> join $ fmap (\k-> L.find ((\(TB1 (KV (PK  l _ ) _ ))-> interPoint ksjoin k  (unAttr . unTB <$> l)) ) i) j ) <$> lks <*> vv
            li <- wrapListBox res2 tb (pure id) showFK
            (ce,evs) <- crudUITable inf pgs (facts res2) [] tbfk  tb
            let eres = fmap (addToList   <$> ) evs
            res2  <-  accumTds lks eres
            chw <- checkedWidget (pure False)
            element ce
              # sink0 UI.style (noneShow <$> (facts $ triding chw))
              # set style [("paddig-left","10px")]
            return (vv,tb, [getElement li,getElement chw,ce])

pdfFrame (elem,sr , call,st) pdf = mkElement (elem ) UI.# sink0 (strAttr sr) (call <$> pdf)  UI.# UI.set style (st)

strAttr :: String -> WriteAttr Element String
strAttr name = mkWriteAttr (set' (attr name))

allNonEmpty [] = Nothing
allNonEmpty l = Just  l

sorting :: Bool -> [Key] -> [TB1 (Key,Showable)]-> [TB1 (Key,Showable)]
sorting b ss  =  L.sortBy (ifApply b flip (comparing (\i ->  fmap (\s -> fmap snd $ F.find ((== s).fst) i  ) ss) ))
  where ifApply True i =  i
        ifApply False _ = id

pruneArray ix tds = if ix > 1 then pruneTidings (isJust <$> tds (ix -1)) (tds ix) else tds ix
