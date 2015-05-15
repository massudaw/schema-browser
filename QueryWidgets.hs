{-# LANGUAGE OverloadedStrings,ScopedTypeVariables,FlexibleContexts,ExistentialQuantification,TupleSections,LambdaCase,RankNTypes,RecordWildCards,DeriveFunctor,NoMonomorphismRestriction,RecursiveDo #-}
module QueryWidgets where

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
import Control.Lens (Lens,(^.),(^?),(&),(.~))
import qualified Control.Lens as Le

import qualified Data.Map as M
import qualified Data.Set as S
import Data.Set (Set)
import Data.Map (Map)
import Data.Traversable(Traversable,traverse)
import qualified Data.Traversable as Tra

import qualified Data.ByteString.Base64 as B64
import Data.Monoid
import Safe
import Data.Foldable (foldl')
import Data.Interval (Interval(..),interval)
import qualified Data.ExtendedReal as ER
import qualified Data.Interval as Interval
import qualified Data.List as L
import Text.Read
import Data.Text.Lazy (Text)
import Warshal
import Types
import Query
import Postgresql
import Data.Maybe
import Data.Time
import qualified Data.Vector as V
import Database.PostgreSQL.Simple.Time
import Data.Functor.Apply
import Widgets
import Schema
import Step
import qualified Data.Foldable as F
import Data.Char
import Data.Tuple
import Database.PostgreSQL.Simple
import Control.Exception
import Debug.Trace
import qualified Data.Text.Lazy as T
import qualified Data.ByteString.Char8 as BSC
import Data.String

containKV f = (\i ->   S.member ( S.fromList $ fmap keyValue $  kattr (Compose . Identity $ fst i)) (S.fromList $ fmap (S.fromList .head) $ fmap snd $ f))

-- [Note] Smooth Plugins
-- Just update when input change
-- Don't overwrite when wont change output
-- Hide when output is already filled
-- Let overwrite output with user command

generateFresh = do
  (e,h) <- liftIO $ newEvent
  b <- stepper Nothing e
  return $ (h,tidings b e)

addAttr (TB1 (KV pk a)) e =  TB1 (KV pk (a <> e))

mergeTB1 (TB1 k) (TB1 k2) = TB1 (k <> k2)

lookFresh inf n tname i = justError "no freshKey" $ M.lookup (n,tname,i) (pluginsMap inf)

createFresh n tname pmap i ty  =  do
  k <- newKey i ty
  return $ M.insert (n,tname,i) k pmap


instance Monoid (KV a) where
  mempty = KV (PK [] []) []
  mappend (KV (PK i j ) l) (KV ( PK m n ) o)  =  (KV (PK (i <> m) ( j <> n)) (l <> o))

pluginUI oinf initItems (StatefullPlugin n tname tf fresh (WrappedCall init ac ) ) = do
  window <- askWindow
  let tdInput = (\i -> maybe False (const True) $ allMaybes $ fmap (\t -> (if fst t then join . fmap unRSOptional' else id ) $ fmap snd $ join $ fmap (indexTable  $ snd t) i) (fst $ head tf ) ) <$>   initItems
  headerP <- UI.button # set text (T.unpack n) # sink UI.enabled (facts tdInput)
  m <- liftIO $  foldl (\i (kn,kty) -> (\m -> createFresh  n tname m kn kty) =<< i ) (return $ pluginsMap oinf) (concat fresh)
  let inf = oinf {pluginsMap = m}
      freshKeys :: [[Key]]
      freshKeys = fmap (lookFresh  inf n tname . fst ) <$> fresh
  freshUI <- Tra.sequence $   zipWith  (\(input,output) freshs -> do
      (h,t :: Tidings (Maybe (TB1 (Key,Showable))) ) <- liftIO $ generateFresh
      elems <- mapM (\fresh -> do
        let hasF l = any (\i -> (head $ head  (snd i)) == keyValue fresh) l
        case  (hasF input , hasF output)  of
             (True,False)-> Right <$> attrUITable (const Nothing <$> initItems) [] (Attr fresh)
             (False,True)->  Left <$> attrUITable (fmap (\v -> Attr . justError ("no key " <> show fresh <> " in " <>  show v ) . L.find ((== fresh) .fst) . F.toList $ v ) <$> t) [] (Attr fresh)
             (True,True)-> error $ "circular reference " <> show fresh
             (False,False)-> error $ "unreferenced variable "<> show fresh
           ) freshs
      let inp = fmap (TB1 . KV (PK [] [])) <$> foldr (liftA2 (liftA2 (:) )) (pure (Just [])) (fmap (fmap ( fmap (Compose .Identity )) . triding) (rights elems) )
      ei <- if not $ any (\i -> any (\fresh -> (head $ head  (snd i)) == keyValue fresh) freshs )  input
         then
          TrivialWidget (pure (Just  $ TB1 mempty) ) <$> UI.div
         else do
          inpPost <- UI.button # set UI.text "Submit"
          trinp <- cutEvent (UI.click inpPost) inp
          ei <- UI.div # set UI.children ((fmap getElement $ rights elems ) <> [inpPost])
          return $ TrivialWidget trinp ei
      return (h,(fmap snd output,t),(lefts elems) ,ei )
           ) tf freshKeys

  el <- UI.div # set UI.children (headerP : (concat $ fmap (\(_,_,o,i)-> concat $ [fmap getElement o ,[getElement i]]) freshUI ))
  liftIO $ forkIO  $ fmap (const ()) $ init $ foldl (\ unoldM (f,((h,htidings,loui,inp),action))  -> unoldM >>= (\unoldItems -> do
      let oldItems = foldl1 (liftA2 (liftA2 mergeTB1)) (triding inp: unoldItems)
      liftEvent window (rumors oldItems) (\i -> action inf  i  (liftIO . h) )
      return  [oldItems]  ))  (return [initItems] ) ( zip tf $ zip freshUI ac)
  element el # sink UI.style (noneShow <$> facts tdInput)
  return (el ,  (  ((\(_,o,_,_) -> o)$ last freshUI ) ))


pluginUI inf unoldItems (BoundedPlugin2 n t f action) = do
  let oldItems = unoldItems
      outputItems = oldItems
  overwrite <- checkedWidget (pure False)
  let tdInput = (\i -> maybe False (const True) $ allMaybes $ fmap (\t -> (if fst t then join . fmap unRSOptional' else id ) $ fmap snd $ join $ fmap (indexTable  $ snd t) i) (fst f) ) <$>  oldItems
      tdOutput1 = (\i -> maybe True (const False) $ allMaybes $ fmap (\f -> (if not(fst f ) then join . fmap unRSOptional' else id ) $ fmap snd $ join $ fmap (indexTable  $ snd f) i) (snd f) ) <$>  outputItems
      tdOutput= liftA2 (\i j -> if i then True else j) (triding overwrite)  tdOutput1
  let ovev =((\ j i  -> if i then j else Nothing) <$>   oldItems <*> tdOutput1)
  cv <- currentValue (facts oldItems)
  headerP <- UI.button # set text (T.unpack n) # sink UI.enabled (facts tdInput)
  let ecv = (facts oldItems<@ UI.click headerP)
  bcv <- stepper cv (facts oldItems <@ UI.click headerP)
  pgOut <- mapTEvent (action inf) (tidings bcv ecv)
  return (headerP, (fmap snd $ snd f ,   pgOut ))


pluginUI inf unoldItems (BoundedPlugin n t f action) = do
  let oldItems = unoldItems -- fmap TB1 . Tra.sequenceA <$> Tra.sequenceA (fmap snd $    unoldItems)
  headerP <- UI.div # set text (T.unpack n)
  overwrite <- checkedWidget (pure False)
  let tdInput = (\i -> maybe False (const True) $ allMaybes $ fmap (\t -> (if fst t then join . fmap unRSOptional' else id ) $ fmap snd $ join $ fmap (indexTable  $ snd t) i) (fst f) ) <$>  oldItems
      tdOutput1 = (\i -> maybe True (const False) $ allMaybes $ fmap (\f -> (if not(fst f ) then join . fmap unRSOptional' else id ) $ fmap snd $ join $ fmap (indexTable  $ snd f) i) (snd f) ) <$>  oldItems
      tdOutput= liftA2 (\i j -> if i then True else j) (triding overwrite)  tdOutput1
  let ovev = ((\ j i  -> if i then j else Nothing) <$>   oldItems <*> tdOutput1)
  ev <- action inf ovev
  bod <- UI.div  # set children [ev] # sink UI.style (noneShowSpan <$> facts tdOutput)
  element overwrite # sink UI.style (noneShowSpan . not <$> facts tdOutput1)
  body <- UI.div # set children [headerP,getElement overwrite,bod] # sink UI.style (noneShowSpan <$> facts tdInput)
  return (body,  ([] , pure Nothing ))

intersectPredTuple  = (\i j -> intersectPred (textToPrim <$> keyType (fst i)) (textToPrim <$> keyType (fst j)) (snd i) (snd j))


lorder lo lref = allMaybes $ fmap (\k -> L.find (\i-> fst i == k ) lref) lo

attrUITable
  :: Tidings (Maybe (TB Identity (Key,Showable)))
     -> [Event (Maybe (TB Identity (Key,Showable)))]
     -> TB Identity Key
     -> UI (TrivialWidget (Maybe (TB Identity (Key, Showable))))
attrUITable  tAttr' evs (Attr i) = do
      l<- UI.span # set text (show i)
      tdi' <- foldr (\i j ->  updateEvent  (fmap (Tra.traverse (Tra.traverse diffOptional ))) i =<< j) (return tAttr') evs
      let tdi = fmap (\(Attr i)-> snd i) <$>tdi'
          justCase i j@(Just _) = j
          justCase i Nothing = i
      attrUI <- buildUI (textToPrim <$> keyType i) tdi
      let
          ei (Just a) = Just a
          ei Nothing = defaultType (keyType i)
      paintEdit l (facts $ triding attrUI ) (facts tAttr)
      sp <- UI.li # set children [l,getElement attrUI ]
      let insertT = fmap (Attr .(i,)) <$> (triding attrUI)
          editT = liftA2 (\n m -> join $ liftA2 (\i j -> if i == j then Nothing else Just j) n m) tAttr' insertT
      return $ TrivialWidget insertT sp
  where tAttr = fmap (\(Attr i)-> snd i) <$> tAttr'

unSComposite (SComposite i) = i
unSComposite i = error ("unSComposite " <> show i)

buildUI i  tdi = case i of
         (KOptional ti) -> fmap (Just. SOptional) <$> buildUI ti (join . fmap unSOptional  <$> tdi)
         (KSerial ti) -> fmap (Just . SSerial) <$> buildUI ti ( join . fmap unSSerial <$> tdi)
         (KArray ti) -> do
            let arraySize = 10
            widgets <- mapM (\i-> buildUI ti (join . fmap (\a -> unSComposite a V.!? i ) <$> tdi )) [0..arraySize]
            let tdcomp =  fmap (SComposite . V.fromList) .  allMaybes .  L.takeWhile (maybe False (const True)) <$> (Tra.sequenceA $ triding <$> widgets)
            sequence $ zipWith (\e t -> element e # sink UI.style (noneShow . maybe False (const True) <$> facts t)) (tail $ getElement <$> widgets) (triding <$> widgets)
            composed <- UI.span # set children (fmap getElement widgets)
            return  $ TrivialWidget tdcomp composed
         (KInterval ti) -> do
            inf <- fmap (fmap ER.Finite) <$> buildUI ti (fmap (\(SInterval i) -> inf' i) <$> tdi)
            sup <- fmap (fmap ER.Finite) <$> buildUI ti (fmap (\(SInterval i) -> sup' i) <$> tdi)
            lbd <- fmap Just <$> checkedWidget (maybe False id . fmap (\(SInterval i) -> snd . Interval.lowerBound' $i) <$> tdi)
            ubd <- fmap Just <$> checkedWidget (maybe False id .fmap (\(SInterval i) -> snd . Interval.upperBound' $i) <$> tdi)
            composed <- UI.span # set UI.children [getElement lbd ,getElement  inf,getElement sup,getElement ubd]
            let td = (\m n -> fmap SInterval $  join . fmap (\i-> if Interval.null i then Nothing else Just i) $ liftF2 interval m n) <$> (liftA2 (,) <$> triding inf  <*> triding lbd) <*> (liftA2 (,) <$> triding sup <*> triding ubd)
            return $ TrivialWidget td composed
         -- (Primitive Position) -> do
                      -- returnA -< (\(SPosition (Position (lon,lat,_)))-> "http://maps.google.com/?output=embed&q=" <> (HTTP.urlEncode $ show lat  <> "," <>  show lon )) <$>  p
            -- mkElement "iframe" # sink UI.src (maybe "" id . dynP req  <$> facts inputs) # set style [("width","99%"),("height","300px")]
         (Primitive PTimestamp) -> do
            itime <- liftIO $  getCurrentTime
            timeButton <- UI.button # set UI.text "now"
            evCurr <-  mapEvent (fmap Just) (pure getCurrentTime <@ UI.click timeButton)
            let  newEv = (unionWith const (rumors tdi) $ fmap (STimestamp . Finite .  utcToLocalTime utc) <$> evCurr)
            tdi2 <- addEvent newEv  tdi
            oneInput tdi2 [timeButton]
         (Primitive PDate) -> do
            itime <- liftIO $  getCurrentTime
            timeButton <- UI.button # set UI.text "now"
            evCurr <-  mapEvent (fmap Just) (pure getCurrentTime <@ UI.click timeButton)
            let  newEv = (unionWith const (rumors tdi) $ fmap (SDate . Finite . localDay . utcToLocalTime utc) <$> evCurr)
            tdi2 <- addEvent newEv  tdi
            oneInput tdi2 [timeButton]
         (Primitive (PMime mime)) -> do
           let binarySrc = (\(SBinary i) -> "data:" <> T.unpack mime <> ";base64," <>  (BSC.unpack $ B64.encode i) <> "")
           clearB <- UI.button # set UI.text "clear"
           tdi2 <- addEvent (const Nothing <$> UI.click clearB) tdi
           let fty = case mime of
                "application/pdf" -> ("iframe",  [("width","100%"),("height","300px")])
                "image/jpg" -> ("img",[])
           f <- pdfFrame fty (maybe "" binarySrc <$> facts tdi2)
           fd <- UI.div # set children [clearB,f]
           return (TrivialWidget tdi2 fd)

         z -> do
            oneInput tdi []
  where
    justCase i j@(Just _) = j
    justCase i Nothing = i
    oneInput tdi elem = do
            inputUI <- UI.input # sink UI.value (facts (forceDefaultType  <$> tdi))
            let pke = foldl1 (unionWith justCase ) [readType i <$> UI.valueChange inputUI,rumors  tdi]
            pk <- stepper (defaultType i)  pke
            let pkt = tidings pk pke
            paintBorder inputUI (facts pkt)
            sp <- UI.span # set children (inputUI : elem)
            return $ TrivialWidget pkt sp
    takeWhileJust snoc empty l = step l
      where
          step (x:xs) =  liftA2 test x (step xs)
          step [] =  pure empty
          test (Just x) os =  snoc  os x
          test Nothing os = os


forceDefaultType  (Just i ) = renderShowable i
forceDefaultType  (Nothing) = ""

diffOptional (SOptional i) = fmap (SOptional .Just)  . join $   unRSOptional' <$> i
diffOptional (SSerial i )  = fmap (SSerial .Just) . join $  unRSOptional' <$>i
diffOptional i   = Just i

tbCase :: InformationSchema -> [Plugins]  ->(forall a . Lens (KV a) (KV a) [a] [a] ) ->  Int -> TB Identity Key -> Set Key -> [(TB Identity Key,TrivialWidget (Maybe (TB Identity (Key,Showable))))] -> [([[[Text]]],Tidings (Maybe (TB1 (Key,Showable))))]-> Tidings (Maybe (TB1 (Key,Showable))) -> UI (TrivialWidget (Maybe (TB Identity (Key,Showable))))
tbCase inf pgs td ix i@(AKT ifk refl  _ [tb1]) created wl plugItens oldItems = do
        let
            thisPlugs = filter (any ((== (fmap (keyValue.unAttr.runIdentity.getCompose) ifk)) . head ) . fst) $  plugItens
            tbi = fmap (\v -> Compose . Identity . unTB . justError "AKT" . (^? unTB1. td . Le.ix ix ) $ v) <$> oldItems
            pfks =  (first (filter (not . L.null ) . fmap (L.drop 1) . L.filter ((== (fmap (keyValue.unAttr.runIdentity.getCompose) ifk)) . head ))  . second (fmap (join . fmap (fmap  (_akttable . runIdentity . getCompose ) .  findTB1 ((== ifk ) . fmap (fmap fst )  . tbAttr . runIdentity . getCompose  )) )) <$> thisPlugs)
        akUITable inf pgs  pfks (fmap (runIdentity . getCompose) <$> tbi) i
tbCase inf pgs td ix i@(FKT ifk _ _ tb1 ) created wl plugItens oldItems  = do
        let
            rr =  tablePKSet tb1
            table = justError "no table found" $ M.lookup rr $ pkMap inf
            rp = rootPaths'  (tableMap inf) table
            tbi = fmap (\v -> Compose . Identity . unTB . justError "FKT" . (^? unTB1. td . Le.ix ix ) $ v) <$> oldItems
            thisPlugs = filter (any ((== (fmap (keyValue.unAttr.runIdentity.getCompose) ifk)) . head ) . fst) $  plugItens
            pfks =  (first ( filter (not . L.null ) . fmap (L.drop 1) . L.filter ((== (fmap (keyValue.unAttr.runIdentity.getCompose) ifk)) . head ))  . second ( fmap ( join .  fmap (fmap  (_fkttable . runIdentity . getCompose ) . findTB1 ((== ifk ) . fmap (fmap fst )  . tbAttr . runIdentity . getCompose  )))  ) <$> thisPlugs)
        res <- liftIO$ queryWith_  (fromAttr (fst rp)) (conn inf)(fromString $ T.unpack $ snd rp)
        fkUITable inf pgs created res pfks (filter (isReflexive .fst) wl) (fmap (runIdentity . getCompose ) <$>  tbi) i
tbCase inf pgs td ix i@(IT ifk tb1 ) created wl plugItens oldItems  = do
        let tbi = fmap (\v -> Compose . Identity . unTB . justError "FKT" . (^? unTB1. td . Le.ix ix ) $ v) <$> oldItems
            thisPlugs = filter (any ((== (fmap (keyValue.unAttr.runIdentity.getCompose) ifk)) . head ) . fst) $  plugItens
            pfks =  (first ( filter (not . L.null ) . fmap (L.drop 1) . L.filter ((== (fmap (keyValue.unAttr.runIdentity.getCompose) ifk)) . head ))  . second ( fmap ( join .  fmap (fmap  (_fkttable . runIdentity . getCompose ) . findTB1 ((== ifk ) . fmap (fmap fst )  . tbAttr . runIdentity . getCompose  )))  ) <$> thisPlugs)
        iUITable inf pgs pfks (fmap (runIdentity . getCompose ) <$>  tbi) i
tbCase inf pgs td ix i@(IAT ifk _ ) created wl plugItens oldItems  = do
        let tbi = fmap (\v -> Compose . Identity . unTB . justError "IAT" . (^? unTB1. td . Le.ix ix ) $ v) <$> oldItems
            thisPlugs = filter (any ((== (fmap (keyValue.unAttr.runIdentity.getCompose) ifk)) . head ) . fst) $  plugItens
            pfks =  (first ( filter (not . L.null ) .  fmap (L.drop 1) . L.filter ((== (fmap (keyValue.unAttr.runIdentity.getCompose) ifk)) . head ))  . second ( fmap ( join .  fmap (fmap  (_akttable . runIdentity . getCompose ) . findTB1 ((== ifk ) . fmap (fmap fst )  . tbAttr . runIdentity . getCompose  )) )  ) <$> thisPlugs)
        iaUITable inf pgs pfks (fmap (runIdentity . getCompose ) <$>  tbi) i

tbCase inf pgs td ix a@(Attr i) created wl plugItens oldItems = do
        let thisPlugs = filter (any ((== [keyValue i]).head) . fst) $  (fmap (fmap (fmap F.toList) ) <$> plugItens)
            tbi = fmap (\v -> unTB . justError "Attr".(^? unTB1.td . Le.ix ix) $ v) <$> oldItems
        let evs  = {-plugTdi <- foldr (\i j ->  updateEvent  (fmap (Tra.traverse (Tra.traverse diffOptional ))) i =<< j) (return tbi )-} ( rumors . fmap ( join . fmap ( fmap Attr . L.find ((== i).fst )) )   <$>  (fmap snd thisPlugs))
        attrUITable tbi evs a

uiTable
  ::
     InformationSchema
     -> [Plugins]
     -- Plugin Modifications
     -> [([[[Text]]],Tidings (Maybe (TB1 (Key,Showable))))]
     -> TB1 Key
     -> Tidings (Maybe (TB1 (Key,Showable)))
     -> UI (Element,Tidings (Maybe (TB1 (Key,Showable))))
uiTable inf pgs pmods ftb@(TB1 (KV (PK k d) a)) oldItems = do
  let
      Just table = M.lookup (S.fromList $ findPK ftb) (pkMap inf)

  res <- mapM (pluginUI inf oldItems) (filter ((== tableName table ) . _bounds ) pgs)
  let plugmods = (snd <$> res ) <> pmods
  let mapMI f e = foldl (\jm (l,m)  -> do
                (w,ok) <- jm
                wn <- f l (unTB m) ok w plugmods oldItems
                return (w <> [(unTB m,wn)],S.fromList (kattr m ) <> ok)
              ) (return ([],e)) . zip [0..]
  fks <- do
      (i,pok) <- mapMI (tbCase inf pgs (kvKey.pkKey)) S.empty k
      (j,dok) <- mapMI (tbCase inf pgs (kvKey.pkDescription)) pok d
      (k,_) <-  mapMI (tbCase inf pgs (kvAttr)) dok a
      return $  KV (PK i j ) k
  let
      tableb :: Tidings (Maybe (TB1 (Key,Showable)))
      tableb  = fmap (TB1 . fmap _tb) . Tra.sequenceA <$> Tra.sequenceA (triding .snd <$> fks)
      tableb2 :: KV (TB Identity Key , Tidings (Maybe (TBIdent   (Key,Showable))))
      tableb2  =  ( fmap (fmap (fmap _tb) . triding ) <$> fks)
  listBody <- UI.ul
    # set children (F.toList (getElement .snd <$> fks))
    # set style [("border","1px"),("border-color","gray"),("border-style","solid"),("margin","1px")]
  plugins <-  if not (L.null (fst <$> res))
    then do
      pluginsHeader <- UI.div # set UI.text "Plugins"
      pure <$> UI.div # set children (pluginsHeader : (fst <$> res))
    else do
      return []
  body <- UI.div
    # set children ( listBody : plugins )
    # set style [("border","2px"),("border-color","gray"),("border-style","solid")]
  return (body, tableb )


crudUITable
  ::
     InformationSchema
     -> [Plugins]
     -- Plugin Modifications
     -> [([[[Text]]],Tidings (Maybe (TB1 (Key,Showable))))]
     -> TB1 Key
     -> Tidings (Maybe (TB1 (Key,Showable)))
     -> UI (Element,Tidings (Maybe (TB1 (Key,Showable))),[Event (Modification Key Showable)])
crudUITable inf pgs pmods ftb@(TB1 (KV (PK k d) a)) oldItems = do
  let
      Just table = M.lookup (S.fromList $ findPK ftb) (pkMap inf)

  res <- mapM (pluginUI inf oldItems) (filter ((== tableName table ) . _bounds ) pgs)
  let plugmods = (snd <$> res ) <> pmods
  let mapMI f e = foldl (\jm (l,m)  -> do
                (w,ok) <- jm
                wn <- f l (unTB m) ok w plugmods oldItems
                return (w <> [(unTB m,wn)],S.fromList (kattr m ) <> ok)
              ) (return ([],e)) . zip [0..]
  fks <- do
      (i,pok) <- mapMI (tbCase inf pgs (kvKey.pkKey)) S.empty k
      (j,dok) <- mapMI (tbCase inf pgs (kvKey.pkDescription)) pok d
      (k,_) <-  mapMI (tbCase inf pgs (kvAttr)) dok a
      return $  KV (PK i j ) k
  let
      tableb :: Tidings (Maybe (TB1 (Key,Showable)))
      tableb  = fmap (TB1 . fmap _tb) . Tra.sequenceA <$> Tra.sequenceA (triding .snd <$> fks)
      tableb2 :: KV (TB Identity Key , Tidings (Maybe (TBIdent   (Key,Showable))))
      tableb2  =  ( fmap (fmap (fmap _tb) . triding ) <$> fks)
  (panelItems,evsa)<- processPanelTable (conn inf) (facts tableb) table oldItems
  listBody <- UI.ul
    # set children (F.toList (getElement .snd <$> fks))
    # set style [("border","1px"),("border-color","gray"),("border-style","solid"),("margin","1px")]
  plugins <-  if not (L.null (fst <$> res))
    then do
      pluginsHeader <- UI.div # set UI.text "Plugins"
      pure <$> UI.div # set children (pluginsHeader : (fst <$> res))
    else do
      return []
  body <- UI.div
    # set children ( listBody : plugins <>  panelItems )
    # set style [("border","2px"),("border-color","gray"),("border-style","solid")]
  return (body, tableb ,evsa)

tbAttr (IT  i _ ) = i
tbAttr (IAT  i _ ) = i
tbAttr (FKT i _ _ _ ) = i
tbAttr a@(Attr i ) = [Compose . Identity $ a]
tbAttr (AKT i _ _ _ ) = i

filterTB1 f = TB1 . filterKV f . _unTB1
findTB1 f =  findKV f . _unTB1
mapTB1 f = TB1 . mapKV f . _unTB1


processPanelTable
   :: Connection
   -> Behavior (Maybe (TB1 (Key, Showable)))
   -> Table
   -> Tidings (Maybe (TB1 (Key, Showable)))
   -> UI ([Element],[Event (Modification Key Showable)])
processPanelTable conn attrsB table oldItemsi = do
  let fkattrsB = fmap (concat . F.toList . fmap (attrNonRec . unTB) . _unTB1. tableNonRef ) <$> attrsB
      oldItems = fmap (concat . F.toList . fmap (attrNonRec .unTB) . _unTB1. tableNonRef ) <$> oldItemsi
  insertB <- UI.button # set text "INSERT"
  -- Insert when isValid
        # sink UI.enabled ( isJust <$> fkattrsB)
  editB <- UI.button # set text "EDIT"
  -- Edit when any persistent field has changed
        # sink UI.enabled (liftA2 (\i j -> maybe False (any fst . F.toList  ) $ liftA2 (liftF2 (\l m -> if l  /= m then traceShow (l,m) (True,(l,m)) else (False,(l,m))) )  i j) (fmap tableNonRef <$> attrsB) (fmap tableNonRef <$> facts oldItemsi))
  deleteB <- UI.button # set text "DELETE"
  -- Delete when isValid
        # sink UI.enabled (isJust <$> facts oldItems)
  let
      deleteAction ki =  do
        res <- liftIO $ catch (Right <$> delete conn ki table) (\e -> return $ Left (show $ traceShowId  (e :: SomeException) ))
        return $ const (DeleteTB ki ) <$> res
      editAction attr old = do
        let
            isM :: Maybe (TB1 (Key,Showable))
            isM =  join $ fmap TB1 . allMaybes . filterKV (maybe False (const True)) <$> (liftA2 (liftF2 (\i j -> if i == j then Nothing else  traceShow (i,j) $ Just i))) (_unTB1 . filterTB1 (isReflexive .runIdentity . getCompose) <$> attr) (_unTB1 . filterTB1 (isReflexive .runIdentity . getCompose)<$> old)
            isM' :: Maybe [(Key,Showable)]
            isM' = (catMaybes . F.toList ) <$> (liftA2 (liftF2  (\i j -> if i == j then Nothing else Just i))) attr old
            kM' = F.toList <$> old
        res <- liftIO $ catch (maybe (return (Left "no attribute changed check edit restriction")) (\l-> Right <$> updateAttr conn l (fromJust old) table) isM ) (\e -> return $ Left (show $ traceShowId (e :: SomeException) ))
        let updated = (\(Just i)-> i) isM'
        return $ fmap (const (EditTB (fromJust isM) (fromJust old) )) res

      insertAction ip = do
          res <- catch (Right <$> insertAttr (fromAttr )  conn ip table) (\e -> return $ Left (show $ traceShowId (e :: SomeException) ))
          return $ InsertTB  <$> res

  let    spMap = fmap split . mapEvent id
  (evid,evir) <- spMap $ filterJust $ (fmap insertAction  <$> attrsB ) <@ (UI.click insertB)
  (evdd,evdr) <- spMap $ filterJust $ (fmap deleteAction <$> facts oldItemsi) <@ UI.click deleteB
  (eved,ever) <- spMap $ (editAction  <$> attrsB <*> (facts oldItemsi) ) <@ UI.click editB
  bd <- stepper [] (unions [evid,evdd,eved])
  errorOut <- UI.div # sink UI.text (L.intercalate "," <$> bd)
  return ([insertB,editB,deleteB,errorOut],[evir,ever,evdr])


unLeft :: (F.Foldable f,Functor f) => Maybe (f (Key,Showable)) -> Maybe (f (Key,Showable))
unLeft i = join $  fmap ( allMaybes . fmap (traverse unSOptional.first unKOptional ) ) i

unLeftBind :: (F.Foldable f,Functor f) => f (Key,Showable) -> Maybe (f (Key,Showable))
unLeftBind i =  ( allMaybes . fmap (traverse unSOptional.first unKOptional ) ) i

makeOptional :: (F.Foldable f, Functor f) => f Key -> Maybe (f (Key,Showable)) -> Maybe (f (Key,Showable))
makeOptional def (Just i ) = Just $ fmap keyOptional i
makeOptional def Nothing = allMaybes $ fmap (\i -> (i,)  <$> showableDef (keyType i)) def

keyOptional ((Key a b c d e) ,v) = (Key a b c d (KOptional e)  ,SOptional $ Just v)


unkeyOptional ((Key a b c d (KOptional e)) ,(SOptional v) ) = fmap (Key a b c d e  , ) v

unKOptional ((Key a b c d (KOptional e))) = (Key a b c d e )
unKOptional i = error ("unKOptional " <> show i)

unKOptional' ((Key a b c d (KOptional e))) = unKOptional' (Key a b c d e )
unKOptional' (Key a b c d e) = (Key a b c d e )

unKArray (Key a b c d (KArray e)) = Key a b c d e
unKArray (Key a b c d (KOptional (KArray e) )) = Key a b c d e
kOptional (Key a b c d e) = Key a b c d (KOptional e)


modifyTB :: (Traversable f ,Ord a) => f a -> Modification a b ->  Maybe ( f (a,b)) -> Maybe (f (a,b))
modifyTB i  (Insert m) =  const (editedMod  i m)
modifyTB _  (Delete m ) =  const Nothing
modifyTB _  (Edit m n ) =  fmap (fmap (\(k,v) -> (k,)  $ (\(Just i)-> i) $ M.lookup k (M.fromList $ (\(Just i)-> i) m) ))


addToList i  (Insert m) =  (\i-> mappend (fmap ((\(k,v)-> (k, v)))  <$> maybeToList i)) (editedMod i m)
addToList _  (InsertTB m) =  (m:)
addToList i  (Delete m ) =  (\i-> concat . L.delete (fmap ((\(k,v)-> (k, v)))  <$> maybeToList i)  . fmap pure ) (editedMod  i  m )
addToList i  (DeleteTB m ) =  L.delete m
addToList i  (Edit m n ) = (map (\e-> if  (e ==  n) then  fmap (\(k,v) -> (k,)  $ (\(Just i)-> i) $ M.lookup k (M.fromList $ (\(Just i)-> i) m) ) e  else e ))
addToList i  (EditTB (TB1 m) n ) = (map (\e-> if  (e ==  n) then  mapTB1 (\i -> maybe i id $ L.find (\k -> (tbAttr $ fmap fst $ runIdentity $ getCompose k) == (tbAttr $ fmap fst $ runIdentity $ getCompose i) ) ls ) e  else e ))
    where ls = F.toList m

-- lookup pk from attribute list
editedMod :: (Traversable f ,Ord a) => f a ->  Maybe [(a,b)] -> Maybe (f (a,b))
editedMod  i  m=  join $ fmap (\mn-> look mn i ) m
  where look mn k = allMaybes $ fmap (\ki -> fmap (ki,) $  M.lookup ki (M.fromList mn) ) k


showFK = (pure ((\v j ->j  # set text (L.intercalate "," $ fmap renderShowable $ F.toList $  _kvKey $ allKVRec $  snd <$> v))))

tablePKSet  tb1 = S.fromList $ fmap (unAttr . runIdentity . getCompose ) $ _pkKey $ _kvKey $ _unTB1 $ tableNonRef tb1

iUITable
  ::
  InformationSchema
  -> [Plugins]
  -- Plugin Modifications
  -> [([[[Text]]],Tidings (Maybe (TB1 (Key,Showable))))]
  -- Selected Item
  -> Tidings (Maybe (TB Identity (Key,Showable)))
  -- Static Information about relation
  -> TB Identity Key
  -> UI (TrivialWidget(Maybe (TB Identity (Key, Showable))))
iUITable inf pgs pmods oldItems  tb@(IT ifk tb1)
    = do
      l <- UI.span # set text (show $ unAttr .unTB <$>   ifk)
      (celem,tcrud) <- uiTable inf pgs pmods tb1 (fmap _fkttable <$> oldItems)
      element celem
          # set style [("padding-left","10px")]
      fk <- UI.li # set  children [l, celem]
      let isLeft = any (any (isKOptional . keyType).  kattr) ifk
      let bres =  fmap (fmap (IT (fmap (,SOptional Nothing ) <$> ifk)  ) )  ((if isLeft then makeOptional tb1 else id)  <$> tcrud )
      paintEdit  (getElement l) (facts bres) (facts oldItems)
      return $ TrivialWidget bres fk

iaUITable
  ::
  InformationSchema
  -> [Plugins]
  -- Plugin Modifications
  -> [([[[Text]]],Tidings (Maybe [TB1 (Key,Showable)]))]
  -- Selected Item
  -> Tidings (Maybe (TB Identity (Key,Showable)))
  -- Static Information about relation
  -> TB Identity Key
  -> UI (TrivialWidget(Maybe (TB Identity (Key, Showable))))
iaUITable inf pgs plmods oldItems  tb@(IAT ifk [tb1])
    = do
      l <- UI.span # set text (show $ unAttr .unTB <$>   ifk)
      items <- mapM (\ix -> (uiTable inf pgs (fmap (fmap ( join .  fmap (\tbl -> atMay  tbl ix))) <$> plmods) tb1 (join . fmap (flip atMay ix . _akttable)  <$> oldItems))) [0..20]
      let tds = snd <$> items
          es = fst <$> items
      sequence $ zipWith (\e t -> element e # sink UI.style (noneShow . maybe False (const True) <$> facts t)) (tail es ) ( tds )
      fk <- UI.li # set  children (l:  ((\(e,_) -> e) <$> items))

      let isLeft = any (any (isKOptional . keyType).  kattr) ifk
      let bres =  fmap ((if isLeft then maybe (Just (IAT (fmap (,SOptional Nothing ) <$> ifk) [] )) Just else id ) .fmap  (IAT (fmap (,SOptional Nothing ) <$> ifk)  ) )  ( allMaybes .  L.takeWhile (maybe False (const True)) <$> (Tra.sequenceA $    (\(_,e) -> e) <$> items))
      paintEdit  (getElement l) (facts bres) (facts oldItems)
      return $ TrivialWidget bres fk


fkUITable
  ::
  InformationSchema
  -> [Plugins]
  -- Created Keys
  -> Set Key
  -- Table Data
  -> [TB1 (Key,Showable)]
  -- Plugin Modifications
  -> [([[[Text]]],Tidings (Maybe (TB1 (Key,Showable))))]
  -- Same Table References
  -> [(TB Identity Key,TrivialWidget (Maybe (TB Identity (Key,Showable))))]
  -- Relation Event
  -> Tidings (Maybe (TB Identity (Key,Showable)))
  -- Static Information about relation
  -> TB Identity Key
  -> UI (TrivialWidget(Maybe (TB Identity (Key, Showable))))
fkUITable inf pgs created res pmods wl  oldItems  tb@(FKT ifk refl rel tb1)
    | not refl = do
        nonInjectiveSelection inf pgs created wl tb (pure res) oldItems
    | otherwise = mdo

      let
          rr = S.fromList $ fmap (unAttr . runIdentity . getCompose ) $ _pkKey $ _kvKey $ _unTB1 $ tableNonRef tb1
          isLeftJoin = any isKOptional $  keyType . unAttr . unTB <$> ifk
          relTable = M.fromList $ fmap swap rel
          tdi :: Tidings (Maybe (TB1  (Key,Showable)))
          tdi =  (if isLeftJoin then join . fmap (Tra.sequence . fmap unkeyOptional . _fkttable ) else fmap _fkttable  ) <$> oldItems
          -- oldSel :: Tidings (Maybe (TB1  (Key,Showable)))
          oldSel =   fmap _tbref <$> oldItems
      l <- UI.span # set text (show $ unAttr .unTB <$>   ifk)

      filterInp <- UI.input
      filterInpBh <- stepper "" (UI.valueChange filterInp )
      let filterInpT = tidings filterInpBh (UI.valueChange filterInp)
          filtering i  = T.isInfixOf (T.pack $ toLower <$> i) . T.toLower . T.intercalate "," . fmap (T.pack . renderShowable) . F.toList . fmap snd
      box <- optionalListBox  (sorting True (S.toList rr) <$> fmap fst res2) tdi  (pure id ) ((\i j -> maybe id (\l  ->   (set UI.style (noneShow $ filtering j l  ) ) . i  l ) )<$> showFK <*> filterInpT)
      let
        reorderPK l = fmap (\i -> justError "reorder wrong" $ L.find ((== i).fst) l )  (unAttr . unTB <$> ifk)
        lookFKsel (ko,v)=  (kn ,transformKey (textToPrim <$> keyType ko ) (textToPrim <$> keyType kn) v)
          where kn = justError "relTable" $ M.lookup ko relTable
        fksel = (if isLeftJoin then Just . maybe (fmap (\k-> (k,justError "non optional type in left join" $ showableDef (keyType k)) ) (unAttr. unTB <$> ifk)) id  else id ) . fmap (reorderPK . fmap lookFKsel)  <$>  (fmap findPK  <$> triding box)
      chw <- checkedWidget (pure False)
      (celem,tcrud,evs) <- crudUITable inf pgs pmods (if isLeftJoin then unKOptional <$> tb1  else tb1 ) (triding box)
      let eres ev = (\e -> second (modifyTB (allRec' (tableMap inf) ((\(Just i)-> i) $ M.lookup rr (pkMap inf))) e) .
                           first (addToList (allRec' (tableMap inf) ((\(Just i)-> i) $ M.lookup rr (pkMap inf))) e) ) <$> ev
      res2  <-  accumTds (liftA2 (,) (pure res) tdi ) (eres <$> evs)
      element celem
          # set UI.style (noneShow False )
          # sink UI.style (noneShow <$> (facts $ triding chw))
          # set style [("padding-left","10px")]
      fk <- UI.li # set  children [l, getElement box,filterInp,getElement chw,celem]
      let bres =  liftA2 (liftA2 (\i -> FKT i refl rel ) ) (fmap (fmap (_tb . Attr)) <$> fksel ) (if isLeftJoin then makeOptional tb1 <$> tcrud else tcrud )
      paintEdit  (getElement l) (facts $ fksel ) (fmap (fmap (unAttr. runIdentity.getCompose)) <$> facts oldSel)
      return $ TrivialWidget bres fk


akUITable inf pgs plmods  oldItems  tb@(AKT ifk@[_] refl rel  [tb1])
  | otherwise = do
     let isLeft = any (any (isKOptional . keyType).  kattr) ifk
         indexItens ix = join . fmap (\(AKT [l] refl _ m) -> (\li mi ->  FKT  [li] refl (fmap (first unKArray) rel) mi ) <$> (join $ traverse (indexArray ix  ) <$> (if isLeft then unLeftBind l else Just l)) <*> (if isLeft then unLeft else id ) (atMay m ix) )  <$>  oldItems
         fkst = FKT (fmap (fmap unKArray ) (if isLeft then fmap unKOptional <$> ifk else ifk)) refl (fmap (first (unKArray)) rel) (if isLeft then fmap unKOptional tb1 else tb1 )
         rr = tablePKSet tb1
         rp = rootPaths'  (tableMap inf) (fromJust $ M.lookup rr $ pkMap inf )
     res <- liftIO$ queryWith_ (fromAttr (fst rp)) (conn  inf) (fromString $ T.unpack $ snd rp)
     fks <- mapM (\ix-> fkUITable inf pgs S.empty res (fmap (fmap ( join . fmap (\tbl -> atMay  tbl ix))) <$> plmods) [] (indexItens ix) fkst ) [0..8]
     l <- UI.span # set text (show $ unAttr .unTB <$>   ifk)
     sequence $ zipWith (\e t -> element e # sink UI.style (noneShow . maybe False (const True) <$> facts t)) (getElement <$> tail fks) (triding <$> fks)
     dv <- UI.div # set children (getElement <$> fks)
     fksE <- UI.li # set children (l : [dv])
     let bres = (if isLeft then Just . maybe (AKT (fmap (\k-> (k ,fromJust $ showableDef (keyType k) ) ) <$> ifk) refl rel [((\k-> (k ,fromJust $ showableDef (keyType k) ))  <$> tb1)]) id else id) . fmap (\l -> AKT ( fmap  (( if isLeft then keyOptional else id) . (,SComposite $ V.fromList $  (fmap fst l))) <$> ifk) refl rel (fmap snd l)). allMaybes .  L.takeWhile (maybe False (const True)) <$> Tra.sequenceA (fmap (fmap (\(FKT i _ _ j ) -> (head $ fmap (snd.unAttr.unTB) $ i, (if isLeft then fmap keyOptional else id ) j)) )  . triding <$> fks)
     paintEdit (getElement l) (facts bres) (facts oldItems)
     return $  TrivialWidget bres  fksE
akUITable  _ _  _ _ _ = error "akUITable not implemented"

interPoint ks i j = all (\(l,m) -> justError "interPoint wrong fields" $ liftA2 intersectPredTuple  (L.find ((==l).fst) i ) (L.find ((==m).fst) j)) ks


indexArray ix s =  atMay (unArray s) ix

unArray (k,SComposite s) = (unKArray k,) <$> V.toList s
unArray o  = error $ "unArray no pattern " <> show o

-- Create non
nonInjectiveSelection
  ::
  InformationSchema
  -> [Plugins ]
  -> Set Key
  -> [(TB Identity Key,TrivialWidget (Maybe (TB Identity (Key,Showable))))]
  -> TB Identity Key
  -> Tidings [TB1 (Key,Showable)]
  -> Tidings (Maybe (TB Identity (Key,Showable)))
  -> UI (TrivialWidget (Maybe (TB Identity (Key,Showable ))))
nonInjectiveSelection inf pgs created wl  attr@(FKT fkattr refl ksjoin tbfk ) lks selks
  | all isPrim (keyType . unAttr.unTB<$> fkattr ) = do
      let
          fkattr' = unTB <$> fkattr
          oldASet :: Set Key
          oldASet = S.fromList (filter (flip S.member created) $ unAttr <$> fkattr' )
          iold :: Tidings ([Maybe [(Key,Showable)]])
          iold  =    (Tra.sequenceA $ fmap (fmap ( kattr . _tb ) ) . triding .snd <$> L.filter (\i-> not . S.null $ S.intersection (S.fromList $ kattr $ _tb $ fst $ i) oldASet) wl)
          sel = fmap (\i->  (Just . unAttr .unTB<$> _tbref i) ) . fmap (fmap snd) <$> selks
      (vv ,ct, els) <- inner tbfk sel  fkattr' iold
      l <- UI.span # set text (show $ unAttr <$> fkattr')
      o <- UI.li # set children (l: els)
      let bres = (liftA2 (liftA2 (\i j-> FKT (fmap (_tb.Attr) i)  refl ksjoin j)  ) vv ct)
      paintEdit (getElement l) (facts ct ) (fmap _fkttable <$> facts selks)
      return $ TrivialWidget    bres o
  | all isKOptional (keyType . unAttr.unTB<$> fkattr ) = do
      let
          fkattr'=  unTB <$> (fmap unKOptional  <$> fkattr)
          oldASet :: Set Key
          oldASet = S.fromList (filter (flip S.member created) $ unAttr <$> fkattr' )
          iold :: Tidings ([Maybe [(Key,Showable)]])
          iold  =   fmap (join . fmap (allMaybes . fmap (  (\(i,j)-> (unKOptional i,)<$> j) . fmap unSOptional))) <$> (Tra.sequenceA $ fmap (fmap ( kattr . _tb ) ) . triding .snd <$> L.filter (\i-> not . S.null $ S.intersection (S.fromList $ kattr $ _tb $ fst $ i) oldASet) wl)
          tbfk' = unKOptional <$> tbfk
          sel = fmap (\i->  (unSOptional . unAttr .unTB<$> _tbref i) ) . fmap (fmap snd) <$> selks
      (vv ,ct, els) <- inner tbfk' sel fkattr' iold
      l <- UI.span # set text (show $ unAttr . unTB <$> fkattr)
      let vvo = (fmap (fmap Attr ). makeOptional (unAttr . unTB <$> fkattr) <$> vv)
      o <- UI.div # set children (l: els)
      let
          fksel = (fmap (fmap (_tb . Attr ) ). makeOptional (fmap (unAttr .unTB) fkattr) <$> vv)
          bres = (liftA2 (liftA2 (\i -> FKT i refl ksjoin ) ) fksel (makeOptional tbfk <$> ct))
      paintEdit (getElement l) (makeOptional tbfk <$> facts ct ) (fmap _fkttable  <$> facts selks)
      return $ TrivialWidget    bres o
  | otherwise = error (show attr)
  where inner tbfk sel fkattr' iold = mdo
            let
                o1 = tablePKSet tbfk
                vv =  join . fmap (lorder (unAttr <$> fkattr') ) . fmap concat . allMaybes  <$> iold
                tb = (\i j -> join $ fmap (\k-> L.find ((\(TB1 (KV (PK  l _ ) _ ))-> interPoint ksjoin k  (unAttr . unTB <$> l)) ) i) j ) <$> lks <*> vv
            li <- wrapListBox res2 tb (pure id) showFK
            (ce,ct,evs) <- crudUITable inf pgs [] tbfk  tb
            let eres = fmap (addToList  (allRec' (tableMap inf) ((\(Just i)-> i) $ M.lookup o1 (pkMap inf))) <$> ) evs
            res2  <-  accumTds lks eres
            chw <- checkedWidget (pure False)
            element ce
              # sink UI.style (noneShow <$> (facts $ triding chw))
              # set style [("paddig-left","10px")]
            return (vv,ct, [getElement li,getElement chw,ce])

pdfFrame fty pdf = mkElement (fst fty ) UI.# sink UI.src pdf  UI.# UI.set style (snd fty)

allNonEmpty [] = Nothing
allNonEmpty l = Just  l

sorting :: Bool -> [Key] -> [TB1 (Key,Showable)]-> [TB1 (Key,Showable)]
sorting b ss  =  L.sortBy (ifApply b flip (comparing (\i ->  fmap (\s -> fmap snd $ F.find ((== s).fst) i  ) ss) ))
  where ifApply True i =  i
        ifApply False _ = id

