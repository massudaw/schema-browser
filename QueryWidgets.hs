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
import Control.Lens (Lens,(^?))
import qualified Control.Lens as Le

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
import GHC.Stack

containKV f = (\i ->   S.member ( S.fromList $ fmap keyValue $  kattr (Compose . Identity $ fst i)) (S.fromList $ fmap (S.fromList .head) $ fmap snd $ f))

-- [Note] Smooth Plugins
-- Just update when input change
-- Don't overwrite when wont change output
-- Hide when output is already filled
-- Let overwrite output with user command

-- modifyTB :: (Traversable f ,Ord a) => f a -> Modification a b ->  Maybe ( f (a,b)) -> Maybe (f (a,b))
modifyTB  (InsertTB m) =  const (Just m)
modifyTB  (DeleteTB m ) =  const Nothing
modifyTB  (EditTB (TB1 m) n ) =  fmap( mapTB1 (\i -> maybe i id $ L.find (\k -> (tbAttr $ fmap fst $ runIdentity $ getCompose k) == (tbAttr $ fmap fst $ runIdentity $ getCompose i) ) ls ) )
    where ls = F.toList m

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
             (True,True)-> errorWithStackTrace $ "circular reference " <> show fresh
             (False,False)-> errorWithStackTrace $ "unreferenced variable "<> show fresh
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
      -- outputItems = oldItems
  overwrite <- checkedWidget (pure False)
  let tdInput = (\i -> maybe False (const True) $ allMaybes $ fmap (\t -> (if fst t then join . fmap unRSOptional' else id ) $ fmap snd $ join $ fmap (indexTable  $ snd t) i) (fst f) ) <$>  oldItems
      -- tdOutput1 = (\i -> maybe True (const False) $ allMaybes $ fmap (\f -> (if not(fst f ) then join . fmap unRSOptional' else id ) $ fmap snd $ join $ fmap (indexTable  $ snd f) i) (snd f) ) <$>  outputItems
      -- tdOutput= liftA2 (\i j -> if i then True else j) (triding overwrite)  tdOutput1
  -- let ovev =((\ j i  -> if i then j else Nothing) <$>   oldItems <*> tdOutput1)
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
      l<- flabel # set text (show i)
      tdi' <- foldr (\i j ->  updateEvent  (fmap (Tra.traverse (Tra.traverse diffOptional ))) i =<< j) (return tAttr') evs
      let tdi = fmap (\(Attr i)-> snd i) <$>tdi'
      attrUI <- buildUI (textToPrim <$> keyType i) tdi
      paintEdit l (facts $ triding attrUI ) (facts tAttr)
      sp <- UI.li # set children [l,getElement attrUI ]
      let insertT = fmap (Attr .(i,)) <$> (triding attrUI)
      return $ TrivialWidget insertT sp
  where tAttr = fmap (\(Attr i)-> snd i) <$> tAttr'

unSComposite (SComposite i) = i
unSComposite i = errorWithStackTrace ("unSComposite " <> show i)

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
         {-(Primitive Position) -> do
            let addrs = (\(SPosition (Position (lon,lat,_)))-> "http://maps.google.com/?output=embed&q=" <> (HTTP.urlEncode $ show lat  <> "," <>  show lon )) <$>  tdi
            mkElement "iframe" # sink UI.src (maybe "" id <$> facts addrs) # set style [("width","99%"),("height","300px")]-}
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
           let binarySrc = (\(SBinary i) -> "data:" <> T.unpack mime <> ";base64," <>  (BSC.unpack $ B64.encode i) )
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


forceDefaultType  (Just i ) = renderShowable i
forceDefaultType  (Nothing) = ""

diffOptional (SOptional i) = fmap (SOptional .Just)  . join $   unRSOptional' <$> i
diffOptional (SSerial i )  = fmap (SSerial .Just) . join $  unRSOptional' <$>i
diffOptional i   = Just i

tbCase :: InformationSchema -> [Plugins]  ->(forall a . Lens (KV a) (KV a) [a] [a] ) ->  Int -> TB Identity Key -> Set Key -> [(TB Identity Key,TrivialWidget (Maybe (TB Identity (Key,Showable))))] -> [([[[Text]]],Tidings (Maybe (TB1 (Key,Showable))))]-> Tidings (Maybe (TB1 (Key,Showable))) -> UI (TrivialWidget (Maybe (TB Identity (Key,Showable))))
tbCase inf pgs td ix i@(FKT ifk _ _ tb1 ) created wl plugItens oldItems  = do
        let
            rr =  tablePKSet tb1
            table = justError "no table found" $ M.lookup rr $ pkMap inf
            rp = rootPaths'  (tableMap inf) table
            tbi = fmap (\v -> Compose . Identity . unTB . justError "FKT" . (^?  td . Le.ix ix ) . _unTB1  $ v) <$> oldItems
            thisPlugs = filter (any ((== (fmap (keyValue.unAttr.runIdentity.getCompose) ifk)) . head ) . fst) $  plugItens
            pfks =  (first ( filter (not . L.null ) . fmap (L.drop 1) . L.filter ((== (fmap (keyValue.unAttr.runIdentity.getCompose) ifk)) . head ))  . second ( fmap ( join .  fmap (fmap  (_fkttable . runIdentity . getCompose ) . findTB1 ((== ifk ) . fmap (fmap fst )  . tbAttr . runIdentity . getCompose  )))  ) <$> thisPlugs)
        res <- liftIO$ queryWith_  (fromAttr (fst rp)) (conn inf)(fromString $ T.unpack $ snd rp)
        fkUITable inf pgs created res pfks (filter (isReflexive .fst) wl) (fmap (runIdentity . getCompose ) <$>  tbi) i
tbCase inf pgs td ix i@(IT ifk na tb1 ) created wl plugItens oldItems  = do
        let tbi = fmap (\v -> Compose . Identity . unTB . justError "FKT" . (^?  td . Le.ix ix ) . _unTB1 $ v) <$> oldItems
            thisPlugs = filter (any ((== (fmap (keyValue.unAttr.runIdentity.getCompose) ifk)) . head ) . fst) $  plugItens
            pfks =  (first ( filter (not . L.null ) . fmap (L.drop 1) . L.filter ((== (fmap (keyValue.unAttr.runIdentity.getCompose) ifk)) . head ))  . second ( fmap ( join .  fmap (fmap  (_fkttable . runIdentity . getCompose ) . findTB1 ((== ifk ) . fmap (fmap fst )  . tbAttr . runIdentity . getCompose  )))  ) <$> thisPlugs)
        iUITable inf pgs pfks (fmap (runIdentity . getCompose ) <$>  tbi) i
tbCase inf pgs td ix a@(Attr i) created wl plugItens oldItems = do
        let thisPlugs = filter (any ((== [keyValue i]).head) . fst) $  (fmap (fmap (fmap F.toList) ) <$> plugItens)
            tbi = fmap (\v -> unTB . justError "Attr".(^? td . Le.ix ix) . _unTB1  $ v) <$> oldItems
            evs  = (rumors . fmap ( join . fmap ( fmap Attr . L.find ((== i).fst )) )   <$>  (fmap snd thisPlugs))
        attrUITable tbi evs a

uiTable
  ::
     InformationSchema
     -> [Plugins]
     -- Plugin Modifications
     -> Text
     -> [([[[Text]]],Tidings (Maybe (TB1 (Key,Showable))))]
     -> TB1 Key
     -> Tidings (Maybe (TB1 (Key,Showable)))
     -> UI (Element,Tidings (Maybe (TB1 (Key,Showable))))
uiTable inf pgs tname pmods ftb@(TB1 (KV (PK k d) a)) oldItems = do
  let
      Just table = M.lookup tname  (tableMap inf)

  res <- mapM (pluginUI inf oldItems) (filter ((== rawName table ) . _bounds ) pgs)
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


unLeftTB  = join . fmap  un
  where
      un (LeftTB1 i) = i
      un i = errorWithStackTrace ("unleft " <> show i )

crudUITable
  ::
     InformationSchema
     -> [Plugins]
     -> [([[[Text]]],Tidings (Maybe (TB1 (Key,Showable))))]
     -> TB1 Key
     -> Tidings (Maybe (TB1 (Key,Showable)))
     -> UI (Element,Tidings (Maybe (TB1 (Key,Showable))),[Event (Modification Key Showable)])
crudUITable inf pgs pmods ftb@(TB1 (KV (PK k d) a)) oldItems = do
  let
      Just table = M.lookup (S.fromList $ findPK ftb) (pkMap inf)

  res <- mapM (pluginUI inf oldItems) (filter ((== rawName table ) . _bounds ) pgs)
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
    # set children ( listBody : panelItems <> plugins )
    # set style [("border","2px"),("border-color","gray"),("border-style","solid")]
  return (body, tableb ,evsa)

tbAttr (IT  i _ _ ) = i
tbAttr (FKT i _ _ _ ) = i
tbAttr a@(Attr i ) = [Compose . Identity $ a]

filterTB1 f = TB1 . filterKV f . _unTB1
findTB1 f =  findKV f . _unTB1
mapTB1 f = TB1 . mapKV f . _unTB1

unTB1 (LeftTB1 (Just i) ) = unTB1 i
unTB1 (ArrayTB1 [i] ) = unTB1 i
unTB1 (TB1 i)  = i

tb1Diff f (TB1 k1 ) (TB1 k2) =  liftF2 f k1 k2

processPanelTable
   :: Connection
   -> Behavior (Maybe (TB1 (Key, Showable)))
   -> Table
   -> Tidings (Maybe (TB1 (Key, Showable)))
   -> UI ([Element],[Event (Modification Key Showable)])
processPanelTable conn attrsB table oldItemsi = do
  let fkattrsB = fmap (concat . F.toList . fmap (attrNonRec . unTB) . _unTB1. tableNonRef ) <$> attrsB
      oldItems = fmap (concat . F.toList . fmap (attrNonRec .unTB) . _unTB1. tableNonRef ) <$> oldItemsi
  insertB <- UI.button # set text "INSERT" # set UI.style (noneShowSpan ("INSERT" `elem` rawAuthorization table ))
  -- Insert when isValid
        # sink UI.enabled ( isJust <$> fkattrsB)
  editB <- UI.button # set text "EDIT" # set UI.style (noneShowSpan ("UPDATE" `elem` rawAuthorization table ))

  -- Edit when any persistent field has changed
        # sink UI.enabled (liftA2 (\i j -> maybe False (any fst . F.toList  ) $ liftA2 (tb1Diff (\l m -> if l  /= m then traceShow (l,m) (True,(l,m)) else (False,(l,m))) )  i j) (fmap tableNonRef <$> attrsB) (fmap tableNonRef <$> facts oldItemsi))
  deleteB <- UI.button # set text "DELETE" # set UI.style (noneShowSpan ("DELETE" `elem` rawAuthorization table ))
  -- Delete when isValid
        # sink UI.enabled (isJust <$> facts oldItems)
  let
      deleteAction ki =  do
        res <- liftIO $ catch (Right <$> delete conn ki table) (\e -> return $ Left (show $ traceShowId  (e :: SomeException) ))
        return $ const (DeleteTB ki ) <$> res
      editAction attr old = do
        let
            isM :: Maybe (TB1 (Key,Showable))
            isM =  join $ fmap TB1 . allMaybes . filterKV (maybe False (const True)) <$> (liftA2 (liftF2 (\i j -> if i == j then Nothing else  traceShow (i,j) $ Just i))) (_unTB1 . tableNonRef  <$> attr) (_unTB1 . tableNonRef <$> old)
        res <- liftIO $ catch (maybe (return (Left "no attribute changed check edit restriction")) (\l-> Right <$> updateAttr conn l (fromJust old) table) isM ) (\e -> return $ Left (show $ traceShowId (e :: SomeException) ))
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



keyOptional (k,v) = (kOptional k ,SOptional $ Just v)

unKeyOptional (k  ,(SOptional v) ) = fmap (unKOptional k, ) v

kOptional (Key a b c d e) = Key a b c d (KOptional e)

unKOptional ((Key a b c d (KOptional e))) = (Key a b c d e )
unKOptional i = errorWithStackTrace ("unKOptional " <> show i)

unKArray (Key a b c d (KArray e)) = Key a b c d e
unKArray (Key a b c d (KOptional (KArray e) )) = Key a b c d e



addToList _ (InsertTB m) =  (m:)
addToList i (DeleteTB m ) =  L.delete m
addToList i (EditTB (TB1 m) n ) = (map (\e-> if  (e ==  n) then  mapTB1 (\i -> maybe i id $ L.find (\k -> (tbAttr $ fmap fst $ runIdentity $ getCompose k) == (tbAttr $ fmap fst $ runIdentity $ getCompose i) ) ls ) e  else e ))
    where ls = F.toList m

-- lookup pk from attribute list
editedMod :: (Traversable f ,Ord a) => f a ->  Maybe [(a,b)] -> Maybe (f (a,b))
editedMod  i  m=  join $ fmap (\mn-> look mn i ) m
  where look mn k = allMaybes $ fmap (\ki -> fmap (ki,) $  M.lookup ki (M.fromList mn) ) k


showFK = (pure ((\v j ->j  # set text (L.intercalate "," $ fmap renderShowable $ F.toList $  _kvKey $ allKVRec $  snd <$> v))))

tablePKSet  tb1 = S.fromList $ fmap (unAttr . runIdentity . getCompose ) $ _pkKey $ _kvKey $ unTB1 $ tableNonRef tb1

flabel = UI.span # set UI.class_ (L.intercalate " " ["label","label-default"])


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
iUITable inf pgs pmods oldItems  tb@(IT ifk na  (TB1 tb1))
    = do
      l <- flabel # set text (show $ unAttr .unTB <$>   ifk)
      (celem,tcrud) <- uiTable inf pgs na pmods (TB1 tb1) (fmap _fkttable <$> oldItems)
      element celem
          # set style [("padding-left","10px")]
      fk <- UI.li # set  children [l, celem]
      let bres =  fmap (fmap (IT (fmap (,SOptional Nothing ) <$> ifk) na  ) ) (tcrud)
      paintEdit  (getElement l) (facts bres) (facts oldItems)
      return $ TrivialWidget bres fk
iUITable inf pgs pmods oldItems  tb@(IT ifk na (LeftTB1 (Just tb1))) = do
   tr <- iUITable inf pgs (fmap (fmap unLeftTB) <$> pmods) (join . fmap (\(IT itk na (LeftTB1 l)) -> IT itk na <$>  l) <$>  oldItems) (IT ifk na tb1)
   return $  Just . maybe ((IT (fmap (,SOptional Nothing ) <$> ifk) na  (LeftTB1 Nothing))) (\(IT i na j ) -> IT i na (LeftTB1 (Just j)))  <$> tr
iUITable inf pgs plmods oldItems  tb@(IT ifk na (ArrayTB1 [tb1]))
    = do
      offset <- UI.input # set UI.text "0"
      let offsetE =  (filterJust $ readMaybe <$> onEnter offset)
      offsetB <- stepper 0 offsetE
      let
         offsetT = tidings offsetB offsetE
      l <- flabel # set text (show $ unAttr .unTB <$>   ifk)
      items <- mapM (\ix -> (iUITable inf pgs ((fmap (\i -> (\o ->  join .  fmap (\(ArrayTB1 tbl) -> atMay  tbl (ix + o) )) <$> offsetT <*> i))   <$> plmods) ((\o -> join . fmap (\(IT i na  (ArrayTB1 j)) -> IT i na <$>  atMay j (ix + o)   ))  <$> offsetT <*> oldItems)) (IT (ifk) na tb1) ) [0..8]
      let tds = triding <$> items
          es = getElement <$> items
      sequence $ zipWith (\e t -> element e # sink UI.style (noneShow . maybe False (const True) <$> facts t)) (tail es ) ( tds )
      fk <- UI.li # set  children (l: offset:  (getElement <$> items))
      let bres2 = fmap (fmap (\(IT i na j ) -> j)) . allMaybes . L.takeWhile (maybe False (const True)) <$> Tra.sequenceA (triding <$> items)
          emptyFKT = Just . maybe (IT (fmap (,SOptional Nothing ) <$> ifk) na (ArrayTB1 []) ) id
          bres = (\o -> liftA2 (\l (IT _ na (ArrayTB1 m )) -> IT (fmap (,SOptional Nothing ) <$> ifk)  na (ArrayTB1 $ L.take o m <> l <> L.drop  (o + 9 ) m ))) <$> offsetT <*> bres2 <*> (emptyFKT <$> oldItems)
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
fkUITable inf pgs created res pmods wl  oldItems  tb@(FKT ifk refl rel tb1@(TB1 _ ) )
    | not refl = do
        nonInjectiveSelection inf pgs created wl tb (pure res) oldItems
    | otherwise = mdo
      let
          rr = S.fromList $ fmap (unAttr . runIdentity . getCompose ) $ _pkKey $ _kvKey $ _unTB1 $ tableNonRef tb1
          relTable = M.fromList $ fmap swap rel
          tdipre = fmap _fkttable <$> oldItems
          plmods =  pmods
      tdi <- foldr (\i j ->  updateEvent  (fmap (Tra.traverse (Tra.traverse diffOptional ))) i   =<< j)  (return tdipre) (rumors . snd <$> plmods)
      l <- flabel # set text (show $ unAttr .unTB <$> ifk)

      filterInp <- UI.input
      filterInpBh <- stepper "" (UI.valueChange filterInp )
      let filterInpT = tidings filterInpBh (UI.valueChange filterInp)
          filtering i  = T.isInfixOf (T.pack $ toLower <$> i) . T.toLower . T.intercalate "," . fmap (T.pack . renderShowable) . F.toList . fmap snd
      box <- optionalListBox  (sorting True (S.toList rr) <$> fmap fst res2) tdi (pure id ) ((\i j -> maybe id (\l  ->   (set UI.style (noneShow $ filtering j l  ) ) . i  l ) )<$> showFK <*> filterInpT)
      let
        reorderPK l = fmap (\i -> justError "reorder wrong" $ L.find ((== i).fst) l )  (unAttr . unTB <$> ifk)
        lookFKsel (ko,v)=  (kn ,transformKey (textToPrim <$> keyType ko ) (textToPrim <$> keyType kn) v)
          where kn = justError "relTable" $ M.lookup ko relTable
        fksel =  (\box -> fmap (\ibox -> FKT (fmap (_tb . Attr). reorderPK . fmap lookFKsel $ ibox) refl rel (fromJust box) ) .  join . fmap findPKM $ box ) <$>  ( triding box)
      chw <- checkedWidget (pure False)
      (celem,_ ,evs) <- crudUITable inf pgs plmods tb1  (triding box)
      let eres ev = (\e -> second (modifyTB  e) .
                           first (addToList (allRec' (tableMap inf) ((\(Just i)-> i) $ M.lookup rr (pkMap inf))) e) ) <$> ev
      res2  <-  accumTds (liftA2 (,) (pure res) tdi ) (eres <$> evs)
      element celem
          # set UI.style (noneShow False )
          # sink UI.style (noneShow <$> (facts $ triding chw))
          # set style [("padding-left","10px")]
      fk <- UI.li # set  children [l, getElement box,filterInp,getElement chw,celem]
      paintEdit  (getElement l) (facts fksel) ( facts oldItems)
      return $ TrivialWidget fksel fk





fkUITable inf pgs created res plmods  wl oldItems  tb@(FKT ilk refl rel  (LeftTB1 (Just tb1 ))) = do
    tb <- fkUITable inf pgs created res (fmap (fmap unLeftTB) <$> plmods)  wl (join . fmap (\(FKT ifk refl rel  (LeftTB1 tb)) -> liftA2 (\ik -> FKT ik  refl (first unKOptional <$> rel)) (traverse (traverse (unKeyOptional )) ifk) tb) <$> oldItems)  (FKT (fmap unKOptional<$> ilk) refl (first unKOptional <$> rel) tb1)
    let emptyFKT = (FKT (fmap (,SOptional Nothing)  <$> ilk) refl rel (LeftTB1 Nothing))
    return $ (Just . maybe  emptyFKT (\(FKT ifk refl rel  tb)-> FKT (fmap keyOptional <$> ifk) refl rel (LeftTB1 (Just tb)))) <$> tb
fkUITable inf pgs created res2 plmods  wl oldItems  tb@(FKT ifk@[_] refl rel  (ArrayTB1 [tb1]) ) = do
     offset <- UI.input # set UI.text "0"
     let offsetE =  (filterJust $ readMaybe <$> onEnter offset)
     offsetB <- stepper 0 offsetE
     let
         offsetT = tidings offsetB offsetE
         indexItens ix = (\o -> join . fmap (\(FKT [l] refl _ (ArrayTB1 m)  )  -> (\li mi ->  FKT  [li] refl (fmap (first unKArray) rel) mi ) <$> (traverse (indexArray (ix + o) )   l) <*> (atMay (L.drop o m) ix) ))  <$>  offsetT <*> oldItems
         fkst = FKT (fmap (fmap unKArray ) ifk) refl (fmap (first (unKArray)) rel)  tb1
         rr = tablePKSet tb1
         rp = rootPaths'  (tableMap inf) (fromJust $ M.lookup rr $ pkMap inf )
     res <- liftIO$ queryWith_ (fromAttr (fst rp)) (conn  inf) (fromString $ T.unpack $ snd rp)
     fks <- mapM (\ix-> fkUITable inf pgs S.empty res (fmap (\t -> liftA2 (\o ->   join . fmap (\(ArrayTB1 tbl)-> atMay  tbl (ix + o) )) offsetT t ) <$> plmods ) [] (indexItens ix) fkst ) [0..8]
     l <- flabel # set text (show $ unAttr .unTB <$>   ifk)
     sequence $ zipWith (\e t -> element e # sink UI.style (noneShow . maybe False (const True) <$> facts t)) (getElement <$> tail fks) (triding <$> fks)
     dv <- UI.div # set children (getElement <$> fks)
     fksE <- UI.li # set children (l : offset: [dv])

     let bres2 =    allMaybes .  L.takeWhile (maybe False (const True))  <$> Tra.sequenceA (fmap (fmap (\(FKT i _ _ j ) -> (head $ fmap (snd.unAttr.unTB) $ i,  j)) )  . triding <$> fks)
         emptyFKT = Just . maybe (FKT (fmap (,SComposite (V.empty)) <$> ifk) refl rel (ArrayTB1 []) ) id
         bres = (\o -> liftA2 (\l (FKT [lc] refl rel (ArrayTB1 m )) -> FKT ( fmap  ( (,SComposite $ V.fromList $  ((L.take o $ F.toList $ unSComposite $snd $ (unAttr $ runIdentity $ getCompose lc)  )<> fmap fst l <> (L.drop (o + 9 )  $ F.toList $ unSComposite $snd $ (unAttr $ runIdentity $ getCompose lc)  )))) <$> ifk) refl rel (ArrayTB1 $ L.take o m <> fmap snd l <> L.drop  (o + 9 ) m ))) <$> offsetT <*> bres2 <*> (emptyFKT <$> oldItems)
     paintEdit (getElement l) (facts bres) (facts oldItems )
     return $  TrivialWidget bres  fksE

fkUITable  _ _ _ _  _ _ _ _ = errorWithStackTrace "akUITable not implemented"

interPoint ks i j = all (\(l,m) -> justError "interPoint wrong fields" $ liftA2 intersectPredTuple  (L.find ((==l).fst) i ) (L.find ((==m).fst) j)) ks


indexArray ix s =  atMay (unArray s) ix

unArray (k,SComposite s) = (unKArray k,) <$> V.toList s
unArray o  = errorWithStackTrace $ "unArray no pattern " <> show o

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
      l <- flabel # set text (show $ unAttr <$> fkattr')
      o <- UI.li # set children (l : els)
      let bres = liftA2 (liftA2 (\i j-> FKT (fmap (_tb.Attr) i)  refl ksjoin j)) vv ct
      paintEdit (getElement l) (facts ct) (fmap _fkttable <$> facts selks)
      return $ TrivialWidget bres o
  | otherwise = errorWithStackTrace (show attr)
  where inner tbfk sel fkattr' iold = mdo
            let
                o1 = tablePKSet tbfk
                vv =  join . fmap (lorder (unAttr <$> fkattr') ) . fmap concat . allMaybes  <$> iold
                tb = (\i j -> join $ fmap (\k-> L.find ((\(TB1 (KV (PK  l _ ) _ ))-> interPoint ksjoin k  (unAttr . unTB <$> l)) ) i) j ) <$> lks <*> vv
            li <- wrapListBox res2 tb (pure id) showFK
            (ce,_,evs) <- crudUITable inf pgs [] tbfk  tb
            let eres = fmap (addToList  (allRec' (tableMap inf) ((\(Just i)-> i) $ M.lookup o1 (pkMap inf))) <$> ) evs
            res2  <-  accumTds lks eres
            chw <- checkedWidget (pure False)
            element ce
              # sink UI.style (noneShow <$> (facts $ triding chw))
              # set style [("paddig-left","10px")]
            return (vv,tb, [getElement li,getElement chw,ce])

pdfFrame fty pdf = mkElement (fst fty ) UI.# sink UI.src pdf  UI.# UI.set style (snd fty)

allNonEmpty [] = Nothing
allNonEmpty l = Just  l

sorting :: Bool -> [Key] -> [TB1 (Key,Showable)]-> [TB1 (Key,Showable)]
sorting b ss  =  L.sortBy (ifApply b flip (comparing (\i ->  fmap (\s -> fmap snd $ F.find ((== s).fst) i  ) ss) ))
  where ifApply True i =  i
        ifApply False _ = id

