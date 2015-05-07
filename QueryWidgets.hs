{-# LANGUAGE OverloadedStrings,ScopedTypeVariables,FlexibleContexts,ExistentialQuantification,TupleSections,LambdaCase,RankNTypes,RecordWildCards,DeriveFunctor,NoMonomorphismRestriction,RecursiveDo #-}
module QueryWidgets where

import Data.Functor.Compose
import Data.Functor.Identity
import Control.Monad
import Control.Concurrent
import Reactive.Threepenny
import Data.Either
import qualified Graphics.UI.Threepenny as UI
import Graphics.UI.Threepenny.Core hiding (delete)
import Data.Bifunctor
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

data WrappedCall =  forall m . MonadIO m =>  WrappedCall
      { runCall ::  forall a . m a -> IO a
      , stepsCall :: [Connection -> InformationSchema -> MVar (Maybe (TB1 (Key,Showable)))  -> (Maybe (TB1 (Key,Showable)) -> m ()) -> m () ]
      }




data Plugins
  = BoundedPlugin
  { _name :: Text
  , _bounds :: Text
  , _arrowbounds :: ([(Bool,[[Text]])],[(Bool,[[Text]])])
  , _boundedAction :: Connection -> InformationSchema -> (Tidings (Maybe (TB1 (Key,Showable)))) -> UI Element
  }
  | StatefullPlugin
  { _name ::  Text
  , _bounds :: Text
  , _statebounds :: [([(Bool,[[Text]])],[(Bool,[[Text]])])]
  , _statevar :: [[(Text,KType Text)]]
  , _statefullAction :: WrappedCall
  }
  | BoundedPlugin2
  { _name :: Text
  , _bounds :: Text
  , _arrowbounds :: ([(Bool,[[Text]])],[(Bool,[[Text]])])
  , _boundedAction2 :: Connection -> InformationSchema -> (Maybe (TB1 (Key,Showable))) -> IO (Maybe (TB1 (Key,Showable)))
  }


data  PollingPlugins fi fo
  = BoundedPollingPlugins
  { _pollingName :: String
  , _pollingTime :: Int
  , _pollingBounds :: (Text,([(Bool,[[Text]])],[(Bool,[[Text]])]))
  , _pollingBoundedAction :: Connection -> InformationSchema ->  fi -> fo
  }

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

pluginUI conn oinf initItems (StatefullPlugin n tname tf fresh (WrappedCall init ac ) ) = do
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
             (True,False)-> Right <$> attrUITable (const Nothing <$> initItems) (Attr fresh)
             (False,True)->  Left <$> attrUITable (fmap (\v -> Attr . justError ("no key " <> show fresh <> " in " <>  show v ) . L.find ((== fresh) .fst) . F.toList $ v ) <$> t) (Attr fresh)
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
      liftEvent window (rumors oldItems) (\i -> action conn inf  i  (liftIO . h) )
      return  [oldItems]  ))  (return [initItems] ) ( zip tf $ zip freshUI ac)
  element el # sink UI.style (noneShow <$> facts tdInput)
  return (el ,  (  ((\(_,o,_,_) -> o)$ last freshUI ) ))


pluginUI conn inf unoldItems (BoundedPlugin2 n t f action) = do
  let oldItems = unoldItems
      outputItems = oldItems
  overwrite <- checkedWidget (pure False)
  let tdInput = (\i -> maybe False (const True) $ allMaybes $ fmap (\t -> (if fst t then join . fmap unRSOptional' else id ) $ fmap snd $ join $ fmap (indexTable  $ snd t) i) (fst f) ) <$>  oldItems
      tdOutput1 = (\i -> maybe True (const False) $ allMaybes $ fmap (\f -> (if not(fst f ) then join . fmap unRSOptional' else id ) $ fmap snd $ join $ fmap (indexTable  $ snd f) i) (snd f) ) <$>  outputItems
      tdOutput= liftA2 (\i j -> if i then True else j) (triding overwrite)  tdOutput1
  let ovev =((\ j i  -> if i then j else Nothing) <$>   oldItems <*> tdOutput1)
  cv <- currentValue (facts ovev)
  headerP <- UI.button # set text (T.unpack n) # sink UI.enabled (facts tdInput)
  let ecv = (facts ovev <@ UI.click headerP)
  bcv <- stepper cv (facts ovev <@ UI.click headerP)
  pgOut <- mapTEvent (action conn inf) (tidings bcv ecv)
  return (headerP, (fmap snd $ snd f ,   pgOut ))


pluginUI conn inf unoldItems (BoundedPlugin n t f action) = do
  let oldItems = unoldItems -- fmap TB1 . Tra.sequenceA <$> Tra.sequenceA (fmap snd $    unoldItems)
  headerP <- UI.div # set text (T.unpack n)
  overwrite <- checkedWidget (pure False)
  let tdInput = (\i -> maybe False (const True) $ allMaybes $ fmap (\t -> (if fst t then join . fmap unRSOptional' else id ) $ fmap snd $ join $ fmap (indexTable  $ snd t) i) (fst f) ) <$>  oldItems
      tdOutput1 = (\i -> maybe True (const False) $ allMaybes $ fmap (\f -> (if not(fst f ) then join . fmap unRSOptional' else id ) $ fmap snd $ join $ fmap (indexTable  $ snd f) i) (snd f) ) <$>  oldItems
      tdOutput= liftA2 (\i j -> if i then True else j) (triding overwrite)  tdOutput1
  let ovev = ((\ j i  -> if i then j else Nothing) <$>   oldItems <*> tdOutput1)
  ev <- action conn inf ovev
  bod <- UI.div  # set children [ev] # sink UI.style (noneShowSpan <$> facts tdOutput)
  element overwrite # sink UI.style (noneShowSpan . not <$> facts tdOutput1)
  body <- UI.div # set children [headerP,getElement overwrite,bod] # sink UI.style (noneShowSpan <$> facts tdInput)
  return (body,  ([] , pure Nothing ))

intersectPredTuple  = (\i j -> intersectPred (textToPrim <$> keyType (fst i)) (textToPrim <$> keyType (fst j)) (snd i) (snd j))


lorder lo lref = allMaybes $ fmap (\k -> L.find (\i-> fst i == k ) lref) lo

attrUITable
  :: Tidings (Maybe (TB Identity (Key,Showable)))
     -> TB Identity Key
     -> UI (TrivialWidget (Maybe (TB Identity (Key, Showable))))
attrUITable  tAttr' (Attr i) = do
      l<- UI.span # set text (show i)
      let tdi = tAttr
          justCase i j@(Just _) = j
          justCase i Nothing = i
      attrUI <- buildUI (textToPrim <$> keyType i) tdi
      let
          ei (Just a) = Just a
          ei Nothing = defaultType (keyType i)
      paint l (facts $ triding attrUI )
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
            -- el <- UI.div
            let arraySize = 10
            widgets <- mapM (\i-> buildUI ti (join . fmap (\a -> unSComposite a V.!? i ) <$> tdi )) [0..arraySize]
            let tdcomp = fmap (\v -> if V.null v then showableDef i else Just . SComposite $ v ). takeWhileJust  (flip V.cons) V.empty $ ( triding <$> widgets)
                hideNext Nothing Nothing = False
                hideNext (Just _) _ = True
                tshow = fmap (\idx-> noneShow <$> liftA2 hideNext ((if (idx -1 ) < 0 then const (showableDef i  ) else join . fmap (\(SComposite a)-> a V.!?  (idx - 1)  )) <$> tdcomp ) (join . fmap (\(SComposite a)-> a V.!? idx ) <$> tdcomp )) [0..arraySize]
                ziped = zipWith (\i j -> element j # sink UI.style (facts i))  tshow (fmap getElement widgets)
            sequence ziped
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
         (Primitive PTimestamp) -> do
            itime <- liftIO $  getCurrentTime
            timeButton <- UI.button # set UI.text "now"
            let evCurr = unsafeMapIO (fmap Just) (pure getCurrentTime <@ UI.click timeButton)
                newEv = (unionWith const (rumors tdi) $ fmap (STimestamp . Finite .  utcToLocalTime utc) <$> evCurr)
            tdi2 <- addEvent newEv  tdi
            oneInput tdi2 [timeButton]
         (Primitive PDate) -> do
            itime <- liftIO $  getCurrentTime
            timeButton <- UI.button # set UI.text "now"
            let evCurr = unsafeMapIO (fmap Just) (pure getCurrentTime <@ UI.click timeButton)
                newEv = (unionWith const (rumors tdi) $ fmap (SDate . Finite . localDay . utcToLocalTime utc) <$> evCurr)
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


crudUITable
  :: Connection
     -> InformationSchema
     -> [Plugins]
     -- Plugin Modifications
     -> [([[[Text]]],Tidings (Maybe (TB1 (Key,Showable))))]
     -> TB1 Key
     -> Tidings (Maybe (TB1 (Key,Showable)))
     -> UI (Element,Tidings (Maybe (TB1 (Key,Showable))),[Event (Modification Key Showable)])
crudUITable conn inf pgs pmods ftb@(TB1 (KV (PK k d) a)) oldItems = do
  let
      Just table = M.lookup (S.fromList $ findPK ftb) (pkMap inf)
      tbCase :: (forall a . Lens (KV a) (KV a) [a] [a] ) -> Int -> TB Identity Key -> Set Key -> [(TB Identity Key,TrivialWidget (Maybe (TB Identity (Key,Showable))))] -> [([[[Text]]],Tidings (Maybe (TB1 (Key,Showable))))]-> Tidings (Maybe (TB1 (Key,Showable))) -> UI (TrivialWidget (Maybe (TB Identity (Key,Showable))))
      tbCase td ix i@(AKT ifk refl  _ _) created wl plugItens oldItems = do
        akUITable conn inf pgs ((\(Just i)-> i) $ L.find (\(Path ifkp _ _) -> S.fromList (unAttr . unTB  <$> ifk ) == ifkp) $ S.toList $ rawFKS table) (fmap (\v -> unTB. justError "AKT" .(^? unTB1.td . Le.ix ix ) $ v) <$> oldItems) i
      tbCase td ix i@(FKT ifk _ _) created wl plugItens oldItems  = do
        let path@(Path _ _ rr)  = (justError "no path Found"  $ L.find (\(Path ifkp _ _) -> S.fromList ((\(Attr i) -> i) . unTB  <$> ifk ) == ifkp) $ S.toList $ rawFKS table)
        let rp = rootPaths'  (tableMap inf) (fromJust $ M.lookup rr $ pkMap inf )
        res <- liftIO$ queryWith_ (fromAttr (fst rp)) conn  (fromString $ T.unpack $ snd rp)
        let thisPlugs = filter (any ((== (fmap (keyValue.unAttr.runIdentity.getCompose) ifk)) . head ) . traceShowId . fst) $  plugItens
            tbi = fmap (\v -> Compose . Identity . unTB . justError "FKT" . (^? unTB1. td . Le.ix ix ) $ v) <$> oldItems
            pfks =  (first (traceShowId . filter (not . L.null ) . fmap (L.drop 1) . L.filter ((== (fmap (keyValue.unAttr.runIdentity.getCompose) ifk)) . head ))  . second ( fmap ( join .  fmap (fmap  (_fkttable . runIdentity . getCompose ) . findTB1 ((== ifk ) . fmap (fmap fst )  . tbAttr . runIdentity . getCompose  )))  ) <$> thisPlugs)
        fkUITable conn inf pgs created res pfks (filter (isReflexive .fst) wl) path  (fmap (runIdentity . getCompose ) <$>  tbi) i
      tbCase td ix a@(Attr i) created wl plugItens oldItems = do
        let thisPlugs = filter (any ((== [keyValue i]).head) . fst) $  (fmap (fmap (fmap F.toList) ) <$> plugItens)
            tbi = fmap (\v -> unTB . justError "Attr".(^? unTB1.td . Le.ix ix) $ v) <$> oldItems
        plugTdi <- foldr (\i j ->  updateEvent  (fmap (Tra.traverse (Tra.traverse diffOptional ))) i =<< j) (return tbi ) ( rumors . fmap ( join . fmap ( fmap Attr . L.find ((== i).fst)))   <$> fmap snd thisPlugs)
        attrUITable plugTdi a
  res <- mapM (pluginUI conn inf oldItems) (filter ((== tableName table ) . _bounds ) pgs)
  let plugmods = (snd <$> res ) <> pmods
  let mapMI f e = foldl (\jm (l,m)  -> do
                (w,ok) <- jm
                wn <- f l (unTB m) ok w plugmods oldItems
                return (w <> [(unTB m,wn)],S.fromList (kattr m ) <> ok)
              ) (return ([],e)) . zip [0..]
  fks <- do
      (i,pok) <- mapMI (tbCase (kvKey.pkKey)) S.empty k
      (j,dok) <- mapMI (tbCase (kvKey.pkDescription)) pok d
      (k,_) <-  mapMI (tbCase (kvAttr)) dok a
      return $  KV (PK i j ) k
  let
      tableb :: Tidings (Maybe (TB1 (Key,Showable)))
      tableb  = fmap (TB1 . fmap _tb) . Tra.sequenceA <$> Tra.sequenceA (triding .snd <$> fks)
      tableb2 :: KV (TB Identity Key , Tidings (Maybe (TBIdent   (Key,Showable))))
      tableb2  =  ( fmap (fmap (fmap _tb) . triding ) <$> fks)
  (panelItems,evsa)<- processPanelTable conn (facts tableb) table oldItems
  listBody <- UI.ul
    # set children (F.toList (getElement .snd <$> fks))
    # set style [("border","1px"),("border-color","gray"),("border-style","solid"),("margin","1px")]
  pluginsHeader <- UI.div # set UI.text "Plugins"
  plugins <- UI.div # set children (pluginsHeader : (fst <$> res))
  body <- UI.div
    # set children ( listBody : plugins :  panelItems )
    # set style [("border","2px"),("border-color","gray"),("border-style","solid")]
  return (body, tableb ,evsa)

tbAttr (FKT i _ _ ) = i
tbAttr a@(Attr i ) = [Compose . Identity $ a]
tbAttr (AKT i _ _ _ ) = i

filterTB1 f = TB1 . filterKV f . _unTB1
findTB1 f =  findKV f . _unTB1
mapTB1 f = TB1 . mapKV f . _unTB1


tableNonRef (TB1 (KV (PK l m ) n)  )  = TB1 (KV (PK (fun l) (fun m) ) (fun n))
  where nonRef (Attr i ) = [Compose $ Identity $ Attr i]
        nonRef (FKT i True _ ) = i
        nonRef (FKT i False _ ) = []
        nonRef (AKT i True _ _ ) = i
        nonRef (AKT i False _ _ ) = []
        fun  = concat . fmap (nonRef . runIdentity . getCompose)

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
        let k = fmap (concat . F.toList .fmap (attrNonRec .unTB) ._unTB1 ) ki
            kf = fmap F.toList ki
        res <- liftIO $ catch (Right <$> delete conn ((\(Just i)-> i) k) table) (\e -> return $ Left (show $ traceShowId  (e :: SomeException) ))
        return $ const (Delete kf ) <$> res
      editAction attr old = do
        let i = join $ fmap (\m -> if L.null m then Nothing else Just m ) isM
            k = (\(Just i)-> i) kM
            kM = (L.nubBy (\i j -> fst i == fst j  )  .concat . F.toList .fmap (attrNonRec .unTB) ._unTB1 ) <$> old
            isM :: Maybe [(Key,Showable)]
            isM = ( L.nubBy (\i j -> fst i == fst j  ) . catMaybes . concat . F.toList  . fmap (attrNonRec. unTB ) .  mapKV traceShowId . filterKV (isReflexive .runIdentity . getCompose) ._unTB1)  <$> (liftA2 (liftF2  (\i j -> if i == j then Nothing else  traceShow (i,j) $ Just i))) attr old
            isM' :: Maybe [(Key,Showable)]
            isM' = (catMaybes . F.toList ) <$> (liftA2 (liftF2  (\i j -> if i == j then Nothing else Just i))) attr old
            kM' = F.toList <$> old
        res <- liftIO $ catch (maybe (return (Left "no attribute changed check edit restriction")) (\l-> Right <$> update conn l (fromJust old) table) i ) (\e -> return $ Left (show $ traceShowId (e :: SomeException) ))
        let updated = (\(Just i)-> i) isM'
        return $ fmap (const (Edit (fmap (mappend updated) (filter (\(k,_) -> not $ k `elem` (fmap fst updated)) <$> kM') ) (fromJust old) )) res

      insertAction ip = do
          let i2 = F.toList  ip
              i = L.nubBy (\i j -> fst i == fst j  )  .concat .  F.toList .fmap (attrNonRec .unTB) ._unTB1 $ ip
          res <- catch (Right <$> insertPK fromShowableList conn i table) (\e -> return $ Left (show $ traceShowId (e :: SomeException) ))
          return $ (\v -> Insert $ Just $ (v <> (filter (not . flip elem (fst <$> v) . fst) i2))) <$> res

      evir, ever ,evdr:: Event (Modification Key Showable)
      (evid,evir) = spMap $ filterJust $ (fmap insertAction  <$> attrsB ) <@ (UI.click insertB)
      (evdd,evdr) = spMap $ (deleteAction <$> facts oldItemsi) <@ UI.click deleteB
      (eved,ever) = spMap $ (editAction  <$> attrsB <*> (facts oldItemsi) ) <@ UI.click editB
      spMap = split . unsafeMapIO id
  return ([insertB,editB,deleteB],[evir,ever,evdr])




unLeft :: (F.Foldable f,Functor f) => Maybe (f (Key,Showable)) -> Maybe (f (Key,Showable))
unLeft i = join $  fmap ( allMaybes . fmap (traverse unSOptional.first unKOptional ) ) i

unLeftBind :: (F.Foldable f,Functor f) => f (Key,Showable) -> Maybe (f (Key,Showable))
unLeftBind i =  ( allMaybes . fmap (traverse unSOptional.first unKOptional ) ) i

makeOptional :: (F.Foldable f, Functor f) => f Key -> Maybe (f (Key,Showable)) -> Maybe (f (Key,Showable))
makeOptional def (Just i ) = Just $ fmap keyOptional i
makeOptional def Nothing = allMaybes $ fmap (\i -> (i,)  <$> showableDef (keyType i)) def
-- makeOptional def Nothing = Just $ fmap (\i -> (kOptional i,  SOptional $ showableDef (keyType i))) def

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


addToList i  (Insert m) =  (\i-> mappend (fmap ((\(k,v)-> (k, v)))  <$> maybeToList i)) (editedMod  i m )
addToList i  (Delete m ) =  (\i-> concat . L.delete (fmap ((\(k,v)-> (k, v)))  <$> maybeToList i)  . fmap pure ) (editedMod  i  m )
addToList i  (Edit m n ) =   (map (\e-> if  (e ==  n) then  fmap (\(k,v) -> (k,)  $ (\(Just i)-> i) $ M.lookup k (M.fromList $ (\(Just i)-> i) m) ) e  else e ) ) --addToList i  (Insert  m) . addToList i  (Delete n)

-- lookup pk from attribute list
editedMod :: (Traversable f ,Ord a) => f a ->  Maybe [(a,b)] -> Maybe (f (a,b))
editedMod  i  m=  join $ fmap (\mn-> look mn i ) m
  where look mn k = allMaybes $ fmap (\ki -> fmap (ki,) $  M.lookup ki (M.fromList mn) ) k


showFK = (pure ((\v-> UI.span # set text (L.intercalate "," $ fmap renderShowable $ F.toList $  _kvKey $ allKVRec $  snd <$> v))))


fkUITable
  :: Connection
  -> InformationSchema
  -> [Plugins]
  -- Created Keys
  -> Set Key
  -- Table Data
  -> [TB1 (Key,Showable)]
  -- Plugin Modifications
  -> [([[[Text]]],Tidings (Maybe (TB1 (Key,Showable))))]
  -- Same Table References
  -> [(TB Identity Key,TrivialWidget (Maybe (TB Identity (Key,Showable))))]
  -- Foreign Key Path -- TODO: Remove and move relation to TB Identity Key
  -> Path (Set Key) (SqlOperation Text)
  -- Relation Event
  -> Tidings (Maybe (TB Identity (Key,Showable)))
  -- Static Information about relation
  -> TB Identity Key
  -> UI (TrivialWidget(Maybe (TB Identity (Key, Showable))))
fkUITable conn inf pgs created res pmods wl path@(Path _ (FKJoinTable _  rel _ ) rr ) oldItems  tb@(FKT ifk refl tb1)
    | not refl = do
        nonInjectiveSelection conn inf pgs created wl path tb (pure res) oldItems
    | otherwise = mdo
      let
          isLeftJoin = any isKOptional $  keyType . unAttr . unTB <$> ifk
          relTable = M.fromList $ fmap swap rel
          tdi :: Tidings (Maybe (TB1  (Key,Showable)))
          tdi =  (if isLeftJoin then join . fmap (Tra.sequence . fmap unkeyOptional . _fkttable ) else fmap _fkttable  ) <$> oldItems
      l <- UI.span # set text (show $ unAttr .unTB <$>   ifk)

      filterInp <- UI.input
      filterInpBh <- stepper "" (onEnter filterInp )
      let filterInpT = tidings filterInpBh (onEnter filterInp)
          filtering i= filter (L.isInfixOf (toLower <$> i) . fmap toLower . show  )
          listRes = filtering <$> filterInpT <*> res2

      box <- if isLeftJoin
                then optionalListBox  listRes tdi  (maybe UI.div <$> showFK)
                else wrapListBox listRes tdi showFK
      let
        reorderPK l = fmap (\i -> justError "reorder wrong" $ L.find ((== i).fst) l )  (unAttr . unTB <$> ifk)
        lookFKsel (ko,v)=  (kn ,transformKey (textToPrim <$> keyType ko ) (textToPrim <$> keyType kn) v)
          where kn = justError "relTable" $ M.lookup ko relTable
        fksel = (if isLeftJoin then Just . maybe (fmap (\k-> (k,justError "non optional type in left join" $ showableDef (keyType k)) ) (unAttr. unTB <$> ifk)) id  else id ) . fmap (reorderPK . fmap lookFKsel)  <$>  (fmap findPK  <$> triding box)
      paint (getElement l) (facts fksel)
      chw <- checkedWidget (pure False)
      (celem,tcrud,evs) <- crudUITable conn inf pgs pmods (if isLeftJoin then unKOptional <$> tb1  else tb1 ) (triding box)
      let eres = fmap (addToList  (allRec' (tableMap inf) ((\(Just i)-> i) $ M.lookup rr (pkMap inf))) <$> ) evs
      res2  <-  accumTds (pure res) eres
      element celem
          # sink UI.style (noneShow <$> (facts $ triding chw))
          # set style [("padding-left","10px")]
      fk <- UI.li # set  children [l, getElement box,filterInp,getElement chw,celem]
      let bres =  liftA2 (liftA2 (\i -> FKT i refl ) ) (fmap (fmap (_tb . Attr)) <$> fksel ) (if isLeftJoin then makeOptional tb1 <$> tcrud else tcrud )
      return $ TrivialWidget bres fk


akUITable conn inf pgs path@(Path rl (FKJoinTable frl  rel frr ) rr ) oldItems  tb@(AKT ifk@[_] refl _ [tb1])
  | otherwise = do
     let isLeft = any (any (isKOptional . keyType).  kattr) ifk
         path = Path (S.map (kOptional . unKArray) $ if isLeft then S.map unKOptional rl else rl ) (FKJoinTable frl (fmap (first (kOptional.unKArray)) rel) frr) rr
         indexItens ix = join . fmap (\(AKT [l] refl _ m) -> (\li mi ->  FKT  [li] refl  mi ) <$> (join $ traverse (indexArray ix ) <$> (if isLeft then unLeftBind l else Just l)) <*> (if isLeft then unLeft else id ) (atMay m ix) )  <$>  oldItems
         fkst = FKT (fmap (fmap (kOptional . unKArray) ) ifk) refl (fmap kOptional $ if isLeft then fmap unKOptional tb1 else tb1 )
     let rp = rootPaths'  (tableMap inf) (fromJust $ M.lookup rr $ pkMap inf )
     res <- liftIO$ queryWith_ (fromAttr (fst rp)) conn  (fromString $ T.unpack $ snd rp)
     fks <- mapM (\ix-> fkUITable conn inf pgs S.empty res [] [] path  (makeOptional fkst <$>indexItens ix) fkst ) [0..8]
     sequence $ zipWith (\e t -> element e # sink UI.style (noneShow . maybe False (const True) <$> facts t)) (getElement <$> tail fks) (fmap unLeft . triding <$> fks)
     fksE <- UI.li # set children (getElement <$> fks )
     let bres = fmap (\l -> AKT (fmap  (,SComposite $ V.fromList $  (fmap fst l)) <$> ifk) refl [] (fmap snd l)). allMaybes .  L.takeWhile (maybe False (const True)) <$> Tra.sequenceA (fmap (fmap (\(FKT i _ j ) -> (head $ fmap (snd.unAttr.unTB) $ i, j)) ) . fmap unLeft . triding <$> fks)
     return $ (if isLeft then makeOptional tb else id) <$>  TrivialWidget bres fksE
akUITable _ _ _ _ _ _ = error "akUITable not implemented"

interPoint ks i j = all (\(l,m) -> justError "interPoint wrong fields" $ liftA2 intersectPredTuple  (L.find ((==l).fst) i ) (L.find ((==m).fst) j)) ks

indexArray ix s =  atMay (unArray s) ix

unArray (k,SComposite s) = (unKArray k,) <$> V.toList s

-- Create non
nonInjectiveSelection
  :: Connection
  -> InformationSchema
  -> [Plugins ]
  -> Set Key
  -> [(TB Identity Key,TrivialWidget (Maybe (TB Identity (Key,Showable))))]
  -> Path (Set Key) (SqlOperation Text)
  -> TB Identity Key
  -> Tidings [TB1 (Key,Showable)]
  -> Tidings (Maybe (TB Identity (Key,Showable)))
  -> UI (TrivialWidget (Maybe (TB Identity (Key,Showable ))))
nonInjectiveSelection conn inf pgs created wl (Path _ (FKJoinTable _ ksjoin _ ) o1 ) attr@(FKT fkattr refl tbfk ) lks selks
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
      paint (getElement l) (facts vv)
      o <- UI.li # set children (l: els)
      return $ TrivialWidget   (liftA2 (liftA2 (\i j-> FKT (fmap (_tb.Attr) i)  refl j)  ) vv ct) o
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
      paint (getElement l) (facts vvo)
      o <- UI.div # set children (l: els)
      return $ TrivialWidget   (liftA2 (liftA2 (\i -> FKT i refl ) ) (fmap (fmap (_tb . Attr ) ). makeOptional (fmap (unAttr .unTB) fkattr) <$> vv) (makeOptional tbfk <$> ct)) o
  | otherwise = error (show attr)
  where inner tbfk sel fkattr' iold = mdo
            let
                vv =  join . fmap (lorder (unAttr <$> fkattr') ) . fmap concat . allMaybes  <$> iold
                tb = (\i j -> join $ fmap (\k-> L.find ((\(TB1 (KV (PK  l _ ) _ ))-> interPoint ksjoin k  (unAttr . unTB <$> l)) ) i) j ) <$> lks <*> vv
            li <- wrapListBox res2 tb showFK
            (ce,ct,evs) <- crudUITable conn inf pgs [] tbfk  tb
            let eres = fmap (addToList  (allRec' (tableMap inf) ((\(Just i)-> i) $ M.lookup o1 (pkMap inf))) <$> ) evs
            res2  <-  accumTds lks eres
            chw <- checkedWidget (pure False)
            element ce
              # sink UI.style (noneShow <$> (facts $ triding chw))
              # set style [("paddig-left","10px")]
            return (vv,ct, [getElement li,getElement chw,ce])

pdfFrame fty pdf = mkElement (fst fty ) UI.# sink UI.src pdf  UI.# UI.set style (snd fty)
