{-# LANGUAGE FlexibleContexts,TupleSections,LambdaCase,RankNTypes,RecordWildCards,DeriveFunctor,NoMonomorphismRestriction,RecursiveDo #-}
module QueryWidgets where

import Data.Functor.Compose
import Data.Functor.Identity
import Control.Monad
import Reactive.Threepenny
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

data Plugins
  = BoundedPlugin
  { _name :: String
  , _bounds :: (Text,([(Bool,[[Text]])],[(Bool,[[Text]])]))
  , _boundedAction :: Connection -> InformationSchema -> (Tidings (Maybe (TB1 (Key,Showable)))) -> UI Element
  }
  | BoundedPlugin2
  { _name :: String
  , _bounds :: (Text,([(Bool,[[Text]])],[(Bool,[[Text]])]))
  , _boundedAction2 :: Connection -> InformationSchema -> (Maybe (TB1 (Key,Showable))) -> IO (Maybe (TB1 (Key,Showable)))
  }


data  PollingPlugins fi fo
  = BoundedPollingPlugins
  { _pollingName :: String
  , _pollingTime :: Int
  , _pollingBounds :: (Text,([(Bool,[[Text]])],[(Bool,[[Text]])]))
  , _pollingBoundedAction :: Connection -> InformationSchema ->  fi -> fo
  }

filterKV i (KV (PK l m) n) = KV (PK (filter i l) (filter i m )) (filter i n)
containKV f = (\i ->   S.member ( S.fromList $ fmap keyValue $  kattr (Compose . Identity $ fst i)) (S.fromList $ fmap (S.fromList .head) $ fmap snd $ f))

-- [Note] Smooth Plugins
-- Just update when input change
-- Don't overwrite when wont change output
-- Hide when output is already filled
-- Let overwrite output with user command

pluginUI conn inf unoldItems (BoundedPlugin2 n (t,f) action) = do
  let oldItems = unoldItems -- fmap TB1 . Tra.sequenceA <$> Tra.sequenceA (fmap snd    unoldItems)
      outputItems = oldItems -- fmap TB1 . Tra.sequenceA <$> Tra.sequenceA (fmap snd $ (filterKV (containKV (fst f)) )   unoldItems)

  overwrite <- checkedWidget (pure False)
  let tdInput = (\i -> maybe False (const True) $ allMaybes $ fmap (\t -> (if fst t then join . fmap unRSOptional' else id ) $ fmap snd $ join $ fmap (indexTable  $ snd t) i) (fst f) ) <$>  oldItems
      tdOutput1 = (\i -> maybe True (const False) $ allMaybes $ fmap (\f -> (if not(fst f ) then join . fmap unRSOptional' else id ) $ fmap snd $ join $ fmap (indexTable  $ snd f) i) (snd f) ) <$>  outputItems
      tdOutput= liftA2 (\i j -> if i then True else j) (triding overwrite)  tdOutput1
  let ovev =((\ j i  -> if i then j else Nothing) <$>   oldItems <*> tdOutput1)
  cv <- currentValue (facts ovev)
  headerP <- UI.button # set text n # sink UI.enabled (facts tdInput)
  let ecv = (facts ovev <@ UI.click headerP)
  bcv <- stepper cv (facts ovev <@ UI.click headerP)
  pgOut <- mapTEvent (action conn inf) (tidings bcv ecv)
  return (headerP, (fmap snd $ snd f ,  fmap F.toList <$> pgOut ))


pluginUI conn inf unoldItems (BoundedPlugin n (t,f) action) = do
  let oldItems = unoldItems -- fmap TB1 . Tra.sequenceA <$> Tra.sequenceA (fmap snd $    unoldItems)
  headerP <- UI.div # set text n
  overwrite <- checkedWidget (pure False)
  let tdInput = (\i -> maybe False (const True) $ allMaybes $ fmap (\t -> (if fst t then join . fmap unRSOptional' else id ) $ fmap snd $ join $ fmap (indexTable  $ snd t) i) (fst f) ) <$>  oldItems
      tdOutput1 = (\i -> maybe True (const False) $ allMaybes $ fmap (\f -> (if not(fst f ) then join . fmap unRSOptional' else id ) $ fmap snd $ join $ fmap (indexTable  $ snd f) i) (snd f) ) <$>  oldItems
      tdOutput= liftA2 (\i j -> if i then True else j) (triding overwrite)  tdOutput1
  let ovev = ((\ j i  -> if i then j else Nothing) <$>   oldItems <*> tdOutput1)
  ev <- action conn inf ovev
  bod <- UI.div  # set children [ev] # sink UI.style (noneShowSpan <$> facts tdOutput)
  element overwrite # sink UI.style (noneShowSpan . not <$> facts tdOutput1)
  body <- UI.div # set children [headerP,getElement overwrite,bod] # sink UI.style (noneShowSpan <$> facts tdInput)
  return (body,  ([] , pure Nothing :: Tidings (Maybe [(Key,Showable)])))

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
      expandEdit <- checkedWidget (pure False)
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
            let tdcomp = fmap (\i -> if V.null i then Nothing else Just . SComposite $ i ). takeWhileJust  V.snoc V.empty $ ( triding <$> widgets)
                hideNext Nothing Nothing = False
                hideNext (Just _) _ = True
                tshow = fmap (\i-> noneShow <$> liftA2 hideNext ((if (i -1 ) < 0 then const (Just (SOptional Nothing) ) else join . fmap (\(SComposite a)-> a V.!?  (i - 1)  )) <$> tdcomp ) (join . fmap (\(SComposite a)-> a V.!? i ) <$> tdcomp )) [0..arraySize]
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
         (Primitive PPdf) -> do
           let binarySrc = (\(SBinary i) -> "data:application/pdf;base64," <>  (BSC.unpack $ B64.encode i) <> "")
           clearB <- UI.button # set UI.text "clear"
           tdi2 <- addEvent (const Nothing <$> UI.click clearB) tdi
           f <- pdfFrame (maybe "" binarySrc <$> facts tdi2)
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

addEvent ev b = do
 v <- currentValue (facts b)
 let nev = unionWith const ev (rumors b)
 nbev <- stepper v nev
 return  $tidings nbev nev

crudUITable
  :: Connection
     -> InformationSchema
     -> [Plugins]
     -> TB1 Key
     -> Tidings (Maybe (TB1 (Key,Showable)))
     -> UI (Element,Tidings (Maybe (TB1 (Key,Showable))),[Event (Modification Key Showable)])
crudUITable conn inf pgs ftb@(TB1 (KV (PK k d) a)) oldItems = do
  let
      Just table = M.lookup (S.fromList $ findPK ftb) (pkMap inf)
      tbCase :: (forall a . Lens (KV a) (KV a) [a] [a] ) -> Int -> TB Identity Key -> Set Key -> [(TB Identity Key,TrivialWidget (Maybe (TB Identity (Key,Showable))))] -> [([[[Text]]],Tidings (Maybe [(Key,Showable)]))]-> Tidings (Maybe (TB1 (Key,Showable))) -> UI (TrivialWidget (Maybe (TB Identity (Key,Showable))))
      tbCase td ix i@(AKT ifk refl  _ _) created wl plugItens oldItems = do
        akUITable conn inf pgs ((\(Just i)-> i) $ L.find (\(Path ifkp _ _) -> S.fromList (unAttr . unTB  <$> ifk ) == ifkp) $ S.toList $ rawFKS table) (fmap (\v -> unTB. justError "AKT" .(^? unTB1.td . Le.ix ix ) $ v) <$> oldItems) i
      tbCase td ix i@(FKT ifk _ _) created wl plugItens oldItems  = do
        fkUITable conn inf pgs created (filter (isReflexive .fst) wl) ((\(Just i)-> i) $ L.find (\(Path ifkp _ _) -> S.fromList ((\(Attr i) -> i) . unTB  <$> ifk ) == ifkp) $ S.toList $ rawFKS table) (fmap (\v -> unTB . justError "FKT" . (^? unTB1. td . Le.ix ix ) $ v) <$> oldItems) i
      tbCase td ix a@(Attr i) created wl plugItens oldItems = do
        let thisPlugs = filter (any ((== [keyValue i]).head) . fst) $  plugItens
            tbi = fmap (\v -> unTB . justError "Attr".(^? unTB1.td . Le.ix ix) $ v) <$> oldItems
        plugTdi <- foldr (\i j ->  addEvent  i =<< j) (return tbi ) ( rumors . fmap ( join . fmap ( fmap Attr . L.find ((== i).fst)))  <$> fmap snd thisPlugs)
        attrUITable plugTdi a
  res <- mapM (pluginUI conn inf oldItems) (filter ((== tableName table ) . fst  . _bounds ) pgs)
  let plugmods = snd <$> res
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

tbpk :: Lens  (KV a) (KV a) [a] [a]
tbpk = kvKey . pkKey

processPanelTable
   :: Connection
   -> Behavior (Maybe (TB1 (Key, Showable)))
   -> Table
   -> Tidings (Maybe (TB1 (Key, Showable)))
   -> UI ([Element],[Event (Modification Key Showable)])
processPanelTable conn attrsB table oldItemsi = do
  let fkattrsB = fmap (concat . F.toList . fmap (attrNonRec . unTB) . _unTB1) <$> attrsB
      oldItems = fmap (concat . F.toList . fmap (attrNonRec .unTB) . _unTB1) <$> oldItemsi
      efkattrsB :: Behavior (Maybe [(Key,Showable)])
      efkattrsB = fmap (catMaybes . concat .F.toList.  fmap (attrNonRec . unTB). _unTB1 ) <$> liftA2 (liftA2 (liftF2  (\i j -> if i == j then Nothing else Just i))) attrsB (facts oldItemsi)
  deleteB <- UI.button  # sink UI.enabled (isJust <$> facts oldItems) # set text "DELETE"
  editB <- UI.button # sink UI.enabled (liftA2 (&&) (isJust <$>  efkattrsB) (isJust <$> fkattrsB)) # set text "EDIT"
  insertB <- UI.button  # sink UI.enabled ( isJust <$> fkattrsB) # set text "INSERT"
  let
      deleteAction ki =  do
        let k = fmap (concat . F.toList .fmap (attrNonRec .unTB) ._unTB1 ) ki
            kf = fmap F.toList ki
        res <- liftIO $ catch (Right <$> delete conn ((\(Just i)-> i) k) table) (\e -> return $ Left (show $ traceShowId  (e :: SomeException) ))
        return $ const (Delete kf ) <$> res
      editAction attr old = do
        let i = (\(Just i)-> i) isM
            k = (\(Just i)-> i) kM
            kM = (L.nubBy (\i j -> fst i == fst j  )  .concat . F.toList .fmap (attrNonRec .unTB) ._unTB1 ) <$> old
            isM :: Maybe [(Key,Showable)]
            isM = ( L.nubBy (\i j -> fst i == fst j  ) . catMaybes . concat . F.toList  . fmap (attrNonRec .unTB)._unTB1)  <$> (liftA2 (liftF2  (\i j -> if i == j then Nothing else  Just i))) attr old
            isM' :: Maybe [(Key,Showable)]
            isM' = (catMaybes . F.toList  ) <$> (liftA2 (liftF2  (\i j -> if i == j then Nothing else Just i))) attr old
            kM' = F.toList <$> old
        res <- liftIO $ catch (Right <$> update conn i (fromJust old) table) (\e -> return $ Left (show $ traceShowId (e :: SomeException) ))
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

makeOptional :: Functor f => f Key -> Maybe (f (Key,Showable)) -> Maybe (f (Key,Showable))
makeOptional def (Just i ) = Just $ fmap keyOptional i
makeOptional def Nothing = Just $ fmap (\i -> (i,SOptional Nothing)) def

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
  -> Set Key
  -> [(TB Identity Key,TrivialWidget (Maybe (TB Identity (Key,Showable))))]
  -> Path (Set Key) (SqlOperation Text)
  -> Tidings (Maybe (TB Identity (Key,Showable)))
  -> TB Identity Key
  -> UI (TrivialWidget(Maybe (TB Identity (Key, Showable))))
fkUITable conn inf pgs created wl path@(Path rl (FKJoinTable _  rel _ ) rr ) oldItems  tb@(FKT ifk refl tb1)
    | not refl = do
        let rp = rootPaths'  (tableMap inf) (fromJust $ M.lookup rr $ pkMap inf )
        res <- liftIO$ queryWith_ (fromAttr (fst rp)) conn  (fromString $ T.unpack $ snd rp)
        nonInjectiveSelection conn inf pgs created wl path tb (pure res) oldItems
    | otherwise = mdo
      let
          isLeftJoin = any isKOptional $  keyType <$> F.toList rl
          relTable = M.fromList $ fmap swap rel
          tdi :: Tidings (Maybe (TB1  (Key,Showable)))
          tdi =  (if isLeftJoin then join . fmap (Tra.sequence . fmap unkeyOptional . _fkttable ) else fmap _fkttable  ) <$> oldItems
      let rp = rootPaths'  (tableMap inf) (fromJust $ M.lookup rr $ pkMap inf )
      res <- liftIO$ queryWith_ (fromAttr (fst rp) ) conn  (fromString $ T.unpack $ snd rp)
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
        lookFKsel (ko,v)= (kn ,transformKey (textToPrim <$> keyType ko ) (textToPrim <$> keyType kn) v)
          where kn = justError "relTable" $ M.lookup ko relTable
        fksel = fmap (fmap lookFKsel)  <$>  (fmap findPK  <$> triding box)
        tdsel = fmap (\i -> FKT (zipWith (\i j -> (,j) <$> i)  ifk . fmap snd  . findPK $ i ) refl i)  <$>  triding box
        edited = liftA2 (\i j -> join $ liftA2 (\i j-> if  i == j then Nothing else Just j ) i j) oldItems tdsel
      paint (getElement l) (facts $ if isLeftJoin then makeOptional (S.toList rl)<$> fksel else fksel )
      chw <- checkedWidget (pure False)
      (celem,tcrud,evs) <- crudUITable conn inf pgs (if isLeftJoin then unKOptional <$> tb1  else tb1 ) (triding box)
      let eres = fmap (addToList  (allRec' (tableMap inf) ((\(Just i)-> i) $ M.lookup rr (pkMap inf))) <$> ) evs
      res2  <-  accumTds (pure res) eres
      element celem
          # sink UI.style (noneShow <$> (facts $ triding chw))
          # set style [("padding-left","10px")]
      fk <- UI.li # set  children [l, getElement box,filterInp,getElement chw,celem]
      let bres =  liftA2 (liftA2 (\i -> FKT i refl ) ) (fmap (fmap (_tb . Attr)) <$> if isLeftJoin then makeOptional (S.toList rl)<$> fksel else fksel ) (if isLeftJoin then makeOptional tb1 <$> tcrud else tcrud )
      return $ TrivialWidget bres fk
    where ksn = filter (\i -> not $ S.member (fst i) created) rel


akUITable conn inf pgs path@(Path rl (FKJoinTable frl  rel frr ) rr ) oldItems  tb@(AKT ifk@[_] refl _ [tb1])
  | otherwise = do
     let isLeft = any (any (isKOptional . keyType).  kattr) ifk
         path = Path (S.map (kOptional . unKArray) $ if isLeft then S.map unKOptional rl else rl ) (FKJoinTable frl (fmap (first (kOptional.unKArray)) rel) frr) rr
         indexItens ix = join . fmap (\(AKT [l] refl _ m) -> (\li mi ->  FKT  [li] refl  mi ) <$> (join $ traverse (indexArray ix ) <$> (if isLeft then unLeftBind l else Just l)) <*> (if isLeft then unLeft else id ) (atMay m ix) )  <$>  oldItems
         fkst = FKT (fmap (fmap (kOptional . unKArray) ) ifk) refl (fmap kOptional $ if isLeft then fmap unKOptional tb1 else tb1 )
     fks <- mapM (\ix-> fkUITable conn inf pgs S.empty [] path  (makeOptional fkst <$>indexItens ix) fkst ) [0..8]
     sequence $ zipWith (\e t -> element e # sink UI.style (noneShow . maybe False (const True) <$> facts t)) (getElement <$> tail fks) (fmap unLeft . triding <$> fks)
     fksE <- UI.div # set children (getElement <$> fks )
     let bres = fmap (\l -> AKT (fmap  (,SComposite $ V.fromList (fmap fst l)) <$> ifk) refl [] (fmap snd l)). allMaybes .  L.takeWhile (maybe False (const True)) <$> Tra.sequenceA (fmap (fmap (\(FKT i _ j ) -> (head $ fmap (snd.unAttr.unTB) $ i, j)) ) . fmap unLeft . triding <$> fks)
     return $ (\i -> if isLeft then makeOptional tb i else i) <$>  TrivialWidget bres fksE
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
          sel = fmap (\i->  (Just . unAttr .unTB<$> _tbref i) ) . fmap (fmap snd) <$> selks
      (vv ,ct, els) <- inner tbfk sel (unTB <$> fkattr)
      l <- UI.span # set text (show $ unAttr .unTB<$> fkattr)
      paint (getElement l) (facts vv)
      o <- UI.div # set children (l: els)
      return $ TrivialWidget   (liftA2 (liftA2 (\i j-> FKT (fmap (_tb.Attr) i)  refl j)  ) vv ct) o
  | all isKOptional (keyType . unAttr.unTB<$> fkattr ) = do
      let
          fkattr'=  fmap unKOptional'  <$> fkattr
          tbfk' = unKOptional' <$> tbfk
          sel = fmap (\i->  (unRSOptional' . unAttr .unTB<$> _tbref i) ) . fmap (fmap snd) <$> selks
      (vv ,ct, els) <- inner tbfk' sel ( unTB <$> fkattr')
      l <- UI.span # set text (show $ unAttr . unTB <$> fkattr)
      let vvo = (fmap (fmap Attr ). makeOptional (unAttr . unTB <$> fkattr') <$> vv)
      paint (getElement l) (facts vvo)
      o <- UI.div # set children (l: els)
      return $ TrivialWidget   (liftA2 (liftA2 (\i -> FKT i refl ) ) (fmap (fmap (_tb . Attr ) ). makeOptional (fmap (unAttr .unTB) fkattr') <$> vv) (makeOptional tbfk' <$> ct)) o
  | otherwise = error (show attr)
  where inner tbfk sel fkattr' = mdo
            let
                iold :: Tidings ([Maybe [(Key,Showable)]])
                iold  =   fmap (join . fmap (allMaybes . fmap (  (\(i,j)-> (unKOptional' i,)<$> j) . fmap unRSOptional'))) <$> (Tra.sequenceA $ fmap (fmap ( kattr . _tb ) ) . triding .snd <$> L.filter (\i-> not . S.null $ S.intersection (S.fromList $ kattr $ _tb $ fst $ i) oldASet) wl)
                oldASet :: Set Key
                oldASet = S.fromList (filter (flip S.member created) $ unAttr <$> fkattr' )
            let
                vv =  join . fmap (lorder (unAttr <$> fkattr') ) . fmap concat . allMaybes  <$> iold
                tb = (\i j -> join $ fmap (\k-> L.find ((\(TB1 (KV (PK  l _ ) _ ))-> interPoint ksjoin k  (unAttr . unTB <$> l)) ) i) j ) <$> lks <*> vv
            li <- wrapListBox res2 tb showFK
            (ce,ct,evs) <- crudUITable conn inf pgs tbfk  tb
            let eres = fmap (addToList  (allRec' (tableMap inf) ((\(Just i)-> i) $ M.lookup o1 (pkMap inf))) <$> ) evs
            res2  <-  accumTds lks eres
            chw <- checkedWidget (pure False)
            element ce
              # sink UI.style (noneShow <$> (facts $ triding chw))
              # set style [("paddig-left","10px")]
            return (vv,ct, [getElement li,getElement chw,ce])

pdfFrame pdf = mkElement "iframe" UI.# sink UI.src pdf  UI.# UI.set style [("width","100%"),("height","300px")]
