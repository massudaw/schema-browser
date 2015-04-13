{-# LANGUAGE FlexibleContexts,TupleSections,LambdaCase,RankNTypes,RecordWildCards,DeriveFunctor,NoMonomorphismRestriction,RecursiveDo #-}
module QueryWidgets where

import Control.Monad
import Reactive.Threepenny
import qualified Graphics.UI.Threepenny as UI
import Graphics.UI.Threepenny.Core hiding (delete)

import qualified Data.Map as M
import qualified Data.Set as S
import Data.Set (Set)
import Data.Map (Map)
import Data.Traversable(Traversable,traverse)
import qualified Data.Traversable as Tra

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
import Data.String

data Plugins
  = BoundedPlugin
  { _name :: String
  , _bounds :: (Text,([(Bool,[[Text]])],[(Bool,[[Text]])]))-- PluginBoundary Table Key,PluginBoundary Table Key)
  , _boundedAction :: Connection -> InformationSchema -> Tidings (Maybe (TB1 (Key,Showable))) -> UI Element
  }

data  PollingPlugins
  = BoundedPollingPlugins
  { _pollingName :: String
  , _pollingTime :: Int
  , _pollingBounds :: (Text,([(Bool,[[Text]])],[(Bool,[[Text]])]))
  , _pollingBoundedAction :: Connection -> InformationSchema ->  Tidings [TB1 (Key,Showable)] -> UI Element
  }

pluginUI' conn inf oldItems (BoundedPlugin n (t,f) action) = do
  headerP <- UI.div # set text n
  overwrite <- checkedWidget (pure False)
  let tdInput = (\i -> maybe False (const True) $ allMaybes $ fmap (\t -> (if fst t then join . fmap unRSOptional' else id ) $ fmap snd $ join $ fmap (indexTable  $ snd t) i) (fst f) ) <$>  oldItems
      tdOutput1 = (\i -> maybe True (const False) $ allMaybes $ fmap (\f -> (if not(fst f ) then join . fmap unRSOptional' else id ) $ fmap snd $ join $ fmap (indexTable  $ snd f) i) (snd f) ) <$>  oldItems
      tdOutput= liftA2 (\i j -> if i then True else j) (triding overwrite)  tdOutput1
  ev <- action conn inf oldItems
  bod <- UI.div  # set children [ev] # sink UI.style (noneShowSpan <$> facts tdOutput)
  element overwrite # sink UI.style (noneShowSpan . not <$> facts tdOutput1)
  body <- UI.div # set children [headerP,getElement overwrite,bod] # sink UI.style (noneShowSpan <$> facts tdInput)
  return (body,  pure Nothing :: Tidings (Maybe [(Key,Showable)]))





pointInRangeSelection
  :: Connection
  -> InformationSchema
  -> [Plugins ]
  -> TB Key
  -> Tidings [TB1 (Key,Showable)]
  -> Tidings (Maybe (TB (Key,Showable)))
  -> UI (TrivialWidget (Maybe (TB (Key,Showable ))))
pointInRangeSelection conn inf pgs attr@(FKT fkattr tbfk ) lks selks
  | all isPrim (keyType . unAttr<$> fkattr ) = do
      let l = fmap (\(TB1 (KV (PK i _) _)) ->  (\(SInterval iv) -> iv). unAttr <$> i). (fmap (fmap snd)) <$> lks
          sel = fmap (\(FKT i (TB1 (KV (PK j _) _)) )->  zip (unAttr <$> i) ((\(SInterval iv) -> iv). unAttr <$> j)) . fmap (fmap snd) <$> selks

      i <-  Tra.sequence $ zipWith (\l m -> buildUI m (fmap (!!l) <$> (fmap (fmap fst) <$> sel)) ) [0..] (fmap textToPrim . keyType .unAttr <$> fkattr )
      let initSel j im  = join $ (\i -> L.find (\m-> all id $ zipWith Interval.member i m) j  ) <$> im
          vv =  allMaybes <$> Tra.sequenceA (triding <$> i)
      let tb = (\i j -> join $ fmap (\k-> L.find ((\(TB1 (KV (PK  l _ ) _ ))-> all id $ zipWith Interval.member k  ((\(SInterval iv) -> iv). unAttr <$> l)) . fmap snd) i) j ) <$> lks <*> vv
      l <- UI.span # set text (show fkattr)
      (ce,ct,cev) <- crudUITable conn inf pgs tbfk tb
      li <- wrapListBox lks  tb showFK
      chw <- checkedWidget (pure False)
      element ce
        # sink UI.style (noneShow <$> (facts $ triding chw))
        # set style [("padding-left","10px")]
      paint (getElement l) (facts vv)
      o <- UI.div # set children (l: (getElement <$> i) <>  [getElement li,getElement chw,ce])
      return $ TrivialWidget   (liftA2 (liftA2 (\i j-> FKT (zipWith (\l m -> (,m) <$> l)  fkattr i ) j)  ) vv ct) o
  | all isKOptional (keyType . unAttr<$> fkattr ) = do
      let l = fmap (\(TB1 (KV (PK i _) _)) ->  (\(SInterval iv) -> iv). unAttr <$> i). (fmap (fmap snd)) <$> lks
          sel =   join . fmap (\(FKT i (TB1 (KV (PK j _) _)) )->  allMaybes $ zipWith (liftA2 (\m (SInterval l) -> (m,l))) (unSOptional . unAttr <$> i) ( unSOptional . unAttr <$> j)) . fmap (fmap snd) <$> selks

      i <-  Tra.sequence $ zipWith (\l (KOptional m) -> buildUI m (join . fmap (!!l) <$> (fmap (\(FKT i _)->  (unSOptional . snd. unAttr <$> i) ) <$> selks ))) [0..] (fmap textToPrim . keyType .unAttr <$> fkattr )
      let initSel j im  = join $ (\i -> L.find (\m-> all id $ zipWith Interval.member i m) j  ) <$> im
          vv =  allMaybes  <$> Tra.sequenceA (triding <$> i)
          vvm =  allMaybes . fmap (Just .SOptional) <$> Tra.sequenceA (triding <$> i)
      let tb = (\i j -> join $ fmap (\k-> L.find ((\(TB1 (KV (PK  l _ ) _ ))-> all id $ zipWith Interval.member k  ((\(SInterval iv) -> iv). unAttr <$> l)) . fmap snd) i) j ) <$> lks <*> (vv)
      l <- UI.span # set text (show fkattr)
      (ce,ct,cev) <- crudUITable conn inf pgs (unKOptional <$> tbfk ) tb
      li <- wrapListBox lks tb showFK
      chw <- checkedWidget (pure False)
      element ce
        # sink UI.style (noneShow <$> (facts $ triding chw))
        # set style [("paddig-left","10px")]
      paint (getElement l) (facts vvm)
      o <- UI.div # set children (l: (getElement <$> i) <>  [getElement li,getElement chw,ce])
      return $ TrivialWidget   (liftA2 (liftA2 (\i j-> FKT (zipWith (\l m -> (,m) <$> l)  fkattr i ) j)  ) vvm ((maybe (Just $ (,SOptional Nothing)<$> tbfk) Just )<$> ct)) o
  | otherwise = error (show attr)


attrUITable
  :: Tidings (Maybe (TB (Key,Showable)))
     -> TB Key
     -> UI
          (TrivialWidget (Maybe (TB (Key, Showable))))
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


buildUI i  tdi = case i of
         (KOptional ti) -> fmap ((Just. SOptional) ) <$> buildUI ti (join . fmap unSOptional <$> tdi)
         (KSerial ti) -> fmap (Just . SSerial) <$> buildUI ti ( join . fmap unSSerial <$> tdi)
         (KArray ti) -> do
            -- el <- UI.div
            widgets <- mapM (\i-> buildUI ti (join . fmap (\(SComposite a)-> a V.!? i ) <$> tdi )) [0..20]
            let tdcomp = fmap (\i -> if V.null i then Nothing else Just . SComposite $ i ). takeWhileJust  V.snoc V.empty $ ( triding <$> widgets)
                hideNext Nothing Nothing = False
                hideNext (Just _) _ = True
                tshow = fmap (\i-> noneShow <$> liftA2 hideNext ((if (i -1 ) < 0 then const (Just (SOptional Nothing) ) else join . fmap (\(SComposite a)-> a V.!?  (i - 1)  )) <$> tdcomp ) (join . fmap (\(SComposite a)-> a V.!? i ) <$> tdcomp )) [0..20]
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
            let td = (\m n -> traceShowId  .fmap SInterval $   liftF2 interval m n) <$> (liftA2 (,) <$> triding inf  <*> triding lbd) <*> (liftA2 (,) <$> triding sup <*> triding ubd)
            return $ TrivialWidget td composed
         (Primitive PTimestamp) -> do
            itime <- liftIO $  getCurrentTime
            timeButton <- UI.button # set UI.text "now"
            let evCurr = unsafeMapIO (fmap Just) (pure getCurrentTime <@ UI.click timeButton)
            currentTime <- stepper Nothing evCurr
            let
                tdcurr = fmap (STimestamp . Finite . utcToLocalTime utc)  <$> tidings currentTime evCurr
                tdi2 = foldrTds justCase tdcurr [tdi]
            oneInput tdi2 [timeButton]
         (Primitive PDate) -> do
            itime <- liftIO $  getCurrentTime
            timeButton <- UI.button # set UI.text "now"
            let evCurr = unsafeMapIO (fmap Just) (pure getCurrentTime <@ UI.click timeButton)
            currentTime <- stepper Nothing evCurr
            let
                tdcurr = fmap (SDate . Finite . localDay . utcToLocalTime utc)  <$> tidings currentTime evCurr
                tdi2 = foldrTds justCase tdcurr [tdi]
            oneInput tdi2 [timeButton]
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


crudUITable
  :: Connection
     -> InformationSchema
     -> [Plugins]
     -> TB1 Key
     -> Tidings (Maybe (TB1 (Key,Showable)))
     -> UI (Element,Tidings (Maybe (TB1 (Key,Showable))),[Event (Modification Key Showable)])
crudUITable conn inf pgs tb@(TB1 (KV (PK k d) a)) oldItems = do
  let
      tbCase :: (forall a . KV a -> [a]) -> Int -> TB Key -> UI (TrivialWidget (Maybe (TB (Key,Showable))))
      tbCase td ix i@(AKT ifk _) = fkUITable conn inf pgs ((\(Just i)-> i) $ L.find (\(Path ifkp _ _) -> S.fromList ((\(Attr i) -> i) <$> ifk ) == ifkp) $ S.toList $ rawFKS table) (fmap (\v -> justError ("AKT" <> show (ix,td $ unTB1 tb, td . unTB1 $ v)). (`atMay` ix) .td .unTB1$ v) <$> oldItems) i
      tbCase td ix i@(FKT ifk _) = fkUITable conn inf pgs ((\(Just i)-> i) $ L.find (\(Path ifkp _ _) -> S.fromList ((\(Attr i) -> i) <$> ifk ) == ifkp) $ S.toList $ rawFKS table) (fmap (\v -> justError ("FKT" <> show (ix,td $ unTB1 tb, td . unTB1 $ v)). (`atMay` ix) .td .unTB1$ v) <$> oldItems) i
      tbCase td ix a@(Attr i) = attrUITable (fmap (\v -> justError ("Attr " <> show (ix, td $ unTB1 tb, td . unTB1 $ v) ).(`atMay`ix) .td .unTB1 $ v) <$> oldItems)  a
      mapMI f = Tra.mapM (uncurry f) . zip [0..]
      Just table = M.lookup (S.fromList $findPK tb) (pkMap inf)
  fks <- liftA3 (\i j k -> KV (PK i j ) k)
      (mapMI (tbCase (pkKey.kvKey)) k)
      (mapMI (tbCase (pkDescription.kvKey)) d)
      (mapMI (tbCase (kvAttr)) a)
  let tb = fmap TB1 . Tra.sequenceA <$> Tra.sequenceA (triding <$> fks)
  res <- mapM (pluginUI' conn inf tb ) (filter (\(BoundedPlugin _ (t,_) _ ) -> t == tableName table) pgs)
  (panelItems,evsa)<- processPanelTable conn (facts tb) table oldItems
  listBody <- UI.ul
    # set children (F.toList (getElement <$> fks))
    # set style [("border","1px"),("border-color","gray"),("border-style","solid"),("margin","1px")]
  body <- UI.div
    # set children ( listBody :  panelItems <> (fst <$> res))
    # set style [("border","2px"),("border-color","gray"),("border-style","solid")]
  return (body, tb ,evsa)

processPanelTable
     :: Connection
     -> Behavior (Maybe (TB1 (Key, Showable)))
     -> Table
     -> Tidings (Maybe (TB1 (Key, Showable)))
     -> UI ([Element],[Event (Modification Key Showable)])
processPanelTable conn attrsB table oldItemsi = do
  let fkattrsB = fmap (concat . F.toList . fmap attrNonRec . unTB1) <$> attrsB
      oldItems = fmap (concat . F.toList . fmap attrNonRec . unTB1) <$> oldItemsi
      efkattrsB :: Behavior (Maybe [(Key,Showable)])
      efkattrsB = fmap (catMaybes . concat .F.toList. fmap attrNonRec . unTB1 ) <$> liftA2 (liftA2 (liftF2  (\i j -> if i == j then Nothing else Just i))) attrsB (facts oldItemsi)
  deleteB <- UI.button  # sink UI.enabled (isJust <$> facts oldItems) # set text "DELETE"
  editB <- UI.button # sink UI.enabled (liftA2 (&&) (isJust <$>  efkattrsB) (isJust <$> fkattrsB)) # set text "EDIT"
  insertB <- UI.button  # sink UI.enabled ( isJust <$> fkattrsB) # set text "INSERT"
  let
      deleteAction ki =  do
        let k = fmap (concat . F.toList .fmap attrNonRec .unTB1 ) ki
            kf = fmap F.toList ki
        res <- liftIO $ catch (Right <$> delete conn ((\(Just i)-> i) k) table) (\e -> return $ Left (show $ traceShowId  (e :: SomeException) ))
        return $ const (Delete kf ) <$> res
      editAction attr old = do
        let i = (\(Just i)-> i) isM
            k = (\(Just i)-> i) kM
            kM = (concat . F.toList .fmap attrNonRec .unTB1 ) <$> old
            isM :: Maybe [(Key,Showable)]
            isM = (catMaybes . concat . F.toList  . fmap attrNonRec .unTB1) <$> (liftA2 (liftF2  (\i j -> if i == j then Nothing else Just i))) attr old
            isM' :: Maybe [(Key,Showable)]
            isM' = (catMaybes . F.toList  ) <$> (liftA2 (liftF2  (\i j -> if i == j then Nothing else Just i))) attr old
            kM' = F.toList <$> old
        res <- liftIO $ catch (Right <$> update conn i k table) (\e -> return $ Left (show $ traceShowId (e :: SomeException) ))
        let updated = (\(Just i)-> i) isM'
        return $ fmap (const (Edit (fmap (mappend updated) (filter (\(k,_) -> not $ k `elem` (fmap fst updated)) <$> kM') ) kM')) res

      insertAction ip = do
          let i2 = F.toList  ip
              i = L.nubBy (\i j -> fst i == fst j  )  .concat .  F.toList .fmap attrNonRec .unTB1 $ ip
          res <- catch (Right <$> insertPK fromShowableList conn i table) (\e -> return $ Left (show $ traceShowId (e :: SomeException) ))
          return $ (\v -> Insert $ Just $ (v <> (filter (not . flip elem (fst <$> v) . fst) i2))) <$> res

      evir, ever ,evdr:: Event (Modification Key Showable)
      (evid,evir) = spMap $ filterJust $ (fmap insertAction  <$> attrsB ) <@ (UI.click insertB)
      (evdd,evdr) = spMap $ (deleteAction <$> facts oldItemsi) <@ UI.click deleteB
      (eved,ever) = spMap $ (editAction  <$> attrsB <*> (facts oldItemsi) ) <@ UI.click editB
      spMap = split . unsafeMapIO id

  return ([insertB,editB,deleteB],[evir,ever,evdr])


findPK = concat . fmap attrNonRec . pkKey  . kvKey . unTB1

attrNonRec (FKT ifk _ ) = concat $ fmap kattr ifk
attrNonRec (AKT ifk _ ) = concat $ fmap kattr ifk
attrNonRec (Attr i ) = [i]

tableNonrec (TB1 k ) = concat $ F.toList $ kvAttr $ fmap attrNonRec k

makeOptional :: Functor f => f Key -> Maybe (f (Key,Showable)) -> Maybe (f (Key,Showable))
makeOptional def (Just i ) = Just $ fmap keyOptional i
makeOptional def Nothing = Just $ fmap (\i -> (i,SOptional Nothing)) def

keyOptional ((Key a b c d e) ,v) = (Key a b c d (KOptional e)  ,SOptional $ Just v)
unkeyOptional ((Key a b c d (KOptional e)) ,(SOptional v) ) = fmap (Key a b c d e  , ) v
unKOptional ((Key a b c d (KOptional e))) = (Key a b c d e )
kOptional ((Key a b c d e)) = (Key a b c d (KOptional e) )

addToList i  (Insert m) =  (\i-> mappend (fmap ((\(k,v)-> (k, v)))  <$> maybeToList i) ) (editedMod  i m )
addToList i  (Delete m ) =  (\i-> concat . L.delete (fmap ((\(k,v)-> (k, v)))  <$> maybeToList i)  . fmap pure ) (editedMod  i  m )
addToList i  (Edit m n ) =  (map (\e-> if maybe False (e == ) (editedMod i n) then  fmap (\(k,v) -> (k,)  $ (\(Just i)-> i) $ M.lookup k (M.fromList $ (\(Just i)-> i) m) ) e  else e ) ) --addToList i  (Insert  m) . addToList i  (Delete n)

-- lookup pk from attribute list
editedMod :: (Show (f (a,b)),Show (a,b),Traversable f ,Ord a) => f a ->  Maybe [(a,b)] -> Maybe (f (a,b))
editedMod  i  m=  join $ fmap (\mn-> look mn i ) m
  where look mn k = allMaybes $ fmap (\ki -> fmap (ki,) $  M.lookup ki (M.fromList mn) ) k

data Inclusion
  = Equal
  | Contains
  | Elem
  deriving(Eq,Ord,Show)

classifyFK (Attr (KOptional (Primitive i ))) (Attr (KInterval (Primitive j ))) | i == j =  [Elem]
classifyFK (Attr (Primitive i )) (Attr (KInterval (Primitive j ))) | i == j =  [Elem]
classifyFK (Attr (Primitive i )) (Attr (Primitive j))  | i == j = [Equal]
classifyFK (FKT i _) (FKT j _) = concat $ liftA2 classifyFK i j
classifyFK i j = [Equal]


showFK = (pure ((\v-> UI.span # set text (L.intercalate "," $ fmap renderShowable $ F.toList $  fmap unAttr $ kvKey $ unTB1  $  snd <$> v))))

fkUITable
  :: Connection
  -> InformationSchema
  -> [Plugins]
  -> Path (Set Key) (SqlOperation Text)
  -> Tidings (Maybe (TB (Key,Showable)))
  -> TB Key
  -> UI (TrivialWidget(Maybe (TB (Key, Showable))))
fkUITable conn inf pgs (Path rl (FKJoinTable _  rel _ ) rr ) oldItems  tb@(FKT ifk tb1)
    | all (==Elem) (concat $ zipWith classifyFK (Attr . fmap textToPrim .keyType <$> F.toList rl ) (Attr .fmap textToPrim . keyType <$> F.toList rr) ) = do
        let rp = rootPaths'  (tableMap inf) (fromJust  $ M.lookup (S.fromList $ findPK tb1)  $ pkMap inf )
        res <- liftIO$ queryWith_ (fromAttr (fst rp) ) conn  (fromString $ T.unpack $ snd rp)
        -- res <- liftIO $ projectKey conn inf (projectAllRec' (tableMap inf )) (S.fromList $ findPK tb1)
        pointInRangeSelection conn inf pgs tb (pure res) oldItems
    | otherwise = mdo
      let
          o1 = S.fromList $ findPK tb1
          isLeftJoin = any isKOptional $  keyType <$> F.toList rl
          relTable = M.fromList $ fmap swap rel
          tdi :: Tidings (Maybe (TB1  (Key,Showable)))
          tdi =  (if isLeftJoin then join . fmap (\(FKT _ t) -> Tra.sequence $  unkeyOptional  <$> t ) else fmap (\(FKT _ t )-> t) ) <$> oldItems
      let rp = rootPaths'  (tableMap inf) (fromJust  $ M.lookup (S.fromList $ findPK tb1)  $ pkMap inf )
      res <- liftIO$ queryWith_ (fromAttr (fst rp) ) conn  (fromString $ T.unpack $ snd rp)
      --res <- liftIO $ projectKey conn inf (projectAllRec' (tableMap inf )) o1
      l <- UI.span # set text (show ifk)

      filterInp <- UI.input
      filterInpBh <- stepper "" (onEnter filterInp )
      let filterInpT = tidings filterInpBh (onEnter filterInp)
          filtering i= filter (L.isInfixOf (toLower <$> i) . fmap toLower . show )
          listRes = filtering <$> filterInpT <*> res2

      box <- if isLeftJoin
                then optionalListBox  listRes tdi  (maybe UI.div <$> showFK)
                else wrapListBox listRes tdi showFK
      let
        lookFKsel (ko,v)= (kn ,transformKey (textToPrim <$> keyType ko ) (textToPrim <$> keyType kn) v)
          where kn = justError "relTable" $ M.lookup ko relTable
        fksel = fmap (fmap lookFKsel) <$>  (fmap findPK  <$> triding box)
        tdsel = fmap (\i -> FKT (zipWith (\i j -> (,j) <$> i)  ifk . fmap snd  . findPK $ i ) i)  <$>  triding box
        edited = liftA2 (\i j -> join $ liftA2 (\i j-> if  i == j then Nothing else Just j ) i j) oldItems tdsel
      paint (getElement l) (facts $ if isLeftJoin then makeOptional (S.toList rl)<$> fksel else fksel )
      chw <- checkedWidget (pure False)
      (celem,tcrud,evs) <- crudUITable conn inf pgs (if isLeftJoin then unKOptional <$> tb1  else tb1 ) (triding box)
      let eres = fmap (addToList  (allRec' (tableMap inf) ((\(Just i)-> i) $ M.lookup o1 (pkMap inf))) <$> ) evs
      res2  <-  accumTds (pure res) eres
      element celem
          # sink UI.style (noneShow <$> (facts $ triding chw))
          # set style [("padding-left","10px")]
      fk <- UI.li # set  children [l, getElement box,filterInp,getElement chw,celem]
      let bres =  liftA2 (liftA2 FKT) (fmap (fmap Attr) <$> if isLeftJoin then makeOptional (S.toList rl)<$> fksel else fksel ) (if isLeftJoin then makeOptional tb1 <$> tcrud else tcrud )
      return $ TrivialWidget bres fk
fkUITable conn inf pgs path@(Path rl (FKJoinTable _  rel _ ) rr ) oldItems  tb@(AKT ifk [tb1]) =
  do
     fks <- mapM (\ix-> fkUITable conn inf pgs path ( join . fmap (\(AKT l m) -> (\mi -> FKT l mi) <$> atMay m ix )  <$>  oldItems) (FKT ifk tb1)) [0..4]
     sequence $ zipWith (\e t -> element e # sink UI.style (noneShow . maybe False (const True) <$> facts t)) (getElement <$> tail fks) (triding <$> fks)
     fksE <- UI.div # set children (getElement <$> fks )
     let bres = (fmap (\l -> AKT (fmap  (,SComposite $ V.fromList (fmap fst l)) <$> ifk) (fmap snd l)). allMaybes .  L.takeWhile (maybe False (const True))) <$> Tra.sequenceA ( fmap (fmap (\(FKT i j ) -> (head $ fmap (snd.unAttr) $ i, j)) ) . triding <$> fks)
     return $ TrivialWidget bres fksE


