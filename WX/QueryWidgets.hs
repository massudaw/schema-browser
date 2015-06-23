{-# LANGUAGE OverloadedStrings,ScopedTypeVariables,FlexibleContexts,ExistentialQuantification,TupleSections,LambdaCase,RankNTypes,RecordWildCards,DeriveFunctor,NoMonomorphismRestriction,RecursiveDo #-}
module WX.QueryWidgets where

import RuntimeTypes

-- import Reactive.Threepenny
-- import qualified Graphics.UI.Threepenny as UI
-- import Graphics.UI.Threepenny.Core hiding (delete)

import Graphics.UI.WX hiding (interval,Identity,when,newEvent,Event,swap,Key)
import Reactive.Banana hiding (Identity)
import Reactive.Banana.WX hiding (Identity,when)
import Tidings


import Data.Functor.Compose
import Data.Functor.Identity
import Control.Monad
import Control.Concurrent
import Data.Either
import Data.Bifunctor
import Data.Ord
import Control.Lens (Lens,(^?))
import qualified Control.Lens as Le
import Utils

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
import Text.Read hiding (get)
import Data.Text.Lazy (Text)
import Types hiding(label)
import Query
import Postgresql
import Data.Maybe
import Data.Time
import qualified Data.Vector as V
import Database.PostgreSQL.Simple.Time
import Data.Functor.Apply
import WX.Widgets
import Schema
import Step
import qualified Data.Foldable as F
-- import Data.Char
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
modifyTB  (InsertTB m) =  (Just m)
modifyTB  (DeleteTB m ) =  Nothing
modifyTB  (EditTB (TB1 m) n ) =  fmap ( mapTB1 (\i -> maybe i id $ L.find (\k -> (tbAttr $ fmap fst $ runIdentity $ getCompose k) == (tbAttr $ fmap fst $ runIdentity $ getCompose i) ) ls ) ) (Just n)
    where ls = F.toList m

generateFresh = do
  (e,h) <- newEvent
  let b = stepper Nothing e
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

{-
pluginUI window oinf initItems (StatefullPlugin n tname tf fresh (WrappedCall init ac ) ) = do
  let tdInput = (\i -> maybe False (const True) $ allMaybes $ fmap (\t -> (if fst t then join . fmap unRSOptional' else id ) $ fmap snd $ join $ fmap (indexTable  $ snd t) i) (fst $ head tf ) ) <$>   initItems
  headerP <- liftIO $ staticText window  [text := T.unpack n ]
  sink headerP [enabled :== (facts tdInput)]
  -- clickHeader <- event0 headerP command

  m <- liftIO $  foldl (\i (kn,kty) -> (\m -> createFresh  n tname m kn kty) =<< i ) (return $ pluginsMap oinf) (concat fresh)
  let inf = oinf {pluginsMap = m}
      freshKeys :: [[Key]]
      freshKeys = fmap (lookFresh  inf n tname . fst ) <$> fresh
  freshUI <- Tra.sequence $   zipWith  (\(input,output) freshs -> do
      (h,t :: Tidings t (Maybe (TB1 (Key,Showable))) ) <- generateFresh
      elems <- mapM (\fresh -> do
        let hasF l = any (\i -> (head $ head  (snd i)) == keyValue fresh) l
        case  (hasF input , hasF output)  of
             (True,False)-> Right <$> attrUITable window (const Nothing <$> initItems) [] (Attr fresh)
             (False,True)->  Left <$> attrUITable window (fmap (\v -> Attr . justError ("no key " <> show fresh <> " in " <>  show v ) . L.find ((== fresh) .fst) . F.toList $ v ) <$> t) [] (Attr fresh)
             (True,True)-> errorWithStackTrace $ "circular reference " <> show fresh
             (False,False)-> errorWithStackTrace $ "unreferenced variable "<> show fresh
           ) freshs
      let inp = fmap (TB1 . KV (PK [] [])) <$> foldr (liftA2 (liftA2 (:) )) (pure (Just [])) (fmap (fmap ( fmap (Compose .Identity )) . triding) (rights elems) )
      ei <- if not $ any (\i -> any (\fresh -> (head $ head  (snd i)) == keyValue fresh) freshs )  input
         then
          return $ TrivialWidget (pure (Just  $ TB1 mempty) ) undefined --  . widget <$> (liftIO $  panel parent [])
         else do
          inpPost <- liftIO $ button window [text := "Submit"]
          click <- event0 inpPost command
          trinp <- cutEvent click inp
          let ei = column 5 ((fmap trielem $ rights elems ) <> [widget inpPost])
          return $ TrivialWidget trinp ei
      return (h,(fmap snd output,t),(lefts elems) ,ei )
           ) tf freshKeys

  let el = column 0 (widget headerP : (concat $ fmap (\(_,_,o,i)-> concat $ [fmap trielem o ,[trielem i]]) freshUI ))
  liftIO $ forkIO  $ fmap (const ()) $ init $ foldl (\ unoldM (f,((h,htidings,loui,inp),action))  -> unoldM >>= (\unoldItems -> do
      let oldItems = foldl1 (liftA2 (liftA2 mergeTB1)) (triding inp: unoldItems)
      liftEvent (rumors oldItems) (\i -> action inf  i  (liftIO . h) )
      return  [oldItems]  ))  (return [initItems] ) ( zip tf $ zip freshUI ac)
  -- sink el [visible :== facts tdInput]
  return (el ,  (  ((\(_,o,_,_) -> o)$ last freshUI ) ))
-}

pluginUI parent inf unoldItems (BoundedPlugin2 n t f action) = do
  let oldItems = unoldItems
      -- outputItems = oldItems
  check <- liftIO $ checkBox parent []
  overwrite <- checkedWidget check (pure False)
  let tdInput = (\i -> maybe False (const True) $ allMaybes $ fmap (\t -> (if fst t then join . fmap unRSOptional' else id ) $ fmap snd $ join $ fmap (indexTable  $ snd t) i) (fst f) ) <$>  oldItems
      -- tdOutput1 = (\i -> maybe True (const False) $ allMaybes $ fmap (\f -> (if not(fst f ) then join . fmap unRSOptional' else id ) $ fmap snd $ join $ fmap (indexTable  $ snd f) i) (snd f) ) <$>  outputItems
      -- tdOutput= liftA2 (\i j -> if i then True else j) (triding overwrite)  tdOutput1
  -- let ovev =((\ j i  -> if i then j else Nothing) <$>   oldItems <*> tdOutput1)
  v <- currentValue (facts oldItems)
  headerP <- liftIO $ button parent [text := (T.unpack n) ]
  sink headerP [ enabled :== (facts tdInput)]
  click <- event0 headerP command
  let ecv = (facts oldItems<@ click )
      bcv = stepper v (facts oldItems <@ click )
  pgOut <- mapTEvent (action inf) (tidings bcv ecv)
  return (widget headerP, (fmap snd $ snd f ,   pgOut ))



intersectPredTuple  = (\i j -> intersectPred (textToPrim <$> keyType (fst i)) (textToPrim <$> keyType (fst j)) (snd i) (snd j))


lorder lo lref = allMaybes $ fmap (\k -> L.find (\i-> fst i == k ) lref) lo

attrUITable
  :: forall t  a . Frameworks t
     => Window a
     -> Tidings t (Maybe (TB Identity (Key,Showable)))
     -> [Event t (Maybe (TB Identity (Key,Showable)))]
     -> TB Identity Key
     -> Moment t  (TrivialWidget t (Maybe (TB Identity (Key, Showable))))
attrUITable  parent tAttr' evs (Attr i) = do
      l<- liftIO $ staticText parent [ text := (show i)]
      tdi' <- foldr (\i j ->  updateEvent  (fmap (Tra.traverse (Tra.traverse diffOptional ))) i =<< j) (return tAttr') evs
      let tdi = fmap (\(Attr i)-> snd i) <$>tdi'
      attrUI <- buildUI parent (textToPrim <$> keyType i) tdi
      let sp = row 0 [widget l,trielem attrUI ]
      let insertT = fmap (Attr .(i,)) <$> (triding attrUI)
      return $ TrivialWidget insertT sp
  where tAttr = fmap (\(Attr i)-> snd i) <$> tAttr'



buildUI :: forall a t . Frameworks t => Window a -> KType KPrim -> Tidings t (Maybe Showable ) -> Moment t (TrivialWidget t (Maybe Showable) )
buildUI parent i  tdi = case i of
         (KOptional ti) -> fmap (Just. SOptional) <$> buildUI parent ti (join . fmap unSOptional  <$> tdi)
         (KSerial ti) -> fmap (Just . SSerial) <$> buildUI parent ti ( join . fmap unSSerial <$> tdi)
         (KArray ti) -> do
            let arraySize = 10
            widg <- mapM (\i-> do
                         pn <- liftIO $ panel parent [fullRepaintOnResize := True]
                         wid <- buildUI pn ti (join . fmap (\a -> unSComposite a V.!? i ) <$> tdi )
                         liftIO$ set pn [layout := trielem wid]
                         return (pn,wid)
                         ) [0..arraySize]
            let tdcomp =  fmap (SComposite . V.fromList) .  allMaybes .  L.takeWhile (maybe False (const True)) <$> (Tra.sequenceA $ triding . snd <$> widg)
            sequence $ zipWith (\pn t ->  do
                               sink pn [visible :== (maybe False (const True) <$> facts t)]) (tail $ fst <$> widg) (triding . snd <$> widg)
            let composed = column 4 (fmap (widget . fst) widg)
            reactimate $ (\i -> repaintTree parent) <$> rumors tdcomp
            return  $ TrivialWidget tdcomp composed
         (KInterval ti) -> do
            inf <- fmap (fmap ER.Finite) <$> buildUI parent ti (fmap (\(SInterval i) -> inf' i) <$> tdi)
            sup <- fmap (fmap ER.Finite) <$> buildUI parent ti (fmap (\(SInterval i) -> sup' i) <$> tdi)
            lbdW <- liftIO $ checkBox parent []
            lbd <- fmap Just <$> checkedWidget lbdW(maybe False id . fmap (\(SInterval i) -> snd . Interval.lowerBound' $i) <$> tdi)
            ubdW <- liftIO $ checkBox parent []
            ubd <- fmap Just <$> checkedWidget ubdW (maybe False id .fmap (\(SInterval i) -> snd . Interval.upperBound' $i) <$> tdi)
            let composed = row 0 [trielem lbd ,trielem inf,trielem sup,trielem ubd]
            let td = (\m n -> fmap SInterval $  join . fmap (\i-> if Interval.null i then Nothing else Just i) $ liftF2 interval m n) <$> (liftA2 (,) <$> triding inf  <*> triding lbd) <*> (liftA2 (,) <$> triding sup <*> triding ubd)
            return $ TrivialWidget td composed
         {-(Primitive Position) -> do
            let addrs = (\(SPosition (Position (lon,lat,_)))-> "http://maps.google.com/?output=embed&q=" <> (HTTP.urlEncode $ show lat  <> "," <>  show lon )) <$>  tdi
            mkElement "iframe" # sink UI.src (maybe "" id <$> facts addrs) # set style [("width","99%"),("height","300px")]-}
         (Primitive PTimestamp) -> do
            itime <- liftIO $  getCurrentTime
            timeButton <- liftIO $ button parent  [text := "now"]
            click <- event0 timeButton command
            evCurr <-  mapIOEvent (fmap Just) (pure getCurrentTime <@ click )
            let  newEv = (unionWith const (rumors tdi) $ fmap (STimestamp . Finite .  utcToLocalTime utc) <$> evCurr)
            tdi2 <- addEvent newEv  tdi
            oneInput tdi2 [widget timeButton]
         (Primitive PDate) -> do
            itime <- liftIO $  getCurrentTime
            timeButton <- liftIO$ button parent  [text := "now"]
            click <- event0 timeButton command
            evCurr <-  mapIOEvent (fmap Just) (pure getCurrentTime <@ click )
            let  newEv = (unionWith const (rumors tdi) $ fmap (SDate . Finite . localDay . utcToLocalTime utc) <$> evCurr)
            tdi2 <- addEvent newEv  tdi
            oneInput tdi2 [widget timeButton]
         {- (Primitive (PMime mime)) -> do
           let binarySrc = (\(SBinary i) -> "data:" <> T.unpack mime <> ";base64," <>  (BSC.unpack $ B64.encode i) )
           clearB <- UI.button # set UI.text "clear"
           tdi2 <- addEvent (const Nothing <$> UI.click clearB) tdi
           let fty = case mime of
                "application/pdf" -> ("iframe",  [("width","100%"),("height","300px")])
                "image/jpg" -> ("img",[])
           f <- pdfFrame fty (maybe "" binarySrc <$> facts tdi2)
           fd <- UI.div # set children [clearB,f]
           return (TrivialWidget tdi2 fd)
-}
         z -> do
            oneInput tdi []
  where
    justCase i j@(Just _) = j
    justCase i Nothing = i
    oneInput  tdi elem = do
            inputUI <- liftIO$ entry parent  []
            tdInputUI <- reactiveTextEntry inputUI (forceDefaultType  <$> tdi )
            let pke = unions [readType i <$> rumors tdInputUI,rumors  tdi]
                pk = stepper (defaultType i)  pke
                pkt = tidings pk pke
            -- paintBorder inputUI (facts pkt)
            let sp = row 10 (widget inputUI : elem)
            return $ TrivialWidget pkt sp


forceDefaultType  (Just i ) = renderShowable i
forceDefaultType  (Nothing) = ""

diffOptional (SOptional i) = fmap (SOptional .Just)  . join $   unRSOptional' <$> i
diffOptional (SSerial i )  = fmap (SSerial .Just) . join $  unRSOptional' <$>i
diffOptional i   = Just i

tbCase :: forall t w . Frameworks t => Window w -> InformationSchema -> [Plugins]  ->(forall a . Lens (KV a) (KV a) [a] [a] ) ->  Int -> TB Identity Key -> Set Key -> [(TB Identity Key,TrivialWidget t (Maybe (TB Identity (Key,Showable))))] -> [([[[Text]]],Tidings t (Maybe (TB1 (Key,Showable))))]-> Tidings t (Maybe (TB1 (Key,Showable))) -> Moment t (TrivialWidget t (Maybe (TB Identity (Key,Showable))))
tbCase parent inf pgs td ix i@(FKT ifk _ _ tb1 ) created wl plugItens oldItems  = do
        let
            rr =  tablePKSet tb1
            table = justError "no table found" $ M.lookup rr $ pkMap inf
            rp = rootPaths'  (tableMap inf) table
            tbi = fmap (\v -> Compose . Identity . unTB . justError "FKT" . (^?  td . Le.ix ix ) . _unTB1  $ v) <$> oldItems
            thisPlugs = filter (any ((== (fmap (keyValue.unAttr.runIdentity.getCompose) ifk)) . head ) . fst) $  plugItens
            pfks =  (first ( filter (not . L.null ) . fmap (L.drop 1) . L.filter ((== (fmap (keyValue.unAttr.runIdentity.getCompose) ifk)) . head ))  . second ( fmap ( join .  fmap (fmap  (_fkttable . runIdentity . getCompose ) . findTB1 ((== ifk ) . fmap (fmap fst )  . tbAttr . runIdentity . getCompose  )))  ) <$> thisPlugs)
        res <- liftIO$ queryWith_  (fromAttr (fst rp)) (conn inf)(fromString $ T.unpack $ snd rp)
        fkUITable parent inf pgs created res pfks (filter (isReflexive .fst) wl) (fmap (runIdentity . getCompose ) <$>  tbi) i
tbCase f inf pgs td ix i@(IT ifk na tb1 ) created wl plugItens oldItems  = do
        let tbi = fmap (\v -> Compose . Identity . unTB . justError "FKT" . (^?  td . Le.ix ix ) . _unTB1 $ v) <$> oldItems
            thisPlugs = filter (any ((== (fmap (keyValue.unAttr.runIdentity.getCompose) ifk)) . head ) . fst) $  plugItens
            pfks =  (first ( filter (not . L.null ) . fmap (L.drop 1) . L.filter ((== (fmap (keyValue.unAttr.runIdentity.getCompose) ifk)) . head ))  . second ( fmap ( join .  fmap (fmap  (_fkttable . runIdentity . getCompose ) . findTB1 ((== ifk ) . fmap (fmap fst )  . tbAttr . runIdentity . getCompose  )))  ) <$> thisPlugs)
        iUITable f inf pgs pfks (fmap (runIdentity . getCompose ) <$>  tbi) i
tbCase f inf pgs td ix a@(Attr i) created wl plugItens oldItems = do
        let thisPlugs = filter (any ((== [keyValue i]).head) . fst) $  (fmap (fmap (fmap F.toList) ) <$> plugItens)
            tbi = fmap (\v -> unTB . justError "Attr".(^? td . Le.ix ix) . _unTB1  $ v) <$> oldItems
            evs  = (rumors . fmap ( join . fmap ( fmap Attr . L.find ((== i).fst )) )   <$>  (fmap snd thisPlugs))
        attrUITable f tbi evs a

uiTable
  :: forall t w . Frameworks t =>
      Window w
     -> InformationSchema
     -> [Plugins]
     -- Plugin Modifications
     -> Text
     -> [([[[Text]]],Tidings t (Maybe (TB1 (Key,Showable))))]
     -> TB1 Key
     -> Tidings t (Maybe (TB1 (Key,Showable)))
     -> Moment t (Layout ,Tidings t (Maybe (TB1 (Key,Showable))))
uiTable parent inf pgs tname plmods ftb@(TB1 (KV (PK k d) a)) oldItems = do
  let
      Just table = M.lookup tname  (tableMap inf)

  res <- mapM (pluginUI parent inf oldItems) (filter ((== rawName table ) . _bounds ) pgs)
  let plugmods = (snd <$> res ) <> plmods
  let mapMI f e = foldl (\jm (l,m)  -> do
                (w,ok) <- jm
                wn <- f l (unTB m) ok w plugmods oldItems
                return (w <> [(unTB m,wn)],S.fromList (kattr m ) <> ok)
              ) (return ([],e)) . zip [0..]
  fks <- do
      (i,pok) <- mapMI (tbCase parent inf pgs (kvKey.pkKey)) S.empty k
      (j,dok) <- mapMI (tbCase parent inf pgs (kvKey.pkDescription)) pok d
      (k,_) <-  mapMI (tbCase parent inf pgs (kvAttr)) dok a
      return $  KV (PK i j ) k
  let
      tableb :: Tidings t (Maybe (TB1 (Key,Showable)))
      tableb  = fmap (TB1 . fmap _tb) . Tra.sequenceA <$> Tra.sequenceA (triding .snd <$> fks)
  let listBody = column 0 (F.toList (trielem .snd <$> fks))
  {-plugins <-  if not (L.null (fst <$> res))
    then do
      -- pluginsHeader <- UI.div # set UI.text "Plugins"
      pure <$> UI.div # set children (pluginsHeader : (fst <$> res))
    else do
      return []
  -}
  return (listBody, tableb )


unLeftTB  = join . fmap  un
  where
      un (LeftTB1 i) = i
      un i = errorWithStackTrace ("unleft " <> show i )

crudUITable
  ::
     forall w t . Frameworks t => Window w
     -> InformationSchema
     -> [Plugins]
     -> Behavior t [TB1 (Key,Showable)]
     -> [([[[Text]]],Tidings t (Maybe (TB1 (Key,Showable))))]
     -> TB1 Key
     -> Tidings t (Maybe (TB1 (Key,Showable)))
     -> Moment t  (Layout ,[Event t (Modification Key Showable)])
crudUITable parent inf pgs res pmods ftb@(TB1 (KV (PK k d) a)) oldItems = do
  let  Just table = M.lookup (S.fromList $ findPK ftb) (pkMap inf)
  (listBody, tableb) <- uiTable parent inf pgs (tableName table) pmods ftb oldItems
  (panelItems,evsa)<- processPanelTable parent (conn inf)  (facts tableb) res table oldItems
  let body = column 0 [ listBody , panelItems ]
  return (body,evsa)


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

-- on :: (Ord a) => (b -> a) -> b -> b -> Ordering
onBin bin p x y = bin (p x) (p y)

processPanelTable
   :: forall a t . Frameworks t => Window a -> Connection
   -> Behavior t (Maybe (TB1 (Key, Showable)))
   -> Behavior t [TB1 (Key,Showable)]
   -> Table
   -> Tidings t (Maybe (TB1 (Key, Showable)))
   -> Moment t (Layout ,[Event t (Modification Key Showable)])
processPanelTable f conn attrsB res table oldItemsi = do
  let
      fkattrsB = fmap (concat . F.toList . fmap (attrNonRec . unTB) . _unTB1. tableNonRef ) <$> attrsB
      oldItems = fmap (concat . F.toList . fmap (attrNonRec .unTB) . _unTB1. tableNonRef ) <$> oldItemsi
      contains v  = maybe True (const False) . L.find (onBin (==) (_pkKey._kvKey . _unTB1) v )
  insertB <- liftIO $ button f [text := "INSERT" ]
  sink insertB [ enabled :== ( liftA2 (&&) (isJust <$> fkattrsB) (liftA2 (\i j -> maybe False (flip contains j) i  ) attrsB  res))]
  insertClick <- event0 insertB command
  editB <- liftIO$ button f [text := "EDIT" ]
  sink editB [ enabled :== (liftA2 (\i j -> maybe False (any fst . F.toList  ) $ liftA2 (tb1Diff (\l m -> if l  /= m then traceShow (l,m) (True,(l,m)) else (False,(l,m))) )  i j) (fmap tableNonRef <$> attrsB) (fmap tableNonRef <$> facts oldItemsi))]
  editClick <- event0 editB command
  deleteB <- liftIO $  button f [text := "DELETE" ]
  sink deleteB [ enabled :== (isJust <$> facts oldItems)]
  deleteClick <- event0 deleteB command
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

  let    spMap = fmap split . mapIOEvent id
  (evid,evir) <- spMap $ filterJust $ (fmap insertAction  <$> attrsB ) <@ (insertClick)
  (evdd,evdr) <- spMap $ filterJust $ (fmap deleteAction <$> facts oldItemsi) <@ deleteClick
  (eved,ever) <- spMap $ (editAction  <$> attrsB <*> (facts oldItemsi) ) <@ editClick
  let bd  = stepper [] (unions [evid,evdd,eved])
  errorOut <- liftIO $ staticText f []
  sink errorOut [text :== ( bd)]
  let transaction = column 5 [row 5  [widget insertB,widget editB,widget deleteB],widget errorOut]
  return (transaction ,[evir,ever,evdr])
{-
keyOptional (k,v) = (kOptional k ,SOptional $ Just v)

unKeyOptional (k  ,(SOptional v) ) = fmap (unKOptional k, ) v

kOptional (Key a  c d e) = Key a  c d (KOptional e)

unKOptional ((Key a  c d (KOptional e))) = (Key a  c d e )
unKOptional i = errorWithStackTrace ("unKOptional " <> show i)

unKArray (Key a  c d (KArray e)) = Key a  c d e
unKArray (Key a  c d (KOptional (KArray e) )) = Key a  c d e
-}


addToList  (InsertTB m) =  (m:)
addToList  (DeleteTB m ) =  L.delete m
addToList  (EditTB (TB1 m) n ) = (map (\e-> if  (e ==  n) then  mapTB1 (\i -> maybe i id $ L.find (\k -> (tbAttr $ fmap fst $ runIdentity $ getCompose k) == (tbAttr $ fmap fst $ runIdentity $ getCompose i) ) ls ) e  else e ))
    where ls = F.toList m

-- lookup pk from attribute list
editedMod :: (Traversable f ,Ord a) => f a ->  Maybe [(a,b)] -> Maybe (f (a,b))
editedMod  i  m=  join $ fmap (\mn-> look mn i ) m
  where look mn k = allMaybes $ fmap (\ki -> fmap (ki,) $  M.lookup ki (M.fromList mn) ) k

-- showFKE v =  UI.div # set text (L.intercalate "," $ fmap renderShowable $ F.toList $  _kvKey $ allKVRec $  snd <$> v)

-- showFK = (pure ((\v j ->j  # set text (L.intercalate "," $ fmap renderShowable $ F.toList $  _kvKey $ allKVRec $  snd <$> v))))

tablePKSet  tb1 = S.fromList $ fmap (unAttr . runIdentity . getCompose ) $ _pkKey $ _kvKey $ unTB1 $ tableNonRef tb1

flabel = label -- span # set UI.class_ (L.intercalate " " ["label","label-default"])

repaintTree :: forall a b . Window a -> IO ()
repaintTree ref = do
              windowReFitMinimal ref
              i <- get ref parent
              if objectIsNull i  then return () else repaintTree i
repaintChild :: forall a b . Window a -> IO ()
repaintChild ref = do
              windowReLayoutMinimal ref
              i <- get ref children
              if L.null i  then return () else mapM_ repaintChild i




sliderOffset f  = mdo
      offset <- liftIO $ entry f []
      sink offset [text :== show <$> offsetB]
      offsetEv <- eventText offset
      let offsetE =  (filterJust $ readMaybe <$> offsetEv )
          offsetB = stepper 0 offsetE
      return $ TrivialWidget (tidings offsetB offsetE) (widget offset)

iUITable
  ::
  forall b t . Frameworks t => Window b
  -> InformationSchema
  -> [Plugins]
  -- Plugin Modifications
  -> [([[[Text]]],Tidings t (Maybe (TB1 (Key,Showable))))]
  -- Selected Item
  -> Tidings t (Maybe (TB Identity (Key,Showable)))
  -- Static Information about relation
  -> TB Identity Key
  -> Moment t  (TrivialWidget t (Maybe (TB Identity (Key, Showable))))
iUITable parent inf pgs pmods oldItems  tb@(IT ifk na  (TB1 tb1))
    = do
      l <- liftIO $  staticText parent [text := (show $ unAttr .unTB <$> ifk)]
      -- l <- flabel # set text (show $ unAttr .unTB <$>   ifk)
      (celem,tcrud) <- uiTable parent inf pgs na pmods (TB1 tb1) (fmap _fkttable <$> oldItems)
      let fk = column 0 [widget l, celem]
      let bres =  fmap (fmap (IT (fmap (,SOptional Nothing ) <$> ifk) na  ) ) (tcrud)
      return $ TrivialWidget bres fk
iUITable parent inf pgs pmods oldItems  tb@(IT ifk na (LeftTB1 (Just tb1))) = do
   tr <- iUITable parent inf pgs (fmap (fmap unLeftTB) <$> pmods) (join . fmap (\(IT itk na (LeftTB1 l)) -> IT itk na <$>  l) <$>  oldItems) (IT ifk na tb1)
   return $  Just . maybe ((IT (fmap (,SOptional Nothing ) <$> ifk) na  (LeftTB1 Nothing))) (\(IT i na j ) -> IT i na (LeftTB1 (Just j)))  <$> tr
iUITable parent inf pgs plmods oldItems  tb@(IT ifk na (ArrayTB1 [tb1]))
    = do
      TrivialWidget offsetT offsetE <- sliderOffset parent
      l <- liftIO $  staticText parent [text := (show $ unAttr .unTB <$> ifk)]
      items <- mapM (\ix -> do
                      pn <- liftIO $ panel parent []
                      wid <- (iUITable pn inf pgs ((fmap (\i -> (\o ->  join .  fmap (\(ArrayTB1 tbl) -> atMay  tbl (ix + o) )) <$> offsetT <*> i))   <$> plmods) ((\o -> join . fmap (\(IT i na  (ArrayTB1 j)) -> IT i na <$>  atMay j (ix + o)   ))  <$> offsetT <*> oldItems)) (IT (ifk) na tb1)
                      liftIO$ set pn [layout := trielem wid]
                      return (pn,wid)
                      ) [0..8]

      let tds = triding . snd <$> items
          es = fst <$> items
      sequence $ zipWith (\e t -> do
                           sink e [visible :== ( maybe False (const True) <$> facts t)]
                           reactimate $ (\i -> do
                                        repaintChild e
                                        repaintTree e ) <$> rumors t
                         ) (tail es ) ( tds )
      let fk = row 4 [column 0 [widget l, offsetE ],  column 0 (widget . fst <$> items)]
      let bres2 = fmap (fmap (\(IT i na j ) -> j)) . allMaybes . L.takeWhile (maybe False (const True)) <$> Tra.sequenceA tds
          emptyFKT = Just . maybe (IT (fmap (,SOptional Nothing ) <$> ifk) na (ArrayTB1 []) ) id
          bres = (\o -> liftA2 (\l (IT _ na (ArrayTB1 m )) -> IT (fmap (,SOptional Nothing ) <$> ifk)  na (ArrayTB1 $ L.take o m <> l <> L.drop  (o + 9 ) m ))) <$> offsetT <*> bres2 <*> (emptyFKT <$> oldItems)
      reactimate $  (\i -> repaintTree parent) <$> rumors bres
      liftIO $ repaintTree parent
      return $ TrivialWidget bres fk


fkUITable
  ::
  forall w t . Frameworks t =>
  Window w
  -> InformationSchema
  -> [Plugins]
  -- Created Keys
  -> Set Key
  -- Table Data
  -> [TB1 (Key,Showable)]
  -- Plugin Modifications
  -> [([[[Text]]],Tidings t (Maybe (TB1 (Key,Showable))))]
  -- Same Table References
  -> [(TB Identity Key,TrivialWidget t (Maybe (TB Identity (Key,Showable))))]
  -- Relation Event
  -> Tidings t (Maybe (TB Identity (Key,Showable)))
  -- Static Information about relation
  -> TB Identity Key
  -> Moment t  (TrivialWidget t (Maybe (TB Identity (Key, Showable))))
fkUITable parent inf pgs created res plmods wl  oldItems  tb@(FKT ifk refl rel tb1@(TB1 _ ) )
    -- | not refl = do
        -- nonInjectiveSelection inf pgs created wl tb (pure res) oldItems
    | otherwise = mdo
      let
          relTable = M.fromList $ fmap swap rel
          tdipre = fmap _fkttable <$> oldItems
      tdi <- foldr (\i j -> updateEvent  (fmap (Tra.traverse (Tra.traverse diffOptional ))) i =<< j)  (return tdipre) (rumors . snd <$> plmods)
      l <- liftIO $  staticText parent [text := (show $ unAttr .unTB <$> ifk)]
      {-filterInp <- UI.input
      filterInpBh <- stepper "" (UI.valueChange filterInp )
          filterInpT = tidings filterInpBh (UI.valueChange filterInp)
          filtering i  = T.isInfixOf (T.pack $ toLower <$> i) . T.toLower . T.intercalate "," . fmap (T.pack . renderShowable) . F.toList . fmap snd-}
      let
          Just table = M.lookup (S.fromList $ findPK tb1 ) (pkMap inf)
      listBox <- liftIO $ comboBox parent []
      ol <- reactiveComboDisplay listBox dataList bselection  dataViewer
      let evsel = unionWith const (rumors $ join <$> ol) (rumors tdi)
          prop = stepper Nothing evsel
      let tds = tidings prop evsel
      pan <-liftIO $  panel parent  [visible := False]
      (celem,tableb) <- uiTable pan inf pgs (rawName table) plmods tb1  tds
      (panelItems,evs) <- processPanelTable pan (conn inf) (facts tableb) res2 table tds
      let
          dataList = ((Nothing:) <$>  fmap (fmap Just) (res2))
          bselection = (fmap Just <$> st)
          dataViewer = (pure (maybe "" showFK))
          sel = unions $ [(rumors $ join <$> ol), rumors tdi] <> (fmap modifyTB <$> evs)
      let st = stepper Nothing sel
          res2  = accumB res  ( unions $ fmap addToList <$> evs)
      let
        reorderPK l = fmap (\i -> justError "reorder wrong" $ L.find ((== i).fst) l )  (unAttr . unTB <$> ifk)
        lookFKsel (ko,v)=  (kn ,transformKey (textToPrim <$> keyType ko ) (textToPrim <$> keyType kn) v)
          where kn = justError "relTable" $ M.lookup ko relTable
        box = TrivialWidget (tidings st sel) (widget listBox )
        fksel =  (\box -> fmap (\ibox -> FKT (fmap (_tb . Attr). reorderPK . fmap lookFKsel $ ibox) refl rel (fromJust box) ) .  join . fmap findPKM $ box ) <$>  ( triding box)
      check <- liftIO $ checkBox parent []
      chw <- checkedWidget check  (pure False)
      liftIO $ set pan [ layout := boxed  (T.unpack $ maybe (tableName table) id (rawTranslation table)) $column 0 [celem ,panelItems]]
      sink pan [visible :== (facts $ triding chw)]
      reactimate $ (\_-> do
                   repaintChild parent
                   repaintTree  pan ) <$> (rumors $ triding chw)
      let fk = column 0  [row 5 [widget l, trielem box ,{-filterInp,-}trielem chw],  marginLeft $  widget pan ]
      return $ TrivialWidget fksel fk

fkUITable parent inf pgs created res plmods  wl oldItems  tb@(FKT ilk refl rel  (LeftTB1 (Just tb1 ))) = do
    tb <- fkUITable parent inf pgs created res (fmap (fmap unLeftTB) <$> plmods)  wl (join . fmap (\(FKT ifk refl rel  (LeftTB1 tb)) -> liftA2 (\ik -> FKT ik  refl (first unKOptional <$> rel)) (traverse (traverse (unKeyOptional )) ifk) tb) <$> oldItems)  (FKT (fmap unKOptional<$> ilk) refl (first unKOptional <$> rel) tb1)
    let emptyFKT = (FKT (fmap (,SOptional Nothing)  <$> ilk) refl rel (LeftTB1 Nothing))
    return $ (Just . maybe  emptyFKT (\(FKT ifk refl rel  tb)-> FKT (fmap keyOptional <$> ifk) refl rel (LeftTB1 (Just tb)))) <$> tb
fkUITable parent inf pgs created res2 plmods  wl oldItems  tb@(FKT ifk@[_] refl rel  (ArrayTB1 [tb1]) ) = do
     TrivialWidget offsetT offsetE <- sliderOffset parent
     l <- liftIO $  staticText parent [text := (show $ unAttr .unTB <$> ifk)]
     let indexItens ix = (\o -> join . fmap (\(FKT [l] refl _ (ArrayTB1 m)  )  -> (\li mi ->  FKT  [li] refl (fmap (first unKArray) rel) mi ) <$> (traverse (indexArray (ix + o) )   l) <*> (atMay (L.drop o m) ix) ))  <$>  offsetT <*> oldItems
         fkst = FKT (fmap (fmap unKArray ) ifk) refl (fmap (first (unKArray)) rel)  tb1
         rr = tablePKSet tb1
         rp = rootPaths'  (tableMap inf) (fromJust $ M.lookup rr $ pkMap inf )
     res <- liftIO$ queryWith_ (fromAttr (fst rp)) (conn  inf) (fromString $ T.unpack $ snd rp)

     fks <- mapM (\ix-> do
                   pn <- liftIO $ panel parent [fullRepaintOnResize := True]
                   wid <- fkUITable pn inf pgs S.empty res (fmap (\t -> liftA2 (\o ->   join . fmap (\(ArrayTB1 tbl)-> atMay  tbl (ix + o) )) offsetT t ) <$> plmods ) [] (indexItens ix) fkst
                   liftIO$ set pn [layout := trielem wid]
                   return (pn,wid)
                 ) [0..8]
     -- l <- flabel # set text (show $ unAttr .unTB <$>   ifk)
     sequence $ zipWith (\e t -> do
                        sink e [visible :== ( maybe False (const True) <$> facts t)]
                        reactimate $ (\i -> do
                                     repaintChild e
                                     repaintTree e ) <$> rumors t
                        ) (fst <$> tail fks) (triding . snd <$> fks)
     let
         fksE = row 0 [ column 0 [widget l , offsetE],  column 0 (widget . fst <$> fks)]

     let bres2 =   allMaybes .  L.takeWhile (maybe False (const True))  <$> Tra.sequenceA (fmap (fmap (\(FKT i _ _ j ) -> (head $ fmap (snd.unAttr.unTB) $ i,  j)) )  . triding .snd <$> fks)
         emptyFKT = Just . maybe (FKT (fmap (,SComposite (V.empty)) <$> ifk) refl rel (ArrayTB1 []) ) id
         bres = (\o -> liftA2 (\l (FKT [lc] refl rel (ArrayTB1 m )) -> FKT ( fmap  ( (,SComposite $ V.fromList $  ((L.take o $ F.toList $ unSComposite $snd $ (unAttr $ runIdentity $ getCompose lc)  )<> fmap fst l <> (L.drop (o + 9 )  $ F.toList $ unSComposite $snd $ (unAttr $ runIdentity $ getCompose lc)  )))) <$> ifk) refl rel (ArrayTB1 $ L.take o m <> fmap snd l <> L.drop  (o + 9 ) m ))) <$> offsetT <*> bres2 <*> (emptyFKT <$> oldItems)
     return $  TrivialWidget bres  fksE
{-
fkUITable  _ _ _ _  _ _ _ _ = errorWithStackTrace "akUITable not implemented"
-}
interPoint ks i j = all (\(l,m) -> justError "interPoint wrong fields" $ liftA2 intersectPredTuple  (L.find ((==l).fst) i ) (L.find ((==m).fst) j)) ks


indexArray ix s =  atMay (unArray s) ix

unArray (k,SComposite s) = (unKArray k,) <$> V.toList s
unArray o  = errorWithStackTrace $ "unArray no pattern " <> show o


-- Create non
nonInjectiveSelection
  ::
  forall t w . Frameworks t =>
  Window w
  -> InformationSchema
  -> [Plugins ]
  -> Set Key
  -> [(TB Identity Key,TrivialWidget t (Maybe (TB Identity (Key,Showable))))]
  -> TB Identity Key
  -> Tidings t [TB1 (Key,Showable)]
  -> Tidings t (Maybe (TB Identity (Key,Showable)))
  -> Moment t  (TrivialWidget t (Maybe (TB Identity (Key,Showable ))))
nonInjectiveSelection parent inf pgs created wl  attr@(FKT fkattr refl ksjoin tbfk ) lks selks
  | all isPrim (keyType . unAttr.unTB<$> fkattr ) = do
      let
          fkattr' = unTB <$> fkattr
          oldASet :: Set Key
          oldASet = S.fromList (filter (flip S.member created) $ unAttr <$> fkattr' )
          iold :: Tidings t ([Maybe [(Key,Showable)]])
          iold  =    (Tra.sequenceA $ fmap (fmap ( kattr . _tb ) ) . triding .snd <$> L.filter (\i-> not . S.null $ S.intersection (S.fromList $ kattr $ _tb $ fst $ i) oldASet) wl)
          sel = fmap (\i->  (Just . unAttr .unTB<$> _tbref i) ) . fmap (fmap snd) <$> selks
      (vv ,ct, els) <- inner tbfk sel  fkattr' iold
      l<- liftIO $ staticText parent [ text := (show $ unAttr <$> fkattr')]
      let o =  row 0 (widget l : els)
      let bres = liftA2 (liftA2 (\i j-> FKT (fmap (_tb.Attr) i)  refl ksjoin j)) vv ct
      return $ TrivialWidget bres o
  | otherwise = errorWithStackTrace (show attr)
  where inner tbfk sel fkattr' iold = mdo
            let
                -- o1 = tablePKSet tbfk
                vv =  join . fmap (lorder (unAttr <$> fkattr') ) . fmap concat . allMaybes  <$> iold
                tb = (\i j -> join $ fmap (\k-> L.find ((\(TB1 (KV (PK  l _ ) _ ))-> interPoint ksjoin k  (unAttr . unTB <$> l)) ) i) j ) <$> lks <*> vv
            liw <- liftIO$  comboBox parent []
            li <- reactiveComboDisplay liw res2 (facts tb)  (pure showFK)
            (ce,evs) <- crudUITable parent inf pgs res2 [] tbfk  tb
            let eres = fmap (addToList   <$> ) evs
            inires2 <- initial (facts lks)
            let res2  = accumB inires2 (unions ((const <$> rumors lks ) : eres))
            -- box <- liftIO $ checkBox parent []
            check <- liftIO $ checkBox parent []
            chw <- checkedWidget check (pure False)
            {-element ce
              # sink UI.style (noneShow <$> (facts $ triding chw))
              # set style [("paddig-left","10px")]
              -}
            return (vv,tb, [widget liw,trielem chw,ce])

-- pdfFrame fty pdf = mkElement (fst fty ) UI.# sink UI.src pdf  UI.# UI.set style (snd fty)

showFK = (L.take 100 . L.intercalate "," . (F.toList . fmap (renderShowable . snd ) . _kvKey . allKVRec))

allNonEmpty [] = Nothing
allNonEmpty l = Just  l

sorting :: Bool -> [Key] -> [TB1 (Key,Showable)]-> [TB1 (Key,Showable)]
sorting b ss  =  L.sortBy (ifApply b flip (comparing (\i ->  fmap (\s -> fmap snd $ F.find ((== s).fst) i  ) ss) ))
  where ifApply True i =  i
        ifApply False _ = id

