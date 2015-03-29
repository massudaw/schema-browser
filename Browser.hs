{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE Arrows #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE NoMonomorphismRestriction,UndecidableInstances,FlexibleContexts,OverloadedStrings ,TupleSections, ExistentialQuantification #-}

import Query
-- import Incendio
import Step
import Pdf
import Siapi3
import CnpjReceita
import GHC.Generics
import qualified Network.HTTP as HTTP
import Network.Browser
import Widgets
import Data.Functor.Apply
import System.Directory
import Debug.Trace
import Data.Ord
import Data.Tuple
import OAuth
import Data.Time.Format
import System.Locale
import Data.Aeson
import Utils
import Schema
import Data.Char (toLower)
import Gpx
import GHC.Int
import Data.Functor.Compose (Compose(..))
import PandocRenderer
import Data.Unique
import Control.Monad.Trans.Class as C
import Control.Monad.Trans.Maybe
import Control.Monad
import Postgresql
import Data.Aeson as A
import Data.Maybe
import Data.Distributive
import Data.Functor.Identity
import Text.Read
import qualified Data.HashMap.Strict as HM
import Data.Typeable
import Data.Time.Parse
import Reactive.Threepenny
import           Database.PostgreSQL.Simple.Arrays as Arrays
import Data.Graph(stronglyConnComp,flattenSCCs)
import Control.Exception
import           Data.Attoparsec.Char8 hiding (Result)
import Data.Traversable (mapAccumL,Traversable,traverse)
import qualified Data.Traversable as Tra
import Warshal
import Data.Time.LocalTime
import Data.IORef
import Control.Monad((>=>),void,mapM,replicateM,liftM,join)
import Data.Functor.Compose
import qualified Database.PostgreSQL.Simple.TypeInfo.Static as TI
import qualified Data.List as L
import Data.Vector(Vector)
import qualified Data.Vector as V
import qualified Data.Interval as Interval
import qualified Data.ExtendedReal as ER
import qualified Data.ByteString.Char8 as BS
import qualified Data.ByteString.Lazy.Char8 as BSL
import Data.Time

import Reactive.Threepenny
import qualified Graphics.UI.Threepenny as UI
import Graphics.UI.Threepenny.Core hiding (get,delete)
import Data.Monoid hiding (Product(..))
import Data.Time.Parse

import System.IO.Unsafe
import Debug.Trace
import qualified Data.Foldable as F
import qualified Data.Text.Lazy as T
import qualified Data.Text.Lazy.IO as T
import Data.ByteString.Lazy(toStrict)
import Data.Text.Lazy.Encoding
import qualified Data.Text.Encoding as TE
import qualified Data.Text as TE
import Data.Text.Lazy (Text)
import qualified Data.Set as S
import Data.Set (Set)


import Database.PostgreSQL.Simple
import Database.PostgreSQL.Simple.Time
import Database.PostgreSQL.Simple.Ok
import Database.PostgreSQL.Simple.FromField as F
import qualified Database.PostgreSQL.Simple.ToField as TF
import qualified Database.PostgreSQL.Simple.FromRow as FR
import Data.GraphViz (preview)
import qualified Data.Map as M
import Blaze.ByteString.Builder(fromByteString)
import Blaze.ByteString.Builder.Char8(fromChar)
import Data.Map (Map)
import Data.String

import GHC.Show
import Data.Functor.Classes

import Control.Arrow
import Data.ByteString.Search (replace)
import Crea

setup
     ::  Window -> UI ()
setup w = void $ do
  return w # set title "Data Browser"
  (evDB,chooserDiv) <- databaseChooser
  body <- UI.div
  getBody w #+ [element chooserDiv , element body]
  onEvent evDB $ (\(conn,inf@(_,baseTables,_,schema,invSchema,graphP))-> do
    let k = M.keys baseTables
    let pg = catMaybes [documentSprinklerProject inf , pluginOAuth inf ,pluginWapp inf ,pluginBradescoCsv inf,pluginItauTxt inf ,pluginAndamentoId inf  ]
    span <- chooserKey  conn pg inf k
    element body # set UI.children [span] )

layout  infT = do
  vis <- UI.div # set UI.id_ "visualization"
  let draw inf  =
        let
            g = graphP inf
            v :: [(Int,Set Key)]
            v = zip [0..] (L.nub $ hvertices g <> tvertices g)
            e = filter  (\case {(Path _ _ _)-> True ; i -> False}) $ concat $ fmap snd $ M.toList $ edges g
            vmap = M.fromList $ swap <$>  v
            genVertices (i,t ) = object [ "id" .= i, "label" .= T.intercalate "," (F.toList (S.map keyValue t)) ]
            genEdges (Path i (FKJoinTable m _ l)  j ) = object [ "from" .= lid i , "to" .= lid j  , "label" .= (tableName m <> " join " <> tableName l ) ]
            genEdges (Path i (FetchTable  l)  j ) = object [ "from" .= lid i , "to" .= lid j  , "label" .= tableName l ]
            lid t = justError ("no key " <> show t) (M.lookup t vmap)
            nodesJSON = "var nodes = " <> encode (genVertices <$> v) <> ";"
            edgesJSON = "var edges = " <> encode (genEdges <$> e) <> ";"
            graphJSON = "<script> " <> (BSL.unpack (nodesJSON <> edgesJSON))  <> "var container = document.getElementById('visualization');  var data = { nodes: nodes,edges: edges}; var options = { hierarchicalLayout : { layout : 'direction' } , edges : { style : 'arrow'}} ;  var network = new vis.Network(container, data, options ); </script> "
        in graphJSON
  script <- UI.div # sink UI.html (maybe "" draw <$> infT)
  UI.div # set children [vis,script]

listDBS = do
  connMeta <- connectPostgreSQL ("user=postgres dbname=postgres")
  dbs :: [Only Text]<- query_  connMeta "SELECT datname FROM pg_database  WHERE datistemplate = false"
  M.fromList <$> mapM (\db -> do
        connDb <- connectPostgreSQL ("user=postgres dbname=" <> toStrict (encodeUtf8 db))
        schemas :: [Only Text] <- query_  connDb "SELECT schema_name from information_schema.schemata"
        return (db,filter (not . (`elem` ["information_schema","pg_catalog","pg_temp_1","pg_toast_temp_1","pg_toast","public"])) $ fmap unOnly schemas)) (fmap unOnly dbs)

databaseChooser = do
  dbs  <- liftIO$ listDBS
  dbsW <- UI.listBox (pure $ concat $ fmap (\(i,j) -> (i,) <$> j) $ M.toList dbs ) (pure Nothing ) (pure (\i -> UI.div # set text (show i)))
  load <- UI.button # set UI.text "Connect" # sink UI.enabled (facts (isJust <$> UI.userSelection dbsW) )
  let genSchema (dbN,schemaN) = do
        conn <- connectPostgreSQL ("user=postgres dbname=" <> toStrict ( encodeUtf8 dbN ))
        inf@(k,baseTables,_,schema,invSchema,graphP) <- keyTables conn  schemaN
        return (conn,inf)
  chooserT <-  mapT (traverse genSchema) (UI.userSelection dbsW )
  let chooserEv = facts chooserT <@ UI.click load
  ll <- layout (fmap snd <$> facts chooserT )
  chooserDiv <- UI.div # set children [getElement dbsW,load,ll]
  return $ (filterJust chooserEv,chooserDiv)

-- TODO: Remove Normalization to avoid inconsistencies

unSSerial (SSerial i ) = i
unSSerial i = traceShow ("No Pattern Match SSerial-" <> show i) Nothing

unSOptional (SOptional i ) = i
unSOptional i = traceShow ("No Pattern Match SOptional-" <> show i) Nothing

unRSOptional (SOptional i ) = join $ fmap unRSOptional i
unRSOptional i = traceShow ("No Pattern Match SOptional-" <> show i) Nothing

unRSOptional' (SOptional i ) = join $ unRSOptional' <$> i
unRSOptional' (SSerial i )  = join $ unRSOptional' <$>i
unRSOptional' i   = Just i


unSOptional' (SOptional i ) = i
unSOptional' (SSerial i )  = i
unSOptional' i   = Just i

takeWhileJust snoc empty l = step l
  where
      step (x:xs) =  liftA2 test x (step xs)
      step [] =  pure empty
      test (Just x) os =  snoc  os x
      test Nothing os = os

applyUI el f = (\a-> getWindow el >>= \w -> runUI w (f a))

buildUI i  tdi = case i of
         (KOptional ti) -> fmap ((Just. SOptional) ) <$> buildUI ti (join . fmap unSOptional <$> tdi)
         (KSerial ti) -> fmap (Just . SSerial) <$> buildUI ti ( join . fmap unSSerial <$> tdi)
         {-
         (KArray ti)  -> do
            inputUI <- UI.textarea # sink UI.value (facts (forceDefaultType  <$> tdi)) # set UI.style [("width","300px"),("height","60px"),("vertical-align","middle")]
            let pke = foldl1 (unionWith justCase) [readType i <$> UI.valueChange inputUI,rumors  tdi]
            pk <- stepper (defaultType i)  pke
            let pkt = tidings pk pke
            return $ TrivialWidget pkt inputUI
            -}
         (KArray ti) -> do
            el <- UI.div
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
            inf <- buildUI ti (fmap (\(SInterval i) -> inf' i) <$> tdi)
            sup <- buildUI ti (fmap (\(SInterval i) -> sup' i) <$> tdi)
            composed <- UI.span # set UI.children (fmap getElement [inf,sup])
            let td = (\m n -> fmap SInterval $  liftF2 interval' m n) <$> triding inf  <*> triding sup
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



crudUITable
  :: Connection
     -> InformationSchema
     -> [Plugins]
     -> TB1 Key
     -> Tidings (Maybe (TB1 (Key,Showable)))
     -> UI (Element,Tidings (Maybe (TB1 (Key,Showable))),[Event (Modification Key Showable)])
crudUITable conn inf pgs tb@(TB1 (KV (PK k d) a)) oldItems = do
  let
      tbCase td ix i@(FKT ifk _) = fkUITable conn inf pgs ((\(Just i)-> i) $ L.find (\(Path ifkp _ _) -> S.fromList ifk == ifkp) $ S.toList $ rawFKS table) (fmap ((!!ix) .td .unTB1) <$> oldItems) i
      tbCase td ix a@(Attr i) = attrUITable (fmap ((!!ix) .td .unTB1) <$> oldItems)  a
      mapMI f = Tra.mapM (uncurry f) . zip [0..]
      Just table = M.lookup (S.fromList $findPK tb) (pkMap inf)
  fks <- liftA3 (\i j k -> KV (PK i j ) k)
      (mapMI (tbCase (pkKey.kvKey)) k)
      (mapMI (tbCase (pkDescription.kvKey)) d)
      (mapMI (tbCase (kvAttr)) a)
  let tb = fmap TB1 . Tra.sequenceA <$> Tra.sequenceA (snd <$> fks)
  res <- mapM (pluginUI' conn inf tb ) (filter (\(BoundedPlugin _ (t,_) _ ) -> t == tableName table) pgs)
  (panelItems,evsa)<- processPanelTable conn (facts tb) table oldItems
  listBody <- UI.ul
    # set children (F.toList (fst <$> fks))
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
  let fkattrsB = fmap (concat . F.toList .fmap attrNonRec .unTB1 ) <$> attrsB
      oldItems = fmap (concat . F.toList .fmap attrNonRec .unTB1 ) <$> oldItemsi
      efkattrsB :: Behavior (Maybe [(Key,Showable)])
      efkattrsB = fmap (catMaybes . concat .F.toList. fmap attrNonRec . unTB1 ) <$> liftA2 (liftA2 (liftF2  (\i j -> if i == j then Nothing else Just i))) attrsB (facts oldItemsi)
  deleteB <- UI.button  # sink UI.enabled (isJust <$> facts oldItems) # set text "DELETE"
  editB <- UI.button # sink UI.enabled (liftA2 (&&) (isJust <$>  efkattrsB) (isJust <$> fkattrsB)) # set text "EDIT"
  insertB <- UI.button  # sink UI.enabled (isJust <$> fkattrsB) # set text "INSERT"
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
              i = concat . F.toList .fmap attrNonRec .unTB1 $ ip
          res <- catch (Right <$> insertPK fromShowableList conn i table) (\e -> return $ Left (show $ traceShowId (e :: SomeException) ))
          return $ (\v -> Insert $ Just $ (v <> (filter (not . flip elem (fst <$> v) . fst) i2))) <$> res

      evir, ever ,evdr:: Event (Modification Key Showable)
      (evid,evir) = spMap $ filterJust $ (fmap insertAction  <$> attrsB ) <@ (UI.click insertB)
      (evdd,evdr) = spMap $ (deleteAction <$> facts oldItemsi) <@ UI.click deleteB
      (eved,ever) = spMap $ (editAction  <$> attrsB <*> (facts oldItemsi) ) <@ UI.click editB
      spMap = split . unsafeMapIO id

  return ([insertB,editB,deleteB],[evir,ever,evdr])


attrUITable
  :: Tidings (Maybe (TB (Key,Showable)))
     -> TB Key
     -> UI
          (Element, Tidings (Maybe (TB (Key, Showable))))
attrUITable  tAttr' (Attr i) = do
      l<- UI.span # set text (show i)
      let tdi = tAttr -- foldrTds justCase plugItens [tAttr]
          justCase i j@(Just _) = j
          justCase i Nothing = i
      attrUI <- buildUI (textToPrim <$> keyType i) tdi
      expandEdit <- checkedWidget (pure False)
      let
          ei (Just a) = Just a
          ei Nothing = defaultType (keyType i)
      -- e <- buildUI (textToPrim <$>keyType i) tAttr
      -- eplug <- buildUI (textToPrim <$>keyType i) (pure Nothing)
      -- element e # sink UI.style (noneShowSpan <$> (facts $ triding expandEdit)) # set UI.enabled False
      -- element eplug # sink UI.style (noneShowSpan <$> (facts $ triding expandEdit)) # set UI.enabled False
      paint l (facts $ triding attrUI )
      sp <- UI.li # set children [l,getElement attrUI {-, getElement expandEdit,getElement e,getElement eplug-}]
      let insertT = fmap (Attr .(i,)) <$> (triding attrUI)
          editT = liftA2 (\n m -> join $ liftA2 (\i j -> if i == j then Nothing else Just j) n m) tAttr' insertT
      return (sp,insertT)
  where tAttr = fmap (\(Attr i)-> snd i) <$> tAttr'


findPK = concat . fmap attrNonRec . pkKey  . kvKey . unTB1

attrNonRec (FKT ifk _ ) = ifk
attrNonRec (Attr i ) = [i]

tableNonrec (TB1 k ) = concat $ F.toList $ kvAttr $ fmap attrNonRec k

makeOptional :: Functor f => f Key -> Maybe (f (Key,Showable)) -> Maybe (f (Key,Showable))
makeOptional def (Just i ) = Just $ fmap keyOptional i
makeOptional def Nothing = Just $ fmap (\i -> (i,SOptional Nothing)) def


fkUITable
  :: Connection
  -> InformationSchema
  -> [Plugins]
  -> Path (Set Key) (SqlOperation Text)
  -> Tidings (Maybe (TB (Key,Showable)))
  -> TB Key
  -> UI (Element,Tidings (Maybe (TB (Key, Showable))))
fkUITable conn inf pgs (Path rl (FKJoinTable _  rel _ ) rr ) oldItems  tb@(FKT ifk tb1) = mdo
      let
          o1 = S.fromList $ findPK tb1
          isLeftJoin = any isKOptional $  keyType <$> F.toList rl
          relTable = M.fromList $ fmap swap rel
          tdi :: Tidings (Maybe (TB1  (Key,Showable)))
          tdi =  (if isLeftJoin then join . fmap (\(FKT _ t) -> Tra.sequence $  unkeyOptional  <$> t ) else fmap (\(FKT _ t )-> t) ) <$> oldItems
      res <- liftIO $ projectKey conn inf (projectAllRec' (tableMap inf )) o1
      l <- UI.span # set text (show ifk)

      filterInp <- UI.input
      filterInpBh <- stepper "" (onEnter filterInp )
      let filterInpT = tidings filterInpBh (onEnter filterInp)
          filtering i= filter (L.isInfixOf (toLower <$> i) . fmap toLower . show )
          listRes = filtering <$> filterInpT <*> res2

      box <- if isLeftJoin
                then optionalListBox  listRes tdi (pure (maybe (UI.div ) (\v-> UI.span # set text (L.intercalate "," $ fmap renderShowable $ F.toList $  kvKey $ allKVRec $  snd <$> v))  ))
                else wrapListBox listRes tdi (pure ((\v-> UI.span # set text (L.intercalate "," $ fmap renderShowable $ F.toList $  kvKey $ allKVRec $  snd <$> v))))
      let
        lookFKsel (ko,v)= (kn ,transformKey (textToPrim <$> keyType ko ) (textToPrim <$> keyType kn) v)
          where kn = (\(Just i)-> i) $ M.lookup ko relTable
        fksel = fmap (fmap lookFKsel ) <$>  (fmap findPK  <$> triding box)
        tdsel = fmap (\i -> FKT (zip ifk . fmap snd  . findPK $ i ) i)  <$>  triding box
        edited = liftA2 (\i j -> join $ liftA2 (\i j-> if  i == j then Nothing else Just j ) i j) oldItems tdsel
      paint (getElement l) (facts $ if isLeftJoin then makeOptional (S.toList rl)<$> fksel else fksel )
      chw <- checkedWidget (pure False)
      (celem,tcrud,evs) <- crudUITable conn inf pgs (if isLeftJoin then unKOptional <$> tb1  else tb1 ) (triding box)
      let eres = fmap (addToList  (allRec (tableMap inf) ((\(Just i)-> i) $ M.lookup o1 (pkMap inf))) <$> ) evs
      res2  <-  accumTds (pure $ if isLeftJoin then  res else res) eres
      element celem
        # sink UI.style (noneShow <$> (facts $ triding chw))
        # set style [("padding-left","10px")]
      fk <- UI.li # set  children [l, getElement box,filterInp,getElement chw,celem]
      let bres =  liftA2 (liftA2 FKT) (if isLeftJoin then makeOptional (S.toList rl)<$> fksel else fksel ) (if isLeftJoin then makeOptional tb1 <$> tcrud else tcrud )
      return (fk,bres)


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


forceDefaultType  (Just i ) = renderShowable i
forceDefaultType  (Nothing) = ""

paint e b = element e # sink UI.style (greenRed . isJust <$> b)
paintBorder e b = element e # sink UI.style (greenRed . isJust <$> b)
  where
      greenRed True = [("border-color","green")]
      greenRed False = [("border-color","red")]

data Plugins
  = Plugins
  { _name :: String
  ,_inputs :: (Table, S.Set Key)
  , _action :: Connection -> InformationSchema -> Tidings (Maybe [(Key,Showable)]) -> UI (Element,Tidings (Maybe (Map Key Showable)) )
  }
  | BoundedPlugin
  { _name :: String
  , _bounds :: (Text,([(Bool,[[Text]])],[(Bool,[[Text]])]))-- PluginBoundary Table Key,PluginBoundary Table Key)
  , _boundedAction :: Connection -> InformationSchema -> Tidings (Maybe (TB1 (Key,Showable))) -> UI Element
  }

data  PollingPlugins
  = PollingPlugins
  { _pollingName :: String
  , _pollingTime :: Int
  , _pollingInputs :: (Table, S.Set Key)
  , _pollingAction :: Connection -> InformationSchema ->  Tidings [[(Key,Showable)]] -> UI (Element,Tidings (Maybe (Map Key Showable)) )
  }
  | BoundedPollingPlugins
  { _pollingName :: String
  , _pollingTime :: Int
  , _pollingBounds :: (Text,([(Bool,[[Text]])],[(Bool,[[Text]])]))
  , _pollingBoundedAction :: Connection -> InformationSchema ->  Tidings [TB1 (Key,Showable)] -> UI Element
  }

attrSet pkm (Raw s t pk desc fk allI) =  pk <> allI <>  foldr mappend mempty (catMaybes $ pathTable <$> (F.toList fk) )
    where pathTable (Path o t e) = attrSet pkm <$> M.lookup e pkm

pollingUI' conn inf listRes p@(BoundedPollingPlugins n deftime (table,f) a) = do
  let plug = a conn inf
  headerP <- UI.div # set text n
  b <- UI.button # set UI.text "Submit"
  let  convert = 60000
  inp <- UI.input # set UI.value  (show deftime)
  inter <- stepper (deftime*convert) (filterJust  $ fmap (fmap (*convert).readMaybe) (UI.valueChange inp) )
  tmr <- UI.timer # sink UI.interval  inter
  staT <- UI.button # set text "Start" # set UI.enabled True
  stoT <- UI.button # set text "Stop" # set UI.enabled False
  onEvent (UI.click staT) (const (do
          UI.start tmr
          v <- tmr # UI.get UI.interval
          element stoT # set UI.enabled True
          element staT # set UI.enabled False ))
  onEvent (UI.click stoT) (const (do
          UI.stop tmr
          element stoT # set UI.enabled False
          element staT # set UI.enabled True ))
  let
    evpoll =(unionWith const (UI.click b) (UI.tick tmr))
  bht <- stepper Nothing (unsafeMapIO (fmap Just . const getCurrentTime) evpoll)
  output <- UI.div  # sink text ((\v  t -> "Timer Interval: " <> show (fromIntegral v/60000) <> " minutes" <> " -  Last Poll: " <> maybe "-" show t ) <$> inter <*> bht)
  let evb = ( (facts (filter (\i -> tdInput i && tdOutput1 i ) <$>listRes) <@ UI.click b))
      tdInput i =  maybe False (const True) $ allMaybes $ fmap (\t -> (if fst t then join . fmap unRSOptional' else id ) $ fmap snd $ (indexTable  $ snd t) i) (fst f)
      tdOutput1 i =  maybe True (const False) $ allMaybes $ fmap (\f -> (if not(fst f ) then join . fmap unRSOptional' else id ) $ fmap snd $ (indexTable  $ snd f) i) (snd f)

  bh <- stepper []  evb
  ev <- plug  (tidings bh evb)
  body <- UI.div  # set children [headerP,b,inp,staT,stoT,output,ev]
  return body


pluginUI' conn inf oldItems (BoundedPlugin n (t,f) action) = do
  headerP <- UI.div # set text n
  overwrite <- checkedWidget (pure False)
  let plug = action conn inf
      tdInput = (\i -> maybe False (const True) $ allMaybes $ fmap (\t -> (if fst t then join . fmap unRSOptional' else id ) $ fmap snd $ join $ fmap (indexTable  $ snd t) i) (fst f) ) <$>  oldItems
      tdOutput1 = (\i -> maybe True (const False) $ allMaybes $ fmap (\f -> (if not(fst f ) then join . fmap unRSOptional' else id ) $ fmap snd $ join $ fmap (indexTable  $ snd f) i) (snd f) ) <$>  oldItems
      tdOutput= liftA2 (\i j -> if i then True else j) (triding overwrite)  tdOutput1
  ev <- plug  oldItems
  bod <- UI.div  # set children [ev] # sink UI.style (noneShowSpan <$> facts tdOutput)
  element overwrite # sink UI.style (noneShowSpan . not <$> facts tdOutput1)
  body <- UI.div # set children [headerP,getElement overwrite,bod] # sink UI.style (noneShowSpan <$> facts tdInput)
  return (body,  pure Nothing :: Tidings (Maybe [(Key,Showable)]))


pluginUI conn inf oldItems p@(Plugins n (table@(Raw s t pk desc fk allI),keys) a) = do
  let plug = a conn inf
  ev <- plug oldItems
  headerP <- UI.div # set text n
  body <- UI.div  # set children ((headerP:) . pure $  fst ev :: [Element])
  return (body,  snd ev )



-- Split composite PKs in list of atomic pks
invertPK :: PK a -> [PK a]
invertPK  (PK k [] ) = fmap (\i -> PK [i] []) k
invertPK  (PK k d ) = zipWith (\i j -> PK [i] [j]) k d

projectFk schema k = case M.keys <$> M.lookup k schema of
                Just l ->   l
                Nothing -> []




doQueryTable :: Traversable t => Connection -> InformationSchema -> QueryT Identity (t KAttribute)  ->
                    (Map Key [Filter]) -> [PathQuery] -> (S.Set Key) -> IO (t Key,[t Showable])
doQueryTable conn inf q f p arg  = projectTable  conn inf (do
              predicate (concat $ filterToPred <$> (M.toList f))
              addPath p
              q
               ) arg
  where
    filterToPred (k,f) = fmap (k,) f


doQueryAttr :: Traversable t => Connection -> InformationSchema -> QueryT Identity (t KAttribute)  ->
                    (Map Key [Filter]) -> (S.Set Key) -> IO [t (Key,Showable)]
doQueryAttr conn inf q f arg  = fmap (fmap (fmap (\(Metric k , t)-> (k,t)))) $ projectKey' conn inf (do
              predicate (concat $ filterToPred <$> (M.toList f))
              q ) arg
  where
    filterToPred (k,f) = fmap (k,) f


doQuery :: Traversable t => Connection -> InformationSchema -> QueryT Identity (t KAttribute)  ->
                    (Map Key [Filter]) -> (S.Set Key) -> IO [t Showable]
doQuery conn inf q f arg  = fmap (fmap (fmap snd )) $ projectKey' conn inf (do
              predicate (concat $ filterToPred <$> (M.toList f))
              q
               ) arg
  where
    filterToPred (k,f) = fmap (k,) f


filterMaybe f (Just i ) = f i
filterMaybe _ _  = []


filterWidget
  :: Connection -> InformationSchema
     -> Tidings (S.Set Key)
     -> Tidings (Map Key [Filter])
     -> UI (UI.MultiListBox (PK Showable ),UI.ListBox (S.Set Key ),RangeBox (PK Showable),TrivialWidget (Map Key [Filter]))
filterWidget conn inf bBset filterT = do
  -- Filter Box (Saved Filter)
  ff  <- insdel (facts filterT)

  -- Filterable Keys
  let bFk = fmap (projectFk (hashedGraph inf) ) bBset
  fkbox <- UI.listBox (liftA2 (:)  bBset bFk) (const <$> pure Nothing <*> fmap Just bBset) (pure (\i-> UI.li # set text (showVertex i)))

  -- Filter Query
  bp <- joinT $ (\i j-> maybe (return []) id (fmap (doQuery conn inf (projectAllRec' (tableMap inf) )  i) j)) <$> triding ff <*> UI.userSelection fkbox
  rangeWidget <- rangeBoxes (UI.userSelection fkbox)  (fmap (kvKey . allKVRec ) <$> bp)

  -- Filter Selector
  filterItemBox <- UI.multiListBox (fmap (kvKey . allKVRec) <$> bp) (const <$> pure [] <*> UI.userSelection fkbox) (pure (\i-> UI.li # set text (show i)))
  return  (filterItemBox,fkbox, rangeWidget ,ff)

line n = UI.li # set  text n

tableElem h b =  grid $ header h : body b
  where header = fmap st
        body = fmap (fmap st)
        st i = UI.div # set text (show  i) # set UI.style [("padding","5px"),("border-width","1px"),("border-color","gray"),("border-style","solid")]


selectedItems enabled conn inf ff key = do
  let
    invItems :: Tidings [(S.Set Key , [PathQuery])]
    invItems = ((\k -> case  M.lookup k (hashedGraphInv inf) of
            Just invItems ->   M.toList invItems
            Nothing -> [] )) <$> key
  let
    query ena i j key
      | M.null i  || not ena = return []
      | otherwise =  traverse (\k-> traverse (\sk-> catMaybes <$> traverse (\ski -> (`catch` (\e-> traceShow (e :: SomeException)  $ return  Nothing ) ) $ traverse (\lv->  (ski,) <$> doQueryTable conn inf  (projectTableAttrs lv)  i (pure  ski)  key)  ( M.lookup (fst k) (pkMap inf)) ) sk ) k ) j
  bp <- joinT $ (query <$> enabled <*> ff <*> invItems <*> key)
  body <- UI.div # sink items (fmap (\(v,i) -> UI.div # set items (UI.div # set text (showVertex  v ) : (fmap (\(p,v) -> UI.div # set items (UI.div # set text (show p) :  [tableElem  (F.toList $ fst v) $ fmap F.toList (snd v)] )) i ) ) )  . filter (not . all ( null  . snd  . snd) .snd) . fmap (fmap (filter (not.null.snd.snd)))  <$> facts bp)
  UI.div # set children [body]


chooserKey conn pg inf kitems  = do
  -- Base Button Set
  filterInp <- UI.input
  filterInpBh <- stepper "" (onEnter filterInp)
  bset <- buttonFSet  (L.sortBy (comparing (fmap keyValue . S.toList )) kitems) ((\j -> (\i -> L.isInfixOf (toLower <$> j) (toLower <$> i) ))<$> filterInpBh) (\i -> case M.lookup i (pkMap inf) of
                                       Just (Raw _ i  _ _ _ _ )-> T.unpack i
                                       Nothing -> showVertex i )
  let bBset = triding bset
  body <- UI.div # sink items (facts (pure . chooseKey conn pg inf <$> bBset ))
  UI.div # set children [filterInp,getElement bset, body]

chooseKey
  :: Connection
     -> [Plugins]
     -> InformationSchema -> S.Set Key -> UI Element
chooseKey conn  pg inf key = mdo
  -- Filter Box (Saved Filter)
  let bBset = pure key :: Tidings (S.Set Key)
  (filterItemBox,fkbox,range,ff) <- filterWidget conn inf bBset filterT

  -- countAll Query
  let
    bFk = projectFk (hashedGraph inf) key

  -- Filter Map Selected
  let
    {- rangeT :: Tidings (Map Key [Filter])
    rangeT = corners <$> _rangeSelection range <*> (fmap S.toList  <$> UI.userSelection fkbox)
      where corners i mk = case i of
              Just i -> case Interval.lowerBound i of
                          Just l -> case  Interval.upperBound i of
                            Just u -> case (fmap (\k -> zipWith (\m n-> (n,[RangeFilter m])) [l u ] k) mk) of
                              Just res -> M.fromList res
                              Nothing -> M.empty
                            Nothing -> M.empty
                          Nothing -> M.empty
              _ ->  M.empty-}
    categoryT :: Tidings (Map Key [Filter])
    categoryT = M.fromListWith mappend <$> (filterMaybe (fmap (\(fkv,kv)-> (fkv,[Category (S.fromList kv)]))) <$> arg)
      where arg :: Tidings (Maybe [(Key, [PK Showable])])
            arg = (\i j -> fmap (\nj -> zipWith (,) nj (L.transpose j) ) i) <$> (fmap S.toList  <$> UI.userSelection fkbox ) <*> (fmap invertPK <$> UI.multiUserSelection filterItemBox)
    filterT = categoryT -- liftA2 (M.unionWith mappend) categoryT rangeT


  vp <-   joinT $ doQueryAttr conn inf (projectAllRec' (tableMap inf)) <$> (M.unionWith mappend <$> filterT <*> triding ff) <*>  bBset
  -- Final Query ListBox
  filterInp <- UI.input
  filterInpBh <- stepper "" (onEnter filterInp)

  let filterInpT = tidings filterInpBh (onEnter  filterInp)

  let sortSet = filter (filterIntervalSort . keyType ) . F.toList . allRec (tableMap inf) . (\(Just i)-> i) . flip M.lookup (pkMap inf) <$> bBset
      filterIntervalSort (KInterval i) = False
      filterIntervalSort (KOptional i) = filterIntervalSort i
      filterIntervalSort i = True
  sortList  <- UI.listBox sortSet ((safeHead . F.toList) <$> sortSet) (pure (line . show))
  asc <- checkedWidget (pure False)
  let listManip :: (Show (f Showable), Traversable f) => String ->[f (Key,Showable)] -> Maybe Key -> Bool -> [f (Key,Showable)]
      listManip i j Nothing  _ =  filtering  i j
      listManip i j (Just s) b  =   L.sortBy ( ifApply (const b) flip (comparing (fmap snd .F.find ((== s).fst) )) ) $ filtering i j
      filtering :: (Show (f Showable), Functor f) => String -> [f (Key,Showable)] -> [f (Key,Showable)]
      filtering i = filter (L.isInfixOf (toLower <$> i) . fmap toLower . show  . fmap snd)
      listRes = listManip  <$> filterInpT <*> res2 <*> UI.userSelection sortList <*> triding asc
      reducer i@(SDouble _) j@(SDouble _)  =  i + j
      reducer (SOptional i) (SOptional j)  =  SOptional $ liftF2 reducer  i  j
      reducer (SSerial i) (SSerial j)  =  SSerial $ liftF2 reducer  i  j
      reducer i j = error $ "not reducible : " <> show i <> " - " <> show j
      isReducible (Primitive PDouble)  = True
      isReducible (KOptional i )  =  isReducible i
      isReducible (KSerial i )  =  isReducible i
      isReducible i = False

  itemList <- UI.listBox listRes  (pure Nothing) (pure (\i -> line $   L.intercalate "," (F.toList $ fmap (renderShowable . snd ) $  kvKey $ allKVRec i) <> "," <>  (L.intercalate "," $ fmap (renderShowable.snd) $  tableNonrec i)))
  element itemList # set UI.style [("width","100%"),("height","300px")]
  let foldr1Safe f [] = []
      foldr1Safe f xs = foldr1 f xs
  total <- UI.div  # sink UI.text (("Total: " <> ) . show . (\k-> foldr1Safe (zipWith (\(k,v) (k1,v1) -> (k,reducer v v1)) )  ( filter(isReducible . fmap textToPrim . keyType . fst) . F.toList <$> k )) <$>  facts listRes)

  let
    categoryT1 :: Tidings (Map Key [Filter])
    categoryT1 = M.fromListWith mappend <$> (filterMaybe (fmap (\(fkv,kv)-> (fkv,[Category (S.fromList kv)]))) <$> arg)
      where arg :: Tidings (Maybe [(Key, [PK Showable])])
            arg = (\i j -> fmap (\nj -> zipWith (,) nj (L.transpose j) ) i) <$> (fmap S.toList  . Just <$> bBset ) <*> (fmap invertPK  . maybeToList . fmap (\i -> snd <$> kvKey ( allKVRec i) )  <$> UI.userSelection itemList)

  sel <- UI.multiListBox (pure bFk) (pure bFk) (pure (line . showVertex))
  selCheck <- checkedWidget (pure False)
  selected <- selectedItems (triding selCheck) conn inf categoryT1  bBset
  element (getElement itemList) # set UI.multiple True
  element (getElement filterItemBox) # set UI.multiple True
  pluginsChk <- checkedWidget (pure False)
  pollingChk <- checkedWidget (pure False)
  pres  <- mapM (\i -> (_pollingName i ,) <$> pollingUI' conn inf ((\i j ->if i then j else [] ) <$> triding pollingChk <*>listRes ) i)  (filter (\(BoundedPollingPlugins n _  (tb,_)  _ )-> tb  == (tableName $ (\(Just i)-> i) $ M.lookup key (pkMap inf)  ))  [queryPollAndamentoB ,queryPollArtAndamento])
  res  <- mapM (\i -> (_name i ,) <$> pluginUI conn inf ((\i j ->if i then fmap F.toList j else Nothing) <$> triding pluginsChk <*> UI.userSelection itemList  ) i )   (filter (\(Plugins n tb _ )-> S.isSubsetOf  (snd tb) (attrSet (pkMap inf) ((\(Just i)-> i) $ M.lookup key (pkMap inf)))  ) pg )
  pluginsDiv <- tabbed ((\(l,(d,_))-> (l,d) )<$> res)
  pollingsDiv <- tabbed ((\(l,d)-> (l,d) )<$> pres)
  let plugins = ("PLUGINS" ,(pluginsChk,pluginsDiv))
      pollings = ("POLLINGS" ,(pollingChk ,pollingsDiv ))
  let
      tdi2 = case snd .snd <$> res of
        [] -> pure Nothing
        xs -> foldr1 (liftA2 mappend)  xs

  let
     filterOptions = case M.keys <$> M.lookup key (hashedGraph inf) of
               Just l -> key :  l
               Nothing -> [key]
     convertPK i = case fmap F.toList i of
        Nothing -> Just []
        i -> i
     table = (\(Just i)-> i) $ M.lookup key (pkMap inf)

  let whenWriteable = do
            (crud,_,evs) <- crudUITable conn inf ([lplugOrcamento ,queryArtCrea , queryArtBoletoCrea , queryShowMap ,queryCEPBoundary ,queryGeocodeBoundary,queryCNPJBoundary ,queryTimeline, queryAndamentoB,queryArtAndamento ] ) (allRec (tableMap inf) table) (UI.userSelection itemList)
            let eres = fmap (addToList  (allRec (tableMap inf ) table )  <$> ) evs
            res2 <- accumTds vp  eres
            insertDiv <- UI.div # set children [crud]
            chk <- checkedWidget (pure True)
            return (res2 ,Just ("CRUD",(chk,insertDiv)) )
  (res2,crud) <- whenWriteable
  codeChk <- checkedWidget (pure False)
  createcode <- UI.textarea # set UI.text (T.unpack$ createTable table)
              # set style [("width","100%"),("height","300px")]
  dropcode <- UI.textarea # set UI.text (T.unpack$ dropTable table)
              # set style [("width","100%"),("height","300px")]
  code <- tabbed [("CREATE",createcode),("DROP",dropcode)]
  filterSel <- UI.div # set children [getElement ff,getElement fkbox,getElement range, getElement filterItemBox]
  tab <- tabbedChk  ( maybeToList crud <>[("SELECTED",(selCheck ,selected)),plugins,pollings,("CODE",(codeChk,code))])
  itemSel <- UI.div # set children [filterInp,getElement sortList,getElement asc]
  UI.div # set children ([itemSel,getElement itemList,total,tab] )


genPlugin :: (Ord a1, Ord t, Ord a) => t -> [a] -> (Map (t, a) a1, t1, Map t t2, t3, t4, t5) -> Maybe (t2, Set a1)
genPlugin tname attr inf = do
  table2 <- M.lookup tname (tableMap inf)
  keys2 <- allMaybes $ fmap (flip M.lookup (keyMap inf) . (tname,)) attr
  return $ (table2,S.fromList keys2)


plug :: (Ord a, Ord t) => String -> (Connection -> InformationSchema -> Tidings (Maybe [(Key, Showable)]) -> UI (Element, Tidings (Maybe (Map Key Showable)))) -> t -> [a] -> (Map (t, a) Key, t1, Map t Table, t3, t4, t5) -> Maybe Plugins
plug  name fun table attr inf = flip (Plugins name ) fun <$> (genPlugin table attr inf)

poll :: (Ord a, Ord t) => String -> Int -> (Connection -> InformationSchema -> Tidings [[(Key, Showable)]] -> UI (Element, Tidings (Maybe (Map Key Showable)))) -> t -> [a] -> (Map (t, a) Key, t1, Map t Table, t3, t4, t5) -> Maybe PollingPlugins
poll name time fun table attr inf = flip (PollingPlugins name time) fun <$> genPlugin table attr inf

lplugOrcamento = BoundedPlugin "Orçamento" ("pricing",fst renderProjectPricingA )  (\i j k -> snd renderProjectPricingA $   k)



documentSprinklerProject = plug "Memorial Sprinkler" renderFireProjectReport "project_sprinkler" []

pluginOAuth = plug "Contact" pluginContactDiv "contact" ["id_contact"]

pluginContactDiv conn inf inp = do
  b <- UI.button # set UI.text "query"
  st <- stepper "" (unsafeMapIO (fmap show) (pure (pluginContact inf )<@ UI.click b))
  e <- UI.div # sink UI.text st
  (,pure Nothing ) <$> UI.div # set UI.children [b,e]

-- Address Plugins -
--------------------

pluginAndamentoId = plug "Andamento" queryAndamento2 "fire_project" ["id_bombeiro"]

pluginItauTxt = plug  "Extrato Itau" itauExtractTxt "account" ["id_account"]

pluginBradescoCsv = plug  "Extrato Bradesco" bradescoExtractTxt "account" ["id_account"]

pluginWapp = plug  "Import Conversation" wappImport "chat" ["chat_instant"]

pollingAndamento = poll "Andamento Poll" 60 queryAndamento3 "fire_project" ["id_bombeiro"]


simpleGetRequest =  fmap BSL.pack . join . fmap HTTP.getResponseBody . HTTP.simpleHTTP . HTTP.getRequest

shortCutClick  t i = tidings (facts t) (facts t <@ i)

renderUrlM args url = fmap address . kv
  where
    kv i = allMaybes $ (\k -> join . fmap (\inp ->  fmap (snd k,) . M.lookup (fst k) . M.fromList $ fmap (\(k,v)-> (keyValue k,v)) inp ) $  i ) <$> args
    renderKv = HTTP.urlEncodeVars . fmap (\(k,v)-> (k , renderShowable v))
    address i =  url <> "?"  <> renderKv i

renderUrl args url = address
  where
    kv i = catMaybes $ (\k -> join . fmap (\inp ->  fmap (snd k,) . M.lookup (fst k) . M.fromList $ fmap (\(k,v)-> (keyValue k,v)) inp ) $  i ) <$> args
    renderKv = HTTP.urlEncodeVars . fmap (\(k,v)-> (k , renderShowable v))
    address i =  url <> "?"  <> renderKv (kv i)
-- This Iframe needs cross reference scripting enabled in the browser , this implies big security concerns

testPlugin db pg input = startGUI defaultConfig $ \w -> do
    let e = withConnInf db (\conn inf -> fst <$> pg conn inf (pure (fmap (\((t,k),v) -> (lookKey inf t k ,v)) <$> input)))
    getBody w #+ [e]
    return ()

getRequest ::  String -> MaybeT IO BSL.ByteString
getRequest = join . C.lift . (`catch` (\e ->  traceShow (e :: IOException) $ return mzero ) ).  fmap return . simpleGetRequest


hasInput k v inp = case snd <$> lookInput  k inp of
                        Just i  -> testShowable v i
                        Nothing -> False

testShowable  v s = case s of
          (SOptional Nothing ) -> False
          (SOptional (Just i)) -> testShowable v i
          i -> v i

lookInput k = L.find ((== k ) . keyValue . fst )

queryAndamentoB =  BoundedPlugin "Andamento Bombeiro" ("fire_project", staticP arrow ) elem
  where
    arrow :: FunArrowPlug (Maybe Showable)
    arrow = proc t -> do
      idp <- varT "id_project" -< t
      ano <- varT "ano" -< t
      protocolo <- varT "protocolo" -< t
      cpf <- varT "id_owner,id_contact:id_owner:cgc_cpf" -< t
      odx "aproval_date" -<t
      returnA -< idp
    elem conn inf inputs = fst <$> queryAndamento2  conn inf (fmap F.toList <$> inputs)

queryPollAndamentoB =  BoundedPollingPlugins "Andamento Bombeiro" 10  ("fire_project", staticP arrow ) elem
  where
    arrow :: FunArrowPlug (Maybe Showable)
    arrow = proc t -> do
      idp <- varT "id_project" -< t
      ano <- varT "ano" -< t
      protocolo <- varT "protocolo" -< t
      cpf <- varT "id_owner,id_contact:id_owner:cgc_cpf" -< t
      odx "aproval_date" -< t
      returnA -< idp
    elem conn inf inputs = fst <$> queryAndamento3  conn inf (fmap F.toList <$> inputs)



queryAndamento4 conn inf  inputs = fmap (snd $ (\(Just i)-> i) .L.find ((== "project_description") . keyValue . fst )$ inputs,) <$> (runMaybeT $  do
              let
                  fire_project = lookTable inf "fire_project"
                  andamento = lookTable inf "andamento"
              ano <- MaybeT $ return $ lookInput "ano" $ filter (not . isEmptyShowable. snd )  $ inputs
              if testShowable (<=14) (snd ano )
                then do
                let
                    addrs ="http://siapi.bombeiros.go.gov.br/consulta/consulta_protocolo.php"
                    translate = [("protocolo" , "protocolo"),("ano","ano")]
                (lkeys,modB) <- if not $ elem "id_bombeiro" ((keyValue . fst)<$>  filter (not . isEmptyShowable. snd ) inputs )
                   then do
                    url <- MaybeT $ return $ renderUrlM translate addrs  $ filter (not . isEmptyShowable. snd )  <$> Just inputs
                    lq <-  getRequest . traceShowId $ url
                    let
                      lq2 =  Just . maybe M.empty (uncurry M.singleton . ("id_bombeiro",)) . fmap SNumeric . readMaybe.  fst .  break (=='&') . concat . tail .  splitL ("php?id=")  .T.unpack . decodeLatin1  $  lq
                      lkeys = fmap ( M.toList . M.mapKeys ((\(Just i)-> i) . flip M.lookup (keyMap inf) . ("fire_project",)  ))  $ lq2
                    mod <- C.lift $ updateMod conn ((\(Just i)-> i) lkeys) inputs  fire_project
                    return $  (lkeys,mod)
                   else do return $ (fmap (\i-> [i])   $ L.find ((== "id_bombeiro") .  keyValue . fst) inputs,Nothing)
                let
                  tkeys t v =  M.mapKeys (lookKey inf t )  v
                  insertAndamento :: MaybeT IO [Maybe (TableModification Showable)]
                  insertAndamento   = do
                    let
                        addrs_a ="http://siapi.bombeiros.go.gov.br/consulta/consulta_andamento.php"
                        translate_a = [("id_bombeiro" , "id")]
                    MaybeT $ return $ if elem "aproval_date" ((keyValue . fst)<$>  filter (not . isEmptyShowable. snd ) inputs )  then Nothing else Just undefined
                    tq <-  getRequest . traceShowId . (renderUrl translate_a addrs_a)  $  lkeys
                    let
                      i =  T.unpack $  decodeLatin1 tq
                      convertAndamento [da,desc] = [("andamento_date",SDate . Finite . localDay . fst . justError "wrong date parse" $  strptime "%d/%m/%y" da  ),("andamento_description",SText (T.filter (not . (`elem` "\n\r\t")) $ T.pack  desc))]
                      convertAndamento i = error $ "convertAndamentoLegacy:  " <> show i
                      prepareArgs  = fmap ( tkeys "andamento". M.fromList . convertAndamento ) .  tailEmpty . concat
                      lookInput = justError "could not find id_project" . fmap (\(k,v) -> let k1 = (\(Just i)-> i) $ M.lookup ("andamento","id_project") (keyMap inf) in (k1, transformKey (textToPrim <$> keyType k)  (textToPrim <$> keyType k1) v) ) . L.find ((== "id_project") . keyValue . fst)

                    C.lift $ do
                      html <- readHtml $ i
                      let
                          args :: S.Set (Map Key Showable)
                          args = S.fromList $ fmap (uncurry M.insert  (lookInput inputs )) $ prepareArgs html
                      mod <- case filter ( maybe False (\(SText t) -> T.isInfixOf "Aprovado" t ) .  M.lookup "andamento_description" . M.mapKeys keyValue )  $ S.toList args of
                          [i] -> updateMod  conn [(justError "could not lookup approval_date " . flip M.lookup (keyMap inf) $ ("fire_project","aproval_date") , justError "could not lookup andamento_date" $ M.lookup "andamento_date"  $ M.mapKeys keyValue i)] inputs fire_project
                          i -> return Nothing
                      vp <- doQueryAttr conn inf (projectAllRec' (tableMap inf)) (uncurry M.singleton $  fmap ( (\i->[i]) . Category . S.singleton . flip PK [].(\i->[i]) ) (lookInput inputs ) ) ( (\(Raw _ _ pk _ _ _ ) -> pk ) andamento )

                      let kk = S.fromList (fmap (M.fromList . filter ((`elem` ["id_project","andamento_description","andamento_date"] ) . keyValue . fst ) . concat . F.toList . fmap attrNonRec . unTB1) vp) :: S.Set (Map Key Showable)
                      adds <- {-traceShow ("KK " <> show kk <> " \n ARGS " <> show args) $-} mapM (\kv -> (`catch` (\e -> return $ trace ( show (e :: SqlError)) Nothing )) $ insertMod conn  (M.toList kv) (andamento )) (S.toList $ args  `S.difference`  kk)
                      return $ mod : adds

                  updateSolicitacao :: MaybeT IO (Maybe (TableModification Showable))
                  updateSolicitacao = do
                    MaybeT $ return $ if maybe False (\(_,SOptional  mb)-> maybe False (\(SBoolean b) -> b) mb)$ L.find ((=="taxa_paga"). keyValue . fst) $ (filter (not . isEmptyShowable. snd ) inputs )  then Nothing else Just undefined
                    let  addrs_b ="http://siapi.bombeiros.go.gov.br/consulta/consulta_solicitacao.php"
                         translate_b = [("id_bombeiro" ,"id")]
                    tq3 <-  getRequest . traceShowId . (renderUrl translate_b addrs_b)  $  lkeys
                    htmlSoli <- C.lift $ testSolicitation tq3
                    let tq4 = catMaybes .fmap Tra.sequence . M.toList . tkeys  "fire_project" . M.fromList $ htmlSoli
                    MaybeT $ return $ if not $ maybe False (\(_,SBoolean mb)-> mb) $ L.find ((=="taxa_paga"). keyValue . fst)  tq4 then Nothing else Just undefined
                    C.lift $ updateMod  conn tq4 inputs fire_project
                  getPdf = do
                    MaybeT $ return $ if (\i->elem "analista" i || elem "aproval_date" i ) $ (keyValue . fst <$> filter (not . isEmptyShowable. snd ) inputs ) then Nothing else Just undefined
                    C.lift $ testPdfGet conn inf inputs
                and <- C.lift $ concat . maybeToList <$> runMaybeT insertAndamento
                sol <- C.lift $ maybeToList <$> runMaybeT updateSolicitacao
                gets <-C.lift $ maybeToList <$> runMaybeT getPdf
                let mods =  catMaybes (   modB :  gets <> and  <> sol)
                mapM (C.lift . logTableModification inf conn) mods
                MaybeT $ return  $ (\case {[] -> Nothing ; i -> Just i }) mods
              else do
                    MaybeT $ return $ if elem "aproval_date" ((keyValue . fst)<$>  filter (not . isEmptyShowable. snd ) inputs )  then Nothing else Just undefined
                    html <- MaybeT $   fmap join $ Tra.sequence $  liftA3 siapi3 (getInput "protocolo" inputs) (getInput "ano" inputs) (getInput "cgc_cpf" inputs)
                    MaybeT $ return $ case (L.null $ join $ join $  html) of
                                  True -> Nothing
                                  False -> Just undefined
                    let
                      tkeys t v =  M.mapKeys (lookKey inf t)  v
                      convertAndamento [_,da,desc,s,sta] = [("andamento_date",SDate . Finite . localDay . fst . justError "wrong date parse" $  strptime "%d/%m/%Y %H:%M:%S" da  ),("andamento_description",SText $ T.pack  desc)]
                      convertAndamento i = error $ "convertAndamento2015 :  " <> show i
                      prepareArgs  = fmap (tkeys "andamento" . M.fromList . convertAndamento)
                      lookInput = justError "could not find id_project" . fmap (\(k,v) -> let k1 = (\(Just i)-> i) $ M.lookup ("andamento","id_project") (keyMap inf) in (k1, transformKey (textToPrim <$> keyType k)  (textToPrim <$> keyType k1) v) ) . L.find ((== "id_project") . keyValue . fst)

                    mods <- C.lift $  do
                      let
                          args :: S.Set (Map Key Showable)
                          args = S.fromList $ fmap (uncurry M.insert  (lookInput inputs )) $  prepareArgs  $ html
                      mod <- case filter ( maybe False (\(SText t) -> T.isInfixOf "APROVADO" t ) .  M.lookup "andamento_description" . M.mapKeys keyValue )  $ S.toList args of
                          [] -> return Nothing
                          i:xs -> updateMod  conn [(lookKey inf "fire_project" "aproval_date"  , justError "could not lookup andamento_date" $ M.lookup "andamento_date"  $ M.mapKeys keyValue i)] inputs fire_project
                      vp <- doQueryAttr conn inf (projectAllRec' (tableMap inf)) (uncurry M.singleton $  fmap ( (\i->[i]) . Category . S.singleton . flip PK [].(\i->[i]) ) (lookInput inputs ) ) ( (\(Raw _ _ pk _ _ _ ) -> pk ) andamento )

                      let kk = S.fromList (fmap (M.fromList . filter ((`elem` ["id_project","andamento_description","andamento_date"] ) . keyValue . fst ) . concat . F.toList . fmap attrNonRec . unTB1) vp) :: S.Set (Map Key Showable)
                      adds <- {-traceShow ("KK " <> show kk <> " \n ARGS " <> show args) $-} mapM (\kv -> (`catch` (\e -> return $ trace ( show (e :: SqlError)) Nothing )) $ insertMod conn  (M.toList kv) (andamento )) (S.toList $ args  `S.difference`  kk)
                      return $ mod : adds
                    MaybeT $ return  $ (\case {[] -> Nothing ; i -> Just i }) (catMaybes mods ))

getInput k = fmap (BSL.toStrict. BSL.pack .renderShowable . snd) . lookInput k

allNonEmpty [] = Nothing
allNonEmpty l = Just  l

eitherToMaybeT (Left i) =  Nothing
eitherToMaybeT (Right r) =  Just r

queryAndamento3 conn inf  input = do
        tq <-  mapT (mapM (queryAndamento4 conn inf  ) ) input
        e <- UI.div # sink appendItems ( fmap (\i -> UI.div # set text (show $ (fmap (fmap renderShowable)) <$> i) ) . catMaybes  <$> facts tq  )
        return (e , pure Nothing :: Tidings (Maybe (Map Key Showable)))

updateMod conn kv old table = do
  (i,j) <- update conn  kv old table
  return $ Just j

insertMod conn kv table = do
  insert conn  kv table
  return $ Just $ TableModification table (Insert $ Just kv)

logTableModification inf conn (TableModification table i) = do
  let look k = lookKey inf "modification_table" k
  time <- getCurrentTime
  let ltime = STimestamp . Finite . utcToLocalTime utc $ time
  insertPK fromShowableList conn [(look "modification_time", ltime ) ,(look "table_name" ,SText $ tableName  table) , (look "modification_data", SText $ T.pack $ show i)] ((\(Just i)-> i) $ M.lookup ("modification_table") (tableMap inf))

bradescoRead file = do
  file <- TE.decodeLatin1 <$> BS.readFile file
  let result =  fmap (fmap TE.unpack . L.take 5) $ filter (\(i:xs) -> isJust $ strptime "%d/%m/%y" (TE.unpack i)) $ filter ((>5) . length) $  TE.split (';'==) <$> TE.split (=='\r') file
  return result

testIAG = do
  f <- BSL.readFile "testiag.html"
  testSolicitation f
testFranklin = do
  f <- BSL.readFile "solicitacao.html"
  testSolicitation f
testHimalaia= do
  f <- BSL.readFile "himalaia.html"
  testSolicitation f

testSolicitation f = do
  -- f <- BSL.readFile "solicitacao.html"
  let dec =  decodeLatin1 f
  html <-  (head <$> readHtml ( T.unpack $ dec ))
  let packed = fmap (fmap T.pack) html
      log = fmap (splitAt 2) $ safeHead $ filter ((==4).length) packed
      tx = fmap (splitAt 2) $ safeHead $ filter (T.isInfixOf "TAXA" . head ) $ filter ((==3).length) packed
      translateSolicitation :: [(Text,(Text,Text-> Maybe Showable))]
      translateSolicitation  =
        [("ÁREA CONSTRUÍDA",("area",(\i-> SDouble <$> readMaybe (T.unpack $ fst $ T.break (' '==) i))))
        ,("VALOR  DA TAXA",("taxa_aprovacao",(\i -> SDouble <$> readMaybe (T.unpack $ fst $ T.breakOn ("\160") i))))
        ,("LOCAL DE ATENDIMENTO",("local_atendimento",fmap SText . nonEmpty ))
        ,("REGIÃO DE ATENDIMENTO",("regiao_atendimento",fmap SText . nonEmpty ))
        ,("TAXA PAGA",("taxa_paga",fmap SBoolean . readMaybe . T.unpack))
        ]
      nonEmpty "" = Nothing
      nonEmpty i = Just i
      keyvalue = fmap (\[i,j]-> (T.strip $ fst (T.breakOn "..:" i) ,j)) $ (filter ((==2). length) $   packed <> maybe [] (\(logr,num) -> [logr,num]) log  <> maybe [["TAXA PAGA..:","True"]] (\(taxa,apagar) -> [taxa,["TAXA PAGA..:", T.pack $ show $ not $ T.isInfixOf "TAXA A RECOLHER" dec ]] ) tx)
      result =  catMaybes .fmap (\(k,v) -> fmap ($v) <$> M.lookup k (M.fromList translateSolicitation))
  return $ (result keyvalue)


sdate  = SDate . Finite .localDay
stimestamp  = STimestamp . Finite


bradescoExtractTxt  conn  inf   inputs = do
    pathInput <- UI.input -- # set UI.type_ "file"
    b <- UI.button # set UI.text "Import"
    bhInp <- stepper "" (UI.valueChange pathInput)
    let process (Just inp) path = do
          content <- bradescoRead  path
          let parse  = uncurry M.insert (lookInput inp )  . tkeys . parseField  <$> content
              lookInput = (\(Just i)-> i) .L.find ((== "id_account") . keyValue . fst)
              tkeys v =  M.mapKeys (lookKey inf "transaction")  v
              parseField [d,desc,_,v,""] = M.fromList [("transaction_date",sdate $ fst $ (\(Just i)-> i) $ strptime "%d/%m/%y" d),("transaction_description",SText $ T.pack desc),("transaction_price", SDouble $ read $ fmap (\i -> if i == ',' then '.' else i) $ filter (not . (`elem` ".\"")) v)]
              parseField [d,desc,_,"",v] = M.fromList [("transaction_date",sdate $ fst $ (\(Just i)-> i) $ strptime "%d/%m/%y" d),("transaction_description",SText $ T.pack desc),("transaction_price", SDouble $ read $ fmap (\i -> if i == ',' then '.' else i) $ filter (not . (`elem` ".\"")) v)]
          vp <- doQueryAttr conn inf (projectAllRec' (tableMap inf)) (uncurry M.singleton $  fmap ( (\i->[i]) . Category . S.singleton . flip PK [].(\i->[i]) ) (lookInput inp ) ) ( (\(Raw _ _ pk _ _ _ ) -> pk ) $(\(Just i)-> i) $  M.lookup  "transaction" (tableMap inf ))
          let kk = S.fromList (fmap (M.fromList . filter ((`elem` ["id_account","transaction_description","transaction_date","transaction_price"] ) . keyValue . fst ) . F.toList ) vp) :: S.Set (Map Key Showable)
          adds <- mapM (\kv -> (`catch` (\e -> return $ trace ( show (e :: SqlError)) Nothing )) $ fmap Just $ insertPK fromShowableList  conn  (M.toList kv) ((\(Just i)-> i) $ M.lookup  "transaction" (tableMap inf) )) (S.toList $ ( S.fromList parse ) `S.difference` kk)
          return parse
        process Nothing _ = do return []
        j = unsafeMapIO id $ process  <$> facts inputs <*> bhInp <@ UI.click b
    outStp <- stepper "" (fmap show $ j)
    out <- UI.div # sink UI.text outStp
    (,pure Nothing) <$> UI.div # set children [pathInput,b,out]

itauExtractTxt  conn  inf   inputs = do
    pathInput <- UI.input -- # set UI.type_ "file"
    b <- UI.button # set UI.text "Import"
    bhInp <- stepper "" (UI.valueChange pathInput)
    let process (Just inp) path = do
          file <-  readFile (traceShowId path)
          let parse  = uncurry M.insert (lookInput inp )  . tkeys . parseField . unIntercalate (';'==) <$> lines (filter (/='\r') file)
              lookInput = (\(Just i)-> i) .L.find ((== "id_account") . keyValue . fst)
              tkeys v =  M.mapKeys (lookKey  inf "transaction")  v
              parseField [d,desc,v] = M.fromList [("transaction_date",SDate $ Finite $ localDay $ fst $ (\(Just i)-> i) $ strptime "%d/%m/%Y" d),("transaction_description",SText $ T.pack desc),("transaction_price", SDouble $ read $ fmap (\i -> if i == ',' then '.' else i) v)]
          vp <- doQueryAttr conn inf (projectAllRec' (tableMap inf)) (uncurry M.singleton $  fmap ( (\i->[i]) . Category . S.singleton . flip PK [].(\i->[i]) ) (lookInput inp ) ) ( (\(Raw _ _ pk _ _ _ ) -> pk ) $(\(Just i)-> i) $  M.lookup  "transaction" (tableMap inf ))
          let kk = S.fromList (fmap (M.fromList . filter ((`elem` ["id_account","transaction_description","transaction_date","transaction_price"] ) . keyValue . fst ) . F.toList ) vp) :: S.Set (Map Key Showable)
          adds <- mapM (\kv -> (`catch` (\e -> return $ trace ( show (e :: SqlError)) Nothing )) $ fmap Just $ insertPK fromShowableList  conn  (M.toList kv) ((\(Just i)-> i) $ M.lookup  "transaction" (tableMap inf) )) (S.toList $ ( S.fromList parse ) `S.difference` kk)
          return parse
        process Nothing _ = do return []
        j = unsafeMapIO id $ process  <$> facts inputs <*> bhInp <@ UI.click b
    outStp <- stepper "" (fmap show $ j)
    out <- UI.div # sink UI.text outStp
    (,pure Nothing) <$> UI.div # set children [pathInput,b,out]

fkattrsB inputs fks = foldr (liftA2 (:))   inputs fks

lookAttr inp attr = justError ("Error looking Attr: " <> show attr <> " " <> show inp) $ M.lookup attr  inp

lookKeyMap inp attr = justError ("Error looking KeyMap: " <> show attr <> " " <> show inp) $ M.lookup attr  inp



wappImport conn inf  _ = do
  let chat@(Raw _ _ pk desc ifk attrs) = lookTable inf "chat"
  pathInput <- UI.input  -- # set UI.type_ "file"
  b <- UI.button # set UI.text "Import"
  bhInp <- stepper "" (UI.valueChange pathInput)
  v <- mapM (\path -> fkUITable conn inf [] path (pure Nothing)  . fmap snd . fkCase (tableMap inf) False PathRoot $ path) $ S.toList ifk
  let
      ninputs = allMaybes <$> (fkattrsB (pure mempty) (snd <$> v))
  output <- UI.div # set children (fst <$> v)
  let process (Just inp) path = do
        file <-  liftIO $ T.readFile path
        let result =  S.fromList $ M.fromList <$>  (fmap  parse $ filter (\(i,xs) -> isJust $ strptime "%d de %b %R" (T.unpack $ translateMonth i)) $   T.breakOn ("-") <$> T.split (=='\n') file)
            parse (d,t) =  (\(k,s)-> (lookKey inf "chat"  k,s)) <$>  [("chat_instant",STimestamp $ Finite $ fst $ (\(Just i)-> i) $ strptime "%d de %b %R %Y" (T.unpack (translateMonth d) <> " 2014")),("chat_text",SText $ T.drop 2 c), ("speaker_contact",snd $ head speaker )  ,("target_contact",snd $ head target)]
              where (p,c) =  T.breakOn (":") t
                    name = T.unpack $ T.drop 2 p
                    Just (FKT speaker _ )= F.find (L.isInfixOf name . show ) inp
                    Just (FKT target _ )= F.find (not . L.isInfixOf name. show ) inp
            queryFilter [(k1,v1),(k2,v2)] = M.fromList $  fmap (fmap ( (\i->[i]) . Category . S.singleton . flip PK [].(\i->[i]) )) [(lookKeyMap (keyMap inf) ("chat","speaker_contact"),v1),(lookKeyMap (keyMap inf) ("chat","target_contact"),v2)]
        vp <- mapM (\speaker -> doQueryAttr conn inf (projectAllRec' (tableMap inf)) (queryFilter ((\(FKT [i] _ )-> i ) <$> speaker))  pk) (L.permutations inp)
        let kk = S.fromList (fmap (M.fromList . filter ((`elem` ["speaker_contact","target_contact","chat_text","chat_instant"] ) . keyValue . fst ) . F.toList ) (concat vp)) :: S.Set (Map Key Showable)
        adds <- mapM (\kv -> (`catch` (\e -> return $ trace ( show (e :: SomeException)) Nothing )) $ fmap Just $ insertPK fromShowableList  conn  (M.toList kv) chat ) (S.toList $  result  `S.difference` kk)
        return result
      process Nothing  path = do return S.empty
      j = unsafeMapIO id $ process  <$> facts ninputs <*> bhInp <@ UI.click b
  outStp <- stepper "" (fmap show $ j)
  out <- UI.div # sink UI.text outStp
  inpOut <- UI.div # sink UI.text (show <$> facts ninputs)
  (,pure Nothing) <$> UI.div # set children [output,pathInput,b,out,inpOut]

queryAndamento2 conn inf   input = do
        b <- UI.button # set UI.text "Submit"  # sink UI.enabled (maybe False (\i -> not $ elem "aproval_date" ((keyValue . fst)<$>  filter (not . isEmptyShowable. snd )i) ) <$> facts input)
        tq <-  mapT (\case {Just input -> queryAndamento4 conn inf input ; Nothing -> return Nothing}) (shortCutClick input (UI.click b))
        e <- UI.div # sink UI.text (fmap (maybe "" show ) $ facts $ tq)
        body <-UI.div # set children [b,e]
        return (body , pure Nothing :: Tidings (Maybe (Map Key Showable)))

tailEmpty [] = []
tailEmpty i  = tail i



data PluginBoundary b a
  = PluginBoundary  (b,[a])
  | PluginBoundaryTB  (b,TB1 a)
  deriving(Show)

pluginTable (PluginBoundary (i,_)) = i
pluginTable (PluginBoundaryTB  (i,_)) = i

queryShowMap = BoundedPlugin "Google Map" ("address", fst showMap') (\i j k -> snd showMap'$ k)

showMap' = (staticP req , element)
  where
      varT t =   join . fmap (unRSOptional'.snd)  <$> idxT t
      req :: FunArrowPlug  (Maybe String)
      req = proc t -> do
            p<- varT "geocode" -< t
            returnA -< (\(SPosition (Position (lon,lat,_)))-> "http://maps.google.com/?output=embed&q=" <> (HTTP.urlEncode $ show lat  <> "," <>  show lon )) <$>  p
      element inputs = do
        iframe  # sink UI.src (maybe "" id . dynP req  <$> facts inputs) # set style [("width","99%"),("height","300px")]

data Timeline
  = Timeline
  { header :: String
  , dates :: [(Day,String)]
  }

queryTimeline = BoundedPlugin "Timeline" ("pricing",staticP arrow)  elem
  where
    convDateArr i = fmap swap $ fmap (fmap (\(SDate (Finite f)) -> f)) $ catMaybes $ fmap (traverse unRSOptional') $ catMaybes $ i
    arrow :: FunArrowPlug [(Day,String)]
    arrow = proc t -> do
      prd <- varT "pricing_date" -< t
      apd <- varN "id_project:aproval_date" -< t
      returnA -<  convDateArr  [("Orçamento",)<$> prd,("Aprovação",) <$> apd]
    elem con inf inputs = do
        e <- UI.div # set UI.id_ "timeline-embed"
        let
            generateEvents (PluginBoundary (_,inp))= fmap (\(i,SDate (Finite j))-> (j,T.unpack $ keyValue i )) $filter ((==(Primitive PDate)).  fmap textToPrim .keyType.unKOptional.fst) inp
            timeline i = Timeline "hello" (dynP arrow $ i)
        i <- UI.div # sink UI.html  (fmap (\i->  "<script>    var container = document.getElementById('timeline-embed');var items = new vis.DataSet("  <>  BSL.unpack (traceShowId $ encode (timeline i)) <> ") ;  var options = {} ; if (container.vis != null ) { container.vis.destroy(); } ; container.vis = new vis.Timeline(container,items,options); </script>") $ facts inputs)
        UI.div # set children [e,i]


instance ToJSON Timeline where
  toJSON (Timeline h v) = toJSON (dates <$> zip [0..] v)

    where dates (id,(i,j)) = object ["id" .= (id :: Int) ,"start" .=  ti i, "content" .= j, "type" .= ("point" :: String)]
          ti  = formatTime defaultTimeLocale "%Y/%m/%d"

queryArtCrea = BoundedPlugin "Documento Final Art Crea" ("art",staticP url) elem
  where
    varTB = fmap ( fmap (BS.pack . renderShowable ))<$>  varT
    url :: ArrowPlug (Kleisli IO) (Maybe String)
    url = proc t -> do
      i <- varTB "art_number" -< t
      idxT "payment_date" -<  t
      r <- at "crea_register" (proc t -> do
                               n <- varTB "crea_number" -< t
                               u <- varTB "crea_user"-< t
                               p <- varTB "crea_password"-< t
                               returnA -< liftA3 (, , ) n u p  ) -< t
      act (fmap join  . traverse (\(i, (j, k,a)) -> creaLoginArt  j k a i ) ) -< liftA2 (,) i r
    elem conn inf inputs = do
       let ev = unsafeMapIO (dynPK url) (rumors inputs)
       i <- stepper  "" (maybe "" id <$> ev)
       print<-printIFrame "creaFrame"
       frame<-iframe  # set UI.name "creaFrame" # set UI.id_ "creaFrame" # UI.sink (strAttr "srcdoc") i # UI.set UI.style [("width","100%"),("height","300px")]
       UI.div # set children [print,frame]

queryArtBoletoCrea = BoundedPlugin "Boleto Art Crea" ("art",staticP url) elem
  where
    varTB = fmap ( fmap (BS.pack . renderShowable ))<$>  varT
    url :: ArrowPlug (Kleisli IO) (Maybe String)
    url = proc t -> do
      i <- varTB "art_number" -< t
      idxT "verified_date" -< t
      odx "payment_date" -<  t
      r <- at "crea_register" (proc t -> do
                               n <- varTB "crea_number" -< t
                               u <- varTB "crea_user"-< t
                               p <- varTB "crea_password"-< t
                               returnA -< liftA3 (, , ) n u p  ) -< t
      act ( traverse (\(i, (j, k,a)) -> creaBoletoArt  j k a i ) ) -< liftA2 (,) i r
    elem conn inf inputs = do
       let ev = unsafeMapIO (dynPK url) (rumors inputs)
       i <- stepper "" (maybe "" id <$> ev)
       pdfFrame i # set UI.name "creaBoletoFrame" # set UI.id_ "creaBoletoFrame"


printIFrame i = do
   print <- UI.button # set UI.text "Imprimir"
   bh <- stepper "" (pure ("<script> window.frames[\"" <> i <>  "\"].focus(); window.frames[\"" <> i <> "\"].print();</script>") <@ UI.click print)
   dv <- UI.div # UI.sink UI.html bh
   UI.div # set children [print,dv]

checkOutput i = proc t -> do
      o <- odx i -< fst t
      v <- odx i -< snd t
      returnA -< if isJust o  && fmap snd o == fmap snd v
         then Nothing
         else v


queryPollArtAndamento = BoundedPollingPlugins "Andamento Art Crea"  10  ("art",staticP url) elem
  where
    varTB = fmap ( fmap (BS.pack . renderShowable ))<$>  varT
    url :: ArrowPlug (Kleisli IO) [(Text,Showable)]
    url = proc t -> do
      i <- varTB "art_number" -< t
      odx "verified_date" -< t
      odx "payment_date" -< t
      r <- at "crea_register" (proc t -> do
                               n <- varTB "crea_number" -< t
                               u <- varTB "crea_user"-< t
                               p <- varTB "crea_password"-< t
                               returnA -< liftA3 (, , ) n u p  ) -< t
      o <- act (fmap (join .maybeToList) . traverse (\(i, (j, k,a)) -> creaConsultaArt  j k a i ) ) -< liftA2 (,) i r
      let
          artVeri d = Attr ("verified_date" ,SOptional $ Just $ STimestamp $ Finite $ (\(Just i)-> fst i) $ strptime "%d/%m/%Y %H:%M" ( d !!1) )
          artPayd d = Attr ("payment_date" ,SOptional $Just $ STimestamp $ Finite $ (\(Just i)-> fst i) $ strptime "%d/%m/%Y %H:%M" (d !!1) )
          artInp :: [[String]] -> TB1 (Text,Showable)
          artInp inp = TB1 $ KV (PK [] []) $ catMaybes [artVeri <$>  L.find (\[h,d,o] -> L.isInfixOf "Cadastrada" h )  inp ,artPayd <$> L.find (\[h,d,o] -> L.isInfixOf "Registrada" h ) (traceShowId inp) ]
      i <- checkOutput "verified_date" -< (t,Just$ artInp o)
      j <- checkOutput "payment_date" -< (t,Just $artInp o)
      returnA -< (catMaybes [i, j] )


    elem conn inf inputs = do
       let ev = unsafeMapIO (mapM (\im -> do
                              h <- dynPK url (Just im)
                              updateArtStatus (Just im)  h).traceShowId  ) (rumors inputs)
           updateArtStatus  im it = do
              let i = fmap (first (lookKey inf "art")) it
              if null (i)
                 then return []
                 else maybeToList <$> updateMod conn (i)  (fromJust $ fmap F.toList im) (lookTable inf "art")
       bh <- stepper [] ev
       UI.div # sink UI.text (show <$> bh )



queryArtAndamento = BoundedPlugin "Andamento Art Crea" ("art",staticP url) elem
  where
    varTB = fmap ( fmap (BS.pack . renderShowable ))<$>  varT
    url :: ArrowPlug (Kleisli IO) [[String]]
    url = proc t -> do
      i <- varTB "art_number" -< t
      r <- at "crea_register" (proc t -> do
                               n <- varTB "crea_number" -< t
                               u <- varTB "crea_user"-< t
                               p <- varTB "crea_password"-< t
                               returnA -< liftA3 (, , ) n u p  ) -< t
      act (fmap (join .maybeToList) . traverse (\(i, (j, k,a)) -> creaConsultaArt  j k a i ) ) -< liftA2 (,) i r
    elem conn inf inputs = do
       consulta <- UI.button # set UI.text "Consultar"
       let ev = unsafeMapIO (\im -> do
                              h <- dynPK url im
                              updateArtStatus im  h ) (facts inputs <@ UI.click consulta)
           updateArtStatus  im i = do
              let artVeri d = (lookKey inf "art" "verified_date" ,STimestamp $ Finite $ (\(Just i)-> fst i) $ strptime "%d/%m/%Y %H:%M" ( d !!1) )
                  artPayd d = (lookKey inf "art" "payment_date" ,STimestamp $ Finite $ (\(Just i)-> fst i) $ strptime "%d/%m/%Y %H:%M" (d !!1) )
                  artInp inp = catMaybes [artVeri <$>  L.find (\[h,d,o] -> L.isInfixOf "Cadastrada" h )  inp ,artPayd <$> L.find (\[h,d,o] -> L.isInfixOf "Registrada" h ) (traceShowId inp) ]
              if null (artInp i)
                 then return []
                 else maybeToList <$> updateMod conn (artInp i)  (fromJust $ fmap F.toList im) (lookTable inf "art")
       i <- stepper [] ev
       out <- UI.div # sink UI.text (show <$> i )
       UI.div # set children [consulta ,out]

testParse = strptime "%d/%m/%Y %H:%M""24/03/2015 08:30"

strAttr :: String -> WriteAttr Element String
strAttr name = mkWriteAttr (set' (attr name))

queryGeocodeBoundary = BoundedPlugin "Google Geocode" ("address",staticP url) elem
  where
    elem conn inf inputs = do
      b <- UI.button # set UI.text "Import"
      let
          req im = runMaybeT $ do
            r <- getRequest  . traceShowId  . dynP url $im
            let dec = decode r :: Maybe Value
                loc = dec !> "results" !!> 0 !> "geometry" !> "location"
                bounds = dec !> "results" !!> 0 !> "geometry" !> "bounds"
                viewport = dec !> "results" !!> 0 !> "geometry" !> "viewport"
                lkey  = lookKey inf "address"
                getPos l = Position <$> liftA2 (\(A.Number i) (A.Number j)-> (realToFrac i ,realToFrac j ,0)) (l !> "lng" )( l  !> "lat" )
            p <- MaybeT $ return $ getPos loc
            b <- MaybeT $ return $ case (fmap Bounding $  (\i j -> Interval.interval (ER.Finite i ,True) (ER.Finite j ,True))<$> getPos (bounds !> "southwest") <*> getPos (bounds !> "northeast"), fmap Bounding $ (\i j -> Interval.interval (ER.Finite i ,True) (ER.Finite j ,True))<$> getPos (viewport !> "southwest") <*> getPos (viewport !> "northeast")) of
                                        (i@(Just _), _ ) -> i
                                        (Nothing , j) -> j
            mod <- C.lift $ updateMod conn [(lkey "geocode" ,SPosition p),( lkey "bounding", SBounding b)] (fromJust $ fmap F.toList im) (lookTable inf "address")
            C.lift $ traverse (logTableModification inf conn) mod
            return [(lkey "geocode" ,SPosition p),( lkey "bounding", SBounding b)]
      let et =  unsafeMapIO req (facts inputs <@ UI.click b)
      t <- stepper "" (show <$> et)
      out <- UI.div # UI.sink text t
      UI.div # set children [b,out]

    url :: FunArrowPlug String
    url = proc t -> do
      id <- varT "id" -< t
      log <- varT "logradouro"-< t
      num <- varN "number"-< t
      bai <- varN "bairro"-< t
      mun <- varT "municipio"-< t
      uf <- varT "uf"-< t
      returnA -<  "http://maps.googleapis.com/maps/api/geocode/json?address=" <> (HTTP.urlEncode $ vr log <> " , " <> vr num <> " - " <>  vr bai<> " , " <> vr mun <> " - " <> vr uf)
      where vr =  maybe "" renderShowable


varT t = join . fmap (unRSOptional'.snd)  <$> idxT t
varN t = fmap snd  <$> idx t

type FunArrowPlug o = Step.Parser (->) (Bool,[[Text]]) (Maybe (TB1 (Key,Showable))) o
type ArrowPlug a o = Step.Parser a (Bool,[[Text]]) (Maybe (TB1 (Key,Showable))) o

dynPK =  runKleisli . dynP

queryCEPBoundary = BoundedPlugin  "Correios CEP" ("address",staticP open  )  element
  where
      open :: ArrowPlug  (Kleisli IO ) (Maybe (Map Text Text))
      open = proc t -> do
          i <- varT "cep" -< t
          odx "bairro" -< t
          odx "municipio" -< t
          odx "uf" -< t
          odx "logradouro" -< t
          r <- (act (fmap join . traverse (\input -> do
                       v <- ( (`catch` (\e ->  return $ trace (show (e :: IOException )) "{}" ) ). simpleGetRequest  . traceShowId .  (\i-> addrs <> i <> ".json") ) . T.unpack $ input

                       return $ ( \i -> fmap ( M.filter (/="")) $ decode i ) v ))) -< (\(SText t)-> t) <$> i
          returnA -< r

      addrs ="http://cep.correiocontrol.com.br/"
      element conn inf inputs = do
        b <- UI.button # set UI.text "Submit"
        let
          tq :: Event (Maybe (Map Text Text))
          tq = unsafeMapIO (dynPK open) (facts inputs <@ UI.click b)

        bh <- stepper Nothing tq
        let
          Just table2 = M.lookup "address"  (tableMap inf)
          translate :: Text -> Text
          translate "localidade" =  "municipio"
          translate "cep" =  "cep"
          translate "uf" =  "uf"
          translate "bairro" =  "bairro"
          translate i = i
          -- tkeys = fmap (fmap SText . M.mapKeys ((\(Just i)-> i) . flip M.lookup (keyMap inf) . ("address",) . translate))  <$> (tidings bh (bh <@ UI.click b))
        e <- UI.div # sink UI.text (show <$> bh )
        body <-UI.div # set children [b,e]
        return body

executeStep
  :: Connection
  -> [(Key,Showable)]
  -> StepPlan (Maybe Showable)
  -> IO (Maybe [(Key,Showable)])
executeStep  conn inputs (TBPlan t  ta steps) =  do
          k <- mapM (executeStep conn inputs ) steps
          case t of
            TInsert -> do
               traverse (\i -> insertMod conn (concat i) ta) (allMaybes k)
               return $ Just []
            TUpdate -> do
               traverse (\i -> updateMod conn (concat i) inputs ta) (onlyJust k)
               return $ Just []
executeStep  _ _ (SPAttr t k v) = return $ fmap (\i -> [(k,i)]) v
executeStep  conn inputs (SPFK t (Path  i (FKJoinTable ti s tj ) j) steps) = do
  k <-  mapM (executeStep conn inputs) steps
  traceShowId <$> joinTable (M.fromList $ swap <$> s) <$> case t of
       FKEInsertGenerated -> do
         traverse (\i -> insertPK fromShowableList conn (concat i) tj) (allMaybes k)
       FKEUpdateFK -> do
         traverse (\i -> do
                    updateMod conn ( concat  i) inputs tj
                    let upPKs = filter ((`S.member` j) .fst) (concat i)
                    return  upPKs
                  ) (onlyJust k)

joinTable  m  i= join $ allMaybes . fmap (fmap swap . Tra.sequence . fmap (flip M.lookup  m) . swap ) <$> i

onlyJust = allNonEmpty . catMaybes

testPlan conn inf input ndata = executeStep  conn input   .  generateValues ndata .  traceShowId . generateStepPlan inf input

generateValues
  :: (Ord k, Functor f) => Map k a -> f (k, Maybe a -> b) -> f b
generateValues m plan = fmap (\(l,f)->  f  $ M.lookup l m ) plan

generateStepPlan
  :: InformationSchema
     -> [(Key, b)]
     -> (Text, [Step a])
     -> StepPlan (String, Maybe a -> Maybe Showable)
generateStepPlan inf input (tname , i) = TBPlan TUpdate table (fmap (attrPlan table) i)
  where
    attrPlan table (SAttr i) =  (if k `S.member` inputSet  then SPAttr AEUpdate  else SPAttr AEInsert) k $ transformAttr table i
        where k = (lookKey inf  (tableName  table) . fst . snd $ i)
    attrPlan table (SFK fk steps)
      | all (`S.member` inputSet) (fmap (lookKey inf (tableName table)) $ F.toList fk ) = SPFK FKEUpdateFK (fmap (lookTable inf) <$> path)  (attrPlan tfk <$> steps)
      | all (isSerial . keyType ) . filter (not . (`S.member` inputSet)  ) $ (F.toList fkt) = SPFK FKEInsertGenerated (fmap (lookTable inf) <$> path)  (attrPlan tfk <$> steps)
      | otherwise  = SPFK FKEInsertFind (fmap (lookTable inf) <$> path)  (attrPlan tfk <$> steps)
        where path@(Path _ (FKJoinTable _ _ j) fkt )  = justError ("table  " <> T.unpack (tableName table ) <>  " has no path for keyset " <> show fk  ) $ L.find (\(Path i _ _) -> S.map keyValue i == fk) (F.toList (rawFKS table) )
              tfk = lookTable inf j
    inputSet = S.fromList $ fmap fst input
    transformAttr table (i,(k,f)) = (i,(readTypeOpt (textToPrim <$> keyType nk ) .  fmap f))
        where nk = lookKey inf (tableName table) k
    table = lookTable inf tname

testPlan1 conn inf = testPlan conn inf (testInput inf ) testData ("owner",testStep)

testInput inf = [(lookKey inf "owner" "id_owner",SSerial $  Just $ SNumeric 4) {-,(lookKey inf "owner" "address" , SOptional $Just $SNumeric 41 ), (lookKey inf "address" "id" , SSerial$ Just $SNumeric 41 )-}]


testData :: (IsString a, IsString k, Ord k) => Map k a
testData = M.fromList [("NOME EMPRESARIAL","Massuda Engenharia"),("CEP","74140140"),("UF","GO"),("LOGRADOURO","Rua Rui Brasil Cavalcante"),("NÚMERO","436"),("COMPLEMENTO","APT 502"),("BAIRRO/DISTRITO","Setor Oeste"),("MUNICÍPIO","Goiânia")]

testStep = translate_o
  where
    translate_o =
      [SAttr ("NOME EMPRESARIAL",("owner_name",id))
      ,SFK (S.singleton "address") translate]
    translate = fmap SAttr
      [("CEP",("cep" , filter (not . (`elem` "-."))))
      ,("UF",("uf",id ))
      ,("LOGRADOURO",("logradouro", id))
      ,("NÚMERO",("number",id))
      ,("COMPLEMENTO",("complemento",id))
      ,("BAIRRO/DISTRITO",("bairro",id))
      ,("MUNICÍPIO",("municipio",id))]

testPlanner = withConnInf "incendio" testPlan1

testPdfGet conn inf inp =  runMaybeT$ do
  let addrs = "http://siapi.bombeiros.go.gov.br/relatorios/relatorio_exigencia_projeto_web.php"
      translate = [("protocolo" , "protocolo"),("ano","ano")]
      tempName = "temp" <> renderShowable (snd $ justError "no id project testPdfGet"  $L.find ((=="id_project").keyValue .fst) inp) <> ".pdf"
      fire_project = lookTable inf "fire_project"
      translate_q =
            [("Name",("analista",id))
            ,("tipo",("id_tipo",id))
            ,("subtipo",("id_subtipo",id))
            ,("Carga de incêndio",("carga_incendio", fst . L.break (' '==) ))]
      transK = nonUpdateTranslator inp $ translateK inf "fire_project" translate_q
  if (not . null $  transK )
     then do
        url <- MaybeT $ return $ renderUrlM translate addrs  $ filter (not . isEmptyShowable. snd )  <$> Just inp
        pdf <- getRequest $ traceShowId url
        C.lift $ BS.writeFile (tempName) (BSL.toStrict pdf)
        v <- C.lift $ parseBombeiroPdf tempName
        C.lift $ removeFile tempName
        v <- MaybeT $ return $ eitherToMaybeT $ v
        let vp  =  catMaybes . applyTranslator (M.fromList transK) . fmap (fmap (T.unpack . T.fromStrict ) )  $  v
        MaybeT $   updateMod  conn vp inp fire_project
      else MaybeT $ return Nothing



queryCNPJBoundary =
  let arrow :: FunArrowPlug  (Maybe Text)
      arrow = proc t -> do
        i <- varT "cnpj_number" -< t
        returnA -< (\(SText s)->  s)  <$> i
      elem conn inf inputs = do
          out <- UI.div
          ev <- liftIO  $ cnpjquery out (maybe "" id . fmap (BS.pack.T.unpack) . dynP arrow <$> inputs)
          s <- stepper [] (unsafeMapIO (\(inp,res) -> do
                      testPlan conn inf (traceShowId. catMaybes . fmap (traverse unRSOptional') . F.toList $ inp) ( M.fromList $ traceShowId res) ("owner",testStep)
                      return []
                            ) (filterJust $ liftA2 (,) <$> facts inputs <@> ev ))
          element out #+ [UI.div # sink UI.text s]
          return out
  in (BoundedPlugin "CNPJ Receita" ("owner",staticP arrow )   elem)

translateK inf t =  fmap  (\(i,(kv,f))->  (i,) $  (\kkv ->  (kkv,) $ readType (textToPrim <$> keyType kkv) . f ) (lkeys kv))
  where
            lkeys = lookKey inf t

nonUpdateTranslator  input =  filter (not . flip S.member (inpSet input) . fst . snd )
  where inpSet = S.fromList . fmap fst .  filter (not . isEmptyShowable . snd )

applyTranslator t i = fmap (\(k,v) ->  join $ (\(kv,f) -> fmap (kv,) (f$v))   <$> (M.lookup k t )) i

iframe = mkElement "iframe"



projectKey
  :: Connection
     -> InformationSchema ->
     (forall t . Traversable t => QueryT Identity (t KAttribute)
         -> S.Set Key -> IO [t (Key,Showable)])
projectKey conn inf q  = (\(j,(h,i)) -> fmap (fmap (zipWithTF (,) (fmap (\(Metric i)-> i) j))) . queryWith_ (fromShowableList j) conn . traceShowId . buildQuery $ i ) . projectAllKeys (pkMap inf ) (hashedGraph inf) q

projectTable
  :: Connection
     -> InformationSchema ->
     (forall t . Traversable t => QueryT Identity (t KAttribute)
         -> S.Set Key -> IO (t Key ,[t Showable]))
projectTable conn inf q  = (\(j,(h,i)) -> fmap (fmap (\(Metric k) -> k) j,)  . queryWith_ (fromShowableList j) conn . traceShowId . buildQuery $ i ) . projectAllKeys (pkMap inf ) (hashedGraph inf) q



projectKey'
  :: Connection
     -> InformationSchema ->
     (forall t . Traversable t => QueryT Identity (t KAttribute)
         -> S.Set Key -> IO [t (KAttribute ,Showable)])
projectKey' conn inf q  = (\(j,(h,i)) -> fmap (fmap (zipWithTF (,) j)) . queryWith_ (fromShowableList j) conn . traceShowId . buildQuery $ i ) . projectAllKeys (pkMap inf ) (hashedGraph inf) q


topSortTables tables = flattenSCCs $ stronglyConnComp item
  where item = fmap (\n@(Raw _ t k _ fk _ ) -> (n,k,fmap (\(Path _ _ end)-> end) (S.toList fk) )) tables


main :: IO ()
main = do
  --let schema = "public"
  --conn <- connectPostgreSQL "user=postgres password=queijo dbname=usda"
  {-
  let sorted = topSortTables (M.elems baseTables)

  print "DROPPING TABLES"
  traverse (\t -> do
    execute_ connTest . fromString . T.unpack . dropTable $ t
    print $ tableName t
    )  $ reverse  sorted

  print "CREATING TABLES"
  traverse (\t -> do
    execute_  connTest . fromString . T.unpack . createTable $ t
    print $ tableName t
    )  sorted
  -}
  -- preview $ cvLabeled (graphP )
--  preview $ cvLabeled (warshall graphP )
  startGUI (defaultConfig { tpStatic = Just "static", tpCustomHTML = Just "index.html"})  setup
  print "Finish"



