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
{-# LANGUAGE UndecidableInstances,FlexibleContexts,OverloadedStrings ,TupleSections, ExistentialQuantification #-}

import Query
import Types hiding (label)
import Step
import Location
import PrefeituraSNFSE
import Safe hiding (at)
import Siapi3
import CnpjReceita
-- import Widgets hiding (items)
import WX.QueryWidgets
import WX.Widgets
import Control.Concurrent
import Data.Functor.Apply
import System.Environment
import Debug.Trace
import Data.Ord
import Data.Tuple
import Data.Time.Format
import System.Locale
import Data.Aeson
import Utils
import Schema
import Data.Char (toLower)
import PandocRenderer
import Control.Monad
import Postgresql
import Data.Maybe
import Data.Functor.Identity
import Data.Time.Parse
-- import Reactive.Threepenny
import Data.Graph(stronglyConnComp,flattenSCCs)
import Data.Traversable (traverse)
import qualified Data.Traversable as Tra
import Data.Time.LocalTime
import Data.Functor.Compose
import qualified Data.List as L
import qualified Data.Vector as Vector
import qualified Data.ByteString.Char8 as BS
import qualified Data.ByteString.Lazy.Char8 as BSL
import Data.Time

import RuntimeTypes
-- import qualified Graphics.UI.Threepenny as UI
-- import Graphics.UI.Threepenny.Core hiding (get,delete)
import Data.Monoid hiding (Product(..))

import qualified Data.Foldable as F
import qualified Data.Text.Lazy as T
import Data.ByteString.Lazy(toStrict)
import Data.Text.Lazy.Encoding
import qualified Data.Text.Encoding as TE
import qualified Data.Text as TE
import Data.Text.Lazy (Text)
import qualified Data.Set as S


import Database.PostgreSQL.Simple as PG
import Database.PostgreSQL.Simple.Time
import qualified Data.Map as M
import Data.Map (Map)
import Data.String

import Graphics.UI.WX hiding (when,newEvent,Event,swap,Key)
import Reactive.Banana hiding (Identity)
import Reactive.Banana.WX hiding (when)

import Tidings



import Control.Arrow
import Crea



deleteChildren ref = do
              i <- get ref children
              mapM_ objectDelete i

main
     :: IO ()
main = start $ do
  args <- getArgs
  fr <- frame [ text := "Data Browser" ]
  f <- scrolledWindow fr [scrollRate := Size 5 5 ]
  set fr [layout := fill $ widget f]
  let net :: forall t . Frameworks t => Moment t ()
      net = do
          pnb1 <- liftIO $ panel f [fullRepaintOnResize := True]
          pnb2 <- liftIO $ panel f [fullRepaintOnResize := True]
          (dataItem ,net) <-  databaseChooser pnb1  args
          liftIO $ set  pnb1  [layout :=  dataItem ]
          liftIO $ set  f [layout := boxed "Database" $ column 5 [widget pnb1,fill $ boxed "Schema" $ widget pnb2 ]]
          runSubnet pnb2 (\paren -> fmap (maybe (column 0 []) id) . traverse (chooserKey (atMay args 4) paren )) net

  network <- compile net
  actuate network
  return ()

-- Run a subnet over a event with a parent window and returning layout
-- Automatically clear the parent and set the new layout
-- Perform Tidings initialization
runSubnet :: forall c a k . Form (Window c ) => Frameworks k => Window c -> (forall b t . Frameworks t => Window c -> a  -> Moment t Layout ) -> Tidings k a -> Moment k ()
runSubnet parent subnet event = do
          ini <- initial (facts event)
          out <- subnet parent ini
          liftIO $ set parent [layout := out]
          let
            nsubnet par inf  = do
                res <- subnet par inf
                liftIO $ set par [layout := res]
                return ()
          reactimate $ (\minf -> do
                        deleteChildren parent
                        ((actuate =<<) . (\inf -> compile ( nsubnet parent inf) )) minf
                        windowReFit parent
                        return () ) <$> rumors event


loginWidget :: forall b t . Frameworks t => Window b -> Maybe String -> Maybe String -> (Moment t (Layout,Tidings t (Maybe (String,String))))
loginWidget f userI passI =  mdo
  username <- liftIO $ entry f []
  password <- liftIO $ entry f [text := maybe "" id passI]
  td <- reactiveTextEntry username (tidings (pure (maybe "" id userI)) (rumors td) )
  sink password [text :== maybe "" id <$> passwordB]

  let dataItem = grid 2 2 [[label "Username:", widget username]
                              ,[label "Password:" , widget password]]
  passwordE <- fmap (\i -> if L.null i then Nothing else Just i) <$> eventText password
  let passwordB = stepper passI passwordE
      passwordT = tidings passwordB passwordE
  return  (dataItem, liftA2 (liftA2 (,)) ((\i -> if L.null i then Nothing else Just i) <$>td) passwordT)




mapTEvent f x = do
  (e,h) <- newEvent
  reactimate ((\i -> liftIO $  (f i)  >>= h) <$> (rumors x))
  i <- initial (facts x)
  be <- liftIO $ f i
  let t = stepper be e
  return $ tidings t e

listDBS ::  String -> IO (Map Text (Connection,[Text]))
listDBS dname = do
  connMeta <- connectPostgreSQL ("user=postgres dbname=postgres")
  dbs :: [Only Text]<- query_  connMeta "SELECT datname FROM pg_database  WHERE datistemplate = false"
  map <- M.fromList <$> mapM (\db -> do
        connDb <- connectPostgreSQL ("user=postgres dbname=" <> toStrict (encodeUtf8 db))
        schemas :: [Only Text] <- query_  connDb "SELECT schema_name from information_schema.schemata"
        return (db,(connDb,filter (not . (`elem` ["information_schema","pg_catalog","pg_temp_1","pg_toast_temp_1","pg_toast","public"])) $ fmap unOnly schemas))) (fmap unOnly dbs)
  return map

databaseChooser f sargs = mdo
  let args = fmap T.pack sargs
  dbs <- liftIO $ listDBS  (head sargs)
  let dbsInit = join $ fmap (\(d,s) -> (d,) . (,s) . fst <$>  M.lookup s dbs ) $ liftA2 (,) (safeHead args) (safeHead $ tail args)
  wid <- loginWidget f (atMay sargs 2) (atMay sargs 3)
  listBox     <- liftIO $ comboBox f []
  td <- reactiveComboDisplay listBox (pure $ concat $ fmap (\(i,(c,j)) -> (i,) . (c,) <$> j) $ M.toList dbs ) sel  (pure (\(i,(_,j))-> show (i,j) ))
  let sel = stepper dbsInit (rumors td)
  connect <- liftIO $ button f [ text := "Connect" ]
  eConnect <- event0 connect command
  sink connect [ enabled :== (facts (isJust . traceShowId .fmap fst<$> td ) )]
  let login = liftA2 (liftA2 (,)) (snd wid) ( td )
      formLogin = form login eConnect
  let genSchema ((user,pass),(dbN,(dbConn,schemaN))) = do
        conn <- connectPostgreSQL $ traceShowId $ ("user=" <> BS.pack user <> " password=" <> BS.pack pass <> " dbname=" <> toStrict ( encodeUtf8 dbN ))
        keyTables dbConn conn (schemaN,T.pack user)
  chooserT <-  mapTEvent (traverse genSchema) formLogin
  ee <- liftIO$ entry f []
  sink ee [text :== maybe "" (show.schemaName) <$> facts chooserT]
  let lay = grid 3 3 [[fst wid,widget connect,widget listBox,widget ee]]
  -- chooserDiv <- UI.div # set children [getElement wid ,getElement dbsW,load]
  return $ (lay,trace "inf" <$> chooserT )

form td ev =  tidings (facts td ) (facts td <@ ev )


instance Ord Connection where
  i < j = 1 < 2
  i <= j = 1 < 2
instance Eq Connection where
  i == j = True






{-
pollingUI' inf listRes p@(BoundedPollingPlugins n deftime (table,f) a) = do
    let plug = a inf
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
-}

line n =  set  text n
{-
-- Fix @select@ event not being fired when items are *un*selected.
fixSelectionsEvent :: (Selecting w, Reactive w, Selections w) => w -> IO ()
fixSelectionsEvent listbox =
    set listbox [ on unclick := handler ]
    where
    handler _ = do
        propagateEvent
        s <- get listbox selections
        when (s == []) $ get listbox (on select) >>= id
-}

-- List of buttons with constant value

chooserKey i f inf = do
  frame1 <- liftIO $ panel f []
  let initKey = pure . join $ fmap rawPK . flip M.lookup (tableMap inf) . T.pack <$> i
      kitems =  M.keys (pkMap inf )
  filterInp <- liftIO $ entry frame1 []
  event <-  eventText filterInp
  let filterInpBh = stepper "" event

  i :: [(Text,Int)] <- liftIO $ query (rootconn inf) (fromString "SELECT table_name,usage from metadata.ordering where schema_name = ?") (Only (schemaName inf))
  let orderMap = Just $ M.fromList  i
  bset <- buttonFSet  frame1 (L.sortBy (flip $  comparing (\ pkset -> liftA2 M.lookup  (fmap rawName . flip M.lookup (pkMap inf) $ pkset ) orderMap)) kitems)  initKey ((\j -> (\i -> L.isInfixOf (toLower <$> j) (toLower <$> i) ))<$> filterInpBh) (\i -> case M.lookup i (pkMap inf) of
                                       Just t -> T.unpack (translatedName t)
                                       Nothing -> show i )
  let bBset = snd bset
  reactimate  $ (\ i ->
      liftIO $ PG.execute (rootconn inf) (fromString $ "UPDATE  metadata.ordering SET usage = usage + 1 where table_name = ? AND schema_name = ? ") (( fmap rawName $ M.lookup i (pkMap inf)) ,  schemaName inf )
         >> return () ) <$> (rumors bBset)
  frame2 <- liftIO $ panel f []
  runSubnet frame2 (\window -> chooseKey window inf) ((snd bset))
  liftIO $ set frame1 [layout := column 5 [ widget filterInp, grid 0 0 (splits 8 $ fst bset)]]
  return $ column 10 [ widget frame1 , fill $ boxed "Table" $ expand $  widget frame2 ]

splits i [] = []
splits i xs = h : splits  i t
  where (h,t) = splitAt i xs

tableNonrec (TB1 k ) = concat $ F.toList $ _kvAttr $ fmap (attrNonRec .unTB) k

filterField f = do
  filterInp <- liftIO $ entry f []
  event <-  eventText filterInp
  let filterInpBh = stepper "" event
      filterInpT = tidings filterInpBh event
  return (filterInp,filterInpT)

-- joinTEvent = mapTEvent  id

chooseKey
  :: forall b t . Frameworks t => Window b -> InformationSchema -> S.Set Key -> Moment t Layout
chooseKey f inf key = mdo
  -- Filter Box (Saved Filter)
  frame1 <- liftIO $ panel f []
  let bBset = pure key :: Tidings t (S.Set Key)
  vp <- mapTEvent  (\j -> do
                    let rp = rootPaths'  (tableMap inf) (fromJust  $ M.lookup j $ pkMap inf )
                    queryWith_ (fromAttr (fst rp) ) (conn inf) (traceShowId $ fromString $ T.unpack $ snd rp)
                    ) bBset
  -- Final Query ListBox
  (filterInp,filterInpT ) <- filterField frame1

  let sortSet =  F.toList . tableNonrec  . allRec' (tableMap inf). (\(Just i)-> i) . flip M.lookup (pkMap inf) <$> bBset
  sortList <- liftIO $ multiListBox frame1 []
  sortListT  <- reactiveMultiListDisplay sortList (facts sortSet)  sortListB  (pure show)
  v <- initial (facts $ F.toList <$> bBset)
  let sortListB = stepper v (unions [ rumors $ F.toList <$> bBset, rumors sortListT])
  box <- liftIO $checkBox frame1 []
  asc <- checkedWidget box (pure True)
  let
      filteringPred i = (T.isInfixOf (T.pack $ toLower <$> i) . T.toLower . T.intercalate "," . fmap (T.pack . renderShowable) . F.toList . fmap snd)
  itemList <- liftIO $ singleListBox frame1 []
  itemListT <- reactiveListDisplay itemList ( sorting <$> (facts (triding asc ))<*> (facts sortListT )<*> res2 )  itemListB  (pure (L.intercalate "," . (F.toList . fmap (renderShowable . snd ) . _kvKey . allKVRec))) -- ((\l -> (\ i -> (set UI.style (noneShow $ filteringPred l i  ) ) . line (   L.intercalate "," (F.toList $ fmap (renderShowable . snd ) $  _kvKey $ allKVRec i) <> "," <>  (L.intercalate "," $ fmap (renderShowable.snd) $  tableNonrec i)))) <$> filterInpT)
  ini <- initial (pure Nothing ) -- (facts itemListT)
  let itemListB = stepper ini (unions [rumors itemListT])
  -- element (getElement itemList) # set UI.multiple True
  -- element itemList # set UI.style [("width","70%"),("height","300px")]

  let
     table = (\(Just i)-> i) $ M.lookup key (pkMap inf)

  (crud,evs) <- crudUITable frame1 inf  {-[queryTimeline,lplugOrcamento ,siapi3Plugin ,siapi2Plugin , gerarPagamentos , notaPrefeitura,queryArtCrea , queryArtBoletoCrea , queryCEPBoundary  ,queryGeocodeBoundary,queryCNPJStatefull,queryCPFStatefull,queryTimeline, queryArtAndamento ] -} []  res2  [] (allRec' (tableMap inf) table) (itemListT )
  vpi <- initial (facts vp)
  let eres = fmap addToList <$> evs
      res2 = accumB vpi  (unions $ (const <$> rumors vp): eres)
  -- (res2,crud) <- whenWriteable
  -- codeChk <- checkedWidget (pure False)
  -- createcode <- UI.textarea # set UI.text (T.unpack$ createTable table)
   --           # set style [("width","100%"),("height","300px")]
  -- dropcode <- UI.textarea # set UI.text (T.unpack$ dropTable table)
    --          # set style [("width","100%"),("height","300px")]
  -- code <- tabbed [("CREATE",createcode),("DROP",dropcode)]
  -- tab <- tabbedChk  (maybeToList crud <> [("CODE",(codeChk,code))])
  -- itemSel <- UI.ul # set items ((\i -> UI.li # set children [ i]) <$> [filterInp,getElement sortList,getElement asc] )
--   itemSelec <- UI.div # set children [getElement itemList, itemSel] # set UI.style [("display","inline-flex")]
 --  UI.div # set children ([itemSelec] )
  liftIO $ set frame1 [layout := (row 10 [column 5 [  widget sortList , widget box, row 10 [label "Filtrar" , widget filterInp],crud ],widget itemList])]
  return $ fill $ widget frame1

{-
lplugOrcamento = BoundedPlugin2 "Orçamento" "pricing" (fst renderProjectPricingA )  ( snd renderProjectPricingA )

{-
testPlugin db pg input = startGUI defaultConfig $ \w -> do
    let e = withConnInf db (\inf -> fst <$> pg inf (pure (fmap (\((t,k),v) -> (lookKey inf t k ,v)) <$> input)))
    getBody w #+ [e]
    return ()
-}


testShowable  v s = case s of
          (SOptional Nothing ) -> False
          (SOptional (Just i)) -> testShowable v i
          i -> v i


(siapi2Polling   :: PollingPlugisIO  , siapi2Plugin :: Plugins) = (BoundedPollingPlugins "Siapi2 Andamento" 60 ("fire_project" ,staticP url) elem,BoundedPlugin2 "Siapi2 Andamento" "fire_project"(staticP url) elemp)

  where
    varTB = fmap ( fmap (BS.pack . renderShowable ))<$>  varT
    url :: ArrowPlug (Kleisli IO) (Maybe (TB1 (Text,Showable)))
    url = proc t -> do
      protocolo <- varTB "protocolo" -< t
      ano <- varTB "ano" -< t
      odx "aproval_date" -< t
      odx "andamentos:andamento_date" -<  t
      odx "andamentos:andamento_description" -<  t
      b <- act ( Tra.traverse  (\(i,j)-> if read (BS.unpack j) >= 15 then  return Nothing else fmap traceShowId (siapi2  i j)  )) -<  (liftA2 (,) protocolo ano )
      let ao bv =   case  join (findTB1 (== iat  bv)<$> (fmap (first keyValue) <$> t)) of
                    Just i -> Nothing
                    Nothing -> Just $ TB1 $ KV (PK [] []) ( [iat bv])
          convertAndamento :: [String] -> TB1 (Text,Showable)
          convertAndamento [da,des] =  TB1 $ fmap (Compose . Identity .Attr ) $ KV  (PK [] []) ([("andamento_date",STimestamp . Finite . fst . justError "wrong date parse" $  strptime "%d/%m/%y" da  ),("andamento_description",SText (T.filter (not . (`L.elem` "\n\r\t")) $ T.pack  des))] )
          convertAndamento i = error $ "convertAndamento " <> show i
          iat bv = Compose . Identity $ (IT
                                            [Compose . Identity $ Attr $ ("andamentos",SOptional Nothing)]
                                            "fire_project_event"
                                            (LeftTB1 $ Just $ ArrayTB1 $ reverse $  fmap convertAndamento bv))
      returnA -< join  (  ao  .  tailEmpty . concat <$> join b)

    elem inf =  fmap (pure. catMaybes) . mapM (\inp -> do
                              b <- dynPK url (Just  inp)
                              let o =  fmap (first (lookKey'  inf ["fire_project_event","fire_project"])) <$> b
                              maybe (return Nothing )  (\i -> updateModAttr inf i inp (lookTable inf "fire_project")) o
                            )
    elemp inf = maybe (return Nothing) (\inp -> do
                              b <- dynPK url (Just inp)
                              return $ fmap (first (lookKey'  inf ["fire_project_event","fire_project"])) <$> b)




type PollingPlugisIO = PollingPlugins [TB1 (Key,Showable)] (IO [([TableModification Showable])])

(siapi3Polling   :: PollingPlugisIO  , siapi3Plugin :: Plugins) = (BoundedPollingPlugins "Siapi3 Andamento" 60 ("fire_project" ,staticP url) elem,BoundedPlugin2 "Siapi3 Andamento" "fire_project"(staticP url) elemp)

  where
    varTB = fmap ( fmap (BS.pack . renderShowable ))<$>  varT
    url :: ArrowPlug (Kleisli IO) (Maybe (TB1 (Text,Showable)))
    url = proc t -> do
      protocolo <- varTB "protocolo" -< t
      ano <- varTB "ano" -< t
      cpf <- varTB "id_owner,id_contact:id_owner:cgc_cpf" -< t
      odx "aproval_date" -< t
      odx "andamentos:andamento_date" -<  t
      odx "andamentos:andamento_description" -<  t
      b <- act (fmap join .  Tra.traverse   (\(i,j,k)-> if read (BS.unpack j) <= 14 then  return Nothing else siapi3  i j k )) -<   (liftA3 (,,) protocolo ano cpf)
      let convertAndamento [_,da,desc,s,sta] = TB1 $ fmap (Compose . Identity .Attr ) $ KV (PK [] []) ([("andamento_date",STimestamp . Finite .  fst . justError "wrong date parse" $  strptime "%d/%m/%Y %H:%M:%S" da  ),("andamento_description",SText $ T.pack  desc)] )
          convertAndamento i = error $ "convertAndamento2015 :  " <> show i
      let ao bv = case  join $ (findTB1 (== iat  bv)<$> (fmap (first keyValue) <$> t)) of
                    Just i ->  Nothing
                    Nothing ->  traceShow (iat bv,t) $  Just $ TB1 $ KV (PK [] []) ( [iat bv])
          iat bv = Compose . Identity $ (IT
                                            [Compose . Identity $ Attr $ ("andamentos",SOptional Nothing)]
                                            "fire_project_event"
                                            (LeftTB1 $ Just $ ArrayTB1 $ reverse $ fmap convertAndamento bv))
      returnA -< join  ( ao . fst <$> b)

    elem inf =  fmap (pure. catMaybes) . mapM (\inp -> do
                              b <- dynPK url (Just  inp)
                              let o =  fmap (first (lookKey'  inf ["fire_project_event","fire_project"])) <$> b
                              maybe (return Nothing )  (\i -> updateModAttr inf i inp (lookTable inf "fire_project")) o
                            )
    elemp inf = maybe (return Nothing) (\inp -> do
                              b <- dynPK url (Just inp)
                              return $ fmap (first (lookKey'  inf ["fire_project_event","fire_project"])) <$> b)


lookKey' inf t k = justError ("lookKey' cant find key " <> show k <> " in " <> show t) $  foldr1 mplus $ fmap (\ti -> M.lookup (ti,k) (keyMap inf)) t

eitherToMaybeT (Left i) =  Nothing
eitherToMaybeT (Right r) =  Just r

deleteMod inf kv table = do
  delete (conn inf)  kv table
  Just <$> logTableModification inf (TableModification Nothing table (DeleteTB kv))

updateModAttr inf kv old table = do
  (i,j) <- updateAttr (conn  inf) kv old table
  Just <$> logTableModification inf j

insertMod inf kv table = do
  kvn <- insertAttr fromAttr (conn  inf) kv table
  let mod =  TableModification Nothing table (InsertTB  kvn)
  Just <$> logTableModification inf mod


logTableModification inf (TableModification Nothing table i) = do
  let look k = lookKey inf "modification_table" k
  time <- getCurrentTime
  let ltime = STimestamp . Finite . utcToLocalTime utc $ time
  s <- insertAttr fromAttr (conn inf) (TB1 $ fmap (Compose . Identity . Attr)$KV (PK  [(look "modification_id",SSerial Nothing)] []) [(look "modification_time", ltime ),(look "table_name" ,SText $ rawName table) , (look "modification_data", SText $ T.pack $ show i)]  ) ((\(Just i)-> i) $ M.lookup ("modification_table") (tableMap inf))
  return (TableModification ((\(SSerial (Just (SNumeric i)))-> Just i ) $  snd $  unAttr $ runIdentity $ getCompose $ head $_pkKey $ _kvKey $ _unTB1 s) table i )


bradescoRead file = do
  file <- TE.decodeLatin1 <$> BS.readFile file
  let result =  fmap (fmap TE.unpack . L.take 5) $ filter (\(i:xs) -> isJust $ strptime "%d/%m/%y" (TE.unpack i)) $ filter ((>5) . length) $  TE.split (';'==) <$> TE.split (=='\r') file
  return result


sdate = SDate . Finite . localDay
stimestamp = STimestamp . Finite

{-
bradescoExtractTxt  inf   inputs = do
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
          vp <- doQueryAttr inf (projectAllRec' (tableMap inf)) (uncurry M.singleton $  fmap ( (\i->[i]) . Category . S.singleton . flip PK [].(\i->[i]) ) (lookInput inp ) ) ( (\(Raw _ _ pk _ _ _ ) -> pk ) $(\(Just i)-> i) $  M.lookup  "transaction" (tableMap inf ))
          let kk = S.fromList (fmap (M.fromList . filter ((`elem` ["id_account","transaction_description","transaction_date","transaction_price"] ) . keyValue . fst ) . F.toList ) vp) :: S.Set (Map Key Showable)
          adds <- mapM (\kv -> (`catch` (\e -> return $ trace ( show (e :: SqlError)) Nothing )) $ fmap Just $ insertPK fromShowableList  (conn inf) (M.toList kv) ((\(Just i)-> i) $ M.lookup  "transaction" (tableMap inf) )) (S.toList $ ( S.fromList parse ) `S.difference` kk)
          return parse
        process Nothing _ = do return []
        j = unsafeMapIO id $ process  <$> facts inputs <*> bhInp <@ UI.click b
    outStp <- stepper "" (fmap show $ j)
    out <- UI.div # sink UI.text outStp
    (,pure Nothing) <$> UI.div # set children [pathInput,b,out]

itauExtractTxt  inf   inputs = do
    pathInput <- UI.input -- # set UI.type_ "file"
    b <- UI.button # set UI.text "Import"
    bhInp <- stepper "" (UI.valueChange pathInput)
    let process (Just inp) path = do
          file <-  readFile (traceShowId path)
          let parse  = uncurry M.insert (lookInput inp )  . tkeys . parseField . unIntercalate (';'==) <$> lines (filter (/='\r') file)
              lookInput = (\(Just i)-> i) .L.find ((== "id_account") . keyValue . fst)
              tkeys v =  M.mapKeys (lookKey  inf "transaction")  v
              parseField [d,desc,v] = M.fromList [("transaction_date", SDate $ Finite $ localDay $ fst $ (\(Just i)-> i) $ strptime "%d/%m/%Y" d),("transaction_description",SText $ T.pack desc),("transaction_price", SDouble $ read $ fmap (\i -> if i == ',' then '.' else i) v)]
          vp <- doQueryAttr inf (projectAllRec' (tableMap inf)) (uncurry M.singleton $  fmap ( (\i->[i]) . Category . S.singleton . flip PK [].(\i->[i]) ) (lookInput inp ) ) ( (\(Raw _ _ pk _ _ _ ) -> pk ) $(\(Just i)-> i) $  M.lookup  "transaction" (tableMap inf ))
          let kk = S.fromList (fmap (M.fromList . filter ((`elem` ["id_account","transaction_description","transaction_date","transaction_price"] ) . keyValue . fst ) . F.toList ) vp) :: S.Set (Map Key Showable)
          adds <- mapM (\kv -> (`catch` (\e -> return $ trace ( show (e :: SqlError)) Nothing )) $ fmap Just $ insertPK fromShowableList  (conn inf)  (M.toList kv) ((\(Just i)-> i) $ M.lookup  "transaction" (tableMap inf) )) (S.toList $ ( S.fromList parse ) `S.difference` kk)
          return parse
        process Nothing _ = do return []
        j = unsafeMapIO id $ process  <$> facts inputs <*> bhInp <@ UI.click b
    outStp <- stepper "" (fmap show $ j)
    out <- UI.div # sink UI.text outStp
    (,pure Nothing) <$> UI.div # set children [pathInput,b,out]
-}

fkattrsB inputs fks = foldr (liftA2 (:))   inputs fks


tailEmpty [] = []
tailEmpty i  = tail i



data Timeline
  = Timeline
  { header :: String
  , dates :: [(Either Day LocalTime,String)]
  }

queryTimeline = BoundedPlugin "Timeline" "pricing"(staticP arrow)  elem
  where
    convDateArr i = swap . fmap projDate  <$> (catMaybes $ fmap (traverse unRSOptional') $ catMaybes $ i)
    projDate (SDate (Finite f)) = Left f
    projDate (STimestamp (Finite f)) =  Right f
    projDate (SOptional (Just j )  ) = projDate j
    projDate i = error $ " projDate " <> show i
    arrow :: FunArrowPlug [(Either Day LocalTime,String)]
    arrow = proc t -> do
      prd <- varT "pricing_date" -< t
      papr <- varN "pricing_approval" -< t
      apd <- varN "id_project:aproval_date" -< t
      arr <- varN "pagamentos:payment_date" -< t
      arrD <- varN "pagamentos:payment_description" -< t
      andDa <- varN "id_project:andamentos:andamento_date" -< t
      andDe <- varN "id_project:andamentos:andamento_description" -< t
      let vv =  concat $ maybeToList $ (\(SComposite i) (SComposite j)-> fmap Just $ zip (renderShowable <$> F.toList j ) (F.toList i)) <$>  arr <*> arrD

      returnA -<  convDateArr ([("Proposta de Enviada",)<$> prd,("Projeto Aprovado",) <$> apd ,("Proposta Aprovada",) <$> papr] <>  vv {-<> vvand -})
    elem inf inputs = do
        e <- UI.div # set UI.id_ "timeline-embed"
        let  timeline i = Timeline "hello" (dynP arrow $ i)
        i <- UI.div # sink UI.html  (fmap (\i->  "<script>    var container = document.getElementById('timeline-embed');var items = new vis.DataSet("  <>  BSL.unpack ( encode (timeline i)) <> ") ;  var options = {} ; if (container.vis != null ) { container.vis.destroy(); } ; container.vis = new vis.Timeline(container,items,options); </script>") $ facts inputs)
        UI.div # set children [e,i]


instance ToJSON Timeline where
  toJSON (Timeline h v) = toJSON (dates <$> zip [0..] v)

    where dates (id,(Right i,j)) = object ["id" .= (id :: Int) ,"start" .=  ti i, "content" .= j, "type" .= ("point" :: String)]
          dates (id,(Left i,j)) = object ["id" .= (id :: Int) ,"start" .=  tti i, "content" .= j, "type" .= ("point" :: String)]
          ti  = formatTime defaultTimeLocale "%Y/%m/%d"
          tti  = formatTime defaultTimeLocale "%Y/%m/%d %H:%M:%S"

attrT = Compose . Identity. Attr
gerarPagamentos = BoundedPlugin2 "Pagamentos" "plano_aluno" (staticP url) elem
  where
    url :: ArrowPlug (Kleisli IO) (Maybe (TB1 (Text,Showable)))
    url = proc t -> do
      v <- varT "frequencia,meses:price" -< t
      m <- varT "frequencia,meses:meses"-< t
      k <- varT "desconto"-< t
      pinicio <- varT "pagamento:inicio"-< t
      p <- varT "pagamento:vezes"-< t
      let valorTotal =  liftA3 (\v m k -> v* (fromIntegral m)*(1 - k)) v m k
          valorParcela = liftA2 (\v p -> v/(p))  valorTotal p
      f <- varT "pagamento:forma_pagamento:forma"-< t
      odx "pagamento:pagamentos:price" -<  t
      odx "pagamento:pagamentos:scheduled_date" -<  t
      let pagamento = Compose $ Identity $ FKT ([Compose $ Identity $ Attr $ ("pagamentos",SOptional  $ Just $ SComposite (Vector.fromList $ replicate (maybe 0 fromIntegral  p)  (SOptional Nothing)))]) True [] (LeftTB1 $ Just $ ArrayTB1 (replicate (maybe 0 fromIntegral  p) (TB1 (KV (PK [attrT ("id",SSerial Nothing)] [attrT ("description",SOptional Nothing)]) [attrT ("price",SOptional valorParcela), attrT ("scheduled_date",SOptional pinicio) ]))))
          ao :: Maybe (TB1 (Text,Showable))
          ao =  Just $ TB1 $ KV (PK [] []) [Compose $ Identity $ IT [Compose $ Identity $ Attr$  ("pagamento",SOptional Nothing)] "parcelamento" (LeftTB1 $ Just $ TB1 $ KV (PK [] [] ) [pagamento ])]

      returnA -< ao

    elem inf = maybe (return Nothing) (\inp -> do
                              b <- dynPK url (Just inp)
                              return $ fmap (first (lookKey' inf ["parcelamento","plano_aluno","pagamento"])) <$> b
                            )


notaPrefeitura = BoundedPlugin2 "Nota Prefeitura" "nota"(staticP url) elem
  where
    varTB = fmap ( fmap (BS.pack . renderShowable ))<$>  varT
    url :: ArrowPlug (Kleisli IO) (Maybe (TB1 (Text,Showable)))
    url = proc t -> do
      i <- varTB "id_nota" -< t
      odx "nota" -<  t
      r <- at "inscricao" (proc t -> do
                               n <- varTB "inscricao_municipal" -< t
                               u <- varTB "goiania_user"-< t
                               p <- varTB "goiania_password"-< t
                               returnA -< liftA3 (, , ) n u p  ) -< t
      b <- act (fmap join  . traverse (\(i, (j, k,a)) -> prefeituraNota j k a i ) ) -< liftA2 (,) i r
      let ao =  Just $ TB1 $ KV (PK [] []) [_tb $ Attr  ("nota",    SOptional b)]
      returnA -< ao

    elem inf = maybe (return Nothing) (\inp -> do
                              b <- dynPK url (Just inp)
                              return $ fmap (first (lookKey inf "nota")) <$> b
                            )

queryArtCrea = BoundedPlugin2 "Documento Final Art Crea" "art"(staticP url) elem
  where
    varTB = fmap ( fmap (BS.pack . renderShowable ))<$>  varT
    url :: ArrowPlug (Kleisli IO) (Maybe (TB1 (Text,Showable)))
    url = proc t -> do
      i <- varTB "art_number" -< t
      idxT "payment_date" -<  t
      odx "art" -<  t
      r <- at "crea_register" (proc t -> do
                               n <- varTB "crea_number" -< t
                               u <- varTB "crea_user"-< t
                               p <- varTB "crea_password"-< t
                               returnA -< liftA3 (, , ) n u p  ) -< t
      b <- act (fmap join  . traverse (\(i, (j, k,a)) -> creaLoginArt  j k a i ) ) -< liftA2 (,) i r
      let ao =  Just $ TB1 $ KV (PK [] []) [_tb $ Attr  ("art",    SOptional b)]
      returnA -< ao
    elem inf = maybe (return Nothing) (\inp -> do
                              b <- dynPK url (Just inp)
                              return $ fmap (first (lookKey inf "art")) <$> b
                            )


queryArtBoletoCrea :: Plugins
queryArtBoletoCrea = BoundedPlugin2 "Boleto Art Crea" "art"(staticP url) elem
  where
    varTB = fmap ( fmap (BS.pack . renderShowable ))<$>  varT
    url :: ArrowPlug (Kleisli IO) (Maybe (TB1 (Text,Showable)))
    url = proc t -> do
      i <- varTB "art_number" -< t
      idxT "verified_date" -< t
      odx "boleto" -< t
      r <- at "crea_register" (proc t -> do
                               n <- varTB "crea_number" -< t
                               u <- varTB "crea_user"-< t
                               p <- varTB "crea_password"-< t
                               returnA -< liftA3 (, , ) n u p  ) -< t
      b <- act ( traverse (\(i, (j, k,a)) -> creaBoletoArt  j k a i ) ) -< liftA2 (,) i r
      let ao =  Just $ TB1 $ KV (PK [] []) [_tb $ Attr  ("boleto",   SOptional $ (SBinary. BSL.toStrict) <$> b)]
      returnA -< ao
    elem inf
       = maybe (return Nothing) (\inp -> do
                            b <- dynPK url (Just inp)
                            return $ fmap (first (lookKey inf "art")) <$> b
                            )



checkOutput i = proc t -> do
      o <- odx i -< fst t
      v <- odx i -< snd t
      returnA -< if isJust o  && fmap snd o == fmap snd v
         then Nothing
         else v



(queryArtAndamento ,artAndamentoPolling :: PollingPlugisIO ) = (BoundedPlugin2 "Andamento Art Crea" "art"(staticP url) elemp,BoundedPollingPlugins "Andamento Art Crea"  60 ("art",staticP url) elem)
  where
    varTB = fmap ( fmap (BS.pack . renderShowable ))<$>  varT
    url :: ArrowPlug (Kleisli IO) (Maybe (TB1 (Text,Showable)))
    url = proc t -> do
      i <- varTB "art_number" -< t
      odx "payment_date" -< t
      odx "verified_date" -< t
      r <- at "crea_register" (proc t -> do
                               n <- varTB "crea_number" -< t
                               u <- varTB "crea_user"-< t
                               p <- varTB "crea_password"-< t
                               returnA -< liftA3 (, , ) n u p  ) -< t
      v <- act (fmap (join .maybeToList) . traverse (\(i, (j, k,a)) -> creaConsultaArt  j k a i ) ) -< liftA2 (,) i r
      let artVeri dm = ("verified_date" ,) . SOptional . join $(\d ->  fmap (STimestamp . Finite . fst) $ strptime "%d/%m/%Y %H:%M" ( d !!1) ) <$> dm
          artPayd dm = ("payment_date" ,) . SOptional . join $ (\d -> fmap (STimestamp . Finite . fst )  $ strptime "%d/%m/%Y %H:%M" (d !!1) ) <$> dm
          artInp inp = Just $ TB1 $ KV (PK [] [] ) $fmap (Compose . Identity . Attr ) $ [artVeri $  L.find (\[h,d,o] -> L.isInfixOf "Cadastrada" h )  inp ,artPayd $ L.find (\[h,d,o] -> L.isInfixOf "Registrada" h ) (inp) ]
      i <- checkOutput "verified_date" -< (t,artInp v)
      j <- checkOutput "payment_date" -< (t,artInp v)
      returnA -< (catMaybes [i, j] )
      returnA -< Just $ TB1 $KV  (PK [] [] ) $ fmap (Compose . Identity . Attr ) $  catMaybes [ i,j]
    elem inf =  fmap (pure. catMaybes) . mapM (\inp -> do
                              b <- dynPK url (Just  inp)
                              let o =  fmap (first (lookKey'  inf ["art"])) <$> b
                              maybe (return Nothing )  (\i -> if L.null (F.toList i) then return Nothing else updateModAttr inf i inp (lookTable inf "art")) o
                            )
    elemp inf
          = maybe (return Nothing) (\inp -> do
                   b <- dynPK url (Just inp)
                   return $ fmap (first (lookKey inf "art")) <$> b)


queryCPFStatefull =  StatefullPlugin "CPF Receita" "owner" [([(True,[["cpf_number"]])],[(False ,[["captchaViewer"]])]),([(True,[["captchaInput"]])],[(True,[["owner_name"]])])]   [[("captchaViewer",Primitive "jpg") ],[("captchaInput",Primitive "character varying")]] cpfCall


queryCNPJStatefull = StatefullPlugin "CNPJ Receita" "owner"
  [([(True,[["cnpj_number"]])]
    ,[(False ,[["captchaViewer"]])])
  ,([(True,[["captchaInput"]])]
    ,[(True,[["owner_name"]])
      ,(True,[["address"]])
      ,(True,[["atividades_secundarias"]])
      ,(True,[["atividades_secundarias"],["id"]])
      ,(True,[["atividades_secundarias"],["description"]])
      ,(True,[["atividade_principal"]])
      ,(True,[["atividade_principal"],["id"]])
      ,(True,[["atividade_principal"],["description"]])
      ,(True,[["address"],["logradouro"]])
      ,(True,[["address"],["number"]])
      ,(True,[["address"],["uf"]])
      ,(True,[["address"],["cep"]])
      ,(True,[["address"],["complemento"]])
      ,(True,[["address"],["municipio"]])
      ,(True,[["address"],["bairro"]])
      ])]
  [[("captchaViewer",Primitive "jpg") ],[("captchaInput",Primitive "character varying")]] wrapplug


topSortTables tables = flattenSCCs $ stronglyConnComp item
  where item = fmap (\n@(Raw _ _ _ t _ k _ fk _ ) -> (n,k,fmap (\(Path _ _ end)-> end) (S.toList fk) )) tables



main :: IO ()
main = do
  args <- getArgs
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
  (e:: Event [[TableModification (Showable) ]] ,h) <- newEvent

  forkIO $ poller h siapi3Polling
  forkIO $ poller h siapi2Polling
  forkIO $ poller h artAndamentoPolling



  startGUI (defaultConfig { tpStatic = Just "static", tpCustomHTML = Just "index.html"})  (setup e args)
  print "Finish"

poller handler (BoundedPollingPlugins n d (a,f) elem ) = do
  conn <- connectPostgreSQL ("user=postgres dbname=incendio")
  inf <- keyTables conn  conn ("incendio","postgres")
  let loop =  do
        print =<<  getCurrentTime
        print ("START" ::String)
        let rp = rootPaths'  (tableMap inf) (fromJust  $ M.lookup  a  $ tableMap inf )
        listRes <- queryWith_ (fromAttr (fst rp) ) conn  (traceShowId $ fromString $ T.unpack $ snd rp)
        let evb = filter (\i -> tdInput i  && tdOutput1 i ) listRes
            tdInput i =  maybe False (const True) $ allMaybes $ fmap (\t -> (if fst t then join . fmap unRSOptional' else id ) $ fmap snd $ (indexTable  $ snd t) i) (fst f)
            tdOutput1 i =  maybe True (const False) $ allMaybes $ fmap (\f -> (if not(fst f ) then join . fmap unRSOptional' else id ) $ fmap snd $ (indexTable  $ snd f) i) (snd f)

        i <- elem inf evb
        handler i
        print =<<  getCurrentTime
        print ("END" ::String)
        threadDelay (d*1000*1000*60)
        loop
  loop
{-
layout  infT = do
  vis <- UI.div # set UI.id_ "visualization"
  let draw inf  =
        let
            -- g = graphP inf
            v :: [(Int,Set Key)]
            v = zip [0..] (L.nub $ hvertices g <> tvertices g)
            e = filter  (\case {(Path _ _ _)-> True ; i -> False}) $ concat $ fmap snd $ M.toList $ edges g
            vmap = M.fromList $ swap <$>  v
            genVertices (i,t ) = object [ "id" .= i, "label" .= T.intercalate "," (F.toList (S.map keyValue t)) ]
            genEdges (Path i (FKJoinTable m _ l)  j ) = object [ "from" .= lid i , "to" .= lid j  , "label" .= (tableName m <> " join " <> tableName l ) ]
            genEdges (Path i (FetchTable  l)  j ) = object [ "from" .= lid i , "to" .= lid j  , "label" .= tableName l ]
            genEdges (Path i (FKInlineTable l)  j ) = object [ "from" .= lid i , "to" .= lid j  , "label" .= tableName l ]
            lid t = justError ("no key " <> show t) (M.lookup t vmap)
            nodesJSON = "var nodes = " <> encode (genVertices <$> v) <> ";"
            edgesJSON = "var edges = " <> encode (genEdges <$> e) <> ";"
            graphJSON = "<script> " <> BSL.unpack (nodesJSON <> edgesJSON) <> "var container = document.getElementById('visualization');  var data = { nodes: nodes,edges: edges}; var options = { hierarchicalLayout : { layout : 'direction' } , edges : { style : 'arrow'}} ;  var network = new vis.Network(container, data, options ); </script> "
        in graphJSON
  script <- UI.div # sink UI.html (maybe "" draw <$> infT)
  UI.div # set children [vis,script]
-}
{- testParse sch q = withConnInf sch (\inf -> do
                                       let (rp,rpq) = rootPaths' (tableMap inf) (fromJust $ M.lookup q (tableMap inf))
                                       putStrLn (  show rpq)
                                       putStrLn (  show rp)
                                       q <- queryWith_ (fromAttr (rp) ) (conn  inf) (fromString $ T.unpack $ rpq)
                                       putStrLn$  unlines $ fmap show q
                                           )
testFireQuery q = testParse "incendio"  q
testAcademia q = testParse "academia"  q
-}
-}

