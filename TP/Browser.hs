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
import Types
import qualified Data.Binary as B
import Step
-- import Graph
import Location
import Plugins
import TP.Widgets
import SortList
import TP.QueryWidgets
import Control.Monad.Reader
import Control.Concurrent
import Data.Functor.Apply
import System.Environment
import Debug.Trace
import Data.Ord
import Control.Exception
import Data.Time.Parse
import Utils
import Schema
import Patch
import Data.Char (toLower)
import Postgresql
import PostgresQuery
import Data.Maybe
import Data.Functor.Identity
import Reactive.Threepenny
import Data.Traversable (traverse)
import qualified Data.Traversable as Tra
import Data.Time.LocalTime
import qualified Data.List as L
import qualified Data.Vector as Vector
import qualified Data.ByteString.Char8 as BS
import qualified Data.ByteString.Lazy.Char8 as BSL
import Data.Time

import RuntimeTypes
import qualified Graphics.UI.Threepenny as UI
import Graphics.UI.Threepenny.Core hiding (get,delete)
import Data.Monoid hiding (Product(..))

import qualified Data.Foldable as F
import qualified Data.Text.Lazy as T
import Data.ByteString.Lazy(toStrict)
import Data.Text.Lazy.Encoding
import Data.Text.Lazy (Text)
import qualified Data.Set as S


import Database.PostgreSQL.Simple
import qualified Data.Map as M
import Data.String


import Control.Arrow

data BrowserState
  = BrowserState
  {host :: String
  ,dbn :: String
  ,user :: String
  ,pass :: String
  ,schema :: Maybe String
  ,table :: Maybe String
  }


argsToState  [h,d,u,p,s,t] = BrowserState h d  u p (Just s) (Just t )
argsToState  [h,d,u,p,s] = BrowserState h d  u p  (Just s)  Nothing
argsToState  [h,d,u,p] = BrowserState h d  u p Nothing Nothing

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

  e <- poller (argsToState (tail args) )  [siapi2Plugin,siapi3Plugin ]

  startGUI (defaultConfig { tpStatic = Just "static", tpCustomHTML = Just "index.html" , tpPort = fmap read $ safeHead args })  (setup e $ tail args)
  print "Finish"

poller db plugs = do
  let poll (BoundedPlugin2 n a f elemp) =  do
        (e:: Event [TableModification (TBIdx Key Showable) ] ,handler) <- newEvent
        conn <- connectPostgreSQL (connRoot db)
        inf <- keyTables conn  conn (T.pack $ dbn db, T.pack $ user db)
        tp  <- query conn "SELECT start_time from metadata.polling where poll_name = ? and table_name = ? and schema_name = ?" (n,a,"incendio" :: String)
        let t = case  tp of
              [Only i] -> Just i :: Maybe UTCTime
              [] -> Nothing
        forkIO $ (maybe (do
          print $ "Closing conn plugin [" <> T.unpack n <> "] not registered"
          close conn ) (\_ -> void $ forever $ do
          [t :: Only UTCTime]  <- query conn "SELECT start_time from metadata.polling where poll_name = ? and table_name = ? and schema_name = ?" (n,a,"incendio" :: String)
          startTime <- getCurrentTime
          let intervalsec = fromIntegral $ 60*d
              d = 60
          if  diffUTCTime startTime  (unOnly t) >  intervalsec
          then do
              execute conn "UPDATE metadata.polling SET start_time = ? where poll_name = ? and table_name = ? and schema_name = ?" (startTime,n,a,"incendio" :: String)
              print ("START " <>T.unpack n <> " - " <> show startTime  ::String)
              let rpt = tableView (tableMap inf) (fromJust  $ M.lookup  a  $ tableMap inf )
                  rpd = accessTB ( fst f <> snd f) rpt
                  rp = selectQuery rpd
              listRes <- queryWith_ (fromAttr (unTlabel rpd )) conn  (fromString $ T.unpack $ rp)
              let evb = filter (\i -> tdInput i  && tdOutput1 i ) listRes
                  tdInput i =  isJust  $ testTable i (fst f)
                  tdOutput1 i =   not $ isJust  $ testTable i (snd f)
              let elem inf  = fmap catMaybes .  mapM (\inp -> do
                          o  <- catchPluginException inf a n (getPK inp)    (elemp inf (Just inp))
                          let diff =   join $ (\i j -> diffUpdateAttr   (unTB1 i ) (unTB1 j)) <$>  o <*> Just inp
                          maybe (return Nothing )  (\i -> updateModAttr inf (unTB1 $ fromJust o) (unTB1 inp) (lookTable inf a )) diff )

              i <- elem inf evb
              handler i
              end <- getCurrentTime
              print ("END " <>T.unpack n <> " - " <> show end ::String)
              execute conn "UPDATE metadata.polling SET end_time = ? where poll_name = ? and table_name = ? and schema_name = ?" (end ,n,a,"incendio" :: String)
              threadDelay (d*1000*1000*60)
          else do
              threadDelay (round $ (*1000000) $  diffUTCTime startTime (unOnly t)) ) t )
            `catch` (\(e :: SomeException )->  do
                print ("Closing conn [" <> T.unpack n <> "] on exception " <> show e)
                (close conn))
        return (a,e)
  mapM poll  plugs



setup
     :: [(Text,Event [TableModification (TBIdx Key Showable)])] -> [String] -> Window -> UI ()
setup e args w = void $ do
  let bstate = argsToState args
  (evDB,chooserItens) <- databaseChooser bstate
  body <- UI.div
  be <- stepper [] (unions $ fmap snd e)
  return w # set title (host bstate <> " - " <>  dbn bstate)
  nav  <- buttonDivSet  ["Nav","Change","Exception"] (pure $ Just "Nav" )(\i -> UI.button # set UI.text i # set UI.class_ "buttonSet btn-xs btn-default pull-right")
  element nav # set UI.class_ "col-xs-5"
  chooserDiv <- UI.div # set children  (chooserItens <> [ getElement nav ] ) # set UI.class_ "row" # set UI.style [("display","flex"),("align-items","flex-end")]
  container <- UI.div # set children [chooserDiv , body] # set UI.class_ "container-fluid"
  getBody w #+ [element container]
  mapEvent (traverse (\inf -> liftIO$ swapMVar  (mvarMap inf) M.empty)) (rumors evDB)
  mapUITEvent body (traverse (\(nav,inf)->
      case nav of
        "Change" -> do
            dash <- dashBoardAll inf
            element body # set UI.children [dash] # set UI.class_ "row"
        "Exception" -> do
            dash <- exceptionAll inf
            element body # set UI.children [dash] # set UI.class_ "row"
        "Nav" -> do
            let k = M.keys $  M.filter (not. null. rawAuthorization) $   (pkMap inf )
            span <- chooserTable  inf e k (table bstate)
            element body # set UI.children [span]# set UI.class_ "row"  )) $ liftA2 (\i -> fmap (i,)) (triding nav) evDB


connRoot dname = (fromString $ "host=" <> host dname <> " user=" <> user dname <> " dbname=" <> dbn  dname <> " password=" <> pass dname <> " sslmode= require" )
listDBS ::  BrowserState -> IO (Text,(Connection,[Text]))
listDBS dname = do
  connMeta <- connectPostgreSQL (connRoot dname)
  dbs :: [Only Text]<- query_  connMeta "SELECT datname FROM pg_database  WHERE datistemplate = false"
  map <- (\db -> do
        connDb <- connectPostgreSQL ((fromString $ "host=" <> host dname <>" user=" <> user dname <> " dbname=" ) <> toStrict (encodeUtf8 db) <> (fromString $ " password=" <> pass dname <> " sslmode= require") )
        schemas :: [Only Text] <- query_  connDb "SELECT schema_name from information_schema.schemata"
        return (db,(connDb,filter (not . (`elem` ["information_schema","pg_catalog","pg_temp_1","pg_toast_temp_1","pg_toast","public"])) $ fmap unOnly schemas))) (T.pack $ dbn dname)
  return map

loginWidget userI passI =  do
  usernamel <- flabel # set UI.text "Usuário"
  username <- UI.input # set UI.name "username" # set UI.style [("width","142px")] # set UI.value (maybe "" id userI)
  passwordl <- flabel # set UI.text "Senha"
  password <- UI.input # set UI.name "password" # set UI.style [("width","142px")] # set UI.type_ "password" # set UI.value (maybe "" id passI)
  let usernameE = (\i -> if L.null i then Nothing else Just i) <$> UI.valueChange username
      passwordE = (\i -> if L.null i then Nothing else Just i) <$> UI.valueChange password

  userDiv <- UI.div # set children [usernamel,username] # set UI.class_  "col-xs-2"
  passDiv <- UI.div # set children [passwordl,password] # set UI.class_  "col-xs-2"
  usernameB <- stepper userI usernameE
  passwordB <- stepper passI passwordE
  let usernameT = tidings usernameB usernameE
      passwordT = tidings passwordB passwordE
  return $ ((liftA2 (liftA2 (,)) usernameT passwordT) ,[userDiv,passDiv])

instance Ord Connection where
  i < j = 1 < 2
  i <= j = 1 < 2
instance Eq Connection where
  i == j = True


form td ev =  tidings (facts td ) (facts td <@ ev )

databaseChooser sargs = do
  dbs <- liftIO $ listDBS  sargs
  let dbsInit = fmap (\s -> (T.pack $ dbn sargs ,) . (,T.pack s) . fst $ snd $ dbs ) $ ( schema sargs)
  (widT,widE) <- loginWidget (Just $ user sargs  ) (Just $ pass sargs )
  dbsW <- listBox (pure $ (\(i,(c,j)) -> (i,) . (c,) <$> j) $ dbs ) (pure dbsInit  ) (pure id) (pure (line . show . snd . fmap snd ))
  schema <- flabel # set UI.text "schema"
  cc <- currentValue (facts $ userSelection dbsW)
  let dbsWE = rumors $ userSelection dbsW
  dbsWB <- stepper cc dbsWE
  let dbsWT  = tidings dbsWB dbsWE
  load <- UI.button # set UI.text "Connect" # set UI.class_ "col-xs-1" # sink UI.enabled (facts (isJust <$> dbsWT) )
  let login = liftA2 (liftA2 (,)) (widT) ( dbsWT )
      formLogin = form login (UI.click load)
  let genSchema ((user,pass),(dbN,(dbConn,schemaN))) = do
        conn <- connectPostgreSQL ("host=" <> (BS.pack $ host sargs) <>" user=" <> BS.pack user <> " password=" <> BS.pack pass <> " dbname=" <> toStrict ( encodeUtf8 dbN )<> " sslmode= require")
        execute_ conn "set bytea_output='hex'"
        keyTables dbConn conn (schemaN,T.pack user)
  element dbsW # set UI.style [("height" ,"26px"),("width","140px")]
  chooserT <-  mapTEvent (traverse genSchema) formLogin
  schemaSel <- UI.div # set UI.class_ "col-xs-2" # set children [ schema , getElement dbsW]
  return $ (chooserT,(widE <> [schemaSel ,load]))




applyUI el f = (\a-> getWindow el >>= \w -> runUI w (f a))

tableNonRec k  =  F.toList $  tableNonRef  k


operator op = UI.div # set text op  # set UI.style [("margin-left","3px"),("margin-right","3px")]

attrLine i e   = do
  let nonRec = tableNonrec i
      attr i (k,v) = set  (strAttr (T.unpack $ keyValue k)) (renderShowable v) i
      attrs   l i  = foldl attr i l
  attrs (F.toList (tableAttrs i) ) $ line ( L.intercalate "," (fmap renderShowable .  allKVRec  $ i) <> "  -  " <>  (L.intercalate "," $ fmap (renderPrim ) nonRec)) e

chooserTable inf e kitems i = do
  let initKey = pure . join $ fmap rawPK . flip M.lookup (tableMap inf) . T.pack <$> i
  filterInp <- UI.input # set UI.style [("width","100%")]
  filterInpBh <- stepper "" (UI.valueChange filterInp)

  i :: [(Text,Int)] <- liftIO $ query (rootconn inf) (fromString "SELECT table_name,usage from metadata.ordering where schema_name = ?") (Only (schemaName inf))
  let orderMap = Just $ M.fromList  i
  let renderLabel = (\i -> case M.lookup i (pkMap inf) of
                                       Just t -> T.unpack (translatedName t)
                                       Nothing -> show i )
      filterLabel = ((\j -> (\i -> L.isInfixOf (toLower <$> j) (toLower <$> renderLabel i) ))<$> filterInpBh)
  bset <- buttonDivSet (L.sortBy (flip $  comparing (\ pkset -> liftA2 M.lookup  (fmap rawName . flip M.lookup (pkMap inf) $ pkset ) orderMap)) kitems)  initKey  (\k -> UI.button # set UI.text (renderLabel k) # set UI.style [("width","100%")] # set UI.class_ "btn-xs btn-default buttonSet" # sink UI.style (noneShow  . ($k) <$> filterLabel ))
  let bBset = triding bset
  onEvent (rumors bBset) (\ i ->
      liftIO $ execute (rootconn inf) (fromString $ "UPDATE  metadata.ordering SET usage = usage + 1 where table_name = ? AND schema_name = ? ") (( fmap rawName $ M.lookup i (pkMap inf)) ,  schemaName inf )
        )
  tbChooserI <- UI.div # set children [filterInp,getElement bset]  # set UI.style [("height","600px"),("overflow","auto"),("height","99%")]
  tbChooser <- UI.div # set UI.class_ "col-xs-2"# set UI.style [("height","600px"),("overflow","hidden")] # set children [tbChooserI]
  nav  <- buttonDivSet ["Viewer","Nav","Exception","Change"] (pure $ Just "Nav")(\i -> UI.button # set UI.text i # set UI.style [("font-size","smaller")]. set UI.class_ "buttonSet btn-xs btn-default pull-right")
  element nav # set UI.class_ "col-xs-5"
  header <- UI.h1 # sink text (T.unpack . translatedName .  justError "no table " . flip M.lookup (pkMap inf) <$> facts bBset ) # set UI.class_ "col-xs-7"
  chooserDiv <- UI.div # set children  [header ,getElement nav] # set UI.class_ "row" # set UI.style [("display","flex"),("align-items","flex-end")]
  body <- UI.div # set UI.class_ "row"

  mapM (\(t,ediff) -> traverse (\ table -> do
      (tmvar,vpt)  <- liftIO $ eventTable inf table
      onEvent ( ((\i j -> foldl applyTable i (fmap (PAtom .tableDiff) j) ) <$> facts vpt <@> ediff)) (liftIO .  putMVar tmvar . fmap unTB1 )) (M.lookup t (tableMap inf))  ) e

  mapUITEvent body (\(nav,table)->
      case nav of
        "Change" -> do
            dash <- dashBoardAllTable inf (justError "no table " $ M.lookup table (pkMap inf))
            element body # set UI.children [dash]
        "Exception" -> do
            dash <- exceptionAllTable inf (justError "no table " $ M.lookup table (pkMap inf))
            element body # set UI.children [dash]
        "Nav" -> do
            span <- viewerKey inf table
            element body # set UI.children [span]
        "Viewer" -> do
            span <- viewer inf (justError "no table with pk" $ M.lookup table (pkMap inf)) Nothing
            element body # set UI.children [span]
        ) $ liftA2 (,) (triding nav) bBset
  subnet <- UI.div # set children [chooserDiv,body] # set UI.class_ "row col-xs-10" # set UI.style [("height","600px"),("overflow","auto")]
  UI.div # set children [tbChooser, subnet ]  # set UI.class_ "row"

viewerKey
  ::
      InformationSchema -> S.Set Key -> UI Element
viewerKey inf key = mdo
  let
      table = fromJust  $ M.lookup key $ pkMap inf

  (tmvar,vpt)  <- liftIO $ eventTable inf table
  vp <- currentValue (facts vpt)

  let
      tdi = pure Nothing
  cv <- currentValue (facts tdi)
  -- Final Query ListBox
  filterInp <- UI.input
  filterInpBh <- stepper "" (UI.valueChange filterInp)
  el <- filterUI  inf (allRec' (tableMap inf)  table)
  let filterInpT = tidings filterInpBh (UI.valueChange filterInp)
      sortSet =  F.toList . tableKeys . tableNonRef . allRec' (tableMap inf ) $ table
  sortList <- selectUI sortSet ((,True) <$> F.toList key) UI.div UI.div conv
  element sortList # set UI.style [("overflow-y","scroll"),("height","200px")]
  asc <- checkedWidget (pure True)
  let
     filteringPred i = (T.isInfixOf (T.pack $ toLower <$> i) . T.toLower . T.intercalate "," . fmap (T.pack . renderPrim ) . F.toList  . _unTB1 )
     tsort = sorting . filterOrd <$> triding sortList
     res3 = flip (maybe id (\(_,constr) ->  L.filter (\e@(TB1 (_, kv) ) -> intersectPredTuple (fst constr) (snd constr)  .  unTB . justError "cant find attr" . M.lookup (S.fromList $  keyattr  (Compose $ Identity $ snd constr) ) $ _kvvalues  $ unTB$ kv ))) <$> res2 <#> triding el
  let pageSize = 20
  itemList <- listBox ((\o -> L.take pageSize . L.drop (o*pageSize))<$> triding offset <*>res3) (tidings st never) (pure id) ((\l -> (\i -> (set UI.style (noneShow $ filteringPred l i)) . attrLine i)) <$> filterInpT)
  offset <- offsetField 0 (negate <$> mousewheel (getElement itemList)) ((\i -> (L.length i `div` pageSize) ) <$> facts res3)
  let evsel =  unionWith const (rumors (userSelection itemList)) (rumors tdi)
  prop <- stepper cv evsel
  let tds = tidings prop evsel

  (cru,ediff,pretdi) <- crudUITable inf plugList  (pure "Editor")  res3 [] [] (allRec' (tableMap inf) table) tds
  diffUp <-  mapEvent (fmap pure)  $ (\i j -> traverse (runDBM inf . flip applyTB1' j ) i) <$> facts pretdi <@> ediff
  let
     sel = filterJust $ fmap (safeHead . concat) $ unions $ [(unions  [rumors  $userSelection itemList  ,rumors tdi]),diffUp]
  st <- stepper cv sel
  inisort <- currentValue (facts tsort)
  res2 <- accumB (inisort vp) (fmap concatenate $ unions [fmap const (($) <$> facts tsort <@> rumors vpt) ,rumors tsort ])
  onEvent ( ((\i j -> foldl applyTable i (expandPSet j)) <$> res2 <@> ediff)) (liftIO .  putMVar tmvar. fmap unTB1)

  element itemList # set UI.multiple True # set UI.style [("width","70%"),("height","350px")] # set UI.class_ "col-xs-9"
  title <- UI.h4  #  sink text ( maybe "" (L.intercalate "," . fmap (renderShowable .snd) . F.toList . getPK)  <$> facts tds) # set UI.class_ "col-xs-8"
  insertDiv <- UI.div # set children [title,head cru] # set UI.class_ "row"
  insertDivBody <- UI.div # set children [insertDiv,last cru]# set UI.class_ "row"
  itemSel <- UI.ul # set items ((\i -> UI.li # set children [ i]) <$> [getElement offset ,filterInp ,getElement sortList,getElement asc, getElement el] ) # set UI.class_ "col-xs-3"
  itemSelec <- UI.div # set children [getElement itemList, itemSel] # set UI.class_ "row"
  UI.div # set children ([itemSelec,insertDivBody ] )


tableNonrec k  = F.toList .  runIdentity . getCompose  . tbAttr  $ tableNonRef k


tableAttrs (TB1  (_,k)) = concat $ fmap aattr (F.toList $ _kvvalues $  runIdentity $ getCompose $ k)
tableAttrs (LeftTB1 (Just i)) = tableAttrs i
tableAttrs (ArrayTB1 [i]) = tableAttrs i


filterCase inf t@(Attr k _ ) = do
  opInp <- UI.input # set UI.text "="
  opBh <- stepper "=" (UI.valueChange opInp)
  let opT = (\v -> if elem v validOp then Just v else Nothing) <$> tidings opBh (UI.valueChange opInp)
  elv <- attrUITable (pure Nothing) [] t
  TrivialWidget (fmap (fmap (t,)) $ liftA2 (liftA2 (,)) opT (triding elv)) <$> UI.div # set children [opInp,getElement elv ]
filterCase inf (FKT l  _ tb1) =  filterUI inf tb1
filterCase inf (IT _ tb1) = filterUI inf tb1

filterUI inf (LeftTB1 (Just i))  =  filterUI inf i
filterUI inf (ArrayTB1 [i])  = filterUI inf i
filterUI inf t@(TB1 (k,v)) = do
  el <- listBox (pure (fmap (first (S.map _relOrigin)) $  M.toList (_kvvalues $ runIdentity $ getCompose v) )) (pure Nothing) (pure id) (pure (\i j -> j # set text (show (T.intercalate "," $ keyValue <$> S.toList (fst i)) )))
  elv <- mapDynEvent (maybe emptyUI  (filterCase inf . unTB . fmap (const ()) . snd )) (TrivialWidget (userSelection el) (getElement el))
  out <- UI.div # sink UI.text (show <$> facts (triding elv))
  TrivialWidget (triding elv) <$> UI.div # set children [getElement el , getElement elv,out]


