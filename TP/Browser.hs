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
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts,OverloadedStrings ,TupleSections, ExistentialQuantification #-}

module Main (main) where

import Query
import Control.Concurrent.Async
import Data.List (foldl')
import Debug.Trace
import Types
import Data.Either
import Step
import Control.Lens (traverseOf,_3)
import Plugins
import TP.Widgets
import SchemaQuery
import PostgresQuery (postgresOps)
import SortList
import Prelude hiding (head)
import TP.QueryWidgets
import Control.Monad.Reader
import Control.Concurrent
import Data.Functor.Apply
import System.Environment
import Network.Google.OAuth2 (OAuth2Tokens(..))
import Data.Ord
import Utils
import Schema
import Patch
import Data.Char (toLower)
import Postgresql
import Data.Maybe
import Data.Functor.Identity
import Reactive.Threepenny
import Data.Traversable (traverse)
import qualified Data.List as L
import qualified Data.ByteString.Char8 as BS
import Data.Time

import RuntimeTypes
import qualified Graphics.UI.Threepenny as UI
import Graphics.UI.Threepenny.Core hiding (get,delete)
import Data.Monoid hiding (Product(..))

import qualified Data.Foldable as F
import qualified Data.Text as T
import Data.Text.Encoding (encodeUtf8)
import Data.Text (Text)
import qualified Data.Set as S


import Database.PostgreSQL.Simple
import qualified Data.Map as M
import Data.String

import OAuth
import GHC.Stack


data BrowserState
  = BrowserState
  {host :: String
  ,port :: String
  ,dbn :: String
  ,user :: String
  ,pass :: String
  ,schema :: Maybe String
  ,tablename :: Maybe String
  }


argsToState  [h,ph,d,u,p,s,t] = BrowserState h ph d  u p (Just s) (Just t )
argsToState  [h,ph,d,u,p,s] = BrowserState h ph d  u p  (Just s)  Nothing
argsToState  [h,ph,d,u,p] = BrowserState h ph d  u p Nothing Nothing
argsToState i = errorWithStackTrace (show i)


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

  smvar <- newMVar M.empty
  plugs smvar (argsToState $ tail args)  plugList
  poller smvar (argsToState $ tail args)  plugList
  startGUI (defaultConfig { tpStatic = Just "static", tpCustomHTML = Just "index.html" , tpPort = fmap read $ safeHead args })  (setup smvar  (tail args))
  print "Finish"


plugs schm db plugs = do
  conn <- connectPostgreSQL (connRoot db)
  inf <- keyTables schm conn conn ("metadata",T.pack $ user db ) Nothing postgresOps plugList
  ((m,td),(s,t)) <- transaction inf $ eventTable  inf (lookTable inf "plugins") Nothing Nothing [] []
  let els = L.filter (not . (`L.elem` F.toList t)) $ (\o->  liftTable' inf "plugins" $ tblist (_tb  <$> [Attr "name" (TB1 $ SText $ _name o) ])) <$> plugs
  p <- transaction inf $ mapM (\table -> fullDiffInsert  (meta inf)  table) els
  putMVar m (s,foldl' applyTable'  t (tableDiff <$> catMaybes p))

poller schm db plugs = do
  conn <- connectPostgreSQL (connRoot db)
  enabled :: [(Text,Int,Text)] <- query_ conn "SELECT schema_name, poll_period_ms,poll_name from metadata.polling"
  let poll (schema,intervalms ,p) =  do
        let f = pluginStatic p
            elemp = pluginAction p
            pname = _name p
            a = _bounds p
        pid <- forkIO $ (void $ forever $ do
          inf <- keyTables  schm conn  conn (schema, T.pack $ user db) Nothing postgresOps plugList
          [[start,endt]] :: [[UTCTime]]<- query conn "SELECT start_time,end_time from metadata.polling where poll_name = ? and schema_name = ?" (pname,schema)
          current <- getCurrentTime
          let intervalsec = intervalms `div` 10^3
          if  diffUTCTime current start  >  fromIntegral intervalsec
          then do
              print ("START " <>T.unpack pname  <> " - " <> show current ::String)
              let fetchSize = 1000
              ((m,listResT),(l,listRes)) <- transaction inf $ eventTable inf (lookTable inf a) Nothing (Just fetchSize) [][]
              let sizeL = justError "no coll" $ M.lookup [] l
                  lengthPage s pageSize  = (s  `div` pageSize) +  if s `mod` pageSize /= 0 then 1 else 0
              i <- concat <$> mapM (\ix -> do
                  print "pre list"
                  ((m,listResT),(l,listResAll)) <- transaction inf $ eventTable inf (lookTable inf a) (Just ix) (Just fetchSize) [][]
                  print "pos list"
                  let listRes = L.take fetchSize . F.toList $ listResAll

                  let evb = filter (\i -> tdInput i  && tdOutput1 i ) listRes
                      tdInput i =  isJust  $ checkTable  (fst f) i
                      tdOutput1 i =   not $ isJust  $ checkTable  (snd f) i

                  i <-  mapConcurrently (mapM (\inp -> do
                      o  <- fmap (fmap (liftTable' inf a)) <$> catchPluginException inf a pname (getPK $ TB1 inp)   (elemp (Just $ mapKey' keyValue inp))
                      v <- traverse (\o -> do
                        let diff =   join $ (\i j -> difftable (j ) (i)) <$>  o <*> Just inp
                        maybe (return Nothing )  (\i -> transaction inf $ (editEd $ schemaOps inf) inf (justError "no test" o) inp ) diff ) o
                      traverse (traverse (\p -> putMVar m  .  (\(l,listRes) -> (l,applyTable' listRes (tableDiff p))) =<< currentValue (facts listResT))) v
                      return v
                        )
                    ) . L.transpose . chuncksOf 20 $ evb

                  (putMVar m ) .  (\(l,listRes) -> (l,foldl' applyTable' listRes (fmap tableDiff (catMaybes $ rights $ concat i)))) =<< currentValue (facts listResT)
                  return $ concat i
                  ) [0..(lengthPage (fst sizeL) fetchSize -1)]
              end <- getCurrentTime
              print ("END " <>T.unpack pname <> " - " <> show end ::String)
              let polling_log = lookTable (meta inf) "polling_log"
              ((plm,plt),_) <- transaction (meta inf) $ eventTable (meta inf) polling_log Nothing Nothing [] []
              let table = tblist
                      [ attrT ("poll_name",TB1 (SText pname))
                      , attrT ("schema_name",TB1 (SText schema))
                      , _tb $ IT (attrT ("diffs",LeftTB1 $ Just$ ArrayTB1 $ [TB1 ()])) (LeftTB1 $ ArrayTB1  <$> (
                                nonEmpty  . catMaybes $
                                    fmap (TB1 . tblist . pure ) .  either (\r ->Just $   attrT ("except", LeftTB1 $ Just $ TB1 (SNumeric r) )) (fmap (\r -> attrT ("modify", LeftTB1 $ Just $ TB1 (SNumeric (justError "no id" $ tableId $  r))   ))) <$> i))
                      , attrT ("duration",srange (time current) (time end))]
                  time  = TB1 . STimestamp . utcToLocalTime utc
              p <- transaction inf $ fullDiffInsert  (meta inf) (liftTable' (meta inf) "polling_log" table)
              traverse (putMVar plm ). traverse (\l -> applyTable' l <$> (fmap tableDiff  p)) =<< currentValue (facts plt)
              execute conn "UPDATE metadata.polling SET start_time = ? where poll_name = ? and schema_name = ?" (current,pname,schema )
              execute conn "UPDATE metadata.polling SET end_time = ? where poll_name = ? and schema_name = ?" (end ,pname,schema)
              threadDelay (intervalms*10^3)
          else do
              threadDelay (round $ (*10^6) $  diffUTCTime current start ) )

        return ()
  mapM poll  $ (catMaybes $ fmap (traverseOf _3  (\n -> L.find ((==n ). _name ) plugList)) enabled )

setup
     ::  MVar (M.Map Text  InformationSchema) ->  [String] -> Window -> UI ()
setup smvar args w = void $ do
  let bstate = argsToState args
  (evDB,chooserItens) <- databaseChooser smvar bstate
  body <- UI.div
  return w # set title (host bstate <> " - " <>  dbn bstate)
  nav  <- buttonDivSet  ["Nav","Poll","Change","Exception"] (pure $ Just "Nav" )(\i -> UI.button # set UI.text i # set UI.class_ "buttonSet btn-xs btn-default pull-right")
  element nav # set UI.class_ "col-xs-5"
  chooserDiv <- UI.div # set children  (chooserItens <> [ getElement nav ] ) # set UI.class_ "row" # set UI.style [("display","flex"),("align-items","flex-end")]
  container <- UI.div # set children [chooserDiv , body] # set UI.class_ "container-fluid"
  getBody w #+ [element container]
  mapUITEvent body (traverse (\(nav,inf)->
      case nav of
        "Poll" -> do
            element body #
              set items
                  [ metaAllTableIndexV inf "polling" [("schema_name",TB1 $ SText (schemaName inf) ) ]
                  , metaAllTableIndexV inf "polling_log" [("schema_name",TB1 $ SText (schemaName inf) ) ]] #
              set UI.class_ "row"
        "Change" -> do
            dash <- metaAllTableIndexV inf "modification_table" [("schema_name",TB1 $ SText (schemaName inf) ) ]
            element body # set UI.children [dash] # set UI.class_ "row"
        "Exception" -> do
            dash <- metaAllTableIndexV inf "plugin_exception" [("schema_name",TB1 $ SText (schemaName inf) ) ]
            element body # set UI.children [dash] # set UI.class_ "row"
        "Nav" -> do
            let k = M.keys $  M.filter (not. null. rawAuthorization) $   (pkMap inf )
            span <- chooserTable  inf  k (tablename bstate)
            element body # set UI.children [span]# set UI.class_ "row"  )) $ liftA2 (\i -> fmap (i,)) (triding nav) evDB


connRoot dname = (fromString $ "host=" <> host dname <> " port=" <> port dname  <> " user=" <> user dname <> " dbname=" <> dbn  dname <> " password=" <> pass dname ) -- <> " sslmode= require" )
listDBS ::  BrowserState -> IO (Text,(Connection,[Text]))
listDBS dname = do
  connMeta <- connectPostgreSQL (connRoot dname)
  dbs :: [Only Text]<- query_  connMeta "SELECT datname FROM pg_database  WHERE datistemplate = false"
  map <- (\db -> do
        connDb <- connectPostgreSQL ((fromString $ "host=" <> host dname <> " port=" <> port dname <>" user=" <> user dname <> " dbname=" ) <> (encodeUtf8 db) <> (fromString $ " password=" <> pass dname )) --  <> " sslmode= require") )
        schemas :: [Only Text] <- query_  connDb "SELECT name from metadata.schema "
        return (db,(connDb,filter (not . (`elem` ["information_schema","pg_temp_1","pg_toast_temp_1","pg_toast","public"])) $ fmap unOnly schemas))) (T.pack $ dbn dname)
  return map

loginWidget userI passI =  do
  usernamel <- flabel # set UI.text "Usuário"
  username <- UI.input # set UI.name "username" # set UI.style [("width","142px")] # set UI.value (maybe "" id userI)
  passwordl <- flabel # set UI.text "Senha"
  password <- UI.input # set UI.name "password" # set UI.style [("width","142px")] # set UI.type_ "password" # set UI.value (maybe "" id passI)
  let usernameE = nonEmpty  <$> UI.valueChange username
      passwordE = nonEmpty <$> UI.valueChange password

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


form :: Tidings a -> Event b -> Tidings a
form td ev =  tidings (facts td ) (facts td <@ ev )

databaseChooser smvar sargs = do
  dbs <- liftIO $ listDBS  sargs
  let dbsInit = fmap (\s -> (T.pack $ dbn sargs ,) . (,T.pack s) . fst $ snd $ dbs ) $ ( schema sargs)
  (widT,widE) <- loginWidget (Just $ user sargs  ) (Just $ pass sargs )
  dbsW <- listBox (pure $ (\(i,(c,j)) -> (i,) . (c,) <$> j) $ dbs ) (pure dbsInit  ) (pure id) (pure (line . show . snd . fmap snd ))
  schema <- flabel # set UI.text "schema"
  cc <- currentValue (facts $ triding dbsW)
  let dbsWE = rumors $ triding dbsW
  reset <- checkedWidget (pure False)
  dbsWB <- stepper cc dbsWE
  let dbsWT  = tidings dbsWB dbsWE
  load <- UI.button # set UI.text "Connect" # set UI.class_ "col-xs-1" # sink UI.enabled (facts (isJust <$> dbsWT) )
  let login = liftA3 (\v a b-> fmap (v,) $ liftA2 (,) a b) (triding reset) widT dbsWT
      formLogin = form login (UI.click load)
  let genSchema (reset,((user,pass),(dbN,(dbConn,schemaN)))) = do
        conn <- connectPostgreSQL ("host=" <> (BS.pack $ host sargs) <> " port=" <> BS.pack (port sargs ) <>" user=" <> BS.pack user <> " password=" <> BS.pack pass <> " dbname=" <> (BS.pack $  dbn sargs) ) -- <> " sslmode= require")
        execute_ conn "set bytea_output='hex'"
        let call = if  reset then keyTablesInit else keyTables
        case schemaN of
          "gmail" ->  do
              metainf <- keyTables smvar dbConn conn ("metadata",T.pack $ user ) Nothing postgresOps plugList
              ((_,tb),_) <- transaction metainf $ eventTable metainf (lookTable metainf "google_auth") Nothing Nothing []  [("=",liftField metainf "google_auth" $ Attr "username" (TB1 $ SText  "wesley.massuda@gmail.com"))]
              let
                  td :: Tidings OAuth2Tokens
                  td = fmap (\o -> justError "" . fmap (toOAuth . _fkttable . unTB) $ L.find ((==["token"]). fmap (keyValue._relOrigin) . keyattr )  $ F.toList (unKV $ snd $   head $ snd $ o )) (fmap F.toList <$> tb)
                  toOAuth v = tokenToOAuth (b,d,a,c)
                    where [a,b,c,d] = fmap TB1 $ F.toList $ snd $ unTB1 v :: [FTB Showable]
              call smvar dbConn conn (schemaN,T.pack $ user ) (Just ("me",td )) gmailOps plugList
          i -> call smvar dbConn conn (schemaN,T.pack user) Nothing postgresOps plugList
  element dbsW # set UI.style [("height" ,"26px"),("width","140px")]
  chooserT <-  mapTEvent (traverse genSchema) formLogin
  schemaSel <- UI.div # set UI.class_ "col-xs-2" # set children [ schema , getElement dbsW]
  return $ (chooserT,( widE <> (getElement reset : [schemaSel ,load])))


attrLine i e   = do
  let nonRec = tableNonrec $ TB1  i
      attr i (k,v) = set  (strAttr (T.unpack $ keyValue k)) (renderShowable v) i
      attrs   l i  = foldl' attr i l
  attrs (F.toList (tableAttrs$ TB1  i) ) $ line ( L.intercalate "," (fmap renderShowable .  allKVRec  $ TB1 i) <> "  -  " <>  (L.intercalate "," $ fmap (renderPrim ) nonRec)) e


chooserTable inf kitems i = do
  let initKey = pure . join $ fmap (S.fromList .rawPK) . flip M.lookup (tableMap inf) . T.pack <$> i
  filterInp <- UI.input # set UI.style [("width","100%")]
  filterInpBh <- stepper "" (UI.valueChange filterInp)

  i <- maybe (return ([] :: [(Text,Int)] ))  (\i -> liftIO $ query (rootconn i) (fromString "SELECT table_name,usage from metadata.ordering where schema_name = ?") (Only (schemaName inf))) (metaschema inf)
  let orderMap = Just $ M.fromList  i
  let renderLabel = (\i -> case M.lookup i (pkMap inf) of
                                       Just t -> T.unpack (translatedName t)
                                       Nothing -> show i )
      filterLabel = ((\j -> (\i -> L.isInfixOf (toLower <$> j) (toLower <$> renderLabel i) ))<$> filterInpBh)
  bset <- buttonDivSet (L.sortBy (flip $  comparing (\ pkset -> liftA2 M.lookup  (fmap rawName . flip M.lookup (pkMap inf) $ pkset ) orderMap)) kitems)  initKey  (\k -> UI.button # set UI.text (renderLabel k) # set UI.style [("width","100%")] # set UI.class_ "btn-xs btn-default buttonSet" # sink UI.style (noneShow . ($k) <$> filterLabel ))
  let bBset = triding bset
  onEvent (rumors bBset) (\ i ->
      when (isJust (metaschema inf)) $  void (liftIO $ execute (rootconn inf) (fromString $ "UPDATE  metadata.ordering SET usage = usage + 1 where table_name = ? AND schema_name = ? ") (( fmap rawName $ M.lookup i (pkMap inf)) ,  schemaName inf )))
  tbChooserI <- UI.div # set children [filterInp,getElement bset]  # set UI.style [("height","600px"),("overflow","auto"),("height","99%")]
  tbChooser <- UI.div # set UI.class_ "col-xs-2"# set UI.style [("height","600px"),("overflow","hidden")] # set children [tbChooserI]
  nav  <- buttonDivSet ["Viewer","Nav","Exception","Change"] (pure $ Just "Nav")(\i -> UI.button # set UI.text i # set UI.style [("font-size","smaller")]. set UI.class_ "buttonSet btn-xs btn-default pull-right")
  element nav # set UI.class_ "col-xs-5"
  header <- UI.h1 # sink text (T.unpack . translatedName .  justError "no table " . flip M.lookup (pkMap inf) <$> facts bBset ) # set UI.class_ "col-xs-7"
  chooserDiv <- UI.div # set children  [header ,getElement nav] # set UI.class_ "row" # set UI.style [("display","flex"),("align-items","flex-end")]
  body <- UI.div # set UI.class_ "row"

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
      table = justError "no key" $ M.lookup key $ pkMap inf

  ((tmvar,vpt),vp)  <-  (liftIO $ transaction inf $ eventTable inf table (Just 0) Nothing  [] [])

  let
      tdi = pure Nothing
  cv <- currentValue (facts tdi)
  -- Final Query ListBox
  filterInp <- UI.input
  filterInpBh <- stepper "" (UI.valueChange filterInp)
  let filterInpT = tidings filterInpBh (diffEvent filterInpBh (UI.valueChange filterInp))
      sortSet = rawPK table <>  L.filter (not .(`L.elem` rawPK table)) (F.toList . tableKeys . TB1 . tableNonRef' . allRec' (tableMap inf ) $ table)
  sortList <- selectUI sortSet ((,True) <$> rawPK table ) UI.div UI.div conv
  element sortList # set UI.style [("overflow-y","scroll"),("height","200px")]
  asc <- checkedWidget (pure True)
  updateBtn <- UI.button # set text "Update"
  let
     filteringPred i = (T.isInfixOf (T.pack $ toLower <$> i) . T.toLower . T.intercalate "," . fmap (T.pack . renderPrim ) . F.toList  .snd )
     tsort = sorting' . filterOrd <$> triding sortList
     filtering res = (\t -> fmap (filter (filteringPred t )) )<$> filterInpT  <*> res
     pageSize = 20
     lengthPage (fixmap,i) = (s  `div` pageSize) +  if s `mod` pageSize /= 0 then 1 else 0
        where (s,_) =justError "no empty pages" $  M.lookup [] fixmap
  inisort <- currentValue (facts tsort)
  (offset,res3)<- mdo
    offset <- offsetField 0 (never ) (lengthPage <$> facts res3)
    res3 <- mapT0Event (fmap inisort (fmap F.toList vp)) return ( (\f i -> fmap f i)<$> tsort <*> (filtering $ fmap (fmap F.toList) $ tidings ( res2) ( rumors vpt) ) )
    return (offset, res3)
  onEvent (rumors $ triding offset) $ (\i -> liftIO $ transaction inf $ eventTable  inf table  (Just $ (i `div` 10)  + 1 ) Nothing  [] [])
  let
    paging  = (\o -> fmap (L.take pageSize . L.drop (o*pageSize)) )<$> triding offset
  page <- currentValue (facts paging)
  res4 <- mapT0Event (page $ fmap inisort (fmap F.toList vp)) return (paging <*> res3)
  itemList <- listBox (fmap snd res4) (tidings st sel ) (pure id) ( pure attrLine )

  let evsel =  unionWith const (rumors (triding itemList)) (rumors tdi)
  prop <- stepper cv evsel
  let tds = tidings prop (diffEvent  prop evsel)

  (cru,ediff,pretdi) <- crudUITable inf (pure "Editor")  (tidings (fmap (F.toList .snd) res2) never)[] [] (allRec' (tableMap inf) table) tds
  diffUp <-  mapEvent (fmap pure)  $ (\i j -> traverse (return . flip applyRecord j ) i) <$> facts pretdi <@> ediff
  let
     sel = filterJust $ fmap (safeHead . concat) $ unions $ [(unions  [rumors  $triding itemList  ,rumors tdi]),diffUp]
  st <- stepper cv sel
  res2 <- stepper (vp) (rumors vpt)
  onEvent (((\(m,i) j -> (m,foldl' applyTable' i [j])) <$> facts vpt <@> ediff)) (liftIO .  putMVar tmvar)
  onEvent (facts vpt <@ UI.click updateBtn ) (\(oi,oj) -> do
              let up =  (updateEd (schemaOps inf) ) inf table (L.maximumBy (comparing (getPK.TB1)) (F.toList oj) ) Nothing (Just 400)
              (l,i,j) <- liftIO $  transaction inf up
              liftIO .  putMVar tmvar  $ (oi , oj <> M.fromList ((\i -> (getPK i,unTB1 i) )<$>  l )) )

  element itemList # set UI.multiple True # set UI.style [("width","70%"),("height","350px")] # set UI.class_ "col-xs-9"
  title <- UI.h4  #  sink text ( maybe "" (L.intercalate "," . fmap (renderShowable .snd) . F.toList . getPK. TB1 )  <$> facts tds) # set UI.class_ "col-xs-8"
  insertDiv <- UI.div # set children [title,head cru] # set UI.class_ "row"
  insertDivBody <- UI.div # set children [insertDiv,last cru]# set UI.class_ "row"
  itemSel <- UI.ul # set items ((\i -> UI.li # set children [ i]) <$> [getElement offset ,filterInp ,getElement sortList,getElement asc] ) # set UI.class_ "col-xs-3"
  itemSelec <- UI.div # set children [getElement itemList, itemSel] # set UI.class_ "row"
  UI.div # set children ([updateBtn,itemSelec,insertDivBody ] )



tableNonrec k  = F.toList .  runIdentity . getCompose  . tbAttr  $ tableNonRef k


tableAttrs (TB1  (_,k)) = concat $ fmap aattr (F.toList $ _kvvalues $  runIdentity $ getCompose $ k)
tableAttrs (LeftTB1 (Just i)) = tableAttrs i
tableAttrs (ArrayTB1 [i]) = tableAttrs i


