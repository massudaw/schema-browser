{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE OverloadedStrings ,TupleSections #-}

module Main (main) where

import NonEmpty (NonEmpty(..))
import qualified NonEmpty as Non
import Data.Unique
import qualified Data.Binary as B
import Query
import Data.Time
import Text
import qualified Types.Index as G
import Poller
import Data.Bifunctor (first)
import Data.List (foldl')
import Debug.Trace
import Types
import SchemaQuery
import Plugins
import TP.Widgets
import SchemaQuery
import PostgresQuery (postgresOps,connRoot)
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
import Types.Patch
import Data.Char (toLower)
import Postgresql
import Data.Maybe
import Data.Functor.Identity
import Reactive.Threepenny hiding(apply)
import Data.Traversable (traverse)
import qualified Data.List as L
import qualified Data.ByteString.Char8 as BS
import qualified Data.ByteString.Lazy as BSL

import RuntimeTypes
import qualified Graphics.UI.Threepenny as UI
import Graphics.UI.Threepenny.Core hiding (get,delete,apply)
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


main :: IO ()
main = do
  args <- getArgs
  print "Start"
  smvar <- newMVar M.empty
  let db = argsToState (tail args)
  -- Load Metadata
  conn <- connectPostgreSQL (connRoot db)
  let amap = authMap smvar db (user db , pass db )
  metas <- keyTables  smvar conn  ("metadata", T.pack $ user db) amap plugList
  plugs smvar amap db plugList
  poller smvar amap db plugList False

  startGUI (defaultConfig { tpStatic = Just "static", tpCustomHTML = Just "index.html" , tpPort = fmap read $ safeHead args })  (setup smvar  (tail args)) (\w ->  liftIO $ do
          print ("delete client" <> show (sToken w))
          deleteClient metas (sToken w) )
  print "Finish"

updateClient metainf inf table tdi clientId now =
    let
      row = tblist . fmap _tb
            $ [ Attr "clientid" (TB1 (SNumeric (fromInteger clientId )))
              , Attr "creation_time" (TB1 (STimestamp (utcToLocalTime utc now)))
              , Attr "schema" (LeftTB1 $ TB1 . SText .  schemaName <$> inf )
              , Attr "table" (LeftTB1 $ TB1 . SText .  tableName <$>table)
              , IT (_tb (Attr "data_index"  (TB1 ()))) (LeftTB1 $ ArrayTB1 . Non.fromList .   fmap (\(i,j) -> TB1 $ tblist $ fmap _tb [Attr "key" (TB1 . SText  $ keyValue i) ,Attr "val" (TB1 . SDynamic $  j) ]) <$>tdi )
              ]
      lrow = liftTable' metainf "clients" row
    in lrow

getClient metainf clientId ccli = G.lookup (G.Idex [(lookKey metainf "clients" "clientid",TB1 (SNumeric (fromInteger clientId)))]) ccli :: Maybe (TBData Key Showable)

deleteClient metainf clientId = do
  (dbmeta ,(_,ccli)) <- transaction metainf $ eventTable metainf (lookTable metainf "clients" ) Nothing Nothing [] []
  putPatch (patchVar dbmeta) [(tableMeta (lookTable metainf "clients") , [(lookKey metainf "clients" "clientid",TB1 (SNumeric (fromInteger clientId)))],[])]


editClient metainf inf table tdi clientId now = do
  (dbmeta ,(_,ccli)) <- transaction metainf $ eventTable metainf (lookTable metainf "clients" ) Nothing Nothing [] []
  let cli :: Maybe (TBData Key Showable)
      cli = getClient metainf clientId ccli
      new :: TBData Key Showable
      new = updateClient metainf inf table tdi clientId now
      lrow :: Maybe (Index (TBData Key Showable))
      lrow = maybe (Just $ patch new ) (flip diff new )  cli
  traverse (putPatch (patchVar dbmeta ) . pure ) lrow
  return dbmeta

addClient clientId metainf inf table dbdata =  do
    now <- getCurrentTime
    let
      tdi = fmap getPKM $ join $ (\inf table -> fmap (tblist' table ) .  traverse (fmap _tb . (\(k,v) -> fmap (Attr k) . readType (keyType $ k) . T.unpack  $ v).  first (lookKey inf (tableName table))  ). F.toList) <$>  inf  <*> table <*> rowpk dbdata
    dbmeta <- editClient metainf inf table tdi clientId now
    return (clientId, getClient metainf clientId <$> collectionTid dbmeta)


setup
     ::  MVar (M.Map Text  InformationSchema) ->  [String] -> Window -> UI ()
setup smvar args w = void $ do
  metainf <- justError "no meta" . M.lookup "metadata" <$> liftIO ( readMVar smvar)
  let bstate = argsToState args
  let amap = authMap smvar bstate (user bstate , pass bstate)
  inf <- liftIO$ traverse (\i -> loadSchema smvar (T.pack i) (conn metainf) (user bstate)  amap ) $ schema  bstate
  (cli,cliTid) <- liftIO $ addClient (sToken w ) metainf inf ((\t inf -> lookTable inf . T.pack $ t) <$> tablename bstate  <*> inf  ) bstate
  (evDB,chooserItens) <- databaseChooser smvar bstate
  body <- UI.div
  return w # set title (host bstate <> " - " <>  dbn bstate)
  hoverBoard<-UI.div # set UI.style [("float","left"),("height","100vh"),("width","15px")]
  let he = const True <$> UI.hover hoverBoard
  bhe <-stepper True he
  menu <- checkedWidget (tidings bhe he)
  nav  <- buttonDivSet  ["Browser","Poll","Stats","Change","Exception"] (pure $ Just "Browser" )(\i -> UI.button # set UI.text i # set UI.class_ "buttonSet btn-xs btn-default pull-right")
  element nav # set UI.class_ "col-xs-5"
  chooserDiv <- UI.div # set children  ([getElement menu] <> chooserItens <> [getElement nav ] ) # set UI.class_ "row" # set UI.style [("display","flex"),("align-items","flex-end"),("height","7vh"),("width","100%")]
  container <- UI.div # set children [chooserDiv , body] # set UI.class_ "container-fluid"
  getBody w #+ [element hoverBoard,element container]
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
        "Stats" -> do
            stats <- metaAllTableIndexV inf "table_stats" [("schema_name",TB1 $ SText (schemaName inf) ) ]
            clients <- metaAllTableIndexV inf "clients" [("schema",LeftTB1 $ Just $ TB1 $ SText (schemaName inf) ) ]
            element body # set UI.children [stats,clients] # set UI.class_ "row"
        "Exception" -> do
            dash <- metaAllTableIndexV inf "plugin_exception" [("schema_name",TB1 $ SText (schemaName inf) ) ]
            element body # set UI.children [dash] # set UI.class_ "row"
        "Browser" -> do
            let k = M.keys $  M.filter (not. null. rawAuthorization) $   (pkMap inf )
            [tbChooser,subnet] <- chooserTable  inf  k cliTid  cli
            element tbChooser # sink0 UI.style (facts $ noneShow <$> triding menu)
            let
                expand True = "col-xs-10"
                expand False = "col-xs-12"
            element subnet # sink0 UI.class_ (facts $ expand <$> triding menu)
            element body # set UI.children [tbChooser,subnet]# set UI.class_ "row" # set UI.style [("display","inline-flex"),("width","100%")] )) $ liftA2 (\i -> fmap (i,)) (triding nav) evDB


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


authMap smvar sargs (user,pass) schemaN =
      case schemaN of
          "gmail" ->  do
              metainf <- justError "no meta" . M.lookup "metadata" <$> liftIO ( readMVar smvar)
              (dbmeta ,_) <- transaction metainf $ eventTable metainf (lookTable metainf "google_auth") Nothing Nothing []  [("=",liftField metainf "google_auth" $ Attr "username" (TB1 $ SText  "wesley.massuda@gmail.com"))]
              let
                  td :: Tidings OAuth2Tokens
                  td = fmap (\o -> justError "" . fmap (toOAuth . _fkttable . unTB) $ L.find ((==["token"]). fmap (keyValue._relOrigin) . keyattr )  $ F.toList (unKV $ snd $   head $ o )) (G.toList <$> collectionTid dbmeta )
                  toOAuth v = tokenToOAuth (b,d,a,c)
                    where [a,b,c,d] = fmap TB1 $ F.toList $ snd $ unTB1 v :: [FTB Showable]
              return (OAuthAuth (Just ("me",td )), gmailOps)
          i ->  do
            conn <- connectPostgreSQL ("host=" <> (BS.pack $ host sargs) <> " port=" <> BS.pack (port sargs ) <>" user=" <> BS.pack (user )<> " password=" <> BS.pack (pass ) <> " dbname=" <> (BS.pack $  dbn sargs) ) -- <> " sslmode= require")
            execute_ conn "set bytea_output='hex'"
            return (PostAuth conn, postgresOps)

loadSchema smvar schemaN dbConn user authMap  =  do
    keyTables smvar dbConn (schemaN,T.pack $ user) authMap plugList

databaseChooser smvar sargs = do
  dbs <- liftIO $ listDBS  sargs
  let dbsInit = fmap (\s -> (T.pack $ dbn sargs ,) . (,T.pack s) . fst $ snd $ dbs ) $ ( schema sargs)
  (widT,widE) <- loginWidget (Just $ user sargs  ) (Just $ pass sargs )
  dbsW <- listBox (pure $ (\(i,(c,j)) -> (i,) . (c,) <$> j) $ dbs ) (pure dbsInit) (pure id) (pure (line . show . snd . fmap snd ))
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
        let auth = authMap smvar sargs (user,pass)
        loadSchema smvar schemaN conn  user auth
  element dbsW # set UI.style [("height" ,"26px"),("width","140px")]
  chooserT <-  mapTEvent (traverse genSchema) formLogin
  schemaSel <- UI.div # set UI.class_ "col-xs-2" # set children [ schema , getElement dbsW]
  return $ (chooserT,( widE <> (getElement reset : [schemaSel ,load])))


attrLine i   = do
  line ( L.intercalate "," (fmap renderShowable .  allKVRec  $ TB1 i))


lookAttr k (_,m) = M.lookup (S.singleton (Inline k)) (unKV m)

chooserTable inf kitems cliTid cli = do
  iv   <- currentValue (facts cliTid)
  let lookT iv = let  i = join $  unLeftItens . unTB <$> lookAttr (lookKey (meta inf) "clients" "table") iv
                in fmap (\(Attr _ (TB1 (SText t))) -> t) i
  let initKey = pure . join $ fmap (S.fromList .rawPK) . flip M.lookup (_tableMapL inf) <$> join (lookT <$> iv)
  filterInp <- UI.input # set UI.style [("width","100%")]
  filterInpBh <- stepper "" (UI.valueChange filterInp)

  (orddb ,(_,orderMap)) <- liftIO $ transaction (meta inf) $ eventTable  (meta inf) (lookTable (meta inf) "ordering" ) (Just 0) Nothing []      [("=",liftField (meta inf) "ordering" $ uncurry Attr $("schema_name",TB1 $ SText (schemaName inf) ))]
  let renderLabel = (\i -> case M.lookup i (pkMap inf) of
                                       Just t -> T.unpack (translatedName t)
                                       Nothing -> show i )
      filterLabel = (\j -> (\i -> L.isInfixOf (toLower <$> j) (toLower <$> renderLabel i) ))<$> filterInpBh
      tableUsage orderMap pkset = lookAttr (lookKey (meta inf) "ordering" "usage" ) $ justError ("no value" <> show (pkset,pk,orderMap)) $ G.lookup  (G.Idex ( pk )) orderMap
          where  pk = L.sortBy (comparing fst ) $ first (lookKey (meta inf ) "ordering") <$> [("table_name",TB1 . SText . rawName $ justLook   pkset (pkMap inf) ), ("schema_name",TB1 $ SText (schemaName inf))]
  bset <- buttonDivSetT (L.sortBy (flip $ comparing (tableUsage orderMap )) kitems) (tableUsage <$> collectionTid orddb ) initKey  (\k -> UI.button  ) (\k e -> e # set UI.text (renderLabel k) # set UI.style [("width","100%")] # set UI.class_ "btn-xs btn-default buttonSet" # sink UI.style (noneShow . ($k) <$> filterLabel ))
  let bBset = triding bset
      incClick pkset orderMap =  (fst field , getPKM field ,[patch $ fmap (+ (SNumeric 1)) (unTB usage )]) :: TBIdx Key Showable
          where  pk = L.sortBy (comparing fst ) $ first (lookKey (meta inf ) "ordering") <$>[("table_name",TB1 . SText . rawName $ justLook   pkset (pkMap inf) ), ("schema_name",TB1 $ SText (schemaName inf))]
                 field =   justError ("no value" <> show (pkset,pk)) $ G.lookup  (G.Idex  pk ) orderMap
                 usage = justError "nopk " $ (lookAttr (lookKey (meta inf) "ordering" "usage" ))  field
  liftIO$ onEventIO (flip incClick <$> facts (collectionTid orddb) <@> rumors bBset)
    (\p -> do
      _ <- transaction inf $ (patchEd $ schemaOps (meta inf)) (meta inf) p
      putPatch (patchVar orddb) [p] )
  tbChooserI <- UI.div # set children [filterInp,getElement bset]  # set UI.style [("height","90vh"),("overflow","auto"),("height","99%")]
  tbChooser <- UI.div # set UI.class_ "col-xs-2"# set UI.style [("height","90vh"),("overflow","hidden")] # set children [tbChooserI]
  nav  <- buttonDivSet ["Viewer","Browser","Exception","Change"] (pure $ Just "Browser")(\i -> UI.button # set UI.text i # set UI.style [("font-size","smaller")]. set UI.class_ "buttonSet btn-xs btn-default pull-right")
  element nav # set UI.class_ "col-xs-5"
  header <- UI.h1 # sink text (T.unpack . translatedName .  justError "no table " . flip M.lookup (pkMap inf) <$> facts bBset ) # set UI.class_ "col-xs-7"
  chooserDiv <- UI.div # set children  [header ,getElement nav]  # set UI.style [("display","flex"),("align-items","flex-end")]
  body <- UI.div


  el <- mapUITEvent body (\(nav,table)->
      case nav of
        "Change" -> do
            let tableob = (justError "no table " $ M.lookup table (pkMap inf))
            dash <- metaAllTableIndexV inf "modification_table" [("schema_name",TB1 $ SText (schemaName inf) ),("table_name",TB1 $ SText (tableName tableob) ) ]
            element body # set UI.children [dash]
        "Exception" -> do
            let tableob = (justError "no table " $ M.lookup table (pkMap inf))
            dash <- metaAllTableIndexV inf "plugin_exception" [("schema_name",TB1 $ SText (schemaName inf) ),("table_name",TB1 $ SText (tableName tableob) ) ]
            element body # set UI.children [dash]
        "Browser" -> do
            span <- viewerKey inf table cli cliTid
            element body # set UI.children [span]
        "Viewer" -> do
            span <- viewer inf (justError "no table with pk" $ M.lookup table (pkMap inf)) Nothing
            element body # set UI.children [span]
        "Stats" -> do
            span <- viewer inf (justError "no table with pk" $ M.lookup table (pkMap inf)) Nothing
            element body # set UI.children [span]
        ) $ liftA2 (,) (triding nav) bBset
  subnet <- UI.div # set children [chooserDiv,body] # set UI.style [("height","90vh"),("overflow","auto")]
  return [tbChooser, subnet ]

viewerKey
  ::
      InformationSchema -> S.Set Key -> Integer -> Tidings  (Maybe (TBData Key Showable)) -> UI Element
viewerKey inf key cli cliTid = mdo
  iv   <- currentValue (facts cliTid)
  let lookT iv = let  i = join $  unLeftItens . unTB <$> lookAttr (lookKey (meta inf) "clients" "table") iv
                in fmap (\(Attr _ (TB1 (SText t))) -> t) i
      lookPK iv = let  i = join $  unLeftItens . unTB <$> lookAttr (lookKey (meta inf) "clients" "data_index") iv
                       unKey t = liftA2 (,) (join $ (\(Attr _ (TB1 (SText i)))-> flip (lookKey inf ) i <$> lookT iv ) . unTB <$> lookAttr (lookKey  (meta inf) "key_value" "key") t  )( (\(Attr _ (TB1 (SDynamic i)))-> i) . unTB <$> lookAttr (lookKey (meta inf) "key_value" "val") t )
                in fmap (\(IT _ (ArrayTB1 t)) -> catMaybes $ F.toList $ fmap (unKey.unTB1) t) i
  let
      table = justLook  key $ pkMap inf
  reftb@(vpt,vp,gist,var ) <- refTables inf table

  let
      tdip = (\i -> join $ traverse (\v -> G.lookup  (G.Idex (justError "" $ traverse (traverse unSOptional' ) $v)) (snd i) ) (join $ lookPK <$> iv) ) <$> vpt
      tdi = if Just (tableName table) == join (lookT <$> iv) then tdip else pure Nothing
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
        where (s,_) = justLook [] fixmap
  inisort <- currentValue (facts tsort)
  (offset,res3)<- mdo
    offset <- offsetField 0 never (lengthPage <$> facts res3)
    res3 <- mapT0Event (fmap inisort (fmap G.toList vp)) return ( (\f i -> fmap f i)<$> tsort <*> (filtering $ fmap (fmap G.toList) $ tidings ( res2) ( rumors vpt) ) )
    return (offset, res3)
  onEvent (rumors $ triding offset) $ (\i ->  liftIO $ do
    print ("page",(i `div` 10 )   )
    transaction inf $ eventTable  inf table  (Just $ i `div` 10) Nothing  [] [])
  let
    paging  = (\o -> fmap (L.take pageSize . L.drop (o*pageSize)) ) <$> triding offset
  page <- currentValue (facts paging)
  res4 <- mapT0Event (page $ fmap inisort (fmap G.toList vp)) return (paging <*> res3)
  itemList <- listBox (fmap snd res4) (tidings st sel ) (pure id) ( pure attrLine )

  let evsel =  unionWith const (rumors (triding itemList)) (rumors tdi)
  liftIO $ onEventIO (evsel ) (\i -> void . editClient (meta inf) (Just inf) (Just table ) (getPKM <$> i) cli =<< getCurrentTime )
  prop <- stepper cv evsel
  let tds = tidings prop (diffEvent  prop evsel)

  (cru,ediff,pretdi) <- crudUITable inf (pure "Editor")  reftb [] [] (allRec' (tableMap inf) table) tds
  diffUp <-  mapEvent (fmap pure)  $ (\i j -> traverse (return . flip apply j ) i) <$> facts pretdi <@> ediff
  let
     sel = filterJust $ fmap (safeHead . concat) $ unions $ [(unions  [rumors  $triding itemList  ,rumors tdi]),diffUp]
  st <- stepper cv sel
  res2 <- stepper (vp) (rumors vpt)
  onEvent (pure <$> ediff) (liftIO .  putPatch var )
  element itemList # set UI.multiple True # set UI.style [("width","70%"),("height","350px")] # set UI.class_ "col-xs-9"
  title <- UI.h4  #  sink text ( maybe "" (L.intercalate "," . fmap (renderShowable .snd) . F.toList . getPK. TB1 )  <$> facts tds) # set UI.class_ "col-xs-8"
  insertDiv <- UI.div # set children [title,head cru] # set UI.class_ "row"
  insertDivBody <- UI.div # set children [insertDiv,last cru]# set UI.class_ "row"
  itemSel <- UI.ul # set items ((\i -> UI.li # set children [ i]) <$> [getElement offset ,filterInp ,getElement sortList,getElement asc] ) # set UI.class_ "col-xs-3"
  itemSelec <- UI.div # set children [getElement itemList, itemSel] # set UI.class_ "row"
  UI.div # set children ([updateBtn,itemSelec,insertDivBody ] )



