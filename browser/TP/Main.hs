{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module TP.Main where

import TP.Selector
import Data.Unique
import qualified Data.Interval as I
import Plugins.Schema (codeOps)
import Control.Exception
import qualified Data.Binary as B
import System.Random
import Postgresql.Backend (connRoot, postgresOps)
import System.Process
import Serializer
import Control.Concurrent.STM
import Data.Tuple
import TP.View
import Data.Aeson (decode,Value(String))
import TP.Account
import TP.Browser
import Control.Monad.Writer (runWriterT)
import TP.Agenda
import TP.Chart
import Control.Lens (_1,_2,(^.),over)
import TP.Map
import Safe
import qualified NonEmpty as Non
import Data.Char
import Step.Common
import Step.Host
import Data.Time
import qualified Types.Index as G
import Debug.Trace
import Types
import SchemaQuery
import TP.Widgets
import Prelude hiding (head)
import TP.QueryWidgets
import Control.Monad.Reader
import Control.Concurrent
import System.Environment
import Data.Ord
import Utils
import Schema
import Types.Patch
import Data.Maybe
import Reactive.Threepenny hiding(apply)
import qualified Data.List as L
import qualified Data.ByteString.Char8 as BS

import RuntimeTypes
import qualified Graphics.UI.Threepenny as UI
import Graphics.UI.Threepenny.Core hiding (get,delete,apply)
import Graphics.UI.Threepenny.Internal (wId,request)
import Data.Monoid hiding (Product(..))

import qualified Data.Foldable as F
import qualified Data.Text as T
import Data.Text (Text)
import qualified Data.Set as S
import Snap.Core (cookieName,cookieValue,rqURI,rqCookies)

import Database.PostgreSQL.Simple
import qualified Data.Map as M
import qualified Data.HashMap.Strict as HM

import GHC.Stack

col :: UI Element -> Int -> UI Element
col i l =   i # set   UI.class_ ("col-xs-" ++ show l)

borderSchema inf  = [("border", "solid 1px" <> maybe "grey" (('#':).T.unpack) (schemaColor inf))]

setup
  ::  TVar DatabaseSchema ->  [String] -> [Plugins] -> Window -> UI ()
setup smvar args plugList w = void $ do
  metainf <- liftIO$ metaInf smvar
  setCallBufferMode BufferAll
  let bstate = argsToState args
      url = fmap BS.unpack $ BS.split '/' $ BS.drop 11 $ rqURI $request w
      iniSchema = safeHead url
      iniTable = safeHead (tail url)
  return w # set title (host bstate <> " - " <>  dbn bstate)
  cliTid <- ui $ lookClient (fromIntegral $ wId w) metainf
  (evDB,chooserItens) <- databaseChooser  (rqCookies $request w) smvar metainf bstate plugList (pure (fmap T.pack $ maybeToList iniSchema))
  cliZone <- jsTimeZone
  selschemas <- ui $ accumDiffCounter (\six -> runUI w . (\inf -> do
    menu <- checkedWidget (pure True)
    body <- UI.div# set UI.class_ "row"
    ui $ addSchemaIO (fromIntegral $ wId w) metainf inf six
    metadataNav <- sequenceA $  M.fromList
               [("Map",fmap (^._2) <$>mapWidgetMeta inf)
               ,("Chart",fmap (^._2) <$> chartWidgetMetadata inf)
               ,("Account",fmap (^._2) <$> accountWidgetMeta inf)
               ,("Agenda",fmap (^._2) <$> eventWidgetMeta inf cliZone)]
    element menu # set UI.class_ "col-xs-1"
    nav  <- buttonDivSet  ["Map","Account","Agenda","Chart","Browser","Metadata"] (pure $ args `atMay` 6  )(\i ->
        UI.button # set UI.text i # set UI.class_ "buttonSet btn-xs btn-default pull-right" # set UI.style (noneShow (maybe True (\i -> isJust .nonEmpty $ i) $ M.lookup i  metadataNav) ))
    element nav # set UI.class_ "col-xs-5 pull-right"
    chooserDiv <- UI.div
        # set children  [getElement menu,getElement nav ]
        # set UI.style [("align-items","flex-end")]
        # set UI.class_ "row"
        # set UI.style (("align-items","flex-end") : borderSchema inf)
    container <- UI.div
        # set children [chooserDiv , body]
        # set UI.class_ "container-fluid"
        # set UI.style (("align-items","flex-end") : borderSchema inf)
    let
      expand True = "col-xs-10"
      expand False = "col-xs-12"
    mdo
      let
        kitems = F.toList (pkMap inf)
        schId = int $ schemaId inf
        initKey = pure (maybeToList $ (\s -> if schemaName inf == T.pack s then lookTable inf . T.pack<$> iniTable   else Nothing) =<< iniSchema )
        buttonStyle lookDesc k e = Just <$> do
           label <- UI.div # sink0 UI.text (fmap T.unpack $ facts $ lookDesc  <*> pure k)  # set UI.class_ "fixed-label col-xs-11"
           element e # set UI.class_ "col-xs-1"
           UI.label # set children [e , label] # set UI.class_ "table-list-item" # set UI.style [("display","-webkit-box")]

      bset <- tableChooser inf  kitems (fst <$> tfilter ) (snd <$> tfilter)  (schemaName inf) (snd (username inf)) initKey
      posSel <- positionSel
      bd <- UI.div  # sink0 UI.class_ (facts $ expand <$> triding menu)
      (sidebar,calendarT) <- calendarSelector
      tbChooser <- UI.div
          # set UI.class_ "col-xs-2"
          # set UI.style ([("height","90vh"),("overflow","hidden")] ++ borderSchema inf)
          # set children [sidebar,posSel ^._1,getElement bset]
          # sink0 UI.style (facts $ noneShow <$> triding menu)
      element body # set children [tbChooser,bd]
      element bd
          # set UI.style ([("height","90vh"),("overflow","auto")] ++ borderSchema inf)
      tfilter <-  traverseUI (\nav-> do
        bdo <- UI.div
        element bd # set children [bdo]
        case nav of
          "Map" -> do
            element bdo  # set UI.style [("width","100%")]
            fmap (flip elem . fmap (^._2)) <$> mapWidget bdo calendarT posSel (triding bset) inf
          "Agenda" -> do
            element bdo  # set UI.style [("width","100%")]
            cliZone <- jsTimeZone
            fmap (flip elem . fmap (^._2)) <$>  eventWidget bdo calendarT (triding bset) inf cliZone
          "Chart" -> do
            element bdo  # set UI.style [("width","100%")]
            cliZone <- jsTimeZone
            fmap (flip elem . fmap (^._2)) <$>  chartWidget bdo calendarT posSel (triding bset) inf cliZone
          "Account" -> do
            element bdo  # set UI.style [("width","100%")]
            fmap (flip elem . fmap (^._2)) <$> accountWidget bdo calendarT (triding bset) inf
          "Metadata" -> do
                let metaOpts = ["Poll","Stats","Change","Exception"]
                    iniOpts = join $ fmap (\i -> if i `elem` metaOpts then Just i else Nothing)$  args `atMay`  7
                    displayOpts  i =  UI.button # set UI.text i # set UI.class_ "buttonSet btn-xs btn-default pull-right"
                metanav <- buttonDivSet metaOpts (pure iniOpts) displayOpts
                element metanav # set UI.class_ "col-xs-5 pull-right"
                metabody <- UI.div
                element bdo # set children [getElement metanav,metabody] # set UI.class_ "row" # set UI.style [("display","block")]
                traverseUI (\(nav,tables)-> case nav  of
                  "Poll" -> do
                      els <- sequence      [ metaAllTableIndexA inf "polling" [(keyRef "schema",Left (schId,Equals) ) ]
                            , metaAllTableIndexA inf "polling_log" [(keyRef "schema",Left (schId,Equals) ) ]]
                      element metabody #
                        set children els
                  "Change" ->
                      case schemaName inf of
                        i -> do
                          let pred = [(keyRef "user_name",Left (txt (snd $ username inf ),Equals)),(keyRef "schema_name",Left (txt $schemaName inf,Equals) ) ] <> if S.null tables then [] else [ (keyRef "table_name",Left (ArrayTB1 $ txt . tableName<$>  Non.fromList (F.toList tables),Flip (AnyOp Equals)))]
                          dash <- metaAllTableIndexA inf "master_modification_table" pred
                          element metabody # set UI.children [dash] # set UI.style [("overflow","auto")] # set UI.class_ "col-xs-12"
                  "Stats" -> do
                      let pred = [(keyRef "schema",Left (schId,Equals) ) ] <> if S.null tables then [] else [ (keyRef "table",Left (ArrayTB1 $ int. tableUnique<$>  Non.fromList (S.toList tables),Flip (AnyOp Equals)))]
                      stats_load <- metaAllTableIndexA inf "stat_load_table" pred
                      stats <- metaAllTableIndexA inf "table_stats" pred
                      clients <- metaAllTableIndexA inf "clients" [(Nested [keyRef "selection"] $ Many [One $ keyRef "schema"],Left (int (schemaId inf),Equals) )]-- <> if M.null tables then [] else [ (Nested (keyRef ["selection"] ) (Many [ keyRef ["table"]]),Left (ArrayTB1 $ txt . rawName <$>  Non.fromList (concat (F.toList tables)),Flip (AnyOp Equals)) )]
                      element metabody # set UI.children [stats,stats_load,clients]
                  "Exception" -> do
                      let pred = [(keyRef "schema",Left (schId,Equals) ) ] <> if S.null tables then [] else [ (keyRef "table",Left (ArrayTB1 $ int . tableUnique<$>  Non.fromList (F.toList tables),Flip (AnyOp Equals)))]
                      dash <- metaAllTableIndexA inf "plugin_exception" pred
                      element metabody # set UI.children [dash]
                  i -> errorWithStackTrace (show i)
                      ) ((,) <$> triding metanav <*> triding bset)
                return bdo# set UI.style [("height","90vh"),("overflow","auto")]
                return  (buttonStyle, const True)
          "Browser" -> do
            subels <- chooserTable  six  inf  bset cliTid (wId w)
            element bdo  # set children  (pure subels) # set UI.style [("height","90vh"),("overflow","auto")]
            return  (buttonStyle, const True)
          i -> errorWithStackTrace (show i)
           )  (triding nav)
      return tfilter
    return container ))   (S.fromList <$> evDB)
  header <- UI.div # set UI.class_ "row" # set  children (chooserItens)
  top <- layoutSel onShiftAlt  (F.toList <$> selschemas )# set UI.class_ "row"
  addBody [header,top]


listDBS ::  InformationSchema -> Text -> Dynamic (Tidings (M.Map Text Text))
listDBS metainf db = do
  (dbvar ,_) <- transactionNoLog metainf $  selectFrom "schema2" Nothing Nothing [] mempty
  let
    schemas schemasTB =  M.fromList $  liftA2 (,) sname  stype <$> F.toList  schemasTB
      where
        sname = untxt . lookAttr' "name"
        stype = untxt . lookAttr' "type"
        unint (TB1 (SNumeric s))= s
        untxt (TB1 (SText s))= s
        untxt (LeftTB1 (Just (TB1 (SText s))))= s
  return (schemas  <$> collectionTid dbvar)

loginWidget userI passI =  do
    usernamel <- flabel # set UI.text "Usuário"
    username <- UI.input # set UI.name "username" # set UI.style [("width","142px")] # set UI.value (Data.Maybe.fromMaybe "" userI)
    passwordl <- flabel # set UI.text "Senha"
    password <- UI.input # set UI.name "password" # set UI.style [("width","142px")] # set UI.type_ "password" # set UI.value (Data.Maybe.fromMaybe "" passI)
    usernameE <- fmap nonEmpty  <$> UI.valueChange username
    passwordE <- fmap nonEmpty <$> UI.valueChange password

    userDiv <- UI.div # set children [usernamel,username] # set UI.class_  "col-xs-5"
    passDiv <- UI.div # set children [passwordl,password] # set UI.class_  "col-xs-5"
    usernameB <- ui $ stepper userI usernameE
    passwordB <-  ui $stepper passI passwordE
    let usernameT = tidings usernameB usernameE
        passwordT = tidings passwordB passwordE
    return (liftA2 (liftA2 (,)) usernameT passwordT ,[userDiv,passDiv])

form :: Tidings a -> Event b -> Tidings a
form td ev =  tidings (facts td ) (facts td <@ ev )

authMap smvar sargs (user,pass) schemaN =
      case schemaN of
          "code" -> return (NoAuth , codeOps)
          i ->  do
            conn <- connectPostgreSQL ("host=" <> BS.pack (host sargs) <> " port=" <> BS.pack (port sargs ) <>" user=" <> BS.pack user<> " password=" <> BS.pack pass <> " dbname=" <> BS.pack (dbn sargs) <> " " )
            execute_ conn "set bytea_output='hex'"
            return (PostAuth conn, postgresOps)

loadSchema smvar schemaN user authMap  plugList =
    keyTables smvar (schemaN,T.pack user) authMap plugList

databaseChooser cookies smvar metainf sargs plugList init = do
  let rCookie = fmap (T.pack . BS.unpack . cookieValue) $ L.find ((=="auth_cookie"). cookieName ) cookies
  (cookiesMap,_) <- ui $ transactionNoLog metainf $  selectFrom "auth_cookies" Nothing Nothing [] mempty
  let loginCookie =  (\m -> maybe Nothing (\ck -> G.lookup (G.Idex [TB1 $ SText ck]) m) rCookie )  <$> collectionTid cookiesMap
  (widT,widE) <- loginWidget (Just $ user sargs  ) (Just $ pass sargs )
  load <- UI.button # set UI.text "Log In" # set UI.class_ "row"
  loadE <- UI.click load
  login <- UI.div # set children widE # set UI.class_ "row"
  authBox <- UI.div # set children [login ,load]   # set UI.class_ "col-xs-2" # sink UI.style (noneShow . isJust <$> facts loginCookie)
  let
      formLogin = form widT loadE
  let db = T.pack $ dbn sargs
      buttonString k = do
          b <- UI.input # set UI.type_ "checkbox"
          chkE <- UI.checkedChange b
          return (k,(b,chkE))

  dbs <- ui $ listDBS  metainf  db
  dbsInit <- currentValue (M.keys <$> facts dbs)
  dbsWPre <- checkDivSetTGen
              dbsInit
              (S.fromList <$> init )
              buttonString

              (pure (\i o -> do
                l <- UI.span # set text (T.unpack  i)
                UI.label  # set children [l,o] # set UI.style [("padding","2px")]  ))
{-
  dbsWPre <- multiListBox
      (M.keys <$> dbs)
      init
      (pure (line . T.unpack))
-}
  let dbsW = TrivialWidget ((\i j ->  (\k -> justError (" no schema" <> show (k,j)) $ (db, ) . (k,)<$> M.lookup k j )<$> i ) <$> (S.toList <$> triding dbsWPre) <*> dbs) (getElement dbsWPre)
  cc <- currentValue (facts $ triding dbsW)
  let dbsWE = rumors $ triding dbsW
  dbsWB <-  ui $stepper cc dbsWE
  let dbsWT  = tidings dbsWB dbsWE
  (schemaE,schemaH) <- ui newEvent
  w <- askWindow
  metainf <- liftIO $ metaInf smvar
  let
    genSchema e@(db,(schemaN,ty)) (user,pass) = case ty of
        "sql" -> do
            let auth = authMap smvar sargs (user,pass)
            gen <- liftIO randomIO
            now <- liftIO getCurrentTime
            let cli = AuthCookies (T.pack user) gen now
            inf <- loadSchema smvar schemaN  user auth plugList
            runUI w . runFunction $ ffi "document.cookie = 'auth_cookie=%1'" gen
            transaction metainf $ insertFrom (lookMeta (metainf) "auth_cookies") (liftTable' metainf "auth_cookies" $ encodeT cli)
            return inf

        "code" -> do
            let auth = authMap smvar sargs (user,pass)
            loadSchema smvar schemaN  user auth plugList

  chooserT <- traverseUI ui $ (\i -> mapM (flip genSchema (justError "no pass" i))  ) <$>  formLogin <*>dbsWT
  schemaSel <- UI.div  # set children [getElement dbsW]
  return (chooserT,[schemaSel ,authBox] )

createVar :: IO (TVar DatabaseSchema)
createVar = do
  args <- getArgs
  let db = argsToState args
  b <- lookupEnv "ROOT_SERVER"
  smvar   <- atomically $newTVar HM.empty
  conn <- connectPostgreSQL (connRoot db)
  l <- query_ conn "select oid,name from metadata.schema"
  atomically $ newTVar  (DatabaseSchema (M.fromList l) (isJust b) (HM.fromList $ swap <$> l) conn smvar)


testSync  = do
  args <- getArgs
  let db = argsToState args
  smvar <- createVar
  let
    amap = authMap smvar db ("postgres", "queijo")
  (meta,fin) <- runDynamic $ keyTables smvar  ("metadata","postgres") amap []
  let
    amap = authMap smvar db ("wesley.massuda@gmail.com", "queijo")
  (inf,fin) <- runDynamic $ keyTables smvar  ("gmail","wesley.massuda@gmail.com") amap []
  let start = "7629481"
  -- runDynamic $ transaction inf $ historyLoad
  return ()

testTablePersist s t w = do
  args <- getArgs
  let db = argsToState args
  smvar <- createVar
  let
    amap = authMap smvar db ("postgres", "queijo")
  (inf,fin) <- runDynamic $ keyTables smvar  (s,"postgres") amap []
  runDynamic $ do
    (e,(_,i)) <- transactionNoLog inf $ selectFrom t Nothing Nothing [] (WherePredicate $ lookAccess inf t <$> w)
    liftIO$ putStrLn "Select"
    liftIO$ mapM print (F.toList i)
    let table = lookTable inf t

    liftIO$ callCommand ("rm dump/" ++ T.unpack s ++ "/"++ T.unpack t) `catch` (\e -> print (e :: SomeException))
    liftIO$ writeSchema (s ,inf)
    liftIO$ atomically $ modifyTVar (mvarMap inf) (const M.empty)
    (_,o) <- readTable inf "dump"  table []
    liftIO$ putStrLn "Read"
    liftIO$ mapM print (F.toList o)

  return ()



testTable s t  = do
  args <- getArgs
  let db = argsToState args
  smvar <- createVar
  let
    amap = authMap smvar db ("postgres", "queijo")
  (inf,fin) <- runDynamic $ keyTables smvar  (s,"postgres") amap []
  ((_,(_,i)),_) <- runDynamic $ transactionNoLog inf $ selectFrom t Nothing Nothing [] mempty

  return i


testPlugin s t p  = do
  args <- getArgs
  let db = argsToState args
  smvar <- createVar
  let
    amap = authMap smvar db ("postgres", "queijo")
  (inf,fin) <- runDynamic $ keyTables smvar  (s,"postgres") amap []
  let (i,o) = pluginStatic p
  print $ liftAccessU inf t i
  print $ liftAccessU inf t o

testCalls = testWidget (do
  setCallBufferMode BufferAll
  i <- runFunction (ffi "var a= 1")
  i <- callFunction (ffi "2")
  j <- callFunction (ffi "1")
  UI.div # set text (show (i + j :: Int))

                       )
