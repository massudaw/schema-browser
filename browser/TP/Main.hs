{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module TP.Main where

import TP.Selector
import TP.Extensions
import Data.Unique
import ClientAccess
import TP.Task
import qualified Data.Interval as I
import TP.QueryWidgets
import Query
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
import TP.Task
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


col :: UI Element -> Int -> UI Element
col i l =   i # set   UI.class_ ("col-xs-" ++ show l)

borderSchema inf  = [("border", "solid 1px" <> maybe "grey" (('#':).T.unpack) (schemaColor inf))]

setup
  ::  TVar DatabaseSchema ->  BrowserState -> [Plugins] -> Window -> UI ()
setup smvar bstate plugList w = void $ do
  metainf <- liftIO$ metaInf smvar
  setCallBufferMode BufferAll
  let
      url = fmap BS.unpack $ BS.split '/' $ BS.drop 11 $ rqURI $request w
      iniSchema = safeHead url
      iniTable = safeHead (tail url)
  return w # set title (host bstate <> " - " <>  dbn bstate)
  cliTid <- fmap (fmap schema_selection) <$>  (ui $ lookClient (fromIntegral $ wId w) metainf)
  (evDB,chooserItens) <- databaseChooser  (rqCookies $request w) smvar metainf bstate plugList (pure (fmap T.pack $ maybeToList iniSchema))
  cliZone <- jsTimeZone
  cliTidIni <- currentValue (facts cliTid)
  selschemas <- ui $ accumDiffCounterIni (maybe 0 L.length cliTidIni)  (\six -> runUI w . (\inf -> do
    reset <- UI.button  # set text "Reset"
    resetE <- UI.click reset
    ui $ onEventIO resetE (\_ -> resetCache inf)
    menu <- checkedWidget (pure True)
    body <- UI.div# set UI.class_ "row"
    ui $ addSchemaIO (fromIntegral $ wId w) metainf inf six
    metadataNav <- sequenceA $  M.fromList
               [("Map",fmap (^._2) <$>mapWidgetMeta inf)
               ,("Chart",fmap (^._2) <$> chartWidgetMetadata inf)
               ,("Plan",fmap (^._2) <$> taskWidgetMeta inf)
               ,("Account",fmap (^._2) <$> accountWidgetMeta inf)
               ,("Agenda",fmap (^._2) <$> eventWidgetMeta inf )]
    let checkNav i =  maybe True (\i -> isJust .nonEmpty $ i) $ M.lookup i  metadataNav
    element menu # set UI.class_ "col-xs-1"
    element reset # set UI.class_ "col-xs-1"
    nav  <- buttonDivSet  (filter checkNav ["Browser","Map","Account","Plan", "Agenda","Chart","Metadata"] ) (pure  Nothing) (\i ->
        UI.button # set UI.text i # set UI.class_ "buttonSet btn-xs btn-default pull-right" )
    element nav # set UI.class_ "col-xs-5 pull-right"
    chooserDiv <- UI.div
        # set children  [getElement menu,getElement reset,getElement nav ]
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
           label <- UI.div # sink0 UI.text (fmap T.unpack $ facts $ lookDesc  <*> pure k) # set UI.class_ "fixed-label col-xs-11"
           element e # set UI.class_ "col-xs-1"
           UI.label # set children [e , label] # set UI.class_ "table-list-item" # set UI.style [("display","-webkit-box")]

      bset <- tableChooser inf  kitems (fst <$> triding tfilter ) (snd <$> triding tfilter)  (schemaName inf) (snd (username inf)) initKey
      posSel <- positionSel
      (sidebar,calendarT) <- calendarSelector
      tbChooser <- UI.div
          # set UI.class_ "col-xs-2"
          # set UI.style ([("height","80vh"),("overflow","hidden")] ++ borderSchema inf)
          # set children [sidebar,posSel ^._1,getElement bset]
          # sink0 UI.style (facts $ noneShow <$> triding menu)
      tfilter <-  switchManyUI (pure (buttonStyle,const True)) (triding nav) (M.fromList
          [("Map",do
            (m,widget) <-  configExtension inf agendaDef (mapWidget calendarT posSel (triding bset) inf)
            st <- once (fmap (flip elem . fmap (^._2)) m)
            return $ TrivialWidget  st widget),
          ("Agenda" ,do
            cliZone <- jsTimeZone
            (m,widget) <-  configExtension inf agendaDef (eventWidget calendarT (triding bset) inf cliZone)
            st <- once (fmap (flip elem . fmap (^._2)) m)
            return $ TrivialWidget st widget),
          ("Chart" ,do
            cliZone <- jsTimeZone
            (m,widget) <-  configExtension inf chartDef (chartWidget calendarT posSel (triding bset) inf cliZone)
            st <- once (fmap (flip elem . fmap (^._2)) m)
            return $ TrivialWidget st widget),
          ("Account" ,do
            (m,widget) <-  configExtension inf accountDef (accountWidget calendarT (triding bset) inf)
            st <- once (fmap (flip elem . fmap (^._2)) m)
            return $ TrivialWidget st widget),
          ("Plan" ,do
            (m,widget) <-  configExtension inf taskDef (taskWidget calendarT (triding bset) inf)
            st <- once (fmap (flip elem . fmap (^._2)) m)
            return $ TrivialWidget st widget),
          ("Metadata" ,do
                let metaOpts = ["Change","Exception","Poll","Stats"]
                    displayOpts  i =  UI.button # set UI.text i # set UI.class_ "buttonSet btn-xs btn-default pull-right"
                metanav <- buttonDivSet metaOpts (pure Nothing) displayOpts
                element metanav # set UI.class_ "col-xs-5 pull-right"
                metabody <- UI.div
                metaDiv <- UI.div # set children [getElement metanav,metabody] # set UI.class_ "row" # set UI.style [("display","block")]
                traverseUI (\(nav,tables)-> case nav  of
                  "Poll" -> do
                    els <- sequence   [ metaTable inf "polling" [(keyRef "schema",Left (schId,Equals) ) ]
                                        , metaTable inf "polling_log" [(keyRef "schema",Left (schId,Equals) ) ]]
                    element metabody #
                        set children els
                  "Change" ->
                      case schemaName inf of
                        i -> do
                          let pred = [(keyRef "user_name",Left (txt (snd $ username inf ),Equals)),(keyRef "schema_name",Left (txt $schemaName inf,Equals) ) ] <> if S.null tables then [] else [ (keyRef "table_name",Left (ArrayTB1 $ txt . tableName<$>  Non.fromList (F.toList tables),Flip (AnyOp Equals)))]
                          dash <- metaTable inf "modification_table" pred
                          element metabody # set UI.children [dash] # set UI.style [("overflow","auto")] # set UI.class_ "col-xs-12"
                  "Stats" -> do
                      let pred = [(keyRef "schema",Left (schId,Equals) ) ] <> if S.null tables then [] else [ (keyRef "table",Left (ArrayTB1 $ int. tableUnique<$>  Non.fromList (S.toList tables),Flip (AnyOp Equals)))]
                      stats_load <- metaTable inf "stat_load_table" pred
                      stats <- metaTable inf "table_stats" pred
                      clients <- metaTable inf "clients" [(RelAccess [keyRef "selection"] $ keyRef "schema",Left (int (schemaId inf),Equals) )]-- <> if M.null tables then [] else [ (Nested (keyRef ["selection"] ) (Many [ keyRef ["table"]]),Left (ArrayTB1 $ txt . rawName <$>  Non.fromList (concat (F.toList tables)),Flip (AnyOp Equals)) )]
                      element metabody # set UI.children [stats,stats_load,clients]
                  "Exception" -> do
                      let pred = [(keyRef "schema",Left (schId,Equals) ) ] <> if S.null tables then [] else [ (keyRef "table",Left (ArrayTB1 $ int . tableUnique<$>  Non.fromList (F.toList tables),Flip (AnyOp Equals)))]
                      dash <- metaTable inf "plugin_exception" pred
                      element metabody # set UI.children [dash]
                  i -> error (show i)
                      ) ((,) <$> triding metanav <*> triding bset)
                st <- once (buttonStyle,const True)
                return  $ TrivialWidget st metaDiv),
          ("Browser" ,do
            subels <- chooserTable  six  inf  bset (fmap (!!six) <$> cliTid) (wId w)
            el <- UI.div # set children  (pure subels)
            st <- once (buttonStyle,const True)
            return  $ TrivialWidget st el )])
      bd <- UI.div # set children [(getElement tfilter)] # set UI.style ([("height","80vh"),("overflow","auto")] ++ borderSchema inf)
                       # sink0 UI.class_ (facts $ expand <$> triding menu)
      element body # set children [tbChooser,bd]
      return tfilter
    return container ))  (S.fromList <$> evDB)
  (edbl,hdbl) <- ui newEvent

  headers <- ui $ accumDiff (\inf -> runUI w $ do
    h <- UI.h3 # set text (T.unpack $ schemaName inf) # set UI.class_ "header"
    ch <- UI.click h
    onEvent ch $ (\_ -> liftIO $ hdbl True)
    return h ) (S.fromList <$> evDB)
  schemaH <- UI.div
  hoverE <- hoverTip schemaH
  hoverT <- ui $ stepperT True (unionWith const edbl hoverE)
  let
    displayH =  (||) <$> hoverT <*> (L.null <$> evDB)
    style True = UI.span # set UI.class_ "glyphicon glyphicon-collapse-up"
    style False = UI.span # set UI.class_ "glyphicon glyphicon-expand"
  header <- UI.div  # set  children chooserItens # set UI.class_ "col-xs-10"
  merged <- ui $ accumDiffMapCounter (\ix (k,(i,j)) -> runUI w $ UI.div # set children [i,j])   (M.intersectionWith (,) <$>  headers <*>  selschemas)
  (layouth,top) <- layoutSel' onShiftAlt  merged
  element header # sink UI.style (noneShow <$> facts displayH)
  element layouth
    # set UI.class_ "col-xs-1"
    # sink UI.style (noneShow <$> facts displayH)
  element schemaH # set children [layouth,header] # set UI.class_ "row"
  addBody [schemaH,top]



listDBS ::  InformationSchema -> Text -> Dynamic (Tidings (M.Map Text (Int,Text)))
listDBS metainf db = do
  dbvar <- transactionNoLog metainf $  selectFrom "schema2" Nothing Nothing [] mempty
  let
    schemas schemasTB =  M.fromList $  liftA2 (,) sname  (liftA2 (,) sid stype) <$> F.toList  schemasTB
      where
        sname = untxt . lookAttr' "name"
        stype = untxt . lookAttr' "type"
        sid = unint . lookAttr' "oid"
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
    usernameT <- ui $ stepperT userI usernameE
    passwordT <- ui $stepperT passI passwordE
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
  cookiesMap <- ui $ transactionNoLog metainf $  selectFrom "auth_cookies" Nothing Nothing [] mempty
  let loginCookie =  (\m -> maybe Nothing (\ck -> G.lookup (G.Idex [TB1 $ SText ck]) m) rCookie )  <$> collectionTid cookiesMap
  (widT,widE) <- loginWidget (Just $ user sargs  ) (Just $ pass sargs )
  load <- UI.button # set UI.text "Log In" # set UI.class_ "row"
  loadE <- UI.click load
  login <- UI.div # set children widE # set UI.class_ "row"
  authBox <- UI.div # set children [login ,load]   # set UI.class_ "col-xs-2" # sink UI.style (noneShow . isJust <$> facts loginCookie)
  orddb  <- ui $ transactionNoLog metainf ((selectFromTable "schema_ordering"  Nothing Nothing []  mempty ))
  let
    ordRow map orderMap inf =  field
      where
        field =  lookAttr' "usage" <$> G.lookup pk orderMap
        pk = idex metainf "schema_ordering" [ ("schema",int $ fst $ fromJust $ M.lookup inf map )]
    formLogin = form widT loadE
    db = T.pack $ dbn sargs
    buttonString k = do
      b <- UI.input # set UI.type_ "checkbox"
      chkE <- UI.checkedChange b
      return (b,chkE)

  dbs <- ui $ listDBS  metainf  db
  dbsInit <- currentValue (M.keys <$> facts dbs)
  dbsWPre <- checkDivSetTGen
              dbsInit
              (ordRow <$> dbs <*> collectionTid orddb)
              (S.fromList <$> init )
              buttonString
              (pure (\i o -> Just $ do
                l <- UI.span # set text (T.unpack  i)
                UI.label  # set children [l,o] # set UI.style [("padding","2px")]  ))
  let dbsW = TrivialWidget ((\i j ->  (\k -> justError (" no schema" <> show (k,j)) $ (db, ) . (k,)<$> M.lookup k j )<$> i ) <$> (S.toList <$> triding dbsWPre) <*> dbs) (getElement dbsWPre)
  cc <- currentValue (facts $ triding dbsW)
  let dbsWE = rumors $ triding dbsW
  dbsWT <-  ui $stepperT cc dbsWE
  (schemaE,schemaH) <- ui newEvent
  w <- askWindow
  metainf <- liftIO $ metaInf smvar
  let
    genSchema e@(db,(schemaN,(sid,ty))) (user,pass) = case ty of
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



withTable s m w =
  withInf [] s (\inf -> runDynamic $ do
    now <- liftIO getCurrentTime
    let pred = (WherePredicate $ lookAccess inf m <$> w)
        -- pred = WherePredicate $ lookAccess inf m <$>(AndColl [OrColl [PrimColl (IProd Nothing "scheduled_date",Left (IntervalTB1 (I.interval (I.Finite (TB1 (STime (SDate (utctDay now) ))),True) (I.Finite (TB1 (STime (SDate (utctDay (addUTCTime (3600*24*35) now))))),True)),Flip Contains))]])
        table = lookTable inf m
    db <- transactionNoLog  inf $ selectFrom m Nothing Nothing []mempty
    i2 <- currentValue (facts $ collectionTid db)
    let
        debug i = show <$> G.toList i
    liftIO $ putStrLn (unlines $ debug i2))

testCreate = withInf [] "metadata"
 (\inf -> liftIO $ createFresh "tables" inf "geo" (Primitive [KOptional] (RecordPrim ("metadata","geo"))))

withInf plugs s v  = do
  args <- getArgs
  let db = argsToState args
  smvar <- createVar
  let
    amap = authMap smvar db ("postgres", "queijo")
  (inf,fin) <- runDynamic $ keyTables smvar  (s,"postgres") amap plugs
  v inf


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
