{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module TP.Main where

import TP.Selector
import TP.Extensions
import Serializer
import ClientAccess
import Safe
import GHC.IO.Unsafe
import PrimEditor
import TP.Task
import TP.QueryWidgets
import Plugins.Schema (codeOps)
import System.Random
import Postgresql.Backend (connRoot, postgresOps)
import Serializer
import Control.Concurrent.STM
import Data.Tuple
import TP.Account
import TP.Browser
import TP.Agenda
import TP.Chart
import Control.Lens (_1,_2,(^.))
import TP.Map
import qualified NonEmpty as Non
import Step.Common
import Data.Time
import qualified Types.Index as G
import Types
import SchemaQuery
import TP.Widgets
import Prelude hiding (head)
import Control.Monad.Reader
import System.Environment
import Utils
import Schema
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
          label <- UI.div # set UI.text (T.unpack $ lookDesc ) # set UI.class_ "fixed-label col-xs-11"
          element e # set UI.class_ "col-xs-1"
          UI.label # set children [e , label] # set UI.class_ "table-list-item" # set UI.style [("display","-webkit-box")]

      bset <- tableChooser inf  kitems (fst <$> triding tfilter ) (snd <$> triding tfilter) initKey
      posSel <- positionSel
      (sidebar,calendarT) <- calendarSelector
      tbChooser <- UI.div
          # set UI.class_ "col-xs-2"
          # set UI.style ([("height","80vh"),("overflow","hidden")] ++ borderSchema inf)
          # set children [sidebar,posSel ^._1,getElement bset]
          # sink0 UI.style (facts $ noneShow <$> triding menu)
      let cliTables = (fmap (!!six) <$> cliTid)
      iniCliTable <- currentValue (facts cliTables)
      ui $ accumDiffCounterIni (maybe 0 (length .table_selection)  iniCliTable) (\ix table->  trackTable (meta inf) (wId w) table six ix) (triding bset)
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
                let metaOpts = ["Change","Exception","Polling","Clients"]
                    displayOpts  i =  UI.button # set UI.text i # set UI.class_ "buttonSet btn-xs btn-default pull-right"
                metanav <- buttonDivSet metaOpts (pure Nothing) displayOpts
                element metanav # set UI.class_ "col-xs-5 pull-right"
                metabody <- UI.div
                metaDiv <- UI.div # set children [getElement metanav,metabody] # set UI.class_ "row" # set UI.style [("display","block")]
                els <- traverseUI (maybe (return []) (\(nav,tables) -> case nav  of
                  "Polling" -> do
                    els <- sequence   [ metaTable inf "polling" [(keyRef "schema",Left (schId,Equals) ) ]                                        ]
                    return els
                  "Change" ->
                      case schemaName inf of
                        i -> do
                          label <- flabel # set UI.text "Revert"
                          refId <- primEditor (pure Nothing )
                          button <- primEditor (pure (Just ()))
                          traverseUI (traverse (ui . transaction inf . revertModification)) (facts (triding refId) <# triding button)
                          let pred = [(keyRef "user_name",Left (txt (username inf ),Equals)),(keyRef "schema_name",Left (txt $schemaName inf,Equals))] <> [(keyRef "table_name",Left (ArrayTB1 $ txt . tableName<$>  Non.fromList tables,Flip (AnyOp Equals)))]
                          dash <-  metaTable inf "modification_table"  pred
                          return  [label,getElement refId,getElement button ,dash]
                  "Clients" -> do
                      let pred = [(keyRef "schema",Left (schId,Equals) ) ] <>  [ (keyRef "table",Left (ArrayTB1 $ int. tableUnique<$>  Non.fromList tables,Flip (AnyOp Equals)))]
                      let pred = [(RelAccess [keyRef "selection"] $ keyRef "schema",Left (int (schemaId inf),Equals) )] <> [ (RelAccess ([keyRef "selection"] ) $ RelAccess ([keyRef "selection"] ) ( keyRef "table"),Left (ArrayTB1 $ txt . rawName <$>  Non.fromList (F.toList tables),IntersectOp)) ]
                      clients <- metaTable inf "clients" pred
                      return [clients]
                  "Exception" -> do
                      let pred = [(keyRef "schema",Left (schId,Equals) ) ] <>  [ (keyRef "table",Left (ArrayTB1 $ int . tableUnique<$>  Non.fromList tables,Flip (AnyOp Equals)))]
                      dash <- metaTable inf "plugin_exception" pred
                      return [dash]
                  i -> error (show i)
                           )) ((\i  -> fmap(i ,)) <$> triding metanav <*> fmap (nonEmpty. F.toList) (triding bset))
                element metabody # sink children (facts els)
                st <- once (buttonStyle,const True)
                return  $ TrivialWidget st metaDiv),
          ("Browser" ,do
            subels <- chooserTable  six  inf  bset cliTables (wId w)
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

authMap schemaN =
      case schemaN of
          "code" -> codeOps
          i ->
            -- conn <- connectPostgreSQL ("host=" <> BS.pack (host sargs) <> " port=" <> BS.pack (port sargs ) <>" user=" <> BS.pack user<> " password=" <> BS.pack pass <> " dbname=" <> BS.pack (dbn sargs) <> " " )
            -- execute_ conn "set bytea_output='hex'"
            postgresOps

loadSchema smvar schemaN user auth plugList =
  keyTables smvar (schemaN,user) auth plugList

databaseChooser cookies smvar metainf sargs plugList init = do
  let rCookie = T.pack . BS.unpack . cookieValue <$> L.find ((=="auth_cookie"). cookieName) cookies
  cookiesMap <- ui $ transactionNoLog metainf $  selectFrom "auth_cookies" Nothing Nothing [] mempty
  let loginCookie =  (\m -> (\ck -> decodeT .mapKey' keyValue . tableNonRef <$> G.lookup (G.Idex [TB1 $ SNumeric ck]) m) =<< readMay . T.unpack =<< rCookie )  <$> collectionTid cookiesMap
  userMap <- ui $ transactionNoLog metainf $  selectFrom "user" Nothing Nothing [] mempty
  cookieUser <- currentValue . facts $  (\l m -> traverse (\ck -> decodeT . mapKey' keyValue <$> G.lookup (G.Idex [TB1 $ SNumeric ck]) m) =<< l )  <$> loginCookie <*> collectionTid userMap
  liftIO $ print ("@@@@@@cookies",rCookie,cookieUser)
  (widT,widE) <- loginWidget (Just $ user sargs  ) (Just $ pass sargs )
  logOut <- UI.button # set UI.text "Log Out" # set UI.class_ "row"
  logOutE <- UI.click logOut
  load <- UI.button # set UI.text "Log In" # set UI.class_ "row"
  loadE <- UI.click load
  login <- UI.div # set children widE # set UI.class_ "row"
  authBox <- UI.div # set children [login ,load]   # set UI.class_ "col-xs-2"
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
    logIn (user,pass)= do
      -- liftIO  $ putStrLn "log in user " ++ T.unpack user
        [Only uid] <- liftIO $ query (rootconn metainf) "select oid from metadata.\"user\" where usename = ?" (Only user)
        cli <- liftIO   $ AuthCookie uid <$> randomIO <*> getCurrentTime
        runUI w . runFunction $ ffi "document.cookie = 'auth_cookie=%1'" (cookie cli)
        transaction metainf $ fullInsert (lookMeta (metainf) "auth_cookies") (liftTable' metainf "auth_cookies" $ encodeT cli)
        return (Just (flip User (T.pack user )<$> cli))
    invalidateCookie cli = do
        liftIO  $ putStrLn "Log out user"
        transaction metainf $ deleteFrom (lookMeta (metainf) "auth_cookies") (liftTable' metainf "auth_cookies" $ encodeT (fmap userId cli))
        return Nothing
    createSchema loggedUser e@(db,(schemaN,(sid,ty))) = do
        let auth = authMap
        liftIO  $ putStrLn "Creating new schema"
        case ty of
          "sql" -> do
            loadSchema smvar schemaN   loggedUser auth plugList
          "code" -> do
            loadSchema smvar schemaN  loggedUser auth plugList
    tryCreate = (\i -> maybe (const $ return []) (\i -> mapM (createSchema i)) i)

  loggedUser <- mdo
    newLogIn <- mapEventUI (\i -> ui $ join <$> traverse logIn i) (rumors formLogin)
    newLogOut <- mapEventUI (\i -> ui $ join <$> traverse invalidateCookie i) (facts loggedUser <@ logOutE)
    loggedUser <- ui $ accumT cookieUser  (unionWith (.) (const <$> newLogIn) (const <$> newLogOut) )
    return loggedUser
  element authBox # sink UI.style (noneShow . isNothing <$> facts loggedUser)
  element logOut # sink UI.style (noneShow . isJust <$> facts loggedUser)
  chooserT <- traverseUI ui $ tryCreate  <$> loggedUser   <*>dbsWT
  schemaSel <- UI.div  # set children [getElement dbsW] # sink UI.style (noneShow . isJust <$> facts loggedUser)
  return (chooserT,[schemaSel ,authBox,logOut ] )

createVar :: IO (TVar DatabaseSchema)
createVar = do
  args <- getArgs
  let db = argsToState args
  b <- lookupEnv "ROOT_SERVER"
  smvar   <- atomically $newTVar HM.empty
  conn <- connectPostgreSQL (connRoot db)
  l <- query_ conn "select oid,name from metadata.schema"
  atomically $ newTVar  (DatabaseSchema (M.fromList l) (isJust b) (HM.fromList $ swap <$> l) conn smvar)



withTable s m w =
  withInf [] s (\inf -> runDynamic $ do
    now <- liftIO getCurrentTime
    let pred = (WherePredicate $ lookAccess inf m <$> w)
        -- pred = WherePredicate $ lookAccess inf m <$>(AndColl [OrColl [PrimColl (IProd Nothing "scheduled_date",Left (IntervalTB1 (I.interval (I.Finite (TB1 (STime (SDate (utctDay now) ))),True) (I.Finite (TB1 (STime (SDate (utctDay (addUTCTime (3600*24*35) now))))),True)),Flip Contains))]])
        table = lookTable inf m
    db <- transactionNoLog  inf $ selectFrom m Nothing Nothing [] pred
    i2 <- currentValue (facts $ collectionTid db)
    addClientLogin inf
    let
      debug i = show <$> G.toList i
      -- debug2 i = show <$> G.projectIndex w i
    liftIO $ putStrLn (unlines $ debug i2)
    -- liftIO $ putStrLn (unlines $ debug2 i2)
               )

testCreate = withInf [] "metadata"
 (\inf -> liftIO $ createFresh "tables" inf "geo" (Primitive [KOptional] (RecordPrim ("metadata","geo"))))

withInf plugs s v  = do
  args <- getArgs
  let db = argsToState args
  smvar <- createVar
  let
    amap = authMap
  (inf,fin) <- runDynamic $ keyTables smvar  (s,postgresUser) amap plugs
  v inf


testPlugin s t p  = do
  args <- getArgs
  let db = argsToState args
  smvar <- createVar
  let
    amap = authMap
  (inf,fin) <- runDynamic $ keyTables smvar  (s,postgresUser ) amap []
  let (i,o) = pluginStatic p
  print $ liftAccessU inf t i
  print $ liftAccessU inf t o

postgresUser = unsafePerformIO $ do
    rnd <- randomIO
    now <-getCurrentTime
    return $ AuthCookie (User 10 "postgres")  rnd now

testCalls = testWidget (do
  setCallBufferMode BufferAll
  i <- runFunction (ffi "var a= 1")
  i <- callFunction (ffi "2")
  j <- callFunction (ffi "1")
  UI.div # set text (show (i + j :: Int))
                       )
