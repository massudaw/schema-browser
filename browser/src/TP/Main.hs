{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module TP.Main where

import TP.Selector
import TP.Extensions
import Control.Exception
import ClientAccess
import Debug.Trace
import Query
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
import qualified Data.Sequence.NonEmpty as NonS
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
    
    menu <- checkedWidget (pure True)
    element menu # set UI.class_ "col-xs-05"
    body <- UI.div# set UI.class_ "row"
    ui $ addSchemaIO (fromIntegral $ wId w) metainf inf six
    metadataNav <- sequenceA $  M.fromList
               [("Map",fmap (^._2) <$>mapWidgetMeta inf)
               ,("Chart",fmap (^._2) <$> chartWidgetMetadata inf)
               ,("Task",fmap (^._2) <$> ui (taskWidgetMeta inf))
               ,("Account",fmap (^._2) <$> ui (accountWidgetMeta inf))
               ,("Agenda",fmap (^._2) <$> eventWidgetMeta inf )]
    let checkNav i =  maybe True (\i -> isJust .nonEmpty $ i) $ M.lookup i  metadataNav
    nav  <- buttonDivSet  (filter checkNav ["Browser","Map","Account","Task", "Agenda","Chart","Metadata"] ) (pure  Nothing) (\i ->
        UI.button # set UI.text i # set UI.class_ "buttonSet btn-xs btn-default pull-right" )
    element nav # set UI.class_ "col-xs-2 pull-right"
    chooserDiv <- UI.div
        # set children  [getElement nav ]
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
        kitems = filter (not . L.null . rawPK ) . concatMap F.toList $ F.toList (tableMap inf)
        schId = int $ schemaId inf
        initKey = pure (maybeToList $ (\s -> if schemaName inf == T.pack s then lookTable inf . T.pack<$> iniTable   else Nothing) =<< iniSchema )
        buttonStyle lookDesc k e = Just <$> do
          label <- UI.div # set UI.text (T.unpack $ lookDesc ) # set UI.class_ "fixed-label col-xs-11"
          element e # set UI.class_ "col-xs-1"
          UI.label # set children [e , label] # set UI.class_ "btn btn-default table-list-item" # set UI.style [("padding","1px"),("display","-webkit-box")]

      bset <- tableChooser inf  kitems (fst <$> triding tfilter ) (snd <$> triding tfilter) initKey
      posSel <- positionSel
      (sidebar,calendarT) <- calendarSelector (pure Nothing)
      tbChooser <- UI.div
          # set UI.class_ "col-xs-2"
          # set UI.style ([("height","92vh"),("overflow-y","hidden")] ++ borderSchema inf)
          # set children [sidebar,posSel ^._1,getElement bset]
          # sink0 UI.style (facts $ noneShow <$> triding menu)
      let cliTables = (join . fmap (flip atMay six) <$> cliTid)
      iniCliTable <- currentValue (facts cliTables)
      ui $ accumDiffCounterIni (maybe 0 (length .table_selection)  iniCliTable) (\ix table->  trackTable (meta inf) (wId w) table six ix) (triding bset)
      tfilter <-  switchManyUI  (triding nav) (M.fromList
          [("Map",do
            (m,widget) <-  configExtension inf mapDef (mapWidget calendarT posSel (triding bset) inf)
            st <- once (fmap (flip elem . fmap (^._2)) m)
            return $ TrivialWidget  st widget),
          ("Agenda" ,do
            cliZone <- jsTimeZone
            ((l,t),widget) <-  configExtension inf agendaDefS (eventWidget calendarT (triding bset) inf cliZone)
            let st = (flip elem . fmap (^._2)) <$>  t
            return $ TrivialWidget (liftA2 (,) l st) widget),
          ("Chart" ,do
            cliZone <- jsTimeZone
            (m,widget) <-  configExtension inf chartDef (chartWidget calendarT posSel (triding bset) inf cliZone)
            st <- once (fmap (flip elem . fmap (^._2)) m)
            return $ TrivialWidget st widget),
          ("Account" ,do
            (m,widget) <-  configExtension inf accountDef (accountWidget calendarT (triding bset) inf)
            st <- once (fmap (flip elem . fmap (^._2)) m)
            return $ TrivialWidget st widget),
          ("Task" ,do
            (m,widget) <-  configExtension inf taskDef (taskWidget calendarT (triding bset) inf)
            st <- once (fmap (flip elem . fmap (^._2)) m)
            return $ TrivialWidget st widget),
          ("Metadata" ,do
            let
              metaOpts = ["Change","Exception","Polling","Clients"]
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
                    let pred = [(keyRef "user_name",Left (txt (username inf ),Equals)),(keyRef "schema_name",Left (txt $schemaName inf,Equals))] <> [(keyRef "table_name",Left (ArrayTB1 $ txt . tableName<$>  NonS.fromList tables,Flip (AnyOp Equals)))]
                    dash <-  metaTable inf "modification_table"  pred
                    return  [label,getElement refId,getElement button ,dash]
              "Clients" -> do
                let pred = [(keyRef "schema",Left (schId,Equals) ) ] <>  [ (keyRef "table",Left (ArrayTB1 $ int. tableUnique<$>  NonS.fromList tables,Flip (AnyOp Equals)))]
                let pred = [(RelAccess (keyRef "selection") $ keyRef "schema",Left (int (schemaId inf),Equals) )] <> [ (RelAccess (keyRef "selection" ) $ RelAccess (keyRef "selection") ( keyRef "table"),Left (ArrayTB1 $ txt . rawName <$>  NonS.fromList (F.toList tables),IntersectOp)) ]
                clients <- metaTable inf "clients" pred
                return [clients]
              "Exception" -> do
                let pred = [(keyRef "schema",Left (schId,Equals) ) ] <>  [ (keyRef "table",Left (ArrayTB1 $ int . tableUnique<$>  NonS.fromList tables,Flip (AnyOp Equals)))]
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
      bd <- UI.div # set children [(getElement tfilter)] # set UI.style ([("height","92vh"),("overflow-y","auto")] ++ borderSchema inf)
                       # sink0 UI.class_ (facts $ expand <$> triding menu)
      element body # set children [tbChooser,bd]
      return tfilter
    return (getElement menu,container) ))  (S.fromList <$> evDB)
  (edbl,hdbl) <- ui newEvent

  headers <- ui $ accumDiff (\inf -> runUI w $ do
    h <- UI.h3 # set text (T.unpack $ schemaName inf) # set UI.class_ "col-xs-9 header"
    ch <- UI.click h
    onEvent ch $ (\_ -> liftIO $ hdbl True)
    return h ) (S.fromList <$> evDB)
  let
    style True = UI.span # set UI.class_ "glyphicon glyphicon-collapse-up"
    style False = UI.span # set UI.class_ "glyphicon glyphicon-expand"
  header <- UI.div  # set  children chooserItens # set UI.class_ "col-xs-11"
  merged <- ui $ accumDiffMapCounter (\ix (k,(i,(m,j))) -> runUI w $ UI.div # set children [m,i,j])   (M.intersectionWith (,) <$>  headers <*>  selschemas)
  (layouth,top) <- layoutSel' onShiftAlt  merged
  element layouth
    # set UI.class_ "col-xs-1"
  schemaH <- UI.div
      # set children [layouth,header]
  addBody [schemaH,top]



listDBS ::  InformationSchema -> Tidings (Maybe Int) -> Text -> Dynamic (Tidings (M.Map Text (Int,Text)))
listDBS metainf userId db = do
  dbvar <- transactionNoLog metainf $  selectFrom "schema2" Nothing mempty
  privileges <- transactionNoLog metainf (selectFrom "catalog_schema_privileges"  Nothing mempty)
  let
    schemas schemasTB =  M.fromList $  liftA2 (,) sname  (liftA2 (,) sid stype) <$> F.toList  schemasTB
      where
        sname = untxt . lookAttr' "name"
        stype = untxt . lookAttr' "type"
        sid = unint . lookAttr' "oid"
        unint (TB1 (SNumeric s))= s
        untxt (TB1 (SText s))= s
        untxt (LeftTB1 (Just (TB1 (SText s))))= s
  return ((\i j u-> maybe M.empty (\u -> M.filterWithKey (\k v -> isJust $ G.lookup (Idex [int u,int (fst v)]) (primary j)) (schemas $primary i) ) u )  <$> collectionTid dbvar <*> collectionTid privileges <*> userId)

loginWidget userI passI =  do
    usernamel <- flabel # set UI.text "Usuário"
    username <- UI.input
        # set UI.name "username"
        # set UI.class_ "form-control"
        # set UI.style [("width","142px")]
        # set UI.value (Data.Maybe.fromMaybe "" userI)
    passwordl <- flabel # set UI.text "Senha"
    password <- UI.input
        # set UI.name "password"
        # set UI.class_ "form-control"
        # set UI.style [("width","142px")]
        # set UI.type_ "password" 
    usernameE <- fmap nonEmpty  <$> UI.valueChange username
    passwordE <- fmap nonEmpty <$> UI.valueChange password

    userDiv <- UI.div # set children [usernamel,username] # set UI.class_  "col-xs-12"
    passDiv <- UI.div # set children [passwordl,password] # set UI.class_  "col-xs-12"
    usernameT <- ui $ stepperT userI usernameE
    passwordT <- ui $ stepperT passI passwordE
    return (liftA2 (liftA2 (,)) usernameT passwordT ,[userDiv,passDiv])

form :: Tidings a -> Event b -> Tidings a
form td ev =  tidings (facts td ) (facts td <@ ev )

authMap schemaN =
  case schemaN of
      "code" -> codeOps
      i -> postgresOps

loadSchema smvar schemaN user auth =
  keyTables smvar (schemaN,user) auth

databaseChooser cookies smvar metainf sargs plugList init = do
  let rCookie = T.pack . BS.unpack . cookieValue <$> L.find ((=="auth_cookie"). cookieName) cookies
  cookiesMap <- ui $ transactionNoLog metainf $  selectFrom "auth_cookies" Nothing mempty
  let loginCookie = (\m -> (\ck -> (\i -> traceShow (ck,i,G.keys (primary m)) i ) $ decodeT .mapKey' keyValue <$> G.lookup (Idex [TB1 $ SNumeric ck]) (primary m)) =<< readMay . T.unpack =<< rCookie )  <$> collectionTid cookiesMap
      -- userMap <- ui $ transactionNoLog metainf $  selectFrom "user" Nothing Nothing [] mempty
  cookieUser <- currentValue . facts $  loginCookie
  (widT,widE) <- loginWidget (Just $ user sargs  ) Nothing 
  logInB <- UI.button # set UI.text "Log In" # set  UI.class_ "btn btn-primary"
  loadE <- UI.click logInB
  login <- UI.div # set children widE # set UI.class_ "row"
  authBox <- UI.div # set children [login ,logInB]
  orddb  <- ui $ transactionNoLog metainf (selectFromTable "schema_ordering"  Nothing mempty )
  let
    ordRow map orderMap inf =  do
        schId <- M.lookup inf map
        let pk = idex metainf "schema_ordering" [("schema",int $ fst schId  )]
        row <- G.lookup pk (primary orderMap)
        return $ lookAttr' "usage" row

    formLogin = form widT loadE
    db = T.pack $ dbn sargs
    buttonString k = do
      b <- UI.input # set UI.type_ "checkbox"
      chkE <- UI.checkedChange b
      return (b,chkE)

  let
    schemaStyle i o = do
      check <- element o # set UI.style [("margin-top","2px")]
      l <- UI.span
        # set text (T.unpack  i)
        # set UI.class_ "btn btn-default"
        # set UI.style [("padding","2px")]
      UI.label
        # set children [check,l]
        # set UI.class_ "btn btn-warning"
        # set UI.style [("padding","1px"),("display","flex"),("flex-flow","row")]

  w <- askWindow
  metainf <- liftIO $ metaInf smvar
  let
    logIn (user',pass')= do
        let connection = (connRoot (sargs {user = user' , pass = pass' }))
        o <- liftIO $ (print connection  >> Just <$> connectPostgreSQL connection )   `catch` (\e -> liftIO ( print  ("Falied login: " <> show ( e :: SomeException )) >> return Nothing ))
        fmap join $ traverse (\_ ->   do
          [Only uid] <- liftIO $ query (rootconn metainf) "select oid from metadata.\"user\" where usename = ?" (Only user')
          cli <- liftIO $ AuthCookie (User uid (T.pack user')) <$> randomIO <*> getCurrentTime
          runUI w . runFunction $ ffi "document.cookie = 'auth_cookie=%1'" (cookie cli)
          transaction metainf $ fullInsert (lookMeta (metainf) "auth_cookies") (liftTable' metainf "auth_cookies" $ encodeT cli)
          return (Just cli) )  o
    invalidateCookie cli = do
        transaction metainf $ deleteFrom (lookMeta (metainf) "auth_cookies") (liftTable' metainf "auth_cookies" $ encodeT cli)
        return Nothing
    createSchema user e@(db,(schemaN,(sid,ty))) = do
        case ty of
          "sql" -> do
            loadSchema smvar schemaN user authMap
          "code" -> do
            loadSchema smvar schemaN user authMap
    tryCreate = (\i -> maybe (const $ return []) (\i -> mapM (createSchema i)) i)

  logOutB <- UI.button # set UI.class_ "col-xs-6" # set UI.text "Log Out" # set UI.class_ "btn btn-primary"
  logOutE <- UI.click logOutB

  loggedUser <- ui $ mdo
    newLogIn <- mapEventDyn (fmap join . traverse logIn) (rumors formLogin)
    newLogOut <- mapEventDyn (fmap join . traverse invalidateCookie) (facts user <@ logOutE)
    user <- accumT cookieUser  (unionWith (.) (const <$> newLogIn) (const <$> newLogOut) )
    return user

  dbs <- ui $ listDBS metainf  (fmap (userId .client) <$>  loggedUser) db
  dbsWPre <- checkDivSetTGen'
              (M.keys <$> dbs)
              (ordRow <$> dbs <*> collectionTid orddb)
              (S.fromList <$> init )
              buttonString
              (pure (schemaStyle))
  let dbsW = TrivialWidget ((\i j ->  catMaybes $(\k ->  (db, ) . (k,)<$> M.lookup k j )<$> i ) <$> (S.toList <$> triding dbsWPre) <*> dbs) (getElement dbsWPre)
  cc <- currentValue (facts $ triding dbsW)
  let dbsWE = rumors $ triding dbsW
  dbsWT <-  ui $stepperT cc dbsWE

  loggedUserD <- UI.div # set UI.class_ "col-xs-6" # sink text (maybe "" (T.unpack . userName . client) <$> facts loggedUser )
  loggedBox <- UI.div #  set children [loggedUserD,logOutB] # set UI.class_ "col-xs-2"
  element authBox # sink UI.style (noneShow . isNothing <$> facts loggedUser)
  chooserT <- traverseUI ui $ tryCreate  <$> loggedUser   <*>dbsWT
  element dbsW
      # set UI.class_ "col-xs-10"
      # set UI.style [("display","flex"),("flex-flow","row wrap")]
  schemaSel <- UI.div
      # set children [getElement dbsW, loggedBox]
      # set UI.class_ "col-xs-12"
      # sink UI.style (noneShow . isJust <$> facts loggedUser)
  return (chooserT,[schemaSel ,authBox])

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
  withInf  s (\inf -> runDynamic $ do
    now <- liftIO getCurrentTime
    let pred = WherePredicate $ lookAccess inf m <$> w
        table = lookTable inf m
    db <- transactionNoLog  inf $ selectFrom m Nothing pred
    i2 <- currentValue (facts $ collectionTid db)
    let
      debug i =  ( (show  <$> M.toList (secondary i)))
    liftIO $ putStrLn (unlines  $ fmap (\i -> show $ G.getIndex (tableMeta table) i ) $ (F.toList $ primary i2))
    return ()
               )


testPartialLoading s t = do
  withInf  s (\inf -> runDynamic $ do
    let desc = recPKDescIndex inf (tableMeta table)  all
        pk = recPK inf (tableMeta table)  all
        all = allRec' (tableMap inf) table
        table  = lookTable inf t
    liftIO $print ("Load desc" ,desc)
    transactionNoLog  inf $ selectFromProj t Nothing mempty desc
    liftIO $print ("Load pk" ,pk)
    transactionNoLog  inf $ selectFromProj t Nothing mempty pk
    liftIO $ print ("Load all" ,all)
    transactionNoLog  inf $ selectFromProj t Nothing mempty all
    liftIO $print ("Load pk" ,pk)
    transactionNoLog  inf $ selectFromProj t Nothing mempty pk
               )

testCreate = withInf  "metadata"
 (\inf -> liftIO $ createFresh "tables" inf "geo" (Primitive [KOptional] (RecordPrim ("metadata","geo"))))


testPlugin s t p  = do
  args <- getArgs
  let db = argsToState args
  smvar <- createVar
  let
    amap = authMap
  (inf,fin) <- runDynamic $ keyTables smvar  (s,postgresUser ) amap
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

withInf s v  = do
  args <- getArgs
  let db = argsToState args
  smvar <- createVar
  let
    amap = authMap
  (inf,fin) <- runDynamic $ keyTables smvar  ("metadata",postgresUser) amap
  (inf,fin) <- runDynamic $ keyTables smvar  ("code",postgresUser) amap
  (inf,fin) <- runDynamic $ keyTables smvar  (s,postgresUser) amap
  v inf


