{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module TP.Main where

import TP.Selector
import Data.Unique
import Plugins.Schema (codeOps)
import Control.Exception
import qualified Data.Binary as B
import Postgresql.Backend (connRoot)
import System.Process
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
import Postgresql.Backend (postgresOps)
import Prelude hiding (head)
import TP.QueryWidgets
import Control.Monad.Reader
import Control.Concurrent
import System.Environment
import Network.Google.OAuth2 (OAuth2Tokens(..))
import Data.Ord
import Utils
import Schema
import Types.Patch
import Data.Maybe
import Reactive.Threepenny hiding(apply)
import qualified Data.List as L
import qualified Data.ByteString.Char8 as BS

import RuntimeTypes
import OAuthClient
import qualified Graphics.UI.Threepenny as UI
import Graphics.UI.Threepenny.Core hiding (get,delete,apply)
import Graphics.UI.Threepenny.Internal (wId)
import Data.Monoid hiding (Product(..))

import qualified Data.Foldable as F
import qualified Data.Text as T
import Data.Text (Text)
import qualified Data.Set as S

import Database.PostgreSQL.Simple
import qualified Data.Map as M
import qualified Data.HashMap.Strict as HM

import OAuth
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
  let amap = authMap smvar bstate (user bstate , pass bstate)
  inf <- ui $ fmap (justError ("no schema" <> show (schema bstate))) $ traverse (\i -> loadSchema smvar (T.pack i)  (user bstate)  amap plugList) $ schema  bstate
  (cli,cliTid) <- ui $ addClient (fromIntegral $ wId w) metainf inf ((\t -> lookTable inf . T.pack $ t) <$> tablename bstate  ) (rowpk bstate)
  (evDB,chooserItens) <- databaseChooser smvar metainf bstate plugList
  body <- UI.div# set UI.class_ "row"
  return w # set title (host bstate <> " - " <>  dbn bstate)


  menu <- checkedWidget (pure True)
  cliZone <- jsTimeZone
  metadataNav <- mapUIFinalizerT body (traverse
        (\inf -> sequenceA $ (M.fromList [("Map",fmap (^._2) <$>mapWidgetMeta inf)
                             ,("Chart",fmap (^._2) <$> chartWidgetMetadata inf )
                             ,("Account",fmap (^._2) <$> accountWidgetMeta inf )
                             ,("Agenda",fmap (^._2) <$> eventWidgetMeta inf cliZone)
                                         ]))) evDB
  element menu # set UI.class_ "col-xs-1"
  nav  <- buttonDivSet  ["Map","Account","Agenda","Chart","Browser","Metadata"] (pure $ args `atMay` 6  )(\i -> do
    UI.button # set UI.text i # set UI.class_ "buttonSet btn-xs btn-default pull-right" # sink  UI.style (noneShow . (maybe True (\i -> isJust .nonEmpty $ i).join . fmap (M.lookup i) ) <$> facts metadataNav ))
  element nav # set UI.class_ "col-xs-5 pull-right"
  chooserDiv <- UI.div
      # set children  ([getElement menu] <> chooserItens <> [getElement nav ])
      # set UI.style [("align-items","flex-end")]
      # set UI.class_ "row"
      # sink0 UI.style (([("align-items","flex-end")] ++ ). maybe [] borderSchema <$> facts evDB)
  container <- UI.div
      # set children [chooserDiv , body]
      # set UI.class_ "container-fluid"

  element body # sink0 UI.style (([("align-items","flex-end")] ++ ). maybe [] borderSchema <$> facts evDB)
  let
    expand True = "col-xs-10"
    expand False = "col-xs-12"
  addBody  [return container]
  mapUIFinalizerT body (traverse (\inf-> mdo
    let
      kitems = F.toList (pkMap inf)
      schId = int $ schemaId inf
      initKey = maybe [] (catMaybes.F.toList)  . (\iv -> fmap (\t -> HM.lookup t (_tableMapL inf))  <$> join (lookT <$> iv)) <$> cliTid
      lookT iv = let  i = indexFieldRec (liftAccess metainf "clients" $ Nested [keyRef "selection"] (pure $ keyRef "table")) iv
                 in fmap (\(TB1 (SText t)) -> t) . traceShowId .unArray  <$> join (fmap unSOptional' i)

    cliIni <- currentValue (facts cliTid)
    iniKey <-currentValue (facts initKey)
    liftIO$ print ("iniKey",iniKey,cliIni)
    let
      buttonStyle lookDesc k e= do
         let tableK = k
         label <- UI.div # sink0 UI.text (fmap T.unpack $ facts $ lookDesc  <*> pure k)  # set UI.class_ "fixed-label col-xs-11"
         state <- element e  # set UI.class_ "col-xs-1"
         UI.div # set children[state, label] # set  UI.class_ "col-xs-12"

    bset <- tableChooser inf  kitems (fst <$> tfilter ) (snd <$> tfilter)  ((schemaName inf)) (snd (username inf)) (pure iniKey)

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
        # set UI.style ([("height","90vh"),("overflow","hidden")] ++ borderSchema inf)
    tfilter <-  mapUIFinalizerT bd (\nav-> do
      bdo <- UI.div
      element bd # set children [bdo]
      case nav of
        "Map" -> do
          element bdo  # set UI.style [("width","100%")]
          fmap ((\i j -> elem j i) . fmap (^._2)) <$> mapWidget bdo calendarT posSel (triding bset) inf
        "Agenda" -> do
          element bdo  # set UI.style [("width","100%")]
          cliZone <- jsTimeZone
          fmap ((\i j -> elem j i) . fmap (^._2)) <$>  eventWidget bdo calendarT (triding bset) inf cliZone
        "Chart" -> do
          element bdo  # set UI.style [("width","100%")]
          cliZone <- jsTimeZone
          fmap ((\i j -> elem j i) . fmap (^._2)) <$>  chartWidget bdo calendarT posSel (triding bset) inf cliZone
        "Account" -> do
          element bdo  # set UI.style [("width","100%")]
          fmap ((\i j -> elem j i) . fmap (^._2)) <$> accountWidget bdo calendarT (triding bset) inf
        "Metadata" -> do
              let metaOpts = ["Poll","Stats","Change","Exception"]
                  iniOpts = join $ fmap (\i -> if elem i metaOpts then Just i else Nothing)$  args `atMay`  7
                  displayOpts  i =  UI.button # set UI.text i # set UI.class_ "buttonSet btn-xs btn-default pull-right"
              metanav <- buttonDivSet metaOpts (pure iniOpts) displayOpts
              element metanav # set UI.class_ "col-xs-5 pull-right"
              metabody <- UI.div # set UI.class_ "col-xs-10"
              element bdo # set children [getElement metanav,metabody] # set UI.class_ "row" # set UI.style [("display","block")]
              mapUIFinalizerT metabody (\(nav,tables)-> case nav  of
                "Poll" -> do
                    els <- sequence      [ metaAllTableIndexA inf "polling" [(keyRef "schema",Left (schId,Equals) ) ]
                          , metaAllTableIndexA inf "polling_log" [(keyRef "schema",Left (schId,Equals) ) ]]
                    element metabody #
                      set children els
                "Change" -> do
                    case schemaName inf of
                      {-"gmail" -> do
                        b <- UI.button # set text "sync"
                        (dbvar,(m,t))  <- ui $ transactionNoLog inf $ selectFrom "history" Nothing Nothing []  mempty
                        itemListEl <- UI.select # set UI.class_ "col-xs-9" # set UI.style [("width","70%"),("height","350px")] # set UI.size "20"
                        itemListEl2 <- UI.select # set UI.class_ "col-xs-9" # set UI.style [("width","70%"),("height","350px")] # set UI.size "20"
                        do
                          (ref,res) <- ui $ transactionNoLog inf $ syncFrom (lookTable inf "history") Nothing Nothing [] mempty
                          listBoxEl itemListEl2 ( G.toList <$> collectionTid ref)  (pure Nothing) (pure id) ( pure attrLine ) element metabody # set children [itemListEl,itemListEl2]-}
                      i -> do
                        let pred = [(keyRef "schema_name",Left (txt $schemaName inf,Equals) ) ] <> if M.null tables then [] else [ (keyRef "table_name",Left (ArrayTB1 $ txt . tableName<$>  Non.fromList (concat (F.toList tables)),Flip (AnyOp Equals)))]
                        dash <- metaAllTableIndexA inf "modification_table" pred
                        element metabody # set UI.children [dash]
                "Stats" -> do
                    let pred = [(keyRef "schema",Left (schId,Equals) ) ] <> if M.null tables then [] else [ (keyRef "table",Left (ArrayTB1 $ int. tableUnique<$>  Non.fromList (concat (F.toList tables)),Flip (AnyOp Equals)))]
                    stats_load <- metaAllTableIndexA inf "stat_load_table" pred
                    stats <- metaAllTableIndexA inf "table_stats" pred
                    clients <- metaAllTableIndexA inf "clients"$  [(keyRef "schema",Left (int (schemaId inf),Equals) )]-- <> if M.null tables then [] else [ (Nested (keyRef ["selection"] ) (Many [ keyRef ["table"]]),Left (ArrayTB1 $ txt . rawName <$>  Non.fromList (concat (F.toList tables)),Flip (AnyOp Equals)) )]
                    element metabody # set UI.children [stats,stats_load,clients]
                "Exception" -> do
                    let pred = [(keyRef "schema",Left (schId,Equals) ) ] <> if M.null tables then [] else [ (keyRef "table",Left (ArrayTB1 $ int . tableUnique<$>  Non.fromList (concat (F.toList tables)),Flip (AnyOp Equals)))]
                    dash <- metaAllTableIndexA inf "plugin_exception" pred
                    element metabody # set UI.children [dash]
                i -> errorWithStackTrace (show i)
                    ) ((,) <$> triding metanav <*> triding bset)
              return bdo
              return  (buttonStyle,const True)
        "Browser" -> do
              subels <- chooserTable  inf  bset cliTid  cli
              element bdo  # set children  subels # set UI.style [("height","90vh"),("overflow","auto")]
              return  (buttonStyle, const True  )
        i -> errorWithStackTrace (show i)
         )  (triding nav)
    return tfilter
      ) )  evDB
  element body


listDBS ::  InformationSchema -> Text -> Dynamic (Tidings [(Text,Text)])
listDBS metainf db = do
  (dbvar ,_) <- transactionNoLog metainf $  selectFrom "schema2" Nothing Nothing [] mempty
  let
    schemas schemasTB =  liftA2 (,) sname  stype <$> F.toList  schemasTB
      where
        sname = untxt . lookAttr' metainf "name"
        stype = untxt . lookAttr' metainf "type"
        untxt (Attr _ (TB1 (SText s)))= s
        untxt (Attr _ ((LeftTB1 (Just (TB1 (SText s))))))= s
  return (schemas  <$> collectionTid dbvar)

loginWidget userI passI =  do
  usernamel <- flabel # set UI.text "Usuário"
  username <- UI.input # set UI.name "username" # set UI.style [("width","142px")] # set UI.value (maybe "" id userI)
  passwordl <- flabel # set UI.text "Senha"
  password <- UI.input # set UI.name "password" # set UI.style [("width","142px")] # set UI.type_ "password" # set UI.value (maybe "" id passI)
  usernameE <- fmap nonEmpty  <$> UI.valueChange username
  passwordE <- fmap nonEmpty <$> UI.valueChange password

  userDiv <- UI.div # set children [usernamel,username] # set UI.class_  "col-xs-5"
  passDiv <- UI.div # set children [passwordl,password] # set UI.class_  "col-xs-5"
  usernameB <- ui $ stepper userI usernameE
  passwordB <-  ui $stepper passI passwordE
  let usernameT = tidings usernameB usernameE
      passwordT = tidings passwordB passwordE
  return $ ((liftA2 (liftA2 (,)) usernameT passwordT) ,[userDiv,passDiv])




form :: Tidings a -> Event b -> Tidings a
form td ev =  tidings (facts td ) (facts td <@ ev )


authMap smvar sargs (user,pass) schemaN =
      case schemaN of
          "code" -> return (NoAuth , codeOps)
          "gmail" ->  oauth False
          "tasks" ->  oauth True
          i ->  do
            conn <- connectPostgreSQL ("host=" <> (BS.pack $ host sargs) <> " port=" <> BS.pack (port sargs ) <>" user=" <> BS.pack (user )<> " password=" <> BS.pack (pass ) <> " dbname=" <> (BS.pack $  dbn sargs) <> " " )
            execute_ conn "set bytea_output='hex'"
            return (PostAuth conn, postgresOps)
    where oauth tag = do
              user <- justError "no google user" <$> lookupEnv "GOOGLE_USER"
              metainf <- metaInf smvar
              ((dbmeta ,_),_) <- runDynamic $ transactionNoLog metainf $ selectFromTable "google_auth" Nothing Nothing [] [(keyRef "username",Left ((txt  $ T.pack user ),Equals) )]
              let
                  td :: Tidings (OAuth2Tokens)
                  td = (\o -> let
                            token = justError "" . fmap (toOAuth . unTB1 . _fkttable . unTB) $ L.find ((==["token"]). fmap (keyValue._relOrigin) . keyattr )  $ F.toList (unKV $ snd $ head o )
                            in token) . G.toList <$> collectionTid dbmeta
                  toOAuth v = case transToken v of
                                Just a -> a
                                i -> errorWithStackTrace ("wrong token" <> show i)


              return (OAuthAuth (Just (if tag then "@me" else T.pack user,td )), gmailOps)

loadSchema smvar schemaN user authMap  plugList =  do
    keyTables smvar (schemaN,T.pack $ user) authMap plugList

databaseChooser smvar metainf sargs plugList = do
  let db = T.pack $ dbn sargs
  dbs <- ui $ listDBS  metainf  db
  dbsWPre <- listBox
      ((\j ->  fst <$> j) <$> dbs)
      (pure $ fmap T.pack $ schema sargs)
      (pure id)
      (pure (line . T.unpack ))
  let dbsW = TrivialWidget ((\i j ->  join $ (\k -> (db, ) <$> L.find ((==k).fst) j) <$> i ) <$> triding dbsWPre <*> dbs) (getElement dbsWPre)
  cc <- currentValue (facts $ triding dbsW)
  let dbsWE = rumors $ triding dbsW
  dbsWB <-  ui $stepper cc dbsWE
  let dbsWT  = tidings dbsWB dbsWE
  (schemaE,schemaH) <- ui newEvent
  metainf <- liftIO $ metaInf smvar
  let
    genSchema (db,(schemaN,ty))
        = case ty of
          "rest" -> do
              userEnv <- liftIO$ lookupEnv "GOOGLE_USER"
              liftIO $ print userEnv
              usernamel <- flabel # set UI.text "Usuário"
              username <- UI.input # set UI.name "username" # set UI.style [("width","142px")] # set value (fromMaybe "" userEnv)
              usernameE <-  fmap nonEmpty  <$> UI.valueChange username

              usernameB <-  ui $stepper userEnv usernameE

              load <- UI.button # set UI.text "Log In" # set UI.class_ "col-xs-4" # sink UI.enabled (facts (isJust <$> dbsWT) )
              loadE <- UI.click load
              ui $ onEventDyn (usernameB <@ loadE )( traverse (\ v ->do
                let auth = authMap smvar sargs (user sargs ,pass sargs )
                inf <- loadSchema smvar schemaN  (user sargs)  auth plugList
                liftIO$schemaH $ Just inf))
              user <- UI.div # set children [usernamel,username] # set UI.class_ "col-xs-8"
              UI.div # set children [user ,load]
          "sql" -> do
            (widT,widE) <- loginWidget (Just $ user sargs  ) (Just $ pass sargs )
            load <- UI.button # set UI.text "Log In" # set UI.class_ "col-xs-2" # sink UI.enabled (facts (isJust <$> dbsWT) )
            loadE <- UI.click load
            let login =   widT
                formLogin = form login  loadE
            ui$ mapTEventDyn
              (traverse (\(user,pass)-> do
                let auth = authMap smvar sargs (user,pass)
                inf <- loadSchema smvar schemaN  user auth plugList
                liftIO$schemaH $ Just inf
                ))(formLogin)

            UI.div # set children (widE <> [load])
          "code" -> do
            UI.div

  element dbsW # set UI.style [("height" ,"26px"),("width","140px")]
  genS <- mapUIFinalizerT (getElement dbsW) (traverse genSchema) dbsWT
  authBox <- UI.div # sink children (maybeToList <$> facts genS) # set UI.class_ "col-xs-4"
  let auth = authMap smvar sargs (user sargs ,pass sargs )
  inf <- ui $traverse (\i -> loadSchema smvar (T.pack i ) (user sargs) auth plugList ) (schema sargs)
  chooserB  <- ui $ stepper inf schemaE
  let chooserT = tidings chooserB schemaE
  element authBox  # sink UI.style (facts $ (\a b -> noneShow $  fromMaybe True $  liftA2 (\(db,(sc,ty)) (csch) -> if sc == (schemaName csch )then False else True ) a b )<$>    dbsWT <*> chooserT )
  schemaSel <- UI.div # set UI.class_ "col-xs-2" # set children [getElement dbsW]
  return $ (chooserT,[schemaSel ]<>  [authBox] )

createVar :: IO (TVar DatabaseSchema)
createVar = do
  args <- getArgs
  let db = argsToState args
  b <- lookupEnv "ROOT_SERVER"
  smvar   <- atomically $newTVar HM.empty
  conn <- connectPostgreSQL (connRoot db)
  l <- query_ conn "select oid,name from metadata.schema"
  atomically $ newTVar  ( DatabaseSchema (M.fromList l) (isJust b) (HM.fromList $ swap <$> l) conn smvar)

{-
testBinary = do
  args <- getArgs
  let db = argsToState args
  smvar <- createVar
  let
    amap = authMap smvar db ("postgres", "queijo")
  (meta,finm) <- runDynamic $ keyTables smvar  ("metadata","postgres") amap []
  let
    amap = authMap smvar db ("wesley.massuda@gmail.com", "queijo")
  (inf,fing) <- runDynamic $ keyTables smvar  ("gmail","wesley.massuda@gmail.com") amap []
  let start = "7629481"
  let t = lookTable inf "messages"
  ((i,(_,s)),_) <- runDynamic $ transactionNoLog inf $ selectFrom (tableName t) Nothing Nothing [] mempty
  runDynamic $ mapM (\p -> transactionNoLog inf $ putPatch (patchVar (iniRef i)).  maybeToList =<<  getFrom t p) (L.take 4  $ G.toList s)
  writeTable inf "dump_test/gmail"  (lookTable inf "messages") (iniRef i)
  writeTable inf "dump_test/gmail"  (lookTable inf "labels") (iniRef i)
  writeTable inf "dump_test/gmail"  (lookTable inf "attachments") (iniRef i)
  (t,l) <- runDynamic $ readTable inf "dump_test" "gmail" (lookTable inf "messages")
  s <- atomically $ readTVar (collectionState (iniRef i))
  let wrong = filter (any not .fst ) (zipWith (\i j -> ([i ==j,G.getIndex i == G.getIndex j,tableNonRef' i == tableNonRef' j, liftTable' inf "messages" (mapKey' keyValue j ) == j , (liftTable' inf "messages" $ B.decode (B.encode (mapKey' keyValue j ))) == j ],(i,j)))(L.sort $ G.toList (snd t)) (L.sort $ G.toList s))
  let readWrite j =  do
        B.encodeFile "test" (  tableNonRef'. mapKey' keyValue <$> j )
        o <- fmap (liftTable' inf "messages") <$>  B.decodeFile "test"
        return $ o == (tableNonRef'<$> j)

  o <- readWrite ( (G.toList (s)))
  print (fmap fst wrong)
  print o
  -- mapM (putStrLn) $ take 2 $ zipWith (\si sj -> ((concat $ fmap differ $   zip  si sj) <> L.drop (L.length sj) si  <> L.drop (L.length si) sj ))  (fmap show $L.sort $ G.toList (snd t)) (fmap show $L.sort $ G.toList s)
  -- mapM (putStrLn) $ take 2 $ zipWith (\si sj -> ((concat $ fmap differ $   zip  si sj) <> L.drop (L.length sj) si  <> L.drop (L.length si) sj ))  (fmap (show .tableNonRef')$L.sort $ G.toList (snd t)) (fmap (show.tableNonRef') $L.sort $ G.toList s)
  --

  -- print (G.toList (snd t))
  -- print (G.toList (snd s))
  sequence_ l
  sequence_ fing
  sequence_ finm
  return ()

-}

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
  runDynamic $ transaction inf $ historyLoad
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

    liftIO$ (callCommand $ "rm dump/" ++ T.unpack s ++ "/"++ T.unpack t) `catch` (\e -> print (e :: SomeException))
    liftIO$ writeSchema (s ,inf)
    liftIO$ atomically $ modifyTVar (mvarMap inf) (const M.empty)
    (_,o) <- readTable inf "dump"  table []
    liftIO$ putStrLn "Read"
    liftIO$ mapM print (F.toList o)

  return ()


testTable s t w = do
  args <- getArgs
  let db = argsToState args
  smvar <- createVar
  let
    amap = authMap smvar db ("postgres", "queijo")
  (inf,fin) <- runDynamic $ keyTables smvar  (s,"postgres") amap []
  ((_,(_,i)),_) <- runDynamic $ transactionNoLog inf $ selectFrom t Nothing Nothing [] (WherePredicate $ lookAccess inf t <$> w)
  print i

  return ()


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

testCalls = testWidget (return $ do
  setCallBufferMode BufferAll
  i <- runFunction (ffi "var a= 1")
  i <- callFunction (ffi "2")
  j <- callFunction (ffi "1")
  UI.div # set text (show (i + j :: Int))

                       )
