{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module TP.Browser where

import TP.Account
import TP.Agenda
import TP.Map
import Safe
import qualified NonEmpty as Non
import Data.Char
import Step.Common
import Query
import Data.Time
import Text
import qualified Types.Index as G
import Data.Bifunctor (first)
import Debug.Trace
import Types
import SchemaQuery
import Plugins
import TP.Widgets
import Postgresql.Backend (postgresOps)
import SortList
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
import Data.Monoid hiding (Product(..))

import qualified Data.Foldable as F
import qualified Data.Text as T
import Data.Text (Text)
import qualified Data.Set as S

import Database.PostgreSQL.Simple
import qualified Data.Map as M

import OAuth
import GHC.Stack

updateClient metainf inf table tdi clientId now =
    let
      row = tblist . fmap _tb
            $ [ Attr "clientid" (TB1 (SNumeric (fromInteger clientId )))
              , Attr "creation_time" (TB1 (STimestamp (utcToLocalTime utc now)))
              , Attr "schema" (LeftTB1 $ TB1 . SText .  schemaName <$> inf )
              , Attr "table" (LeftTB1 $ TB1 . SText .  tableName <$>table)
              , IT "data_index"   (LeftTB1 $ ArrayTB1 . Non.fromList .   fmap (\(i,j) -> TB1 $ tblist $ fmap _tb [Attr "key" (TB1 . SText  $ keyValue i) ,Attr "val" (TB1 . SDynamic $  j) ]) <$>tdi )
              ]
      lrow = liftTable' metainf "clients" row
    in lrow

getClient metainf clientId ccli = G.lookup (G.Idex $ M.fromList [(lookKey metainf "clients" "clientid",TB1 (SNumeric (fromInteger clientId)))]) ccli :: Maybe (TBData Key Showable)

deleteClient metainf clientId = do
  (dbmeta ,(_,ccli)) <- transactionNoLog metainf $ selectFrom "clients"  Nothing Nothing [] $ LegacyPredicate []
  putPatch (patchVar dbmeta) [(tableMeta (lookTable metainf "clients") , G.Idex $ M.fromList [(lookKey metainf "clients" "clientid",TB1 (SNumeric (fromInteger clientId)))],[])]

editClient metainf inf dbmeta ccli  table tdi clientId now = do
  let cli :: Maybe (TBData Key Showable)
      cli = getClient metainf clientId ccli
      new :: TBData Key Showable
      new = updateClient metainf inf table tdi clientId now
      lrow :: Maybe (Index (TBData Key Showable))
      lrow = maybe (Just $ patch new ) (flip diff new )  cli
  traverse (putPatch (patchVar dbmeta ) . pure ) lrow

addClient clientId metainf inf table dbdata =  do
    now <- getCurrentTime
    let
      tdi = fmap (M.toList .getPKM) $ join $ (\inf table -> fmap (tblist' table ) .  traverse (fmap _tb . (\(k,v) -> fmap (Attr k) . readType (keyType $ k) . T.unpack  $ v).  first (lookKey inf (tableName table))  ). F.toList) <$>  inf  <*> table <*> rowpk dbdata
    (dbmeta ,(_,ccli)) <- transactionNoLog metainf $ selectFrom "clients"  Nothing Nothing [] $ LegacyPredicate []
    editClient metainf inf dbmeta ccli table tdi clientId now
    return (clientId, getClient metainf clientId <$> collectionTid dbmeta)

txt = TB1 . SText

setup
     ::  MVar (M.Map Text  InformationSchema) ->  [String] -> Window -> UI ()
setup smvar args w = void $ do
  metainf <- justError "no meta" . M.lookup "metadata" <$> liftIO ( readMVar smvar)
  let bstate = argsToState args
  let amap = authMap smvar bstate (user bstate , pass bstate)
  inf <- liftIO$ traverse (\i -> loadSchema smvar (T.pack i) (conn metainf) (user bstate)  amap ) $ schema  bstate
  (cli,cliTid) <- liftIO $ addClient (0) metainf inf ((\t inf -> lookTable inf . T.pack $ t) <$> tablename bstate  <*> inf  ) bstate
  (evDB,chooserItens) <- databaseChooser smvar metainf bstate
  body <- UI.div# set UI.class_ "col-xs-12"
  return w # set title (host bstate <> " - " <>  dbn bstate)
  hoverBoard<-UI.div # set UI.style [("float","left"),("height","100vh"),("width","15px")]
  let he = const True <$> UI.hover hoverBoard
  bhe <-stepper True he
  menu <- checkedWidget (tidings bhe he)
  element menu # set UI.class_ "col-xs-1"
  nav  <- buttonDivSet  ["Map","Account","Agenda","Browser","Metadata"] (pure $ args `atMay` 6  )(\i -> UI.button # set UI.text i # set UI.class_ "buttonSet btn-xs btn-default pull-right")
  element nav # set UI.class_ "col-xs-5 pull-right"
  chooserDiv <- UI.div # set children  ([getElement menu] <> chooserItens <> [getElement nav ] ) # set UI.style [("align-items","flex-end"),("height","7vh"),("width","100%")] # set UI.class_ "col-xs-12"
  container <- UI.div # set children [chooserDiv , body] # set UI.class_ "container-fluid"
  getBody w #+ [element hoverBoard,element container]
  mapUITEvent body (traverse (\(nav,inf)-> do
      case nav of
        "Map" -> do
            mapWidget inf body# set UI.style [("width","100%")]
        "Agenda" -> do
            eventWidget inf body # set UI.style [("width","100%")]
        "Account" -> do
            accountWidget inf body # set UI.style [("width","100%")]
        "Metadata" -> do
            let metaOpts = ["Poll","Stats","Change","Exception"]
                iniOpts = join $ fmap (\i -> if elem i metaOpts then Just i else Nothing)$  args `atMay`  7
                displayOpts  i =  UI.button # set UI.text i # set UI.class_ "buttonSet btn-xs btn-default pull-right"
            metanav <- buttonDivSet metaOpts (pure iniOpts) displayOpts
            element metanav # set UI.class_ "col-xs-5 pull-right"
            metabody <- UI.div # set UI.class_ "col-xs-12"
            element body # set children [getElement metanav,metabody] # set UI.style [("display","block")]
            mapUITEvent metabody (\nav-> case nav of
              "Poll" -> do
                  element metabody #
                    set items
                        [ metaAllTableIndexV inf "polling" [("schema_name",TB1 $ SText (schemaName inf) ) ]
                        , metaAllTableIndexV inf "polling_log" [("schema_name",TB1 $ SText (schemaName inf) ) ]]
              "Change" -> do
                  case schemaName inf of
                    "gmail" -> do
                      b <- UI.button # set text "sync"
                      (dbvar,(m,t))  <- liftIO$ transactionNoLog inf $ selectFrom "history" Nothing Nothing [] $ LegacyPredicate []
                      itemListEl <- UI.select # set UI.class_ "col-xs-9" # set UI.style [("width","70%"),("height","350px")] # set UI.size "20"
                      itemListEl2 <- UI.select # set UI.class_ "col-xs-9" # set UI.style [("width","70%"),("height","350px")] # set UI.size "20"
                      do
                        ((DBVar2 tmvard _  vpdiff _ _ ),res) <- liftIO$ transactionNoLog inf $ syncFrom (lookTable inf "history") Nothing Nothing [] []
                        let update = F.foldl'(flip (\p-> fmap (flip apply p)))
                        bres <- accumB ((M.empty,G.empty) :: Collection Key Showable) (flip update <$> rumors vpdiff)
                        let
                          vpt =  tidings bres (  update <$> bres <@> rumors vpdiff )
                        listBoxEl itemListEl2 ( G.toList . snd  <$> vpt)  (pure Nothing) (pure id) ( pure attrLine )
                      element metabody # set children [itemListEl,itemListEl2]
                    i -> do
                      dash <- metaAllTableIndexV inf "modification_table" [("schema_name",TB1 $ SText (schemaName inf) ) ]
                      element metabody # set UI.children [dash]
              "Stats" -> do
                  stats <- metaAllTableIndexV inf "table_stats" [("schema_name",TB1 $ SText (schemaName inf) ) ]
                  clients <- metaAllTableIndexV inf "clients" [("schema",LeftTB1 $ Just $ TB1 $ SText (schemaName inf) ) ]
                  element metabody # set UI.children [stats,clients]
              "Exception" -> do
                  dash <- metaAllTableIndexV inf "plugin_exception" [("schema_name",TB1 $ SText (schemaName inf) ) ]
                  element metabody # set UI.children [dash]
              i -> errorWithStackTrace (show i)
                  ) (triding metanav)
            return body
        "Browser" -> do
            [tbChooser,subnet] <- chooserTable  inf   cliTid  cli
            element tbChooser # sink0 UI.style (facts $ noneShow <$> triding menu)
            let
                expand True = "col-xs-10"
                expand False = "col-xs-12"
            element subnet # sink0 UI.class_ (facts $ expand <$> triding menu)
            element body # set UI.children [tbChooser,subnet]#  set UI.style [("width","100%")]
        i -> errorWithStackTrace (show i))
            ) $ liftA2 (\i  -> fmap (i,)) (triding nav)  evDB


listDBS ::  InformationSchema -> BrowserState -> IO (Tidings (Text,[Text]))
listDBS metainf dname = do
  map <- (\db -> do
        (dbvar ,(_,schemasTB)) <- transactionNoLog metainf $  selectFrom "schema" Nothing Nothing [] $ LegacyPredicate []
        let schemas schemaTB = fmap ((\(Attr _ (TB1 (SText s)) ) -> s) .lookAttr' metainf "name") $ F.toList  schemasTB
        return ((db,).schemas  <$> collectionTid dbvar)) (T.pack $ dbn dname)
  return map

loginWidget userI passI =  do
  usernamel <- flabel # set UI.text "Usuário"
  username <- UI.input # set UI.name "username" # set UI.style [("width","142px")] # set UI.value (maybe "" id userI)
  passwordl <- flabel # set UI.text "Senha"
  password <- UI.input # set UI.name "password" # set UI.style [("width","142px")] # set UI.type_ "password" # set UI.value (maybe "" id passI)
  let usernameE = nonEmpty  <$> UI.valueChange username
      passwordE = nonEmpty <$> UI.valueChange password

  userDiv <- UI.div # set children [usernamel,username] # set UI.class_  "col-xs-5"
  passDiv <- UI.div # set children [passwordl,password] # set UI.class_  "col-xs-5"
  usernameB <- stepper userI usernameE
  passwordB <- stepper passI passwordE
  let usernameT = tidings usernameB usernameE
      passwordT = tidings passwordB passwordE
  return $ ((liftA2 (liftA2 (,)) usernameT passwordT) ,[userDiv,passDiv])




form :: Tidings a -> Event b -> Tidings a
form td ev =  tidings (facts td ) (facts td <@ ev )


authMap smvar sargs (user,pass) schemaN =
      case schemaN of
          "gmail" ->  oauth False
          "tasks" ->  oauth True
          i ->  do
            conn <- connectPostgreSQL ("host=" <> (BS.pack $ host sargs) <> " port=" <> BS.pack (port sargs ) <>" user=" <> BS.pack (user )<> " password=" <> BS.pack (pass ) <> " dbname=" <> (BS.pack $  dbn sargs) )
            execute_ conn "set bytea_output='hex'"
            return (PostAuth conn, postgresOps)
    where oauth tag = do
              user <- justError "no google user" <$> lookupEnv "GOOGLE_USER"
              metainf <- metaInf smvar
              (dbmeta ,_) <- transactionNoLog metainf $ selectFromTable "google_auth" Nothing Nothing [] [("=", Attr "username" (TB1 $ SText  $ T.pack user ))]
              let
                  td :: Tidings (OAuth2Tokens)
                  td = (\o -> let
                            token = justError "" . fmap (toOAuth . _fkttable . unTB) $ L.find ((==["token"]). fmap (keyValue._relOrigin) . keyattr )  $ F.toList (unKV $ snd $ head o )
                            in token) . G.toList <$> collectionTid dbmeta
                  toOAuth v = case fmap TB1 $ F.toList $ snd $ unTB1 v :: [FTB Showable] of
                            [a,b,c,d] -> tokenToOAuth (b,d,a,c)
                            i -> errorWithStackTrace ("wrong token" <> show i)
              return (OAuthAuth (Just (if tag then "@me" else T.pack user,td )), gmailOps)

loadSchema smvar schemaN dbConn user authMap  =  do
    keyTables smvar dbConn (schemaN,T.pack $ user) authMap plugList

databaseChooser smvar metainf sargs = do
  dbs <- liftIO $ listDBS  metainf sargs
  let dbsInit = fmap (\s -> (T.pack $ dbn sargs ,T.pack s)) (schema sargs)
  dbsW <- listBox ((\((c,j)) -> (c,) <$> j) <$> dbs ) (pure dbsInit) (pure id) (pure (line . T.unpack. snd  ))
  schemaEl <- flabel # set UI.text "schema"
  cc <- currentValue (facts $ triding dbsW)
  let dbsWE = rumors $ triding dbsW
  dbsWB <- stepper cc dbsWE
  let dbsWT  = tidings dbsWB dbsWE
  (schemaE,schemaH) <- liftIO newEvent
  metainf <- liftIO $ metaInf smvar
  let genSchema (db,schemaN)
        | schemaN  `L.elem` ["gmail","tasks"]  =  do
              userEnv <- liftIO$ lookupEnv "GOOGLE_USER"
              liftIO $ print userEnv
              usernamel <- flabel # set UI.text "Usuário"
              username <- UI.input # set UI.name "username" # set UI.style [("width","142px")] # set value (fromMaybe "" userEnv)
              let usernameE = nonEmpty  <$> UI.valueChange username

              usernameB <- stepper userEnv usernameE

              load <- UI.button # set UI.text "Log In" # set UI.class_ "col-xs-4" # sink UI.enabled (facts (isJust <$> dbsWT) )
              liftIO $ onEventIO (usernameB <@ (UI.click load)) $ traverse (\ v ->do
                let auth = authMap smvar sargs (user sargs ,pass sargs )
                inf <- loadSchema smvar schemaN (rootconn metainf) (user sargs)  auth
                schemaH $ Just inf)
              user <- UI.div # set children [usernamel,username] # set UI.class_ "col-xs-8"
              UI.div # set children [user ,load]

        | otherwise   = do
            (widT,widE) <- loginWidget (Just $ user sargs  ) (Just $ pass sargs )
            load <- UI.button # set UI.text "Log In" # set UI.class_ "col-xs-2" # sink UI.enabled (facts (isJust <$> dbsWT) )
            let login =   widT
                formLogin = form login (UI.click load)
            liftIO$ onEventIO (rumors formLogin)
              (traverse (\(user,pass)-> do
                let auth = authMap smvar sargs (user,pass)
                inf <- loadSchema smvar schemaN (rootconn metainf) user auth
                schemaH $ Just inf
                ))

            UI.div # set children (widE <> [load])

  element dbsW # set UI.style [("height" ,"26px"),("width","140px")]
  authBox <- UI.div # sink items (maybeToList . fmap genSchema <$> facts dbsWT) # set UI.class_ "col-xs-4" # set UI.style [("border", "gray solid 2px")]
  let auth = authMap smvar sargs (user sargs ,pass sargs )
  inf <- traverse (\i -> liftIO $loadSchema smvar (T.pack i ) (rootconn metainf) (user sargs) auth) (schema sargs)
  chooserB  <- stepper inf schemaE
  let chooserT = tidings chooserB schemaE
  element authBox  # sink UI.style (facts $ (\a b -> noneShow $  fromMaybe True $  liftA2 (\(db,sc) (csch) -> if sc == (schemaName csch )then False else True ) a b )<$>    dbsWT <*> chooserT )
  schemaSel <- UI.div # set UI.class_ "col-xs-2" # set children [ schemaEl , getElement dbsW]
  return $ (chooserT,[schemaSel ]<>  [authBox] )


tableChooser  inf tables iniSchemas iniUsers iniTables = do
  let
      pred =  fmap (uncurry Attr)<$> [("IN",("schema_name",ArrayTB1 $ TB1 . SText <$> iniSchemas ))]
      authPred =  fmap (uncurry Attr )<$> [("IN",  ("grantee",ArrayTB1 $ TB1 . SText <$> iniUsers )), ("IN",("table_schema",ArrayTB1 $ TB1 . SText <$> iniSchemas  ))]
  (orddb ,authorization,translation) <- liftIO $ transactionNoLog  (meta inf) $
      (,,) <$> (fst <$> (selectFromTable "ordering"  Nothing Nothing []  pred ))
           <*> (fst <$> (selectFromTable "authorization" Nothing Nothing [] authPred   ))
           <*> (fst <$> (selectFromTable "table_name_translation" Nothing Nothing []  pred ))
  filterInp <- UI.input # set UI.style [("width","100%")]
  filterInpBh <- stepper "" (UI.valueChange filterInp)
  let filterInpT = tidings filterInpBh (UI.valueChange filterInp)

  let
      selTable = flip M.lookup (pkMap inf)
      -- Table Description
      lookDesc = (\i j -> maybe (T.unpack $ maybe "" rawName j)  ((\(Attr _ v) -> renderShowable v). lookAttr' (meta inf)  "translation") $ G.lookup (idex (meta inf) "table_name_translation" [("schema_name" ,TB1 $ SText $ schemaName inf),("table_name",TB1 $ SText (maybe ""  tableName j))]) i) <$> collectionTid translation
      -- Authorization
      authorize =  (\autho t -> isJust $ G.lookup (idex  (meta inf) "authorization"  [("table_schema", TB1 $ SText (schemaName inf) ),("table_name",TB1 $ SText $ tableName t),("grantee",TB1 $ SText $ username inf)]) autho)  <$> collectionTid authorization
      -- Text Filter
      filterLabel = (\j d -> (\i -> L.isInfixOf (toLower <$> j) (toLower <$> d (Just i))))<$> filterInpT <*> lookDesc
      -- Usage Count
      tableUsage orderMap table = maybe (Right 0) (Left ) . fmap (lookAttr' (meta inf)  "usage" ) $  G.lookup  (G.Idex ( M.fromList pk )) orderMap
          where  pk = L.sortBy (comparing fst ) $ first (lookKey (meta inf ) "ordering") <$> [("table_name",TB1 . SText . rawName $ table ), ("schema_name",TB1 $ SText (schemaName inf))]
  bset <- mdo
    let
        buttonStyle k (e,sub) = do
            let tableK = fromJust (selTable k)
            label <- UI.div # sink0 UI.text (facts $ lookDesc  <*> pure (selTable k)) # set UI.style [("width","100%")] # set UI.class_ "btn-xs btn-default buttonSet"
            state <- element e # set UI.type_ "checkbox"  # sink UI.checked (maybe False (not . L.null) . M.lookup k .traceShowId <$> facts (triding bset))
            subels  <- mapM (\(ki,ei) -> do
              element ei # set UI.type_ "checkbox"# sink UI.checked (maybe False (elem ki) . M.lookup k <$> facts (triding bset))
              label <- UI.div # sink0 UI.text (facts $ lookDesc  <*> pure (Just ki)) # set UI.style [("width","100%")] # set UI.class_ "btn-xs btn-default buttonSet"
              UI.div # set children[ei , label] # sink0 UI.style (noneDisplay "flex" <$> facts visible)
              ) (zip (rawUnion tableK) sub)


            prebset <- UI.div # set children subels # set UI.style [("padding-left","5px")] # sink UI.style (noneShow <$> facts visible)
            top <- UI.div # set children[state, label] # sink0 UI.style (noneDisplay "flex" <$> facts visible)
            element prebset  # set UI.style (noneShow . not $ L.null (rawUnion tableK))
            UI.div # set children [top,prebset] # set UI.style [("width","100%")] # sink0 UI.style (noneShow<$> facts visible)
          where
            tb =  justLook   k (pkMap inf)
            visible  = (\i j -> i tb && j tb) <$> filterLabel <*> authorize
        buttonString k = do
          b <- UI.input
          let un = rawUnion tableK
              tableK = fromJust $ selTable k
          unions <- mapM (\i -> (i,) <$> UI.input) un
          let ev = (k,) . (\b -> traceShowId $ if b then (if L.null un then [tableK ] else un,[]) else ([],if L.null un then [tableK] else un))<$>UI.checkedChange b
          let evs = foldr (unionWith const) ev $ fmap (k,) .  (\(ki,e) -> (\i-> (if i then ([ki],[]) else ([],[ki]))) <$> UI.checkedChange e  )<$> unions
          return (k,((b,(snd <$> unions)),evs))
    bset <- checkDivSetTGen tables ((\i j -> tableUsage i (justLook j (pkMap inf))) <$> collectionTid orddb ) (M.fromList . fmap  (\i -> (i,rawUnion $ fromJust $ selTable i))<$> iniTables) buttonString buttonStyle
    return bset
  let
      bBset = M.keys <$> triding bset
      ordRow orderMap pkset =  field
          where
            field =  G.lookup (G.Idex $ M.fromList pk) orderMap
            pk = L.sortBy (comparing fst) $ first (lookKey (meta inf ) "ordering") <$>[("table_name",TB1 . SText . rawName $ justLook   pkset (pkMap inf) ), ("schema_name",TB1 $ SText (schemaName inf))]
      incClick field =  (fst field , G.getIndex field ,[patch $ fmap (+SNumeric 1) usage])
          where
            usage = lookAttr' (meta inf ) "usage"   field
  liftIO$ onEventIO ((\i j -> fmap incClick <$> (ordRow i <$> j)) <$> facts (collectionTid orddb) <@> rumors bBset)
    (traverse (traverse (\p -> do
      _ <- transactionNoLog (meta inf ) $ patchFrom  p
      putPatch (patchVar orddb) [p] )))


  tableHeader <- UI.h3 # set text "Table"
  tbChooserI <- UI.div # set children [tableHeader,filterInp,getElement bset]  # set UI.style [("height","90vh"),("overflow","auto"),("height","99%")]
  return $ TrivialWidget ((\f -> M.mapKeys (fmap (f. selTable) ))<$> lookDesc <*> (M.mapKeys (\i-> (i,i))  <$>triding bset)) tbChooserI




selectFromTable t a b c p = do
  inf  <- ask
  selectFrom  t a b c (LegacyPredicate $ fmap (liftField (meta inf) t) <$>p)

chooserTable inf cliTid cli = do
  iv   <- currentValue (facts cliTid)
  let lookT iv = let  i = unLeftItens $ lookAttr' (meta inf)  "table" iv
                in fmap (\(Attr _ (TB1 (SText t))) -> t) i
  let initKey = pure . maybeToList . join $ fmap (S.fromList .rawPK) . flip M.lookup (_tableMapL inf) <$> join (lookT <$> iv)
      kitems = M.keys (pkMap inf)
      selTable = flip M.lookup (pkMap inf)
  {-
  filterInp <- UI.input # set UI.style [("width","100%")]
  filterInpBh <- stepper "" (UI.valueChange filterInp)
  let filterInpT = tidings filterInpBh (UI.valueChange filterInp)
  -- Load Metadata Tables
      pred =  fmap (uncurry Attr)<$> [("=",("schema_name",TB1 $ SText (schemaName inf) ))]
      authPred =  fmap (uncurry Attr )<$> [("=",  ("grantee",TB1 $ SText (username inf) )), ("=",("table_schema",TB1 $ SText (schemaName inf) ))]
  (orddb ,authorization,translation) <- liftIO $ transactionNoLog  (meta inf) $
      (,,) <$> (fst <$> (selectFromTable "ordering"  Nothing Nothing []  pred ))
             <*> (fst <$>   (selectFromTable "authorization" Nothing Nothing [] authPred   ))
             <*> (fst <$>  (selectFromTable "table_name_translation" Nothing Nothing []  pred ))

  let
      selTable = flip M.lookup (pkMap inf)
      -- Table Description
      lookDesc = (\i j -> maybe (T.unpack $ maybe "" rawName j)  ((\(Attr _ v) -> renderShowable v). lookAttr' (meta inf)  "translation") $ G.lookup (idex (meta inf) "table_name_translation" [("schema_name" ,TB1 $ SText $ schemaName inf),("table_name",TB1 $ SText (maybe ""  tableName j))]) i) <$> collectionTid translation
      -- Authorization
      authorize =  (\autho t -> isJust $ G.lookup (idex  (meta inf) "authorization"  [("table_schema", TB1 $ SText (schemaName inf) ),("table_name",TB1 $ SText $ tableName t),("grantee",TB1 $ SText $ username inf)]) autho)  <$> collectionTid authorization
      -- Text Filter
      filterLabel = (\j d -> (\i -> L.isInfixOf (toLower <$> j) (toLower <$> d (Just i))))<$> filterInpT <*> lookDesc
      -- Usage Count
      tableUsage orderMap table = maybe (Right 0) (Left ) . fmap (lookAttr' (meta inf)  "usage" ) $  G.lookup  (G.Idex ( M.fromList pk )) orderMap
          where  pk = L.sortBy (comparing fst ) $ first (lookKey (meta inf ) "ordering") <$> [("table_name",TB1 . SText . rawName $ table ), ("schema_name",TB1 $ SText (schemaName inf))]
      buttonStyle k e = do
          label <- UI.div # sink0 UI.text (facts $ lookDesc  <*> pure (selTable k)) # set UI.style [("width","100%")] # set UI.class_ "btn-xs btn-default buttonSet"
          state <- e # set UI.type_ "checkbox"
          UI.div # set children [state,label] # set UI.style [("width","100%")] # sink0 UI.style (noneDisplay "flex" <$> facts visible)
        where
          tb =  justLook   k (pkMap inf)
          visible  = (\i j -> i tb && j tb) <$> filterLabel <*> authorize
  bset <- checkDivSetT kitems ((\i j -> tableUsage i (justLook j (pkMap inf))) <$> collectionTid orddb ) initKey  (const UI.input ) buttonStyle
  -}
  bset <- tableChooser inf kitems (pure (schemaName inf)) (pure (username inf)) initKey
  let bBset = triding bset
  nav  <- buttonDivSet ["Browser","Exception","Change"] (pure $ Just "Browser")(\i -> UI.button # set UI.text i # set UI.style [("font-size","smaller")]. set UI.class_ "buttonSet btn-xs btn-default pull-right")
  element nav # set UI.class_ "col-xs-11"
  layout <- checkedWidget (pure False)
  tbChooser <- UI.div # set UI.class_ "col-xs-2"# set UI.style [("height","90vh"),("overflow","hidden")] # set children [getElement bset]
  body <- UI.div
  el <- mapUITEvent body (\l -> mapM (\(nav,((table,desc),sub))-> do
      header <- UI.h3
        # set UI.class_ "header"
        # set text desc
      let layFacts i =  if i then ("col-xs-" <> (show $  (12`div`length l))) else "row"
          layFacts2 i =  if i then ("col-xs-" <> (show $  6)) else "row"
      body <- case nav of
        "Change" -> do
            let tableob = (justError "no table " $ M.lookup table (pkMap inf))
            metaAllTableIndexV inf "modification_table" [("schema_name",TB1 $ SText (schemaName inf) ),("table_name",TB1 $ SText (tableName tableob) ) ]
        "Exception" -> do
            let tableob = (justError "no table " $ M.lookup table (pkMap inf))
            metaAllTableIndexV inf "plugin_exception" [("schema_name",TB1 $ SText (schemaName inf) ),("table_name",TB1 $ SText (tableName tableob) ) ]
        "Browser" -> do
            els <- mapM (\t -> do
                l <- UI.h4 #  set text (T.unpack $fromMaybe (rawName t)  $ rawTranslation t) # set UI.class_ "col-xs-12 header"
                b <- viewerKey inf t cli (layFacts2 . not <$> triding layout) cliTid
                element b # set UI.class_ "col-xs-12"
                UI.div # set children [l,b]
                ) sub
            UI.div # set children els

        "Stats" -> do
            viewer inf (justError "no table with pk" $ M.lookup table (pkMap inf)) Nothing
      UI.div # set children [header,body] # sink0 UI.class_ (facts $ layFacts <$> triding layout)# set UI.style [("border","2px dotted gray")]
        )l ) $ liftA2 (\i j -> (i,) <$> j)  (triding nav) (M.toList <$> bBset)
  element body # sink UI.children (facts el) # set UI.class_ "col-xs-12"
  element layout  # set UI.class_ "col-xs-1"
  subnet <- UI.div # set children [getElement layout,getElement nav,body] # set UI.style [("height","90vh"),("overflow","auto")]
  return [tbChooser, subnet ]

viewerKey
  ::
      InformationSchema -> Table -> Integer -> Tidings String -> Tidings  (Maybe (TBData Key Showable)) -> UI Element
viewerKey inf table cli layout cliTid = mdo
  iv   <- currentValue (facts cliTid)
  let lookT iv = let  i = unLeftItens $ lookAttr' (meta inf)  "table" iv
                in fmap (\(Attr _ (TB1 (SText t))) -> t) i
      lookPK iv = let  i = unLeftItens $ lookAttr' (meta inf)  "data_index" iv
                       unKey t = liftA2 (,) ((\(Attr _ (TB1 (SText i)))-> flip (lookKey inf ) i <$> lookT iv ) $ lookAttr' (meta inf)  "key" t  )( pure $ (\(Attr _ (TB1 (SDynamic i)))-> i) $ lookAttr'  (meta inf)  "val" t )
                in fmap (\(IT _ (ArrayTB1 t)) -> catMaybes $ F.toList $ fmap (unKey.unTB1) t) i
  let
  reftb@(vpt,vp,_ ,var ) <- refTables inf table

  let
      tdip = (\i -> join $ traverse (\v -> G.lookup  (G.Idex (M.fromList $ justError "" $ traverse (traverse unSOptional' ) $v)) (snd i) ) (join $ lookPK <$> iv) ) <$> vpt
      tdi = if Just (tableName table) == join (lookT <$> iv) then tdip else pure Nothing
  cv <- currentValue (facts tdi)
  -- Final Query ListBox
  filterInp <- UI.input
  filterInpBh <- stepper "" (UI.valueChange filterInp)
  let filterInpT = tidings filterInpBh (diffEvent filterInpBh (UI.valueChange filterInp))
      sortSet = rawPK table <>  L.filter (not .(`L.elem` rawPK table)) (F.toList . tableKeys . TB1 . tableNonRef' . allRec' (tableMap inf ) $ table)
  sortList <- selectUI sortSet ((,True) <$> rawPK table ) UI.div UI.div conv
  element sortList # set UI.style [("overflow-y","scroll"),("height","200px")]
  let
     filteringPred i = T.isInfixOf (T.pack $ toLower <$> i) . T.toLower . T.intercalate "," . fmap (T.pack . renderPrim ) . F.toList  .snd
     tsort = sorting' . filterOrd <$> triding sortList
     filtering res = (\t -> fmap (filter (filteringPred t )) )<$> filterInpT  <*> res
     pageSize = 20
     lengthPage (fixmap,i) = (s  `div` pageSize) +  if s `mod` pageSize /= 0 then 1 else 0
        where (s,_)  = fromMaybe (sum $ fmap fst $ F.toList fixmap ,M.empty ) $ M.lookup (LegacyPredicate []) fixmap
  inisort <- currentValue (facts tsort)
  itemListEl <- UI.select # set UI.class_ "col-xs-6" # set UI.style [("width","100%")] # set UI.size "21"
  let wheel = negate <$> mousewheel itemListEl
  (offset,res3)<- mdo
    offset <- offsetField (pure 0) wheel  (lengthPage <$> facts res3)
    res3 <- mapT0Event (fmap inisort (fmap G.toList vp)) return ( (\f i -> fmap f i)<$> tsort <*> (filtering $ fmap (fmap G.toList) $ tidings ( res2) ( rumors vpt) ) )
    return (offset, res3)
  onEvent (rumors $ triding offset) $ (\i ->  liftIO $ do
    print ("page",(i `div` 10 )   )
    transactionNoLog inf $ eventTable  table  (Just $ i `div` 10) Nothing  [] $ LegacyPredicate [])
  let
    paging  = (\o -> fmap (L.take pageSize . L.drop (o*pageSize)) ) <$> triding offset
  page <- currentValue (facts paging)
  res4 <- mapT0Event (page $ fmap inisort (fmap G.toList vp)) return (paging <*> res3)
  itemList <- listBoxEl itemListEl ((Nothing:) . fmap Just <$> fmap snd res4) (fmap Just <$> tidings st sel ) (pure id) (pure (maybe id attrLine))
  let evsel =  rumors (fmap join  $ triding itemList)
  (dbmeta ,(_,_)) <- liftIO$ transactionNoLog (meta inf) $ selectFromTable "clients"  Nothing Nothing [] ([("=",  uncurry Attr $("schema",LeftTB1 $ Just $TB1 $ SText (schemaName inf) )), ("=",Attr "table" $ LeftTB1 $ Just $ TB1 $ SText (tableName table))])
  liftIO $ onEventIO ((,) <$> facts (collectionTid dbmeta ) <@> evsel ) (\(ccli ,i) -> void . editClient (meta inf) (Just inf) dbmeta  ccli (Just table ) (M.toList . getPKM <$> i) cli =<< getCurrentTime )
  prop <- stepper cv evsel
  let tds = tidings prop evsel

  (cru,ediff,pretdi) <- crudUITable inf (pure "+")  reftb [] [] (allRec' (tableMap inf) table) tds
  diffUp <-  mapEvent (fmap pure)  $ (\i j -> traverse (return . flip apply j ) i) <$> facts pretdi <@> ediff
  let
     sel = filterJust $ safeHead . concat <$> unions [ diffUp,unions [rumors  $ fmap join (triding itemList) ]]
  st <- stepper cv sel
  res2 <- stepper (vp) (rumors vpt)
  onEvent (pure <$> ediff) (liftIO .  putPatch var )
  title <- UI.div #  sink items (pure . maybe UI.h4 (\i -> UI.h4 # attrLine i  )  <$> st) # set UI.class_ "col-xs-8"
  expand <- UI.input # set UI.type_ "checkbox" # sink UI.checked filterEnabled# set UI.class_ "col-xs-1"
  let evc = UI.checkedChange expand
  filterEnabled <- stepper False evc
  insertDiv <- UI.div # set children [title,head cru] # set UI.class_ "container-fluid"
  insertDivBody <- UI.div # set children [insertDiv,last cru]
  element sortList # sink UI.style  (noneShow <$> filterEnabled) # set UI.class_ "col-xs-4"
  element offset # set UI.class_ "col-xs-4"
  element filterInp # set UI.class_ "col-xs-3"
  element itemList -- # set UI.class_ "row"
  itemSel <- UI.div # set children ( [expand , filterInp, getElement offset ,getElement sortList] ) -- # set UI.class_ "row"
  itemSelec <- UI.div # set children [itemSel,getElement itemList] -- # set UI.class_ "col-xs-6"
  mapM (\i -> element i # sink0 UI.class_ (facts $ layout)) [itemSelec,insertDivBody]
  UI.div # set children ([itemSelec,insertDivBody ] )



