{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module TP.Main where

import TP.Selector
import Data.Unique
import Postgresql.Backend (connRoot)
import Data.Tuple
import TP.View
import TP.Account
import TP.Browser
import Control.Monad.Writer (runWriterT)
import TP.Agenda
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


setup
  ::  DatabaseSchema ->  [String] -> [Plugins] -> Window -> UI ()
setup smvar args plugList w = void $ do
  metainf <- liftIO$ metaInf smvar
  setCallBufferMode BufferRun
  let bstate = argsToState args
  let amap = authMap smvar bstate (user bstate , pass bstate)
  inf <- ui $ fmap (justError ("no schema" <> show (schema bstate))) $ traverse (\i -> loadSchema smvar (T.pack i)  (user bstate)  amap plugList) $ schema  bstate
  (cli,cliTid) <- ui $ addClient (fromIntegral $ wId w) metainf inf ((\t -> lookTable inf . T.pack $ t) <$> tablename bstate  ) (rowpk bstate)
  (evDB,chooserItens) <- databaseChooser smvar metainf bstate plugList
  body <- UI.div# set UI.class_ "col-xs-12"
  return w # set title (host bstate <> " - " <>  dbn bstate)
  hoverBoard<-UI.div # set UI.style [("float","left"),("height","100vh"),("width","15px")]
  let he = const True <$> UI.hover hoverBoard
  bhe <- ui $stepper True he
  menu <- checkedWidget (tidings bhe he)
  element menu # set UI.class_ "col-xs-1"
  nav  <- buttonDivSet  ["Map","Account","Agenda","Browser","Metadata"] (pure $ args `atMay` 6  )(\i -> UI.button # set UI.text i # set UI.class_ "buttonSet btn-xs btn-default pull-right")
  element nav # set UI.class_ "col-xs-5 pull-right"
  chooserDiv <- UI.div # set children  ([getElement menu] <> chooserItens <> [getElement nav ] ) # set UI.style [("align-items","flex-end"),("height","7vh"),("width","100%")] # set UI.class_ "col-xs-12"
  container <- UI.div # set children [chooserDiv , body] # set UI.class_ "container-fluid"

  let
    expand True = "col-xs-10"
    expand False = "col-xs-12"
  element body # sink0 UI.class_ (facts $ expand <$> triding menu)
  getBody w #+ [element hoverBoard,element container]
  mapUIFinalizerT body (traverse (\inf-> mdo
    let kitems = F.toList (pkMap inf)
        schId = int $ schemaId inf
        initKey = maybe [] (catMaybes.F.toList)  . (\iv -> fmap (\t -> HM.lookup t (_tableMapL inf))  <$> join (lookT <$> iv)) <$> cliTid
        lookT iv = let  i = indexFieldRec (liftAccess metainf "clients" $ Nested (IProd False ["selection"]) (IProd True ["table"])) iv
                    in fmap (\(TB1 (SText t)) -> t) .unArray  <$> join (fmap unSOptional' i)
    iniKey <-currentValue (facts initKey)

    (lookDesc,bset) <- tableChooser inf  kitems (fst <$> tfilter) (snd <$> tfilter)  ((schemaName inf)) (snd (username inf)) (pure iniKey)

    posSel <- positionSel
    bd <- UI.div  # set UI.class_ "col-xs-10"
    (sidebar,calendarT) <- calendarSelector
    tbChooser <- UI.div # set UI.class_ "col-xs-2"# set UI.style [("height","90vh"),("overflow","hidden")] # set children [sidebar,posSel ^._1,getElement bset]# sink0 UI.style (facts $ noneShow <$> triding menu)
    element body # set children [tbChooser,bd]
    let
          buttonStyle k (e,sub) = mdo
            let tableK = k
            label <- UI.div # sink0 UI.text (fmap T.unpack $ facts $ lookDesc  <*> pure k)  # set UI.class_ "fixed-label col-xs-11"
            state <- element e   # sink UI.checked (maybe False (not . L.null) . M.lookup k . M.mapKeys fst <$> facts (triding bset)) # set UI.class_ "col-xs-1"
            subels  <- mapM (\(ki,ei) -> do
              element ei # sink UI.checked (maybe False (elem ki) . M.lookup k. M.mapKeys fst  <$> facts (triding bset)) # set UI.class_ "col-xs-1"
              label <- UI.div # sink0 UI.text (fmap T.unpack $ facts $ lookDesc  <*> pure ki) # set UI.style [("width","100%")] # set UI.class_ "fixed-label col-xs-11"
              UI.div # set children[ei , label]
              ) (zip (rawUnion tableK) sub)


            prebset <- UI.div # set children subels # set UI.style [("padding-left","5px")] # set  UI.class_ "col-xs-12"
            top <- UI.div # set children[state, label] # set  UI.class_ "col-xs-12"
            element prebset  # set UI.style (noneShow . not $ L.null (rawUnion tableK))
            UI.div # set children [top,prebset] # set UI.style [("width","100%")]

    tfilter <-  mapUIFinalizerT bd (\nav-> do
      bdo <- UI.div
      element bd # set children [bdo]
      case nav of
        "Map" -> do
          element bdo  # set UI.style [("width","100%")]
          fmap ((\i j -> elem (tableName j) i) . fmap (^._2._2)) <$> mapWidget bdo calendarT posSel (triding bset) inf
        "Agenda" -> do
          element bdo  # set UI.style [("width","100%")]
          cliZone <- jsTimeZone
          fmap ((\i j -> elem j i) . fmap (^._2._2)) <$>  eventWidget bdo calendarT (triding bset) inf cliZone
        "Account" -> do
          element bdo  # set UI.style [("width","100%")]
          fmap ((\i j -> elem (tableName j) i) . fmap (^._2._2)) <$> accountWidget bdo calendarT (triding bset) inf
        "Metadata" -> do
              let metaOpts = ["Poll","Stats","Change","Exception"]
                  iniOpts = join $ fmap (\i -> if elem i metaOpts then Just i else Nothing)$  args `atMay`  7
                  displayOpts  i =  UI.button # set UI.text i # set UI.class_ "buttonSet btn-xs btn-default pull-right"
              metanav <- buttonDivSet metaOpts (pure iniOpts) displayOpts
              element metanav # set UI.class_ "col-xs-5 pull-right"
              metabody <- UI.div # set UI.class_ "col-xs-10"
              element bdo # set children [getElement metanav,metabody] # set UI.style [("display","block")]
              mapUIFinalizerT metabody (\(nav,tables)-> case nav  of
                "Poll" -> do
                    els <- sequence      [ metaAllTableIndexA inf "polling" [(IProd True ["schema"],Left (schId,Equals) ) ]
                          , metaAllTableIndexA inf "polling_log" [(IProd True ["schema"],Left (schId,Equals) ) ]]
                    element metabody #
                      set children els
                "Change" -> do
                    case schemaName inf of
                      "gmail" -> do
                        b <- UI.button # set text "sync"
                        (dbvar,(m,t))  <- ui $ transactionNoLog inf $ selectFrom "history" Nothing Nothing []  mempty
                        itemListEl <- UI.select # set UI.class_ "col-xs-9" # set UI.style [("width","70%"),("height","350px")] # set UI.size "20"
                        itemListEl2 <- UI.select # set UI.class_ "col-xs-9" # set UI.style [("width","70%"),("height","350px")] # set UI.size "20"
                        do
                          ((DBVar2 tmvard _   _ vpdiff _ _ ),res) <- ui $ transactionNoLog inf $ syncFrom (lookTable inf "history") Nothing Nothing [] mempty
                          let update = F.foldl'(flip (\p-> fmap (flip apply p)))
                          bres <- ui $ accumB ((M.empty,G.empty) :: Collection Key Showable) (flip update <$> rumors vpdiff)
                          let
                            vpt =  tidings bres (  update <$> bres <@> rumors vpdiff )
                          listBoxEl itemListEl2 ( G.toList . snd  <$> vpt)  (pure Nothing) (pure id) ( pure attrLine )
                        element metabody # set children [itemListEl,itemListEl2]
                      i -> do
                        let pred = [(IProd True ["schema"],Left (schId,Equals) ) ] <> if M.null tables then [] else [ (IProd True ["table"],Left (ArrayTB1 $ int . _tableUnique <$>  Non.fromList (concat (F.toList tables)),Flip (AnyOp Equals)))]
                        dash <- metaAllTableIndexA inf "modification_table" pred
                        element metabody # set UI.children [dash]
                "Stats" -> do
                    let pred = [(IProd True ["schema"],Left (schId,Equals) ) ] <> if M.null tables then [] else [ (IProd True ["table"],Left (ArrayTB1 $ int. _tableUnique<$>  Non.fromList (concat (F.toList tables)),Flip (AnyOp Equals)))]
                    stats <- metaAllTableIndexA inf "table_stats" pred
                    clients <- metaAllTableIndexA inf "clients"$  [(IProd True ["schema_name"],Left (LeftTB1 $ Just $ txt (schemaName inf),Equals) ) ]<> if M.null tables then [] else [ (Nested (IProd True ["selection"] ) (Many [ IProd True ["table"]]),Left (ArrayTB1 $ txt . rawName <$>  Non.fromList (concat (F.toList tables)),Flip (AnyOp Equals)) )]
                    element metabody # set UI.children [stats,clients]
                "Exception" -> do
                    let pred = [(IProd True ["schema"],Left (schId,Equals) ) ] <> if M.null tables then [] else [ (IProd True ["table"],Left (ArrayTB1 $ int . _tableUnique<$>  Non.fromList (concat (F.toList tables)),Flip (AnyOp Equals)))]
                    dash <- metaAllTableIndexA inf "plugin_exception" pred
                    element metabody # set UI.children [dash]
                i -> errorWithStackTrace (show i)
                    ) ((,) <$> triding metanav <*> triding bset)
              return bdo
              return  ((buttonStyle,const True))
        "Browser" -> do
              subels <- chooserTable  inf  bset cliTid  cli
              element bdo  # set children  subels # set UI.style [("height","90vh"),("overflow","auto")]
              return  ((buttonStyle, const True))
        i -> errorWithStackTrace (show i)
         )  (triding nav)
    return tfilter
      ) )  evDB
  element body #  set UI.style [("width","100%")]



listDBS ::  InformationSchema -> BrowserState -> Dynamic (Tidings (Text,[Text]))
listDBS metainf dname = do
  map <- (\db -> do
        (dbvar ,(_,schemasTB)) <- transactionNoLog metainf $  selectFrom "schema" Nothing Nothing [] mempty
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
  usernameB <- ui $ stepper userI usernameE
  passwordB <-  ui $stepper passI passwordE
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
              ((dbmeta ,_),_) <- runDynamic $ transactionNoLog metainf $ selectFromTable "google_auth" Nothing Nothing [] [(IProd True ["username"],Left ((txt  $ T.pack user ),Equals) )]
              let
                  td :: Tidings (OAuth2Tokens)
                  td = (\o -> let
                            token = justError "" . fmap (toOAuth . _fkttable . unTB) $ L.find ((==["token"]). fmap (keyValue._relOrigin) . keyattr )  $ F.toList (unKV $ snd $ head o )
                            in token) . G.toList <$> collectionTid dbmeta
                  toOAuth v = case fmap TB1 $ F.toList $ snd $ unTB1 v :: [FTB Showable] of
                            [a,b,c,d] -> tokenToOAuth (b,d,a,c)
                            i -> errorWithStackTrace ("wrong token" <> show i)
              return (OAuthAuth (Just (if tag then "@me" else T.pack user,td )), gmailOps)

loadSchema smvar schemaN user authMap  plugList =  do
    keyTables smvar (schemaN,T.pack $ user) authMap plugList

databaseChooser smvar metainf sargs plugList = do
  dbs <- ui $ listDBS  metainf sargs
  let dbsInit = fmap (\s -> (T.pack $ dbn sargs ,T.pack s)) (schema sargs)
  dbsW <- listBox ((\((c,j)) -> (c,) <$> j) <$> dbs ) (pure dbsInit) (pure id) (pure (line . T.unpack. snd  ))
  schemaEl <- flabel # set UI.text "schema"
  cc <- currentValue (facts $ triding dbsW)
  let dbsWE = rumors $ triding dbsW
  dbsWB <-  ui $stepper cc dbsWE
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

              usernameB <-  ui $stepper userEnv usernameE

              load <- UI.button # set UI.text "Log In" # set UI.class_ "col-xs-4" # sink UI.enabled (facts (isJust <$> dbsWT) )
              ui$ mapEventDyn  ( traverse (\ v ->do
                let auth = authMap smvar sargs (user sargs ,pass sargs )
                inf <- loadSchema smvar schemaN  (user sargs)  auth plugList
                liftIO$schemaH $ Just inf))(usernameB <@ (UI.click load))
              user <- UI.div # set children [usernamel,username] # set UI.class_ "col-xs-8"
              UI.div # set children [user ,load]

        | otherwise   = do
            (widT,widE) <- loginWidget (Just $ user sargs  ) (Just $ pass sargs )
            load <- UI.button # set UI.text "Log In" # set UI.class_ "col-xs-2" # sink UI.enabled (facts (isJust <$> dbsWT) )
            let login =   widT
                formLogin = form login (UI.click load)
            ui$ mapTEventDyn
              (traverse (\(user,pass)-> do
                let auth = authMap smvar sargs (user,pass)
                inf <- loadSchema smvar schemaN  user auth plugList
                liftIO$schemaH $ Just inf
                ))(formLogin)

            UI.div # set children (widE <> [load])

  element dbsW # set UI.style [("height" ,"26px"),("width","140px")]
  genS <- mapUIFinalizerT (getElement dbsW) (traverse genSchema) dbsWT
  authBox <- UI.div # sink children (maybeToList <$> facts genS) # set UI.class_ "col-xs-4" # set UI.style [("border", "gray solid 2px")]
  let auth = authMap smvar sargs (user sargs ,pass sargs )
  inf <- ui $traverse (\i -> loadSchema smvar (T.pack i ) (user sargs) auth plugList ) (schema sargs)
  chooserB  <- ui $ stepper inf schemaE
  let chooserT = tidings chooserB schemaE
  element authBox  # sink UI.style (facts $ (\a b -> noneShow $  fromMaybe True $  liftA2 (\(db,sc) (csch) -> if sc == (schemaName csch )then False else True ) a b )<$>    dbsWT <*> chooserT )
  schemaSel <- UI.div # set UI.class_ "col-xs-2" # set children [ schemaEl , getElement dbsW]
  return $ (chooserT,[schemaSel ]<>  [authBox] )

createVar = do
  args <- getArgs
  let db = argsToState args
  smvar   <- newMVar HM.empty
  conn <- connectPostgreSQL (connRoot db)
  l <- query_ conn "select oid,name from metadata.schema"
  return $ DatabaseSchema (M.fromList l) (HM.fromList $ swap <$> l) conn smvar



testTable s t w = do
  args <- getArgs
  let db = argsToState args
  smvar <- createVar
  let
    amap = authMap smvar db ("postgres", "queijo")
  (inf,fin) <- runDynamic $ keyTables smvar  (s,"postgres") amap []
  wm <- mkWeakMVar  (globalRef smvar) (sequence_ fin)
  (i,_) <- runDynamic $ transactionNoLog inf $ selectFrom t Nothing Nothing [] (WherePredicate $ lookAccess inf t <$> w)
  print (fst (snd i))


testPlugin s t p  = do
  args <- getArgs
  let db = argsToState args
  smvar <- createVar
  let
    amap = authMap smvar db ("postgres", "queijo")
  (inf,fin) <- runDynamic $ keyTables smvar  (s,"postgres") amap []
  wm <- mkWeakMVar  (globalRef smvar) (sequence_ fin)
  let (i,o) = pluginStatic p
  print $ liftAccess inf t i
  print $ liftAccess inf t o




