{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module TP.Browser where

import qualified Data.Interval as Interval
import Data.Time.Calendar.WeekDate
import qualified NonEmpty as Non
import Data.Char
import qualified Data.Text.Encoding as TE
import Query
import Data.Time
import qualified Data.Aeson as A
import Text
import qualified Types.Index as G
import Data.Bifunctor (first)
import Debug.Trace
import Types
import SchemaQuery
import Plugins
import TP.Widgets
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
import Data.Maybe
import Reactive.Threepenny hiding(apply)
import Data.Traversable (traverse)
import qualified Data.List as L
import qualified Data.ByteString.Char8 as BS
import qualified Data.ByteString.Lazy.Char8 as BSL

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
import OAuthClient
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

getClient metainf clientId ccli = G.lookup (G.Idex [(lookKey metainf "clients" "clientid",TB1 (SNumeric (fromInteger clientId)))]) ccli :: Maybe (TBData Key Showable)

deleteClient metainf clientId = do
  (dbmeta ,(_,ccli)) <- transaction metainf $ selectFrom "clients"  Nothing Nothing [] []
  putPatch (patchVar dbmeta) [(tableMeta (lookTable metainf "clients") , [(lookKey metainf "clients" "clientid",TB1 (SNumeric (fromInteger clientId)))],[])]

instance A.ToJSON a => A.ToJSON (FTB a ) where
  toJSON (TB1 i) = A.toJSON i
  toJSON (LeftTB1 i) = fromMaybe (A.toJSON ("" ::String)) (A.toJSON <$> i)

instance A.ToJSON Showable where
  toJSON (SText i ) = A.toJSON i
  toJSON i = A.toJSON (renderPrim i)


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
      tdi = fmap getPKM $ join $ (\inf table -> fmap (tblist' table ) .  traverse (fmap _tb . (\(k,v) -> fmap (Attr k) . readType (keyType $ k) . T.unpack  $ v).  first (lookKey inf (tableName table))  ). F.toList) <$>  inf  <*> table <*> rowpk dbdata
    (dbmeta ,(_,ccli)) <- transaction metainf $ selectFrom "clients"  Nothing Nothing [] []
    editClient metainf inf dbmeta ccli table tdi clientId now
    return (clientId, getClient metainf clientId <$> collectionTid dbmeta)

idex inf t v = G.Idex $ L.sortBy (comparing fst ) $ first (lookKey inf t  ) <$> v

calendarCreate m cal def evs= runFunction $ ffi "$(%1).fullCalendar({header: { left: '',center: 'title' , right: ''},defaultDate: %2,lang: 'pt-br',editable: true,eventLimit: true,events: JSON.parse(%3), defaultView : %4 });" cal def evs m

eventWidget inf body = do
    (_,(_,tmap)) <- liftIO $ transaction (meta inf) $ selectFrom "table_name_translation" Nothing Nothing [] [("=",liftField (meta inf) "table_name_translation" $ uncurry Attr $("schema_name",TB1 $ SText (schemaName inf) ))]
    (evdb,(_,evMap )) <- liftIO $ transaction  (meta inf) $ selectFrom "event" Nothing Nothing [] [("=",liftField (meta inf) "event" $ uncurry Attr $("schema_name",TB1 $ SText (schemaName inf) ))]
    dashes <- mapM (\e -> do
        let t@(Attr _ (TB1 (SText tname))) = lookAttr' (meta inf) "table_name" e

            lookDesc = (\i  -> maybe (T.unpack $ tname)  ((\(Attr _ v) -> renderShowable v). lookAttr' (meta inf)  "translation") $ G.lookup (idex (meta inf) "table_name_translation" [("schema_name" ,txt $ schemaName inf),("table_name",txt tname )]) i ) $ tmap

            (Attr _ (ArrayTB1 efields ))= lookAttr' (meta inf) "event" e
            (Attr _ color )= lookAttr' (meta inf) "color" e

        (evdb,(_,tmap )) <- liftIO $ transaction  inf $ selectFrom tname Nothing Nothing [] []
        let v = F.toList evMap
            convField (Attr _ (IntervalTB1 i )) = [("start", (\(Interval.Finite i) -> i)$ Interval.lowerBound i),("end",(\(Interval.Finite i) -> i)$ Interval.upperBound i)]
            convField (Attr _ v) = [("start",v)]
            projf  r efield@(TB1 (SText field))  = M.fromList $ convField (lookAttr' inf field r) <> [ ("title",TB1 $ SText (T.pack $  L.intercalate "," $ fmap renderShowable $ allKVRec' $  r)) , ("color" , color),("field", efield )] :: M.Map Text (FTB Showable)
            proj r = projf r <$> F.toList efields
        return ((lookDesc,color),filter (isJust . join . fmap unSOptional . M.lookup "start") $concat $ proj <$> G.toList tmap)) ( G.toList evMap)

    iday <- liftIO getCurrentTime
    filterInp <- UI.input # set UI.style [("width","100%")]
    filterInpBh <- stepper "" (UI.valueChange filterInp)
    let allTags =  (fst <$> dashes)
        filterLabel d = (\j ->  L.isInfixOf (toLower <$> j) (toLower <$> d)) <$> filterInpBh
        legendStyle (t,c) b
              =  UI.div
              # set items [UI.div # set items [b], UI.div # set text  t ]
              # sink0 UI.style (mappend [("background-color",renderShowable c),("color","white")]. noneDisplay "-webkit-box" <$> filterLabel t)

    legend <- checkDivSetT  allTags  (pure id) (pure allTags) (\_ -> UI.input # set UI.type_ "checkbox") legendStyle
    let buttonStyle k e = e # set UI.text (fromJust $ M.lookup k transRes)# set UI.class_ "btn-xs btn-default buttonSet"
          where transRes = M.fromList [("month","Mês"),("week","Semana"),("day","Dia")]
        defView = "month"
        viewList = ["month","day","week"] :: [String]
        transMode _ "month" = "month"
        transMode True i = "agenda" <> capitalize i
        transMode False i = "basic" <> capitalize i
        capitalize (i:xs) = toUpper i : xs
        capitalize [] = []

    resolution <- fmap (fromMaybe defView) <$> buttonDivSetT  viewList (pure id) (pure $ Just defView ) (const UI.button)  buttonStyle

    next <- UI.button  # set text ">"
    today <- UI.button # set text "Hoje"
    prev <- UI.button  # set text "<"

    agenda <- mdo
      agenda <- UI.button # sink text ((\b -> if b then "Agenda" else "Basic") <$> agB)
      let agE = pure not <@ UI.click agenda
      agB <- accumB False agE
      return $ TrivialWidget (tidings agB (flip ($) <$> agB <@> agE)) agenda

    current <- UI.div # set children [prev,today,next]
    let
      resRange b "month" d =  d {utctDay = addGregorianMonthsClip (if b then -1 else 1 )  (utctDay d)}
      resRange b "day" d = d {utctDay =addDays (if b then -1 else 1 ) (utctDay d)}
      resRange b "week" d = d {utctDay =addDays (if b then -7 else 7 ) (utctDay d)}
    let currentE = (concatenate <$> unions  [resRange False  <$> facts (triding resolution) <@ UI.click next ,resRange True   <$> facts (triding resolution) <@ UI.click prev , const (const iday) <$> UI.click today ])
    increment <- accumB iday  currentE

    calendar <- UI.div # set UI.class_ "col-xs-10"
    sidebar <- UI.div # set children [getElement agenda,current,getElement resolution,filterInp , getElement legend] #  set UI.class_ "col-xs-2"
    element body # set children [sidebar,calendar]
    let calFun (agenda,iday,res ,selected) = do
            innerCalendar <-UI.div
            element calendar # set children [innerCalendar]
            let

              inRange "day" d (SDate c)=   d == c
              inRange "week" d (SDate c)=    oy == cy && ow == cw
                where
                  (oy,ow,_) = toWeekDate d
                  (cy,cw,_) = toWeekDate c
              inRange "month" d (SDate c)=   oy == cy && od == cd
                where
                  (oy,od,_) = toGregorian d
                  (cy,cd,_) = toGregorian c
              inRange m d (STimestamp c)=   inRange m d (SDate (utctDay (localTimeToUTC utc c)))

            calendarCreate (transMode agenda res) innerCalendar (show iday) (T.unpack $ TE.decodeUtf8 $  BSL.toStrict $ A.encode  (filter (inRange res (utctDay iday ) . unTB1 . fromJust . join . fmap unSOptional. M.lookup "start"  ) $ concat $fmap snd ( filter (flip L.elem (selected) . fst) dashes)))
            return ()
    calFun (False,iday,defView, allTags)
    onEvent (rumors $ (,,,) <$> triding agenda <*> tidings increment (flip ($) <$> increment <@> currentE) <*>(triding resolution) <*> (triding legend)) calFun
    return body


txt = TB1 . SText

setup
     ::  MVar (M.Map Text  InformationSchema) ->  [String] -> Window -> UI ()
setup smvar args w = void $ do
  metainf <- justError "no meta" . M.lookup "metadata" <$> liftIO ( readMVar smvar)
  let bstate = argsToState args
  let amap = authMap smvar bstate (user bstate , pass bstate)
  inf <- liftIO$ traverse (\i -> loadSchema smvar (T.pack i) (conn metainf) (user bstate)  amap ) $ schema  bstate
  (cli,cliTid) <- liftIO $ addClient (sToken w ) metainf inf ((\t inf -> lookTable inf . T.pack $ t) <$> tablename bstate  <*> inf  ) bstate
  (evDB,chooserItens) <- databaseChooser smvar metainf bstate
  body <- UI.div
  return w # set title (host bstate <> " - " <>  dbn bstate)
  hoverBoard<-UI.div # set UI.style [("float","left"),("height","100vh"),("width","15px")]
  let he = const True <$> UI.hover hoverBoard
  bhe <-stepper True he
  menu <- checkedWidget (tidings bhe he)
  nav  <- buttonDivSet  ["Event","Browser","Poll","Stats","Change","Exception"] (pure $ Just "Browser" )(\i -> UI.button # set UI.text i # set UI.class_ "buttonSet btn-xs btn-default pull-right")
  element nav # set UI.class_ "col-xs-5"
  chooserDiv <- UI.div # set children  ([getElement menu] <> chooserItens <> [getElement nav ] ) # set UI.class_ "row" # set UI.style [("display","flex"),("align-items","flex-end"),("height","7vh"),("width","100%")]
  container <- UI.div # set children [chooserDiv , body] # set UI.class_ "container-fluid"
  getBody w #+ [element hoverBoard,element container]

  mapUITEvent body (traverse (\(nav,inf)->
      case nav of
        "Event" -> do
            eventWidget inf body
        "Poll" -> do
            element body #
              set items
                  [ metaAllTableIndexV inf "polling" [("schema_name",TB1 $ SText (schemaName inf) ) ]
                  , metaAllTableIndexV inf "polling_log" [("schema_name",TB1 $ SText (schemaName inf) ) ]] #
              set UI.class_ "row"
        "Change" -> do
            case schemaName inf of
              "gmail" -> do
                b <- UI.button # set text "sync"
                (dbvar,(m,t))  <- liftIO$ transaction inf $ selectFrom "history" Nothing Nothing [] []
                itemListEl <- UI.select # set UI.class_ "col-xs-9" # set UI.style [("width","70%"),("height","350px")] # set UI.size "20"
                itemListEl2 <- UI.select # set UI.class_ "col-xs-9" # set UI.style [("width","70%"),("height","350px")] # set UI.size "20"
                do
                  ((DBVar2 tmvard _  vpdiff _ _ ),res) <- liftIO$ transaction inf $ syncFrom (lookTable inf "history") Nothing Nothing [] []
                  let update = F.foldl'(flip (\p-> fmap (flip apply p)))
                  bres <- accumB ((M.empty,G.empty) :: Collection Key Showable) (flip update <$> rumors vpdiff)
                  let
                    vpt =  tidings bres (  update <$> bres <@> rumors vpdiff )
                  --listBoxEl itemListEl (concat . fmap (runReader (dynPK readHistory $ () ) . Just . mapKey' keyValue) . G.toList . snd  <$> vpt)  (pure Nothing) (pure id) ( pure (\i j -> UI.div # set text (show i)))
                  listBoxEl itemListEl2 ( G.toList . snd  <$> vpt)  (pure Nothing) (pure id) ( pure attrLine )
                element body # set children [itemListEl,itemListEl2]




              i -> do
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
            [tbChooser,subnet] <- chooserTable  inf   cliTid  cli
            element tbChooser # sink0 UI.style (facts $ noneShow <$> triding menu)
            let
                expand True = "col-xs-10"
                expand False = "col-xs-12"
            element subnet # sink0 UI.class_ (facts $ expand <$> triding menu)
            element body # set UI.children [tbChooser,subnet]# set UI.class_ "row" # set UI.style [("display","inline-flex"),("width","100%")] )) $ liftA2 (\i  -> fmap (i,)) (triding nav)  evDB


listDBS ::  InformationSchema -> BrowserState -> IO (Tidings (Text,[Text]))
listDBS metainf dname = do
  map <- (\db -> do
        (dbvar ,(_,schemasTB)) <- transaction metainf $  selectFrom "schema" Nothing Nothing [] []
        let schemas schemaTB = fmap ((\(Attr _ (TB1 (SText s)) ) -> s) .lookAttr' metainf "name") $ F.toList  schemasTB
        return ( (db,).schemas  <$> collectionTid dbvar)) (T.pack $ dbn dname)
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
              (dbmeta ,_) <- transaction metainf $ selectFrom "google_auth" Nothing Nothing []   [("=",liftField metainf "google_auth" $ Attr "username" (TB1 $ SText  $ T.pack user ))]
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
  let dbsInit = fmap (\s -> (T.pack $ dbn sargs ,T.pack s) ) $ ( schema sargs)
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
  authBox <- UI.div # sink items (maybeToList . fmap genSchema <$> facts dbsWT) # set UI.class_ "col-xs-5" # set UI.style [("border", "gray solid 2px")]
  let auth = authMap smvar sargs (user sargs ,pass sargs )
  inf <- traverse (\i -> liftIO $loadSchema smvar (T.pack i ) (rootconn metainf) (user sargs) auth) (schema sargs)
  chooserB  <- stepper inf schemaE
  let chooserT = tidings chooserB schemaE
  schemaSel <- UI.div # set UI.class_ "col-xs-2" # set children [ schemaEl , getElement dbsW]
  return $ (chooserT,[schemaSel ]<>  [authBox] )


attrLine i   = do
  line ( L.intercalate "," (fmap renderShowable .  allKVRec'  $ i))

lookAttr' inf k (i,m) = unTB $ err $  M.lookup (S.singleton (Inline (lookKey inf (_kvname i) k))) (unKV m)
    where
      err= justError ("no attr " <> show k <> " for table " <> show (_kvname i))

chooserTable inf cliTid cli = do
  iv   <- currentValue (facts cliTid)
  let lookT iv = let  i = unLeftItens $ lookAttr' (meta inf)  "table" iv
                in fmap (\(Attr _ (TB1 (SText t))) -> t) i
  let initKey = pure . join $ fmap (S.fromList .rawPK) . flip M.lookup (_tableMapL inf) <$> join (lookT <$> iv)
      kitems = M.keys (pkMap inf)
  filterInp <- UI.input # set UI.style [("width","100%")]
  filterInpBh <- stepper "" (UI.valueChange filterInp)
  -- Load Metadata Tables
  (orddb ,(_,orderMap)) <- liftIO $ transaction  (meta inf) $ selectFrom "ordering"  Nothing Nothing [] [("=",liftField (meta inf) "ordering" $ uncurry Attr $("schema_name",TB1 $ SText (schemaName inf) ))]
  (translation,_) <- liftIO $ transaction (meta inf) $ selectFrom "table_name_translation" Nothing Nothing [] [("=",liftField (meta inf) "table_name_translation" $ uncurry Attr $("schema_name",TB1 $ SText (schemaName inf) ))]
  (authorization,_) <- liftIO$ transaction (meta inf) $ selectFrom "authorization" Nothing Nothing [] [("=",liftField (meta inf) "authorization" $ uncurry Attr $("grantee",TB1 $ SText (username inf) )), ("=",liftField (meta inf) "authorization" $ uncurry Attr $("table_schema",TB1 $ SText (schemaName inf) ))]

  let selTable = join . fmap (flip M.lookup (pkMap inf) )
      lookDesc = (\i j -> maybe (T.unpack $ maybe "" rawName j)  ((\(Attr _ v) -> renderShowable v). lookAttr' (meta inf)  "translation") $ G.lookup (idex (meta inf) "table_name_translation" [("schema_name" ,TB1 $ SText $ schemaName inf),("table_name",TB1 $ SText (maybe ""  tableName j))]) i ) <$> collectionTid translation
      authorize =  (\autho t -> isJust $ G.lookup (idex  (meta inf) "authorization"  [("table_schema", TB1 $ SText (schemaName inf) ),("table_name",TB1 $ SText $ tableName t),("grantee",TB1 $ SText $ username inf)]) autho)  <$> collectionTid authorization
  let
      filterLabel = (\j d -> (\i -> L.isInfixOf (toLower <$> j) (toLower <$> d (Just i)) ))<$> filterInpBh <*> facts lookDesc
      tableUsage orderMap table = maybe (Right 0) (Left ) . fmap (lookAttr' (meta inf)  "usage" ) $  G.lookup  (G.Idex ( pk )) orderMap
          where  pk = L.sortBy (comparing fst ) $ first (lookKey (meta inf ) "ordering") <$> [("table_name",TB1 . SText . rawName $ table ), ("schema_name",TB1 $ SText (schemaName inf))]
      buttonStyle k e = e # sink UI.text (facts $ lookDesc  <*> pure (selTable $ Just k)) # set UI.style [("width","100%")] # set UI.class_ "btn-xs btn-default buttonSet" # sink UI.style (noneShow  <$> visible)
        where tb =  justLook   k (pkMap inf)
              visible  = (\i j -> i tb && j tb  ) <$> filterLabel <*> facts authorize


  bset <- buttonDivSetT (L.sortBy (flip $ comparing (tableUsage orderMap . flip justLook   (pkMap inf))) kitems) ((\i j -> tableUsage i ( justLook   j (pkMap inf) )) <$> collectionTid orddb ) initKey  (\k -> UI.button  ) buttonStyle
  let bBset = triding bset
      ordRow pkset orderMap =  field
          where
            field =  G.lookup  (G.Idex  pk ) orderMap
            pk = L.sortBy (comparing fst ) $ first (lookKey (meta inf ) "ordering") <$>[("table_name",TB1 . SText . rawName $ justLook   pkset (pkMap inf) ), ("schema_name",TB1 $ SText (schemaName inf))]
      incClick field =  (fst field , getPKM field ,[patch $ fmap (+ (SNumeric 1)) (usage )]) :: TBIdx Key Showable
          where
                 usage = lookAttr' (meta inf ) "usage"   field
  liftIO$ onEventIO ((\i j -> incClick <$> join ( flip ordRow i <$> j)) <$> facts (collectionTid orddb) <@> rumors bBset)
    (traverse (\p -> do
      _ <- transaction (meta inf ) $ patchFrom  p
      putPatch (patchVar orddb) [p] ))

  tbChooserI <- UI.div # set children [filterInp,getElement bset]  # set UI.style [("height","90vh"),("overflow","auto"),("height","99%")]
  tbChooser <- UI.div # set UI.class_ "col-xs-2"# set UI.style [("height","90vh"),("overflow","hidden")] # set children [tbChooserI]
  nav  <- buttonDivSet ["Viewer","Browser","Exception","Change"] (pure $ Just "Browser")(\i -> UI.button # set UI.text i # set UI.style [("font-size","smaller")]. set UI.class_ "buttonSet btn-xs btn-default pull-right")
  element nav # set UI.class_ "col-xs-5"
  header <- UI.h1 # sink text (facts $ lookDesc <*>(selTable  <$> bBset)) # set UI.class_ "col-xs-7"
  chooserDiv <- UI.div # set children  [header ,getElement nav]  # set UI.style [("display","flex"),("align-items","flex-end")]
  body <- UI.div

  el <- mapUITEvent body (maybe UI.div (\(nav,table)->
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
            let buttonStyle k e = e # sink UI.text (facts $ lookDesc  <*> pure (Just k)) # set UI.class_ "btn-xs btn-default buttonSet" # sink UI.style (noneShowSpan . ($k) <$> filterLabel)
                tableK = justLook table (pkMap inf)
            prebset <- buttonDivSetT (L.sortBy (flip $ comparing (tableUsage orderMap )) (tableK : (rawUnion tableK ))) (tableUsage <$> collectionTid orddb ) (pure (Just tableK)) (\k -> UI.button  ) buttonStyle
            els <- UI.div
            span <- mapUITEvent body (maybe UI.div  (\t -> viewerKey inf t cli cliTid)) (triding prebset)
            element els # sink UI.children (pure <$> facts span)
            element prebset  # set UI.style (noneShow . not $ L.null (rawUnion tableK))
            element body # set UI.children [getElement prebset,els]
        "Viewer" -> do
            span <- viewer inf (justLook table (pkMap inf)) Nothing
            element body # set UI.children [span]
        "Stats" -> do
            span <- viewer inf (justError "no table with pk" $ M.lookup table (pkMap inf)) Nothing
            element body # set UI.children [span]
        )) $ liftA2 (\i j -> (i,) <$> j)  (triding nav) bBset
  subnet <- UI.div # set children [chooserDiv,body] # set UI.style [("height","90vh"),("overflow","auto")]
  return [tbChooser, subnet ]

viewerKey
  ::
      InformationSchema -> Table -> Integer -> Tidings  (Maybe (TBData Key Showable)) -> UI Element
viewerKey inf table cli cliTid = mdo
  iv   <- currentValue (facts cliTid)
  let lookT iv = let  i = unLeftItens $ lookAttr' (meta inf)  "table" iv
                in fmap (\(Attr _ (TB1 (SText t))) -> t) i
      lookPK iv = let  i = unLeftItens $ lookAttr' (meta inf)  "data_index" iv
                       unKey t = liftA2 (,) ((\(Attr _ (TB1 (SText i)))-> flip (lookKey inf ) i <$> lookT iv ) $ lookAttr' (meta inf)  "key" t  )( pure $ (\(Attr _ (TB1 (SDynamic i)))-> i) $ lookAttr'  (meta inf)  "val" t )
                in fmap (\(IT _ (ArrayTB1 t)) -> catMaybes $ F.toList $ fmap (unKey.unTB1) t) i
  let
  reftb@(vpt,vp,_ ,var ) <- refTables inf table

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
  let
     filteringPred i = (T.isInfixOf (T.pack $ toLower <$> i) . T.toLower . T.intercalate "," . fmap (T.pack . renderPrim ) . F.toList  .snd )
     tsort = sorting' . filterOrd <$> triding sortList
     filtering res = (\t -> fmap (filter (filteringPred t )) )<$> filterInpT  <*> res
     pageSize = 20
     lengthPage (fixmap,i) = (s  `div` pageSize) +  if s `mod` pageSize /= 0 then 1 else 0
        where (s,_)  = fromMaybe (sum $ fmap fst $ F.toList fixmap ,M.empty ) $ M.lookup [] fixmap
  inisort <- currentValue (facts tsort)
  itemListEl <- UI.select # set UI.class_ "col-xs-9" # set UI.style [("width","70%"),("height","350px")] # set UI.size "20"
  let wheel = negate <$> mousewheel itemListEl
  (offset,res3)<- mdo
    offset <- offsetField (pure 0) wheel  (lengthPage <$> facts res3)
    res3 <- mapT0Event (fmap inisort (fmap G.toList vp)) return ( (\f i -> fmap f i)<$> tsort <*> (filtering $ fmap (fmap G.toList) $ tidings ( res2) ( rumors vpt) ) )
    return (offset, res3)
  onEvent (rumors $ triding offset) $ (\i ->  liftIO $ do
    print ("page",(i `div` 10 )   )
    transaction inf $ eventTable  table  (Just $ i `div` 10) Nothing  [] [])
  let
    paging  = (\o -> fmap (L.take pageSize . L.drop (o*pageSize)) ) <$> triding offset
  page <- currentValue (facts paging)
  res4 <- mapT0Event (page $ fmap inisort (fmap G.toList vp)) return (paging <*> res3)
  itemList <- listBoxEl itemListEl (fmap snd res4) (tidings st sel ) (pure id) ( pure attrLine )
  let evsel =  unionWith const (rumors (triding itemList)) (rumors tdi)
  (dbmeta ,(_,_)) <- liftIO$ transaction (meta inf) $ selectFrom "clients"  Nothing Nothing [] (fmap (liftField (meta inf) "clients") <$> [("=",  uncurry Attr $("schema",LeftTB1 $ Just $TB1 $ SText (schemaName inf) )), ("=",Attr "table" $ LeftTB1 $ Just $ TB1 $ SText (tableName table))])
  liftIO $ onEventIO ((,) <$> facts (collectionTid dbmeta ) <@> evsel ) (\(ccli ,i) -> void . editClient (meta inf) (Just inf) dbmeta  ccli (Just table ) (getPKM <$> i) cli =<< getCurrentTime )
  prop <- stepper cv evsel
  let tds = tidings prop (diffEvent  prop evsel)

  (cru,ediff,pretdi) <- crudUITable inf (pure "Editor")  reftb [] [] (allRec' (tableMap inf) table) (tds)
  diffUp <-  mapEvent (fmap pure)  $ (\i j -> traverse (return . flip apply j ) i) <$> facts pretdi <@> ediff
  let
     sel = filterJust $ fmap (safeHead . concat) $ unions $ [(unions  [rumors  $triding itemList  ,rumors tdi]),diffUp]
  st <- stepper cv sel
  res2 <- stepper (vp) (rumors vpt)
  onEvent (pure <$> ediff) (liftIO .  putPatch var )
  title <- UI.h4  #  sink text ( maybe "" (L.intercalate "," . fmap (renderShowable .snd) . F.toList . getPK. TB1 )  <$> facts tds) # set UI.class_ "col-xs-8"
  insertDiv <- UI.div # set children [title,head cru] # set UI.class_ "row"
  insertDivBody <- UI.div # set children [insertDiv,last cru]# set UI.class_ "row"
  itemSel <- UI.ul # set items ((\i -> UI.li # set children [ i]) <$> [getElement offset ,filterInp ,getElement sortList,getElement asc] ) # set UI.class_ "col-xs-3"
  itemSelec <- UI.div # set children [getElement itemList, itemSel] # set UI.class_ "row"
  UI.div # set children ([itemSelec,insertDivBody ] )



