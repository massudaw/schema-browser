{-# LANGUAGE TupleSections,OverloadedStrings #-}
module OAuth where
import Control.Monad (unless)
import System.Info (os)
import System.Process (system, rawSystem)
import System.Exit    (ExitCode(..))
import System.Directory (doesFileExist)
import Network.Google.OAuth2 (formUrl, exchangeCode, refreshTokens,
                              OAuth2Client(..), OAuth2Tokens(..))
import Network.Google (toAccessToken,makeRequest, doRequest)
import Network.Google.Contacts(listContacts)
import Network.HTTP.Conduit  hiding (host)-- (httpLbs,parseUrl,withManager,responseBody,(..))
import Control.Lens hiding (get,delete,set,(#),element,children)
import Control.Applicative
import qualified Data.Set as S
import qualified Data.Foldable as F
import Control.Monad.IO.Class
import Data.Monoid
import Control.Concurrent
import Data.Unique
import Data.Maybe
import System.Environment
import Query
import Data.Aeson.Lens
import Schema
import Postgresql
import qualified Data.Text.Lazy as T
import qualified Data.Text as TS
import Data.Text.Lazy (Text)
import Text.XML.Light.Types
import Text.XML.Light.Proc
import Data.Aeson
import qualified Data.Vector as V
import Safe
import Utils
import Patch

import Types
import Data.IORef
import RuntimeTypes
import Control.Monad
import qualified Data.Map as M
import qualified Data.ByteString.Lazy.Char8 as BL
import Debug.Trace
import SchemaQuery
import qualified Graphics.UI.Threepenny as UI
import Graphics.UI.Threepenny.Core
import TP.Widgets
import TP.QueryWidgets
import TP.Browser
import Data.List (find,intercalate)

--
file   = "./tokens.txt"
--

{-
pluginContact inf = do
  v <- liftIO $ pluginContactGoogle
  let project l = (emails l :  phones l : names l )
        where
          names = catMaybes . concat . maybeToList .   fmap (projectContact inf ) . filterChildName ((=="name").qName)
          emails = projectEmail inf . filterChildrenName ((=="email").qName)

          phones = projectPhone inf  . filterChildrenName ((=="phoneNumber").qName)
  return $ project <$> (filterChildrenName ((=="entry") . qName) v)
-}

gmailScope = "https://www.googleapis.com/auth/gmail.modify"

pluginContactGoogle = do
  Just cid <- lookupEnv "CLIENT_ID"
  Just secret <- lookupEnv "CLIENT_SECRET"
  -- Ask for permission to read/write your fusion tables:
  let client = OAuth2Client { clientId = cid, clientSecret = secret }
      permissionUrl = formUrl client ["https://www.googleapis.com/auth/gmail.readonly",gmailScope]
  b <- doesFileExist file
  unless b $ do
      putStrLn$ "Load this URL: "++show permissionUrl
      case os of
        "linux"  -> rawSystem "chromium" [permissionUrl]
        "darwin" -> rawSystem "open"       [permissionUrl]
        _        -> return ExitSuccess
      putStrLn "Please paste the verification code: "
      authcode <- getLine
      tokens   <- exchangeCode client authcode
      putStrLn $ "Received access token: " ++ show (accessToken tokens)
      tokens2  <- refreshTokens client tokens
      putStrLn $ "As a test, refreshed token: " ++ show (accessToken tokens2)
      writeFile file (show tokens2)
  accessTok <- fmap read (readFile file)
  tokenRef <- newIORef accessTok
  forkIO $ do
    tokens <- readIORef tokenRef
    putStrLn $ "Try refresh token" <> show (accessToken tokens)
    tokens2 <- refreshTokens client  tokens
    putStrLn $ "Refreshed token" <> show (accessToken tokens2)
    writeFile file (show tokens2)
    writeIORef tokenRef tokens2
    threadDelay (1000*1000*60*10)

  gsch <- gmailSchema  tokenRef
  m:args <- getArgs
  startGUI (defaultConfig { tpStatic = Just "static", tpCustomHTML = Just "index.html" , tpPort = fmap read $ safeHead args })  (setupOAuth  gsch $ tail args)

listTable inf table = do
  tok <- readIORef (fromJust $ token inf)
  c <- return . fmap (convertAttrs table ) . maybe [] (\i -> (i :: Value) ^.. key ( T.toStrict $ rawName table ) . values) . decode =<< simpleHttpHeader [("GData-Version","3.0")] ("https://www.googleapis.com/gmail/v1/users/"<> T.unpack (username inf ) <> "/" <> T.unpack (rawName table ) <> "?access_token=" ++ ( accessToken tok ))
  --fmap catMaybes $ mapM (getTable inf table . getPK) (take 5 c)
  return  c

getTable inf table pk = do
  tok <- readIORef (fromJust $ token inf)
  c <- return . fmap (traceShowId . convertAttrs table .traceShowId ) . fmap (\i -> (i :: Value)  ) . decode =<< simpleHttpHeader [("GData-Version","3.0")] (traceShowId $ "https://www.googleapis.com/gmail/v1/users/"<> T.unpack (username inf ) <> "/" <> T.unpack (rawName table ) <> "/" <>  intercalate "," ( renderShowable . snd <$> pk ) <> "?access_token=" ++ ( accessToken tok))
  return $  c

getDiffTable inf table  j = fmap (join . fmap (difftable j. unTB1) ) $ getTable  inf table . getPK $ TB1 j

setupOAuth
      :: InformationSchema -> [String] -> Window -> UI ()
setupOAuth  gsch args w = void $ do
  let bstate = argsToState args
  body <- UI.div
  return w # set title (host bstate <> " - " <>  dbn bstate)
  nav  <- buttonDivSet  ["Nav","Change","Exception"] (pure $ Just "Nav" )(\i -> UI.button # set UI.text i # set UI.class_ "buttonSet btn-xs btn-default pull-right")
  element nav # set UI.class_ "col-xs-5"
  chooserDiv <- UI.div # set children  ([ getElement nav ] ) # set UI.class_ "row" # set UI.style [("display","flex"),("align-items","flex-end")]
  container <- UI.div # set children [chooserDiv , body] # set UI.class_ "container-fluid"
  getBody w #+ [element container]
  (traverse (\inf -> liftIO$ swapMVar  (mvarMap inf) M.empty)) (Just gsch )
  mapUITEvent body (traverse (\(nav,inf)->
      case nav of
        "Change" -> do
            dash <- dashBoardAll inf
            element body # set UI.children [dash] # set UI.class_ "row"
        "Exception" -> do
            dash <- exceptionAll inf
            element body # set UI.children [dash] # set UI.class_ "row"
        "Nav" -> do
            let k = M.keys  (pkMap inf )
            span <- chooserTable  inf ([])  k (tablename bstate)
            element body # set UI.children [span]# set UI.class_ "row"  )) $ liftA2 (\i -> fmap (i,)) (triding nav) (pure $ Just gsch)



gmailSchema  token = do
  mvar <- newMVar M.empty
  tbs <- sequence [messages,threads,labels,drafts]
  let
    tmap = (M.fromList $ (\i -> (tableName i,i) ) <$> tbs  )
    keyMap = M.fromList $ concat  $ fmap (\t -> fmap (\k -> ((tableName t, keyValue k),k)) $ F.toList (rawAttrs t)) (F.toList tmap)
    pks = M.fromList $ fmap (\(_,t)-> (rawPK t ,t)) $ M.toList tmap
    i2 =  M.filterWithKey (\k _ -> not.S.null $ k )  pks
  return $ InformationSchema "gmail"  "wesley.massuda@gmail.com" (Just token) keyMap (traceShowId i2) tmap M.empty M.empty  mvar (error "no conn") (error "no conn")Nothing (SchemaEditor undefined undefined undefined listTable getDiffTable )

genKey k un =  Key n Nothing 0 Nothing  un (( fuType (T.unpack fu )) (if T.length ty > 0 then  ty else "text"))
  where (n,tyfu) = T.break (':'==) k
        (ty,fu') = T.break(':'==) (safeTail tyfu)
        fu = safeTail fu'
        fuType ('[':']':xs) i = KArray (fuType xs i )
        fuType ('*':xs) i = KOptional (fuType xs i)
        fuType ("") i = Primitive i
        safeTail i
          | T.null i = ""
          | otherwise = T.tail i



genTable t pk desc l  = do
    keys <- mapM (\l -> genKey l <$> newUnique) l
    return $ (mapTableK (\k -> fromJust $ find ((==k).keyValue) keys) ( Raw "gmail" ReadWrite Nothing S.empty t [] [] (S.singleton pk) desc S.empty S.empty))  {rawAttrs = S.fromList keys}

messages = genTable "messages" "id"  [] ["id","threadId","labelIds:text:[]","snippet","historyId:bigint","internalDate:integer","sizeEstimate:integer:*"]
payload = genTable "message_payload" "partId" [] ["partId","mimeType","filename","headers","body","parts:"]
labels = genTable "labels" "id"  ["name"] ["id","name","messageListVisibility","labelListVisibility","type"]
threads = genTable "threads" "id"  ["snippet"] ["id","historyId","snippet"]
-- history = genTable "history" "id"  [] ["id"]
drafts = genTable "drafts" "id"  [] ["id","message"]



convertAttrs :: Table -> Value -> TB2 Key Showable
convertAttrs  tb i =   tblist' tb $  Compose . Identity <$> catMaybes (kid <$> S.toList (rawAttrs tb))
  where
    kid  k =  fmap (Types.Attr k ). funO  (keyType k) $ (i ^? ( key (T.toStrict $ keyValue k))  )
    fun (Primitive i) v = join $ fmap TB1 . readPrim (textToPrim i) . TS.unpack <$> (v ^? _String)
    fun (KArray i) v = Just . ArrayTB1. fmap (fromJust . fun i) $ (v ^.. values )
    funO (KOptional i) v = Just . maybe (LeftTB1 Nothing) LeftTB1 . fmap ( fun i) $ v
    funO i v = join $ fmap (fun i) v


convertPK :: Table -> Value -> TB2 Key Showable
convertPK tb i =   tblist' tb $  Compose . Identity <$> catMaybes (kid <$> S.toList (rawPK tb))
  where
    kid  k =  fmap (Types.Attr k ). funO  (keyType k) $ (i ^? ( key (T.toStrict $ keyValue k))  )
    fun (Primitive i) v = join $ fmap TB1 . readPrim (textToPrim i) . TS.unpack <$> (v ^? _String)
    fun (KArray i) v = Just . ArrayTB1. fmap (fromJust . fun i) $ (v ^.. values )
    funO (KOptional i) v = Just . maybe (LeftTB1 Nothing) LeftTB1 . fmap ( fun i) $ v
    funO i v = join $ fmap (fun i) v




-- simpleHttp' :: MonadIO m => (HeaderName,BL.ByteString) -> String -> m BL.ByteString
simpleHttpHeader headers url = liftIO $ withManager $ \man -> do
      req <- liftIO $ parseUrl url
      responseBody <$> httpLbs (setConnectionClose headers req) man


-- setConnectionClose :: Request m -> Request m
setConnectionClose h req = req{requestHeaders = ("Connection", "close") : (h ++ requestHeaders req)}
