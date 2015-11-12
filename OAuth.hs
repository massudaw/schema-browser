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
import Network.HTTP.Conduit  hiding (port,host)-- (httpLbs,parseUrl,withManager,responseBody,(..))
import Control.Lens hiding (get,delete,set,(#),element,children)
import Control.Applicative
import qualified Data.Set as S
import qualified Data.Foldable as F
import Control.Monad.IO.Class
import Data.Monoid
import Data.Biapplicative
import Patch
import Control.Monad.Writer hiding (pass)
import System.Time.Extra
import GHC.Stack
import Data.String
import Control.Concurrent
import Data.Unique
import Data.Maybe
import System.Environment
import Query
import Data.Aeson.Lens
import Schema
import Postgresql
import qualified Data.Text as T
import qualified Data.Text as TS
import Data.Text (Text)
import Text.XML.Light.Types
import Text.XML.Light.Proc
import Data.Aeson
import qualified Data.Vector as V
import Safe
import Utils
import Patch
import Database.PostgreSQL.Simple

import Types
import Data.IORef
import RuntimeTypes
import Control.Monad
import qualified Data.Map as M
import Debug.Trace
import SchemaQuery
import qualified Graphics.UI.Threepenny as UI
import Graphics.UI.Threepenny.Core
import TP.Widgets
import TP.QueryWidgets
import Data.List (null,find,intercalate)

--
file   = "./tokens.txt"
--

gmailScope = "https://www.googleapis.com/auth/gmail.modify"

oauthpoller = do
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
  forkIO $ forever $ do
    tokens <- readIORef tokenRef
    putStrLn $ "Try refresh token" <> show (accessToken tokens)
    tokens2 <- refreshTokens client  tokens
    putStrLn $ "Refreshed token" <> show (accessToken tokens2)
    writeFile file (show tokens2)
    writeIORef tokenRef tokens2
    threadDelay (1000*1000*60*10)
  return tokenRef



listTable inf table page maxResults= do
  tok <- liftIO$ readIORef (snd $fromJust $ token inf)
  let user = fst $ fromJust $ token inf
  decoded <- liftIO $ do
      (t,d) <- duration $ decode <$> simpleHttpHeader [("GData-Version","3.0")] (traceShowId $ "https://www.googleapis.com/gmail/v1/users/"<> T.unpack user <> "/" <> T.unpack (rawName table ) <> "?" <> maybe "" (\(NextToken s) -> "pageToken=" <> T.unpack s <> "&") page  <> maybe "" (\i -> "maxResults=" <> show i <> "&") maxResults <> "access_token=" ++ ( accessToken tok ))
      print ("list",table,t)
      return  d
  c <-  traverse (convertAttrs inf (tableMap inf) table ) . maybe [] (\i -> (i :: Value) ^.. key (  rawName table ) . values) $ decoded
  return (c, fmap (NextToken ) $ fromJust decoded ^? key "nextPageToken" . _String , {-length c +-} (maybe (length c) round $ fromJust decoded ^? key "resultSizeEstimate" . _Number))

getKeyAttr (TB1 (m, k)) = (concat (fmap keyattr $ F.toList $  (  _kvvalues (runIdentity $ getCompose k))))

getTable inf  tb pk
  | S.fromList (fmap _relOrigin (getKeyAttr pk) ) ==  S.fromList (S.toList (rawPK tb <> rawAttrs tb) <> rawDescription tb ) = return Nothing
  | otherwise = do
    tok <- liftIO $readIORef (snd $ fromJust $ token inf)
    let user = fst $ fromJust $ token inf
    decoded <- liftIO $ do
        (t,v) <- duration (simpleHttpHeader [("GData-Version","3.0")] (traceShowId $ "https://www.googleapis.com/gmail/v1/users/"<> T.unpack user <> "/" <> T.unpack (rawName tb ) <> "/" <>  intercalate "," ( renderShowable . snd <$> getPK pk ) <> "?access_token=" ++ ( accessToken tok)))
        print ("get",tb,getPK pk,t)
        return $ decode v
    traverse (convertAttrs inf (tableMap inf) tb ) . fmap (\i -> (i :: Value)  ) $  decoded

getDiffTable inf table  j = fmap (join . fmap (difftable j. unTB1) ) $ getTable  inf table $ TB1 j


gmailOps = (SchemaEditor undefined undefined undefined listTable getDiffTable )

lbackRef (ArrayTB1 t) = ArrayTB1 $ fmap lbackRef t
lbackRef (LeftTB1 t ) = LeftTB1 $ fmap lbackRef t
lbackRef (TB1 t) = snd $ Types.head $ getPK  (TB1 t)

convertAttrs :: InformationSchema -> M.Map Text Table ->  Table -> Value -> TransactionM (TB2 Key Showable)
convertAttrs  infsch inf tb iv =   tblist' tb .  fmap _tb  . catMaybes <$> (traverse kid (S.toList (rawPK tb <> rawAttrs tb) <> rawDescription tb ))
  where
    pathOrigin (Path i _ _ ) = i
    isFKJoinTable (Path _ (FKJoinTable _ _ _) i) = True
    isFKJoinTable _ = False
    kid :: Key -> TransactionM (Maybe (TB Identity Key Showable))
    kid  k
      | S.member k (S.unions $ map pathOrigin $ filter isFKJoinTable $ F.toList $rawFKS tb)
            = let
               fks = justError "" (find ((== S.singleton k). pathOrigin) (F.toList (rawFKS tb)))
               (FKJoinTable _ _ trefname ) = pathRel fks
               fk =  F.toList $  pathRelRel fks
               exchange tname (KArray i)  = KArray (exchange tname i)
               exchange tname (KOptional i)  = KOptional (exchange tname i)
               exchange tname (Primitive i) = InlineTable "gmail" tname
               patt = either
                    (traverse (\v -> do
                        tell (TableModification Nothing (lookTable infsch trefname ) . patchTB1 <$> F.toList v)
                        return $ FKT [Compose .Identity . Types.Attr  k $ (lbackRef    v) ]  fk v))
                    (traverse (\v -> do
                            let ref = [Compose .Identity . Types.Attr  k $ v ]
                            tbs <- liftIO $ runDBM infsch (atTable (tableMeta $ lookTable infsch trefname))
                            return $ FKT ref fk (joinRel fk (fmap unTB ref) tbs) ))

                        -- return $ FKT [Compose .Identity . Types.Attr  k $ v ] fk (ArrayTB1 [] )) )
               funL = funO  (exchange trefname $ keyType k) $   (iv  ^? ( key (keyValue  k ))  )
               funR = funO  (keyType k) $   (iv  ^? ( key (keyValue  k ))  )
               mergeFun = do
                          (l,r) <- liftA2 (,) funL funR
                          return $ case (l,r) of
                            (Left (Just i),Right j) -> Left (Just i)
                            (Left i ,j ) -> j
              in  join . fmap  patt $  mergeFun
      | otherwise =  fmap (either ((\v-> IT (_tb $ Types.Attr k (fmap (const ()) v)) v)  <$> ) (Types.Attr k<$>) ) . funO  ( keyType k)  $ (iv ^? ( key ( keyValue k))  )

    fun :: KType Text -> Value -> TransactionM (Either (Maybe (TB2 Key Showable)) (Maybe (FTB Showable)))
    fun (Primitive i) v = return $ Right $ fmap TB1 $ join $
        case textToPrim i of
          PText -> readPrim (textToPrim i) . T.unpack <$> (v ^? _String)
          PInt -> Just . SNumeric . round <$> (v ^? _Number)
          PDouble -> Just . SDouble . realToFrac  <$> (v ^? _Number)
          PBinary -> readPrim (textToPrim i) . T.unpack  <$> (v ^? _String)
    fun (KArray i) v = (\l -> if null l then return (typ i) else fmap (bimap  nullArr  nullArr) .   biTrav (fun i) $ l ) $ (v ^.. values )
        where nullArr lm = if null l then Nothing else Just (ArrayTB1 l)
                where l = catMaybes lm
    fun (InlineTable i  m ) v = Left . tbNull <$>  convertAttrs infsch inf   (justError "no look" $  M.lookup m inf ) v
        where  tbNull tb = if null (getAttr' tb) then Nothing else Just  tb
    fun (KEither i  m ) v = Left . tbNull <$>  convertAttrs infsch inf   (justError "no look" $  M.lookup m inf ) v
        where  tbNull tb = if null (getAttr' tb) then Nothing else Just  tb
    fun i v = errorWithStackTrace (show (i,v))

    funO ::  KType Text -> Maybe Value -> TransactionM (Either (Maybe (TB2 Key Showable)) (Maybe (FTB Showable)))
    funO (KOptional i) v =  fmap (bimap (Just . LeftTB1) (Just . LeftTB1)) . maybe (return $ typ i) (fun i) $ v
    funO i v = maybe (return $typ i) (fun i) v

    typ (KArray i ) = typ i
    typ (Primitive _ ) = Right Nothing
    typ (InlineTable _ _ ) = Left Nothing
    typ (KEither _ _ ) = Left Nothing


instance Biapplicative Either where
  Right f  <<*>> Right g  = Right $ f  g
  Left f  <<*>> Left g  = Left $ f  g

-- biTravM f (Just x) = bimap pure pure  (f x)

biTrav :: Applicative m => (c -> m (Either a b) ) -> [c] -> m (Either [a] [b])
biTrav f (x:[]) = bimap (pure) (pure)  <$> (f x)
biTrav f (x:xs) = liftA2 (biliftA2 (:) (:)) (f x) (biTrav f xs)
biTrav f [] = errorWithStackTrace "cant be empty"

-- simpleHttp' :: MonadIO m => (HeaderName,BL.ByteString) -> String -> m BL.ByteString
simpleHttpHeader headers url = liftIO $ withManager $ \man -> do
      req <- liftIO $ parseUrl url
      responseBody <$> httpLbs (setConnectionClose headers req) man


-- setConnectionClose :: Request m -> Request m
setConnectionClose h req = req{requestHeaders = ("Connection", "close") : (h ++ requestHeaders req)}
