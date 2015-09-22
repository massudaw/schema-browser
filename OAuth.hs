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
import Network.HTTP.Conduit  -- (httpLbs,parseUrl,withManager,responseBody,(..))
import Control.Applicative
import Control.Monad.IO.Class
import Data.Monoid
import Data.Maybe
import Query
import Schema
import qualified Data.Text.Lazy as T
import Data.Text.Lazy (Text)
import Text.XML.Light.Types
import Text.XML.Light.Proc
import qualified Data.Vector as V

import Types
import Control.Monad
import qualified Data.Map as M
import qualified Data.ByteString.Lazy.Char8 as BL
import Debug.Trace

--
cid    = "303272860482-5poqdtn2qg3tm82r7gbcsdqs9qln1b8k.apps.googleusercontent.com"
secret = "BlFl0V93LxQCSLvXt9UfkHnO"
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
  -- Ask for permission to read/write your fusion tables:
  let client = OAuth2Client { clientId = cid, clientSecret = secret }
      permissionUrl = formUrl client ["https://www.googleapis.com/auth/contacts.readonly",gmailScope]
  b <- doesFileExist file
  unless b $ do
      putStrLn$ "Load this URL: "++show permissionUrl
      case os of
        "linux"  -> rawSystem "firefox" [permissionUrl]
        "darwin" -> rawSystem "open"       [permissionUrl]
        _        -> return ExitSuccess
      putStrLn "Please paste the verification code: "
      authcode <- getLine
      tokens   <- exchangeCode client authcode
      putStrLn $ "Received access token: " ++ show (accessToken tokens)
      tokens2  <- refreshTokens client tokens
      putStrLn $ "As a test, refreshed token: " ++ show (accessToken tokens2)
      writeFile file (show tokens2)
  accessTok <- fmap (accessToken . read) (readFile file)
  BL.writeFile "contacts.json"=<< simpleHttpHeader [("GData-Version","3.0")] ("https://www.googleapis.com/gmail/v1/users" <> "/me/messages/14c37a4056062823?q=\"from:wesley.massuda@gmail.com\"&access_token=" ++ accessTok)

projectPhone inf elem  = lkeys elem
  where
        lkeys =   (\i -> (fromJust $ M.lookup ("contact","phones") (keyMap inf) , SComposite $ V.fromList $ fmap (SText . T.pack )  i))  . fmap strContent


projectEmail inf elem  = lkeys elem
  where
        lkeys =   (\i -> (fromJust $ M.lookup ("contact","emails") (keyMap inf) , SComposite $ V.fromList $ fmap (SText . T.pack )  i))  . catMaybes .   fmap (findAttrBy ((=="address") .  qName))

projectContact inf elem  = fmap (flip lkeys elem) translate
  where
        translate = [("givenName","firstname"),("familyName","lastname"),("additionalName","middlename")] :: [(Text,Text)]
        lkeys (k,j) =  join . fmap (\i -> fmap (,SText $ T.pack $ strContent i) $ M.lookup ("contact",j) (keyMap inf) )  . (filterChildName ((==k) . T.pack . qName))



-- simpleHttp' :: MonadIO m => (HeaderName,BL.ByteString) -> String -> m BL.ByteString
simpleHttpHeader headers url = liftIO $ withManager $ \man -> do
      req <- liftIO $ parseUrl url
      responseBody <$> httpLbs (setConnectionClose headers req) man


-- setConnectionClose :: Request m -> Request m
setConnectionClose h req = req{requestHeaders = ("Connection", "close") : (h ++ requestHeaders req)}
