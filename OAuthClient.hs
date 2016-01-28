{-# LANGUAGE Arrows ,TupleSections,OverloadedStrings #-}
module OAuthClient (oauthpoller,tokenToOAuth) where
import Control.Exception
import qualified Data.Text as T
import Control.Arrow
import Control.Monad.Reader
import Prelude hiding (head)
import Step.Client
import System.Info (os)
import System.Process (rawSystem)
import System.Exit    (ExitCode(..))
import Network.Google.OAuth2 (formUrl, exchangeCode, refreshTokens,
                              OAuth2Client(..), OAuth2Tokens(..))
import Control.Applicative
import System.Environment

import Types
import RuntimeTypes
import Debug.Trace

gmailScope = "https://www.googleapis.com/auth/gmail.modify"

taskscope = "https://www.googleapis.com/auth/tasks"

tokenToOAuth (TB1 (SText t), TB1 (SText r) , TB1 (SDouble i) , TB1 (SText k)) = OAuth2Tokens  (T.unpack t) (T.unpack r) (realToFrac i)  (T.unpack k)
oauthToToken (OAuth2Tokens  t r i  k)
  = TB1 $ tblist $ attrT . fmap (LeftTB1 .Just )<$> [("accesstoken",TB1 (SText $ T.pack t)), ("refreshtoken",TB1 $ SText $ T.pack r) , ("expiresin",TB1 (SDouble $realToFrac i)) , ("tokentype",TB1 (SText $ T.pack k))]

liftA4 f  i j k  l= f <$> i <*> j <*> k <*> l

oauthpoller = BoundedPlugin2 "Gmail Login" "google_auth" url
  where
    url :: ArrowReader
    url = proc t -> do
       user <- idxK "username" -< ()
       token <- atR "token" (liftA4 (,,,) <$> idxM "accesstoken" <*> idxM "refreshtoken" <*> idxM "expiresin" <*> idxM "tokentype" ) -< ()
       v <- act (\i -> liftIO$ do
          Just cid <- lookupEnv "CLIENT_ID"
          Just secret <- lookupEnv "CLIENT_SECRET"
          let client = OAuth2Client { clientId = cid, clientSecret = secret }
              permissionUrl = formUrl client [gmailScope,taskscope]
              requestNew = (do
                  putStrLn$ "Load this URL: "++ show permissionUrl
                  case os of
                    "linux"  -> rawSystem "firefox" [permissionUrl]
                    "darwin" -> rawSystem "open"       [permissionUrl]
                    _        -> return ExitSuccess
                  putStrLn "Please paste the verification code: "
                  authcode <- getLine
                  tokens   <- exchangeCode client authcode
                  putStrLn $ "Received access token: " ++ show (accessToken tokens)
                  return tokens)
          maybe requestNew ((`catch` (\e -> traceShow (e :: SomeException) requestNew)) . refreshTokens client) i
          ) -< tokenToOAuth <$> token
       token <- atR "token" ((,,,) <$> odxR "accesstoken" <*> odxR "refreshtoken" <*> odxR "expiresin" <*> odxR "tokentype" ) -< ()
       odxR "refresh" -< ()
       returnA -< Just . tblist . pure . _tb $ IT "token" (LeftTB1 $  oauthToToken <$> Just v )


