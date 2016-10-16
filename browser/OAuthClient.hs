{-# LANGUAGE TypeFamilies,FlexibleContexts ,Arrows ,TupleSections,OverloadedStrings #-}
module OAuthClient (readHistory ,oauthpoller,transToken,tokenToOAuth,oauthToToken) where
import Data.Maybe
import Utils
import Types.Patch
import Types.Index as G
import Data.Monoid
import Control.Exception
import qualified Data.Text as T
import Control.Arrow
import Control.Monad.Reader
import Prelude hiding (head)
import Step.Client
import qualified Data.Map as M
import System.Info (os)
import System.Process (rawSystem)
import System.Exit    (ExitCode(..))
import Network.Google.OAuth2 (formUrl, exchangeCode, refreshTokens,
                              OAuth2Client(..), OAuth2Tokens(..))
import Control.Applicative
import System.Environment

import Types
import Data.Traversable
import RuntimeTypes
import Debug.Trace

gmailScope = "https://www.googleapis.com/auth/gmail.modify"

taskscope = "https://www.googleapis.com/auth/tasks"

tokenToOAuth (TB1 (SText t), TB1 (SText r) , TB1 (SDouble i) , TB1 (SText k)) = OAuth2Tokens  (T.unpack t) (T.unpack r) (realToFrac i)  (T.unpack k)
oauthToToken (OAuth2Tokens  t r i  k)
  = TB1 $ tblist $ attrT . fmap (LeftTB1 .Just )<$> [("accesstoken",TB1 (SText $ T.pack t)), ("refreshtoken",TB1 $ SText $ T.pack r) , ("expiresin",TB1 (SDouble $realToFrac i)) , ("tokentype",TB1 (SText $ T.pack k))]

liftA4 f  i j k  l= f <$> i <*> j <*> k <*> l

tableToToken = atR "token" (fmap tokenToOAuth <$> (liftA4 (,,,) <$> idxM "accesstoken" <*> idxM "refreshtoken" <*> idxM "expiresin" <*> idxM "tokentype" ))

transToken :: (Show k ,KeyString k ,Applicative m ,Monad m) => Maybe (TBData k Showable ) -> m (Maybe (OAuth2Tokens))
transToken = fmap join . traverse ((fmap return) (dynPure   $ atR "token" (fmap tokenToOAuth <$> (liftA4 (,,,) <$> idxM "accesstoken" <*> idxM "refreshtoken" <*> idxM "expiresin" <*> idxM "tokentype" )) ))

oauthpoller :: PrePlugins
oauthpoller = FPlugins "Gmail Login" "google_auth" (BoundedPlugin2 url)
  where
    url :: ArrowReader
    url = proc t -> do
       user <- idxK "username" -< ()
       token <- tableToToken  -< ()
       v <- act (\i -> liftIO$ do
          Just cid <- lookupEnv "CLIENT_ID"
          Just secret <- lookupEnv "CLIENT_SECRET"
          let client = OAuth2Client { clientId = cid, clientSecret = secret }
              permissionUrl = formUrl client [gmailScope,taskscope]
              requestNew = (do
                  putStrLn$ "Load this URL: "++ show permissionUrl
                  case os of
                    "linux"  -> rawSystem "chromium" [permissionUrl]
                    "darwin" -> rawSystem "open"       [permissionUrl]
                    _        -> return ExitSuccess
                  putStrLn "Please paste the verification code: "
                  authcode <- getLine
                  tokens   <- exchangeCode client authcode
                  putStrLn $ "Received access token: " ++ show (accessToken tokens)
                  return tokens)
          tokens  <- maybe requestNew ((`catch` (\e -> traceShow (e :: SomeException) requestNew)) . refreshTokens client) i
          putStrLn $ "New Token: " ++  show (accessToken tokens)
          return tokens
          ) -< token
       token <- atR "token" ((,,,) <$> odxR "accesstoken" <*> odxR "refreshtoken" <*> odxR "expiresin" <*> odxR "tokentype" ) -< ()
       odxR "refresh" -< ()
       returnA -< Just . tblist . pure . _tb $ IT "token" (LeftTB1 $  oauthToToken <$> Just v )


readHistory :: PluginTable (Maybe (TBData T.Text Showable))
readHistory = proc x -> do
  madded <- atMA "user,messagesAdded->messages" (tb) -< ()
  mdeleted <- atMA "user,messagesDeleted->messages" (idxM "id")  -< ()
  -- labelAdded <- atA "labelsAdded"  ((,) <$> idxK "id" <*> idxK "labels")  -< ()
  -- labelDeleted <- atA "messagesDeleted"   -< ()
  let patchDel i = (kvempty ,  G.Idex $ M.fromList [("id",i)] , [])
      patchCreate i = firstPatch keyString $ patch i
  odxR "showpatch" -< ()
  returnA -< Just $ tblist $ _tb <$> [Attr "showpatch" (TB1 $ SText $ T.pack $ show $ (patchDel <$> catMaybes mdeleted) <>  (patchCreate <$> catMaybes madded))]


