{-# LANGUAGE Arrows ,TupleSections,OverloadedStrings #-}
module OAuth (gmailOps,tokenToOAuth,oauthToToken,oauthpoller) where
import qualified NonEmpty as Non
import Control.Lens
import Control.Exception
import Control.Arrow
import qualified Data.HashMap.Strict as HM
import Data.Time
import qualified Types.Index as G
import Step
import System.Info (os)
import Network.Wreq
import System.Process (rawSystem)
import System.Exit    (ExitCode(..))
import System.Directory (doesFileExist)
import Network.Google.OAuth2 (formUrl, exchangeCode, refreshTokens,
                              OAuth2Client(..), OAuth2Tokens(..))
import Control.Applicative
import Text
import qualified Data.Set as S
import qualified Data.Foldable as F
import Control.Monad.IO.Class
import Data.Monoid
import Data.Biapplicative
import Control.Monad.Writer hiding (pass)
import System.Time.Extra
import GHC.Stack
import Control.Concurrent
import Data.Maybe
import System.Environment
import Query
import Data.Aeson.Lens
import Schema
import qualified Data.Text as T
import Data.Text (Text)
import Data.Aeson
import Utils

import Types
import Types.Patch
import RuntimeTypes
import qualified Data.Map as M
import Data.Map (Map)
import Debug.Trace
import Data.List (find,intercalate)
import qualified Reactive.Threepenny as R

--
file   = "./tokens.txt"
--
gmailScope = "https://www.googleapis.com/auth/gmail.modify"


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
              permissionUrl = formUrl client [gmailScope]
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
          maybe requestNew ((`catch` (\e -> traceShow (e :: SomeException) requestNew)) . refreshTokens client) i
          ) -< tokenToOAuth <$> token
       token <- atR "token" ((,,,) <$> odxR "accesstoken" <*> odxR "refreshtoken" <*> odxR "expiresin" <*> odxR "tokentype" ) -< ()
       odxR "refresh" -< ()
       returnA -< Just . tblist . pure . _tb $ IT (attrT ("token" , LeftTB1 $ Just $ TB1 ())) (LeftTB1 $  oauthToToken <$> Just v )



updateTable inf table reference page maxResults
  | tableName table == "history" = do
    tok <- liftIO$ R.currentValue $ R.facts (snd $justError "no token"$ token inf)
    let user = fst $ justError "no token"$ token inf
    decoded <- liftIO $ do
        let req =  "https://www.googleapis.com/gmail/v1/users/"<> T.unpack user <> "/" <> T.unpack (rawName table ) <> "?" <> "startHistoryId=" <> intercalate "," ( renderShowable . snd <$> getPK (TB1 reference) ) <> "&"<> maybe "" (\(NextToken s) ->  T.unpack s <> "pageToken=" <> T.unpack s <> "&") page  <> maybe "" (\i -> "maxResults=" <> show i <> "&") maxResults <> "access_token=" ++ ( accessToken tok )
        print  req
        (t,d) <- duration $ decode <$> simpleHttpHeader [("GData-Version","3.0")] req
        print ("update",table,t)
        print d
        return  d
    c <-  traverse (convertAttrs inf Nothing (tableMap inf) table ) . maybe [] (\i -> (i :: Value) ^.. key (  rawName table ) . values) $ decoded
    return (c, fmap (NextToken ) $ fromJust decoded ^? key "nextPageToken" . _String , {-length c +-} (maybe (length c) round $ fromJust decoded ^? key "resultSizeEstimate" . _Number))
  | otherwise = return ([], Nothing,0)



listTable inf table offset page maxResults sort ix
  | tableName table == "history" = return ([],Nothing , 0)
  | tableName table == "attachments" = return ([],Nothing , 0)
  | otherwise = do
    tok <- liftIO$ R.currentValue $ R.facts (snd $ justError "no token" $ token $  inf)
    let user = fst $ justError "no token" $ token inf
    decoded <- liftIO $ do
        let req =  "https://www.googleapis.com/gmail/v1/users/"<> T.unpack user <> "/" <> T.unpack (rawName table ) <> "?" <> maybe "" (\(NextToken s) -> "pageToken=" <> T.unpack s <> "&") page  <> ("maxResults=" <> show (maybe 200 id maxResults) <> "&") <> "access_token=" ++ ( accessToken tok )
        print  req
        (t,d) <- duration $ decode <$> simpleHttpHeader [("GData-Version","3.0")] req
        print ("list",table,t)
        return  d
    c <-  traverse (convertAttrs inf Nothing (tableMap inf) table ) . maybe [] (\i -> (i :: Value) ^.. key (  rawName table ) . values) $ decoded
    return (c, fmap (NextToken ) $ fromJust decoded ^? key "nextPageToken" . _String , (maybe (length c) round $ fromJust decoded ^? key "resultSizeEstimate" . _Number))

getKeyAttr (TB1 (m, k)) = (concat (fmap keyattr $ F.toList $  (  _kvvalues (runIdentity $ getCompose k))))


insertTable inf pk
  | otherwise = do
    let
        attrs :: [(Key, FTB Showable)]
        attrs = filter (any (==FWrite) . keyModifier .fst ) $ getAttr' (TB1 pk)
    tok <- liftIO $R.currentValue $ R.facts (snd $ justError "no token" $ token inf)
    let user = fst $ justError "no token" $ token inf
        table = lookTable inf (_kvname (fst pk))
    decoded <- liftIO $ do
        let req = "https://www.googleapis.com/gmail/v1/users/"<> T.unpack user <> "/" <> T.unpack (_kvname (fst pk ) ) <>  "?access_token=" ++ ( accessToken tok)
        (t,v) <- duration
            (postHeaderJSON [("GData-Version","3.0")] req (toJSON $ M.fromList $ fmap (\(a,b) -> (keyValue a , renderShowable b)) $ attrs ) )
        print ("insert",getPK (TB1 pk),t)
        return $ decode v
    fmap (TableModification Nothing table . patch .unTB1) <$> (traverse (convertAttrs inf Nothing (tableMap inf) table ) .  fmap (\i -> (i :: Value)  ) $  decoded)


joinGet inf tablefrom tableref from ref
  | S.fromList (fmap _relOrigin (getKeyAttr ref) ) ==  S.fromList (rawPK tableref <> S.toList (rawAttrs tableref ) <> rawDescription tableref) = return Nothing
  | tableName tableref == "attachments" = do
    tok <- liftIO $ R.currentValue $ R.facts (snd $ fromJust $ token inf)
    let user = fst $ fromJust $ token inf
    decoded <- liftIO $ do
        let req = "https://www.googleapis.com/gmail/v1/users/" <> T.unpack user <> "/" <> T.unpack (rawName tablefrom) <> "/" <>  intercalate "," ( renderShowable . snd <$> getPK from ) <> "/" <> T.unpack (rawName tableref ) <> "/" <>  intercalate "," ( renderShowable . snd <$> getPK ref ) <> "?access_token=" ++ ( accessToken tok)
        (t,v) <- duration
                (simpleHttpHeader [("GData-Version","3.0")] req )
        print ("joinGet",tablefrom,tableref ,getPK from, getPK ref ,t)
        return $ decode v
    traverse (convertAttrs inf (Just $ (tableref,unTB1 ref)) (tableMap inf) tableref ) .  fmap (\i -> (i :: Value)  ) $  decoded
  | otherwise = return Nothing



getTable inf  tb pk
  | tableName tb == "history" = return  Nothing
  | tableName tb == "attachments" = return  Nothing
  | S.fromList (fmap _relOrigin (getKeyAttr pk) ) ==  S.fromList (rawPK tb <> S.toList (rawAttrs tb) <> rawDescription tb) = return Nothing
  | otherwise = do
    tok <- liftIO $ R.currentValue $ R.facts (snd $ fromJust $ token inf)
    let user = fst $ fromJust $ token inf
    decoded <- liftIO $ do
        let req = "https://www.googleapis.com/gmail/v1/users/"<> T.unpack user <> "/" <> T.unpack (rawName tb ) <> "/" <>  intercalate "," ( renderShowable . snd <$> getPK pk ) <> "?access_token=" ++ ( accessToken tok)
        (t,v) <- duration
            (simpleHttpHeader [("GData-Version","3.0")] req )
        print ("get",tb,getPK pk,t)
        return $ decode v
    traverse (convertAttrs inf (Just $ (tb,unTB1 pk)) (tableMap inf) tb ) .  fmap (\i -> (i :: Value)  ) $  decoded

getDiffTable inf table  j = fmap (join . fmap (diff j. unTB1) ) $ getTable  inf table $ TB1 j
joinGetDiffTable inf table  tableref f j = fmap (join . fmap (diff j. unTB1)) $ joinGet  inf table tableref (TB1 f) (TB1 j)


gmailOps = (SchemaEditor undefined undefined insertTable undefined listTable updateTable getDiffTable mapKeyType)

lbackRef (ArrayTB1 t) = ArrayTB1 $ fmap lbackRef t
lbackRef (LeftTB1 t ) = LeftTB1 $ fmap lbackRef t
lbackRef (TB1 t) = snd $ Types.head $ getPKM t

convertAttrs :: InformationSchema -> Maybe (Table,TBData Key Showable) -> M.Map Text Table ->  Table -> Value -> TransactionM (TB2 Key Showable)
convertAttrs  infsch getref inf tb iv =   TB1 . tblist' tb .  fmap _tb  . catMaybes <$> (traverse kid (rawPK tb <> S.toList (rawAttrs tb) <> rawDescription tb ))
  where
    pathOrigin (Path i _ _ ) = i
    isFKJoinTable (Path _ (FKJoinTable _ _ _) _) = True
    isFKJoinTable (Path i (RecJoin _ j  ) k) = isFKJoinTable (Path i j k)
    isFKJoinTable _ = False
    fkFields = S.unions $ map pathOrigin $ filter isFKJoinTable $  F.toList $rawFKS tb
    kid :: Key -> TransactionM (Maybe (TB Identity Key Showable))
    kid  k
      | S.member k fkFields
            = let
               fks = justError "" (find ((== S.singleton k). pathOrigin) (F.toList (rawFKS tb)))
               (FKJoinTable _ _ trefname ) = unRecRel $ pathRel fks
               vk = iv  ^? ( key (keyValue  k))
               fk =  F.toList $  pathRelRel fks
               exchange tname (KArray i)  = KArray (exchange tname i)
               exchange tname (KOptional i)  = KOptional (exchange tname i)
               exchange tname (Primitive i ) = Primitive $ case i of
                        AtomicPrim _ -> RecordPrim ("gmail", tname)
                        RecordPrim i -> RecordPrim i
               patt = either
                    (traverse (\v -> do
                        tell (TableModification Nothing (lookTable infsch trefname ) . patch <$> F.toList v)
                        liftIO $ print (trefname ,"left",v)
                        return $ FKT [Compose .Identity . Types.Attr  k $ (lbackRef    v) ]  fk v))
                    (traverse (\v -> do
                        let ref = [Compose .Identity . Types.Attr  k $ v]
                        liftIO $ print (trefname,"right",v)
                        tbs <- liftIO$ runDBM infsch (atTable (tableMeta $ lookTable infsch trefname))
                        liftIO$ print tbs
                        reftb <- joinRelT fk (fmap unTB ref) (lookTable infsch trefname) (G.toList tbs)
                        liftIO$ print reftb
                        patch <- maybe (return reftb ) (\(tref,getref )-> traverse (\reftb -> do
                            pti <- joinGetDiffTable infsch  tref (lookTable infsch trefname) getref reftb
                            tell (TableModification Nothing (lookTable infsch trefname) <$> maybeToList pti)
                            return $ maybe (reftb) (unTB1 . apply (TB1 reftb) . PAtom) pti) reftb ) getref
                        liftIO$ print patch
                        return $ FKT ref fk   patch ))
               funL = funO  True (exchange trefname $ keyType k) vk
               funR = funO  True ( keyType k) vk
               mergeFun = do
                          (l,r) <- liftA2 (,) funL funR
                          return $ case (l,r) of
                            (Left (Just i),Right (Just j)) -> Right (Just j)
                            (Left (Just i),_) -> Left (Just i)
                            (Left i ,j ) -> j
              in  join . fmap  patt $   mergeFun
      | otherwise =  fmap (either ((\v-> IT (_tb $ Types.Attr k (fmap (const ()) v)) v)  <$> ) (Types.Attr k<$>) ) . funO  False (  keyType k)  $ (iv ^? ( key ( keyValue k))  )

    fun :: Bool -> KType (Prim KPrim (Text,Text))-> Value -> TransactionM (Either (Maybe (TB2 Key Showable)) (Maybe (FTB Showable)))
    fun f (Primitive i) v =
        case i of
          AtomicPrim k -> return $ Right $ fmap TB1 $ join $ case k of
            PText -> readPrim k . T.unpack <$> (v ^? _String)
            PInt -> Just . SNumeric . round <$> (v ^? _Number)
            PDouble -> Just . SDouble . realToFrac  <$> (v ^? _Number)
            PBinary -> readPrim k . T.unpack  <$> (v ^? _String)
          RecordPrim (i,m) ->  Left . tbNull <$>  convertAttrs infsch (if f then Nothing else getref) inf   (justError "no look" $  M.lookup m inf ) v
                where  tbNull tb = if null (getAttr' tb) then Nothing else Just  tb
    fun f (KArray i) v = (\l -> if null l then return (typ i) else fmap (bimap  nullArr  nullArr) .   biTrav (fun f i) $ l ) $ (v ^.. values )
        where nullArr lm = if null l then Nothing else Just (ArrayTB1 $ Non.fromList l)
                where l = catMaybes lm
    fun f i v = errorWithStackTrace (show (i,v))

    funO :: Bool -> KType (Prim KPrim (Text,Text))-> Maybe Value -> TransactionM (Either (Maybe (TB2 Key Showable)) (Maybe (FTB Showable)))
    funO f (KOptional i) v =  fmap (bimap (Just . LeftTB1  ) (Just . LeftTB1)) . maybe (return $ typ i) (fun f i) $ v
    funO f i v = maybe (return $typ i) (fun f i) v

    typ (KArray i ) = typ i
    typ (KOptional i ) = typ i
    typ (KSerial i ) = typ i
    typ (Primitive i ) = case i of
        AtomicPrim _ -> Right Nothing
        RecordPrim _ -> Left Nothing


instance Biapplicative Either where
  Right f  <<*>> Right g  = Right $ f  g
  Left f  <<*>> Left g  = Left $ f  g

-- biTravM f (Just x) = bimap pure pure  (f x)

biTrav :: Applicative m => (c -> m (Either a b) ) -> [c] -> m (Either [a] [b])
biTrav f (x:[]) = bimap (pure) (pure)  <$> (f x)
biTrav f (x:xs) = liftA2 (biliftA2 (:) (:)) (f x) (biTrav f xs)
biTrav f [] = errorWithStackTrace "cant be empty"

simpleHttpHeader h url = do
      let opts = defaults  & headers .~ h
      (^. responseBody ) <$> getWith opts url

postHeaderJSON h url form = do
      let opts = defaults  & headers .~ h
      (^. responseBody ) <$> postWith opts url form

{-
-- simpleHttp' :: MonadIO m => (HeaderName,BL.ByteString) -> String -> m BL.ByteString
simpleHttpHeader headers url = liftIO $ withManager $ \man -> do
      req <- liftIO $ parseUrl url
      responseBody <$> httpLbs (setConnectionClose headers req) man


-- setConnectionClose :: Request m -> Request m
setConnectionClose h req = req{requestHeaders = ("Connection", "close") : (h ++ requestHeaders req)}
-}

preconversion i =  join $ (\t -> M.lookup (i,t) (gmailLiftPrimConv )) <$> ktypeLift  i

conversion i = fromMaybe (id,id) $ preconversion i

topconversion v@(KDelayed n ) =   preconversion v <|> fmap lif (topconversion n )
  where
    lif (a,b) = ((\(DelayedTB1 i) -> DelayedTB1 (fmap a i)), (\(DelayedTB1 i) -> DelayedTB1 (fmap b  i )))
topconversion v@(KSerial n ) =   preconversion v <|> fmap lif (topconversion n )
  where
    lif (a,b) = ((\(SerialTB1 i) -> SerialTB1 (fmap a i)), (\(SerialTB1 i) -> SerialTB1 (fmap b  i )))
topconversion v@(KOptional n ) =   preconversion v <|> fmap lif (topconversion n )
  where
    lif (a,b) = ((\(LeftTB1 i) -> LeftTB1 (fmap a i)), (\(LeftTB1 i) -> LeftTB1 (fmap b  i )))
topconversion v@(KArray n) =  preconversion v <|> fmap lif (topconversion n )
  where
    lif (a,b) = ((\(ArrayTB1 i) -> ArrayTB1 (fmap a i)), (\(ArrayTB1 i) -> ArrayTB1 (fmap b  i )))
topconversion v@(KInterval n) =  preconversion v <|> fmap lif (topconversion n )
  where
    lif (a,b) = ((\(IntervalTB1 i) -> IntervalTB1 (fmap a i)), (\(IntervalTB1 i) -> IntervalTB1 (fmap b  i )))
topconversion v@(Primitive i) =  preconversion v

-- Type Conversions
--
gmailLiftPrim :: Ord b => Map (KType (Prim KPrim b)) (KType (Prim KPrim b))
gmailLiftPrim =
  M.fromList []

gmailLiftPrimConv :: Ord b => Map (KType (Prim KPrim b),KType (Prim KPrim b))  ( FTB  Showable -> FTB Showable , FTB Showable -> FTB Showable )
gmailLiftPrimConv =
  M.fromList []


gmailPrim :: HM.HashMap Text KPrim
gmailPrim =
  HM.fromList
  [("text",PText)
  ,("pdf",PMime "application/pdf")
  ,("ofx",PMime "application/x-ofx")
  ,("jpg",PMime "image/jpg")
  ,("email",PMime "text/plain")
  ,("html",PMime "text/html")
  ,("double precision",PDouble)
  ,("integer",PInt)
  ,("boolean",PBoolean)
  ,("base64url",PText)
  ]

ktypeLift :: Ord b => KType (Prim KPrim b) -> Maybe (KType (Prim KPrim b))
ktypeLift i = (M.lookup i  gmailLiftPrim )

ktypeRec v@(KOptional i) = ktypeLift v <|> ktypeRec i
ktypeRec v@(KArray i) = ktypeLift v <|> ktypeRec i
ktypeRec v@(KInterval i) = ktypeLift v <|> ktypeRec i
ktypeRec v@(KSerial i) = ktypeLift v <|> ktypeRec i
ktypeRec v@(KDelayed i) = ktypeLift v <|> ktypeRec i
ktypeRec v@(Primitive i ) = ktypeLift v

mapKeyType :: FKey (KType PGPrim) -> FKey (KType (Prim KPrim (Text,Text)))
mapKeyType  = fmap mapKType

mapKType :: KType PGPrim -> KType CorePrim
mapKType i = fromMaybe (fmap textToPrim i) $ ktypeRec (fmap textToPrim i)

textToPrim :: Prim (Text,Text) (Text,Text) -> Prim KPrim (Text,Text)
textToPrim (AtomicPrim (s,i)) = case  HM.lookup i  gmailPrim of
  Just k -> AtomicPrim k
  Nothing -> errorWithStackTrace $ "no conversion for type " <> (show i)
textToPrim (RecordPrim i) =  (RecordPrim i)


