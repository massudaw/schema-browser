{-# LANGUAGE RankNTypes,FlexibleContexts ,Arrows ,TupleSections,OverloadedStrings #-}
module OAuth (gmailOps,simpleHttpHeader,historyLoad,url) where
import qualified NonEmpty as Non
import qualified Data.Poset as P
import Step.Host
import SchemaQuery
import Control.Lens
import Control.Exception
import Utils
import qualified Types.Index as G
import qualified Data.ByteString.Lazy.Char8 as BS
import Control.Arrow
import Control.Monad.Reader
import qualified Data.HashMap.Strict as HM
import Data.Time
import Data.Time.Clock.POSIX
import Prelude hiding (head)
import System.Info (os)
import Network.Wreq
import System.Process (rawSystem)
import System.Exit    (ExitCode(..))
import System.Directory (doesFileExist)
import Network.Google.OAuth2 (formUrl, exchangeCode, refreshTokens,
                              OAuth2Client(..), OAuth2Tokens(..))
import Control.Applicative
import OAuthClient
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
import Data.List (find,intercalate,sort)
import qualified Reactive.Threepenny as R
import qualified Data.HashMap.Strict as HM

--
file   = "./tokens.txt"
--

url s u = "https://www.googleapis.com/" <> T.unpack s <> "/v1/users/"<> T.unpack u <> "/"

urlJ :: Text -> TableK Key -> FTB (TBData Key Showable ) -> String
urlJ s j pk
  | tableName j == "google_auth" = prefix <> "users/" <>  intercalate "," (renderShowable <$> F.toList ( getPK pk))  <> "/"
  | tableName j == "messages"  =  prefix <> "users/me/" <>  T.unpack (rawName j ) <> "/" <>  intercalate "," (renderShowable <$> F.toList (getPK pk))  <> "/"
  | otherwise = prefix <>  T.unpack (rawName j ) <> "/" <>  intercalate "," (renderShowable <$> F.toList (getPK pk) )  <> "/"
  where prefix = "https://www.googleapis.com/" <> T.unpack s <> "/v1/"

urlT s u
  | s == "lists" = "https://www.googleapis.com/" <> T.unpack s <> "/v1/" <> "users/me/"
  | otherwise = "https://www.googleapis.com/" <> T.unpack s <> "/v1/"

defsize = 100

readToken (HeadToken) = ""
readToken (NextToken i) = T.unpack i

historyLoad = do
  inf <- ask
  let (user,tokenT )= justError "no token" $ token inf


  dbvar <- lift $ refTable  (meta inf ) (lookTable (meta inf ) "google_auth")
  row <- G.lookup (G.Idex [txt $ user]) <$> R.currentValue (R.facts $collectionTid dbvar)
  let Just (TB1 (SText start ))= join $indexFieldRec (liftAccess (meta inf) "google_auth" (IProd Nothing ["historyid"]  ))<$> row

  token <-R.currentValue (R.facts tokenT)
  let
      getMessage :: Fold Value  (Text,Text)
      getMessage =  runFold ((,) <$> Fold (key "id"._String) <*> Fold (key "threadId". _String))
      patchHeader i l= (mempty,G.Idex [txt user,txt i] , l)
      userfk = PFK [Rel "user" Equals "id"] [PAttr "user" (patch $ txt user)] (PAtom $ patch $ mapKey' keyValue $justError"no row" $ row)
      patchAddMessage  i = fmap (\(i,t) -> [
            liftPatch inf "messages" $
              patchHeader i [PAttr "id" (patch $ txt i),PAttr "threadId" (patch $ txt t),userfk]
           ,liftPatch inf "threads" $
              patchHeader i [PAttr "id" (patch $ txt t),userfk]
            ] ) $  i ^? ( key "message" . getMessage )
      patchDelMessage  i = fmap (\(i,t) -> [liftPatch inf "messages" $ patchHeader i []]) $  i ^? ( key "message" . getMessage )
      req = url "gmail" "wesley.massuda@gmail.com" <> "history" <> "?" <>  "startHistoryId=" ++ T.unpack start <> "&access_token=" ++ ( accessToken token )
      generateAdd res =  fmap (concat .catMaybes .F.toList .fmap (\ i -> patchAddMessage i  ))  $ res ^? key "messagesAdded" . _Array
      generateDel res =   fmap (concat .catMaybes .F.toList .fmap (\ i -> patchDelMessage i  ))  $ res ^? key "messagesDeleted" . _Array
      generate res =  (fromMaybe [] $ generateAdd res <> generateDel res)
  liftIO $ print req
  res <- liftIO$ simpleHttpHeader [("GData-Version","3.0")] req
  let patches = fmap generate (res ^. key "history" . _Array )
      historyNewId = res ^. key "historyId" . _String
      messages = (lookTable inf "messages")
  liftIO $ print patches
  ref <- liftIO$ prerefTable inf messages
  patchRoute (concat $ patches)
  tb <- lift $ refTable inf messages
  v <- R.currentValue (R.facts $ collectionTid tb)
  -- Update Id
  (\i ->
    if i == start
       then
        return Nothing
       else
        lift $ transaction (meta inf)$ patchFrom
                $ liftPatch (meta inf)"google_auth" (mempty,G.Idex [txt user],[PAttr "historyid" (patch $ txt i)])
           ) historyNewId
  return ()


patchRoute l = do
  inf <- ask
  mapM (\p@(t,i,l) -> do
    ref <- liftIO$ prerefTable inf (lookTable inf (_kvname t))
    putPatch (patchVar ref) [p]) l



syncHistory [(tablefrom ,from, (Path _ (FKJoinTable rel _ )))]  ix table offset page maxResults sort _ = do
      inf <- ask
      tok <- getToken [from]
      let user = fst $ justError "no token" $ token inf
      decoded <- liftIO $ do
          let req = urlPath (schemaName inf)  [from]  <> "/" <> T.unpack (rawName table ) <> "?" <> maybe "" (\s -> "pageToken=" <> readToken s <> "&") page  <> ("maxResults=" <> show (maybe defsize id maxResults) <> "&") <>  "startHistoryId=" ++ ( intercalate "" $ renderPrim <$> (F.toList $ snd $ head ix) ) <> "&access_token=" ++ ( accessToken tok )
          print  req
          (t,d) <- duration $ decode <$> simpleHttpHeader [("GData-Version","3.0")] req
          print ("list",table,t)
          return  d
      let idx = if schemaName inf == "tasks" then "items" else rawName table
          relMap = M.fromList $ fmap (\rel -> (_relTarget rel ,_relOrigin rel) ) rel
          refAttr = (_tb $ FKT (kvlist $ fmap _tb $ concat $ F.toList $ backFKRef relMap (_relOrigin <$> rel) <$> TB1 from) rel (TB1 from))
          addAttr refAttr (m ,t ) = (m, mapComp (\(KV i) -> KV  $ M.insert (S.fromList $ keyattr refAttr ) refAttr i ) t)
      c <-  traverse (convertAttrs inf (Just $ tblist [refAttr]) (_tableMapL inf) table ) . maybe [] (\i -> (i :: Value) ^.. key idx  . values) $ decoded
      return ((addAttr refAttr) <$>  c, fmap (NextToken ) $ fromJust decoded ^? key "nextPageToken" . _String , (maybe (length c) round $ fromJust decoded ^? key "resultSizeEstimate" . _Number))


listTable torigin offset page maxResults sort ix
  | tablen == "history" = return ([],Nothing , 0)
  | tablen == "attachments" = return ([],Nothing , 0)
  | otherwise = do
      inf <- ask
      tok <- liftIO$ R.currentValue $ R.facts (snd $ justError "no token" $ token $  inf)
      let user = fst $ justError "no token" $ token inf
      decoded <- liftIO $ do
          let req =  url (schemaName inf) user <> T.unpack (tablen ) <> "?" <> maybe "" (\s -> "pageToken=" <> readToken s <> "&") page  <> ("maxResults=" <> show (maybe defsize id maxResults) <> "&") <> "access_token=" ++ ( accessToken tok )
          print  req
          (t,d) <- duration $ decode <$> simpleHttpHeader [("GData-Version","3.0")] req
          print ("list",tablen,t)
          return  d
      let idx = if schemaName inf == "tasks" then "items" else tablen
      c <-  traverse (convertAttrs inf Nothing (_tableMapL inf) (lookTable inf tablen)) . maybe [] (\i -> (i :: Value) ^.. key idx  . values) $ decoded
      return (c, fmap (NextToken ) $ fromJust decoded ^? key "nextPageToken" . _String , (maybe (length c) round $ fromJust decoded ^? key "resultSizeEstimate" . _Number))
  where
    tablen = _kvname (fst torigin)

getKeyAttr (TB1 (m, k)) = (concat (fmap keyattr $ F.toList $  (  _kvvalues (runIdentity $ getCompose k))))

urlPath :: Text -> [TBData Key Showable ] -> String
urlPath  s m
  = prefix <> "/" <>  intercalate "/" (rewrite <$> m)
  where prefix = "https://www.googleapis.com/" <> T.unpack s <> "/v1"
        rewrite :: TBData Key Showable  -> String
        rewrite v
          | j == "google_auth" = "users" <>  "/" <> ref
          | otherwise =  T.unpack j  <> "/" <> ref
            where j = _kvname (fst v)
                  ref = intercalate "," (renderShowable  <$> F.toList (getPKM v))


deleteRow pk
  | otherwise = do
    inf <- ask
    let
      scoped  = fmap (unTB1 ._fkttable . unTB) $ filter ((`elem` (_rawScope (lookTable inf (_kvname (fst pk))))) . _relOrigin . head . keyattr ) (F.toList $ unKV $snd $ pk)
    tok <- getToken scoped
    let user = fst $ justError "no token" $ token inf
        table = lookTable inf (_kvname (fst pk))
    decoded <- liftIO $ do
        let req = urlPath (schemaName inf)  scoped  <> "/" <> T.unpack (_kvname (fst pk ) ) <> "/" <> ( intercalate "," ( renderShowable . snd <$> notScoped (M.toList $ getPKM pk )))<>  "?access_token=" ++ ( accessToken tok)
            notScoped  = filter (not . (`elem` (_rawScope (lookTable inf (_kvname (fst pk))))).fst)
        (t,v) <- duration
            -- $ "DELETE" <> show req
            (deleteRequest [("GData-Version","3.0")] req)
        print ("delete",getPKM pk ,t)
        return v
    liftIO $print decoded
    let p = if BS.null decoded  then
              Just $ TableModification Nothing table  (fst pk , G.getIndex pk, [])
            else Nothing
    tell (maybeToList p)
    return p


insertTable pk
  | otherwise = do
    inf <- ask
    let
        attrs :: [(Key, FTB Showable)]
        attrs = filter (any (==FWrite) . keyModifier .fst ) $ getAttr' pk
    let
      scoped  = fmap (unTB1 ._fkttable . unTB) $ filter ((`elem` (_rawScope (lookTable inf (_kvname (fst pk))))) . _relOrigin . head . keyattr ) (F.toList $ unKV $snd $ pk)
    tok <- getToken scoped
    let user = fst $ justError "no token" $ token inf
        table = lookTable inf (_kvname (fst pk))
    decoded <- liftIO $ do
        let req =  urlPath (schemaName inf)  scoped  <> "/" <> T.unpack (_kvname (fst pk ) ) <>  "?access_token=" ++ ( accessToken tok)
        (t,v) <- duration
            (postHeaderJSON [("GData-Version","3.0")] req (toJSON $ M.fromList $ fmap (\(a,b) -> (keyValue a , renderShowable b)) $ attrs ) )
        print ("insert",getPK (TB1 pk),t)
        return $ decode $ v
    liftIO $ print decoded
    fmap (TableModification Nothing table . patch . mergeTB1 pk ) <$> (traverse (convertAttrs inf Nothing (_tableMapL inf) table) .  fmap (\i -> (i :: Value)  ) $  decoded)

lookOrigin  k (i,m) = unTB $ err $  find (( k == ). S.fromList . fmap _relOrigin. keyattr ) (F.toList $  unKV m)
    where
      err= justError ("no attr " <> show k <> " for table " <> show (_kvname i))

searchToken :: TBData Key Showable -> Maybe OAuth2Tokens
searchToken from = if (_kvname $ fst from ) == "google_auth" then   transTok   else Nothing
  where
      transTok  = runIdentity $ transToken (Just from)


getToken :: [TBData Key Showable] -> TransactionM (OAuth2Tokens)
getToken from = do
  inf <- ask
  pretok <- liftIO $ R.currentValue $ R.facts (snd $ fromJust $ token inf)
  return $fromMaybe pretok  (foldr1 mplus (searchToken <$> from ))


joinGet tablefrom tableref from ref
  | S.fromList (fmap _relOrigin (getKeyAttr ref) ) ==  S.fromList (rawPK tableref <> S.toList (rawAttrs tableref ) <> rawDescription tableref) = return Nothing
  | tableName tableref == "history" = return Nothing
  |  not $ null $ _rawScope tableref = do
    inf <- ask

    tok <- getToken  [unTB1 from]
    decoded <- liftIO $ do
        let req = (if tableName tableref == "tasks" then urlT (schemaName inf) user  else  urlJ (schemaName inf) tablefrom from )  <>  T.unpack (rawName tableref ) <> "/" <>  intercalate "," ( renderShowable . snd <$> notScoped ( M.toList $ getPK ref) ) <> "?access_token=" ++ ( accessToken tok)
            notScoped  = filter (not . (`elem` (_rawScope tableref)).fst)
        print  req
        (t,v) <- duration
                (simpleHttpHeader [("GData-Version","3.0")] req )
        print ("joinGet",tablefrom,tableref ,getPK from, getPK ref ,t)
        return $ decode v
    traverse (convertAttrs inf (Just $ (unTB1 ref)) (_tableMapL inf) tableref ) .  fmap (\i -> (i :: Value)  ) $  decoded
  | tableName tableref == "attachments"  = do
    inf <- ask
    tok <- getToken [ unTB1 from]
    decoded <- liftIO $ do
        let req = (if tableName tableref == "tasks" then urlT (schemaName inf) user  else  urlJ (schemaName inf) tablefrom from )  <>  T.unpack (rawName tableref ) <> "/" <>  intercalate "," ( renderShowable <$> F.toList (getPK ref ) ) <> "?access_token=" ++ ( accessToken tok)
        print req
        (t,v) <- duration
                (simpleHttpHeader [("GData-Version","3.0")] req )
        return $ decode v
    traverse (convertAttrs inf (Just $ (unTB1 ref)) (_tableMapL inf) tableref ) .  fmap (\i -> (i :: Value)  ) $  decoded
  | otherwise = return Nothing

joinList [(tablefrom ,from, (Path _ (FKJoinTable rel _ )))] tableref offset page maxResults sort ix
  | otherwise = do
      inf <- ask
      tok <- getToken [ from]
      decoded <- liftIO $ do
          let req = urlJ (schemaName inf) tablefrom (TB1 from  )<> T.unpack (rawName tableref) <>  "?" <> maybe "" (\s -> "pageToken=" <> readToken s <> "&") page  <> ("maxResults=" <> show (maybe defsize id maxResults) <> "&")  <> "access_token=" ++ ( accessToken tok)
          print req
          (t,v) <- duration
                  (simpleHttpHeader [("GData-Version","3.0")] req )
          print ("joinList",tablefrom,tableref ,getPKM from, t)
          return $ decode v
      let idx = if schemaName inf == "tasks" then "items" else rawName tableref
          relMap = M.fromList $ fmap (\rel -> (_relTarget rel ,_relOrigin rel) ) rel
          refAttr = (_tb $ FKT (kvlist $ fmap _tb $ concat $ F.toList $ backFKRef relMap (_relOrigin <$> rel) <$> TB1 from) rel (TB1 from))
      c <-  traverse (convertAttrs inf (Just $ tblist [refAttr]) (_tableMapL inf) tableref ) . maybe [] (\i -> (i :: Value) ^.. key idx  . values) $ decoded
      let addAttr refAttr (m ,t ) = (m, mapComp (\(KV i) -> KV  $ M.insert (S.fromList $ keyattr refAttr ) refAttr i ) t)
      return ((addAttr refAttr) <$>  c, fmap (NextToken ) $ fromJust decoded ^? key "nextPageToken" . _String , (maybe (length c) round $ fromJust decoded ^? key "resultSizeEstimate" . _Number))


getTable tb pk
  | tableName tb == "history" = return  Nothing
  | tableName tb == "attachments" = return  Nothing
  | not $ null $ _rawScope tb = do
      inf <- ask
      liftIO $ print $ (tb,_rawScope tb,rawFKS tb)
      let [sref] = filter (\(Path i _) -> S.isSubsetOf i (S.fromList $ _rawScope tb )) (S.toList $ rawFKS tb )
      let
          (Path spk  (FKJoinTable rel stable)) =  sref
          tableScope = _fkttable $ lookOrigin  spk (unTB1 pk)
      let fromtable = (lookSTable inf $ stable)
      joinGet fromtable  tb  tableScope  pk
  | S.fromList (rawPK tb <> S.toList (rawAttrs tb) <> rawDescription tb) `S.isSubsetOf` S.fromList (fmap _relOrigin (getKeyAttr pk) )  = return Nothing
  | otherwise = do
    inf <- ask
    tok <- liftIO $ R.currentValue $ R.facts (snd $ fromJust $ token inf)
    let user = fst $ fromJust $ token inf
    decoded <- liftIO $ do
        let req = url (schemaName inf) user <>  T.unpack (rawName tb ) <> "/" <>  intercalate "," ( renderShowable <$> F.toList (getPK pk )) <> "?access_token=" ++ ( accessToken tok)
        (t,v) <- duration
            (simpleHttpHeader [("GData-Version","3.0")] req )
        print ("get",tb,getPK pk,t)
        return $ decode v
    traverse (convertAttrs inf (Just $ (unTB1 pk)) (_tableMapL inf) tb ) .  fmap (\i -> (i :: Value)  ) $  decoded

getDiffTable table  j = fmap (join . fmap (diff j ) ) $ getTable  table $ TB1 j
joinGetDiffTable table  tableref f j = fmap (join . fmap (diff j)) $ joinGet table tableref (TB1 f) (TB1 j)


gmailOps = (SchemaEditor (error "no op1") (error "no op2") insertTable deleteRow listTable getDiffTable mapKeyType joinList syncHistory (error "no op3")100 (Just historyLoad))

lbackRef (ArrayTB1 t) = ArrayTB1 $ fmap lbackRef t
lbackRef (LeftTB1 t ) = LeftTB1 $ fmap lbackRef t
lbackRef (TB1 t) = snd $ head $ M.toList $ getPKM t

lookMTable inf m = lookSTable inf (_kvschema m,_kvname m)

traverseAccum f  l = foldl (\(a,m) c -> (\ a -> m >>= (\i -> fmap (:i) a )) <$> f  c a  ) (S.empty,return []) l

convertAttrs :: InformationSchema -> Maybe (TBData Key Showable) -> HM.HashMap Text Table ->  Table -> Value -> TransactionM (TBData Key Showable)
convertAttrs  infsch getref inf tb iv =   tblist' tb .  fmap _tb  . catMaybes <$> (snd $ traverseAccum kid (rawPK tb <> S.toList (rawAttrs tb) <> rawDescription tb ))
  where
    pathOrigin (Path i _  ) = i
    isFKJoinTable (Path _ (FKJoinTable  _ _)) = True
    isFKJoinTable (Path i (RecJoin _ j  ) ) = isFKJoinTable (Path i j )
    isFKJoinTable _ = False
    fkFields = S.unions $ map pathOrigin $ filter isFKJoinTable $  F.toList $rawFKS tb
    kid :: Key ->   S.Set Key -> (S.Set Key,TransactionM (Maybe (TB Identity Key Showable)))
    kid  k acc
      | S.member k fkFields
            = let
               fks = justError ("not path origin" <> (show k)) $  (find ((S.singleton k `S.isSubsetOf` ). pathOrigin) (P.sortBy (P.comparing pathRelRel) $F.toList (rawFKS tb)))
               (rel,trefname) = case unRecRel $ pathRel fks of
                       (FKInlineTable  (_,trefname) ) -> ([Inline k],trefname)
                       (FKJoinTable  rel (_,trefname) ) -> (rel,trefname)
               fk =  F.toList $  pathRelRel fks
               treftable = lookTable infsch trefname
               exchange tname (KArray i)  = KArray (exchange tname i)
               exchange tname (KOptional i)  = KOptional (exchange tname i)
               exchange tname (KSerial i)  = KSerial (exchange tname i)
               exchange tname (Primitive i ) = Primitive $ case i of
                        AtomicPrim _ -> RecordPrim ("gmail", tname)
                        RecordPrim i -> RecordPrim i
               patt = either
                    (traverse (\v ->
                        case getref of
                          Just getref  ->  do
                            let transrefs = tblist $ fmap (mapComp (firstTB (\k -> fromMaybe k  $ M.lookup  k relMap ))) $ (filter ((`S.isSubsetOf` (S.fromList (fmap _relOrigin fk))) . S.fromList . fmap _relOrigin . keyattr ) $ F.toList . unKV .snd $ getref)

                                relMap = M.fromList $ fmap (\rel -> (_relOrigin rel ,_relTarget rel) ) rel
                                nv  = flip mergeTB1 transrefs  <$> v
                            tell (TableModification Nothing (lookTable infsch trefname ) . patch <$> F.toList (nv))
                            return $ FKT (kvlist [_tb . Types.Attr  k $ (lbackRef    nv) ])  rel nv
                          Nothing ->  do
                            tell (TableModification Nothing (lookTable infsch trefname ) . patch <$> F.toList (v))
                            return $ FKT (kvlist [_tb . Types.Attr  k $ (lbackRef    v) ])  fk v))
                    (traverse (\v -> do
                        let ref = [_tb $ Attr  k $ v]  <> (filter ((`S.isSubsetOf` (S.fromList (fmap _relOrigin fk))) . S.fromList . fmap _relOrigin . keyattr ) $ concat $    F.toList . unKV .snd <$> maybeToList (tableNonRef' <$> getref))
                            refTB = [_tb $ Attr  k $ v]  <> (filter ((`S.isSubsetOf` (S.fromList (fmap _relOrigin fk))) . S.fromList . fmap _relOrigin . keyattr ) $ concat $    F.toList . unKV .snd .tableNonRef'<$> maybeToList (getref))
                        tbs <- atTable ( lookTable infsch trefname)
                        let reftb = join $ fmap unSOptional $ joinRel2 (tableMeta $ lookTable infsch trefname) (fmap (replaceRel fk . unTB) ref)  tbs
                        reftbT <- joinRelT  fk (fmap unTB refTB) ( lookTable infsch trefname) tbs
                        patch <- maybe (maybe (return reftbT)   (\getref -> traverse (\reftb -> do
                            let scoped
                                  | null (_rawScope treftable) = getref
                                  | otherwise =
                                      case (filter ((`S.isSubsetOf` (S.fromList (fmap _relOrigin fk))) . S.fromList . fmap _relOrigin . keyattr ) $ F.toList . unKV .snd $ getref) of
                                        [i] -> unTB1 (_fkttable (unTB i))

                            pti <- joinGetDiffTable (lookMTable infsch (fst scoped)) treftable scoped reftb
                            tell (TableModification Nothing treftable <$> maybeToList pti)
                            return $ maybe (reftb) (apply reftb  ) pti) reftbT ) getref) return (reftb)
                        return $ FKT (kvlist (filter (not .(`S.member` acc). _tbattrkey.unTB )ref) ) rel patch ))
               funL = funO  True (exchange trefname $ keyType k) vk
               funR = funO  True (keyType k) vk
               vk = iv  ^? ( key (keyValue  k))
               mergeFun = do
                          (l,r) <- liftA2 (,) funL funR
                          return $ case (l,r) of
                            (Left (Just i),Right (Just j)) -> Right (Just j)
                            (Left (Just i),_) -> Left (Just i)
                            (Left i ,j ) -> j
             in  (S.insert k acc,join . fmap  patt $    mergeFun)
      | otherwise =  (S.insert k acc,fmap (either ((\v-> IT ( k) v)  <$> ) (Types.Attr k<$>) ) . funO  False (  keyType k)  $ (iv ^? ( key ( keyValue k))  ))

    resultToMaybe (Success i) = Just i
    resultToMaybe (Error i ) = Nothing
    fun :: Bool -> KType (Prim KPrim (Text,Text))-> Value -> TransactionM (Either (Maybe (TB2 Key Showable)) (Maybe (FTB Showable)))
    fun f (Primitive i) v =
        case i of
          AtomicPrim k -> return $ Right $ fmap TB1 $ case k of
            PText -> join $ readPrim k . T.unpack <$> (v ^? _String)
            PTimestamp _ ->
                (fmap (STimestamp . utcToLocalTime utc) . resultToMaybe . fromJSON $ v ) <|> (STimestamp . utcToLocalTime utc . posixSecondsToUTCTime.realToFrac . (/10^3). read . T.unpack  <$> (v ^? _String))
            PInt _->  (SNumeric . round <$> (v ^? _Number)) <|> (SNumeric . round .read . T.unpack <$> ( v^? _String))
            PDouble -> SDouble . realToFrac  <$> (v ^? _Number)
            PBinary -> join  $ readPrim k . T.unpack  <$> (v ^? _String)
          RecordPrim (i,m) ->  Left .fmap TB1 .  tbNull <$>  convertAttrs infsch (if f then Nothing else getref) inf   (justError "no look" $  HM.lookup m inf ) v
                where  tbNull tb = if null (getAttr' tb) then Nothing else Just  tb
    fun f (KArray i) v = (\l -> if null l then return (typ i) else fmap (bimap  nullArr  nullArr) .   biTrav (fun f i) $ l ) $ (v ^.. values )
        where nullArr lm = if null l then Nothing else Just (ArrayTB1 $ Non.fromList l)
                where l = catMaybes lm
    fun f i v = errorWithStackTrace (show (i,v))

    funO :: Bool -> KType (Prim KPrim (Text,Text))-> Maybe Value -> TransactionM (Either (Maybe (TB2 Key Showable)) (Maybe (FTB Showable)))
    funO f (KOptional i) v =  fmap (bimap (Just . LeftTB1  ) (Just . LeftTB1)) . maybe (return $ typ i) (fun f i) $ v
    funO f (KSerial i) v =  fmap (bimap (Just . SerialTB1 ) (Just . SerialTB1 )) . maybe (return $ typ i) (fun f i) $ v
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

deleteRequest h url = do
      let opts = defaults  & headers .~ h
      (^. responseBody ) <$> deleteWith opts url

postHeaderJSON h url form = do
      let opts = defaults  & headers .~ h
      (^. responseBody ) <$> postWith opts url form


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
  ,("datetime",PTimestamp (Just utc) )
  ,("timestamp",PTimestamp (Just utc) )
  ,("pdf",PMime "application/pdf")
  ,("dwg",PMime "application/dwg")
  ,("ofx",PMime "application/x-ofx")
  ,("jpg",PMime "image/jpg")
  ,("png",PMime "image/png")
  ,("bmp",PMime "image/bmp")
  ,("email",PMime "text/plain")
  ,("html",PMime "text/html")
  ,("double precision",PDouble)
  ,("integer",PInt 8)
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


