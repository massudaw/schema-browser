{-# LANGUAGE RankNTypes,NoMonomorphismRestriction,FlexibleContexts,OverloadedStrings ,TupleSections, ExistentialQuantification #-}
import Query
import Schema
import Data.Traversable (Traversable,traverse)
import Warshal
import Control.Monad(void,mapM,replicateM,liftM)
import Data.Functor.Compose
import qualified Data.List as L
import Data.Vector(Vector)
import qualified Data.ByteString.Char8 as BS

import qualified Graphics.UI.Threepenny as UI
import Graphics.UI.Threepenny.Core
import Data.Monoid

import Debug.Trace
import qualified Data.Foldable as F
import qualified Data.Text.Lazy as T
import Data.ByteString.Lazy(toStrict)
import Data.Text.Lazy.Encoding
import qualified Data.Text.Encoding as TE
import Data.Text.Lazy (Text)
import qualified Data.Set as S
import Database.PostgreSQL.Simple
import Database.PostgreSQL.Simple.Ok
import qualified Database.PostgreSQL.Simple.FromField as F
import qualified Database.PostgreSQL.Simple.FromRow as FR
import Data.GraphViz (preview)
import qualified Data.Map as M
import Data.String

data DB = DB { dbName :: String
          , dbUser :: String
          , dbPassword :: String
          , dbHost :: String
          , dbPort :: String
          }deriving(Show)

renderPostgresqlConn (DB n u p h pt)
  = "user=" <> u <> " password=" <> p <> " dbname=" <> n

db = DB "usda" "postgres" "queijo" "localhost" "5432"

type QueryCursor t =(t Key, (HashSchema Key Table, Table))
--setup :: (S.Set Key -> IO [[Showable]]) -> [Key] -> Window -> UI ()
setup
  ::
     (forall t. Traversable t => (QueryCursor t -> IO [t Showable],
         QueryT (t Key)
         -> S.Set Key -> QueryCursor t ))
     -> [S.Set Key] -> Window -> UI ()
setup action k w = void $ do
  return w # set title "Data Browser"
  dbInfo <- UI.span
  UI.button
  element dbInfo # set text (show db)
  (span,keys) <- chooseKey  action k
  getBody w #+ [grid
    [[string "dbInfo",element dbInfo]]]
  getBody w #+ [grid
    [([string "keys" ] <> fmap (element.snd) keys)
    ]]
  getBody w #+ [element span]

chooseKey
  ::
     (forall t. Traversable t => (QueryCursor t  -> IO [t Showable],
         QueryT (t Key)
         -> S.Set Key -> QueryCursor t ))
     -> [S.Set Key] -> UI (Element,[(S.Set Key, Element)])
chooseKey c@(proj,action) items = do
  buttons <- mapM (\k-> do
    fmap (k,) $ UI.button # set text (showVertex k)) items
  span <- UI.span
  spanH <- UI.div
  spanF <- UI.div
  spanHD <- UI.div
  spanD <- UI.div
  spanB <- UI.div
  mapM_ (\(k,b)-> do
    on UI.click  b $ const $ do
      mapM_ (\(_,i)-> element  i # set UI.enabled True ) buttons
      element b # set UI.enabled False
      let (_,(schema,table)) = action (project (fmap Metric (S.toList k))) k
          filterOptions = case M.keys <$> M.lookup k schema of
                Just l -> k : fmap S.singleton l
                Nothing -> [k]
      fitems <- mapM (\kv-> fmap (S.toList kv,) $ UI.button # set UI.text (showVertex kv) ) filterOptions
      element spanF # set children (fmap snd fitems)
      let baseAction m = action m k
      mapM_ (\(fk,fb)-> do
        on UI.click  fb $ const $ do
          let
            doQuery :: (forall t. Traversable t =>
                  (QueryCursor t  -> IO [t Showable],
                    QueryT (t Key)
                    -> S.Set Key -> QueryCursor t )) ->
                  [Key] -> UI [PK Showable]
            doQuery (p,a) arg =  liftIO $ p $ a projectDesc (S.fromList arg)
          v <- doQuery c fk
          vitems <- mapM (\kv-> fmap (pkKey kv,) $ UI.button # set UI.text (L.intercalate "," (fmap show (pkDescription kv))) ) v
          mapM_ (\(kv,bv)-> do
            on UI.click bv $ const $ do
              let ares@(m,(schema,t)) = baseAction ( do
                  predicate $  fmap (\(fkv,kv)-> (fkv,Category (S.fromList [T.pack $ show kv]))) $ zip  fk   kv
                  projectAll
                  )
              kvd <- liftIO $ proj ares
              element spanHD # set text  (showVertex  (allKeys t))
              elems <- mapM (\i-> UI.li # set text (L.intercalate "," (fmap show i))) (fmap (zip (S.toList $allKeys t)) kvd)
              element spanD # set children elems
              ) vitems
          element spanB # set children (fmap snd vitems)
          ) fitems
      element spanH # set text (show $ fmap keyType (S.toList k))
      element span # set children [spanH,spanF,spanB,spanHD,spanD]
      ) buttons
  return (span,buttons)

graphKeySet g
  =  L.nub $ concatMap S.toList (hvertices g <> tvertices g)

graphAttributeSet baseTables
  =  S.unions $ fmap allKeys $ fmap snd $ M.toList baseTables

data Showable
  = Showable Text
  | Numeric Int
  | DNumeric Double
  | SOptional (Maybe Showable)
  | SComposite (Vector Showable)

renderedType key = \f b ->
   case F.name f  of
      Just name -> let
          go ::  KType
                -> F.Conversion Showable
          go t = case t of
            (KOptional (Primitive i)) -> SOptional <$> prim name i f b
            (Array (Primitive i)) -> SComposite <$> prim name i f b
            (KOptional (Array (Primitive i))) ->  fmap (SOptional . fmap SComposite . getCompose ) $ prim name i f b
            (Primitive i) ->  fmap unOnly $ prim  name i f b
          in case (keyValue key == T.fromStrict (TE.decodeUtf8 name)) of
              True ->  go (keyType key)
              False -> error $ "no match type for " <> BS.unpack name <> " with key" <> show key
      Nothing -> error "no name for field"
     where


unOnly :: Only a -> a
unOnly (Only i) = i

prim :: (F.FromField (f1 Text), F.FromField (f1 Double), F.FromField (f1 Int), Functor f1) =>
          BS.ByteString
        -> Text
        -> F.Field
        -> Maybe BS.ByteString
        -> F.Conversion (f1 Showable)
prim  name p f b = case p of
            "text" ->  s $ F.fromField f b
            "character" ->  s $ F.fromField  f b
            "int8" -> n $ F.fromField  f b
            "int4" -> n $ F.fromField  f b
            "double precision" -> d $ F.fromField  f b
            "float8" -> d $ F.fromField  f b
            "integer" -> n $ F.fromField f b
            "smallint" -> n $ F.fromField f b
            i-> error $ "no case for field " <> BS.unpack name <> " of type " <> T.unpack i <> " in renderedType"
  where
    s = fmap (fmap Showable)
    n = fmap (fmap Numeric)
    d = fmap (fmap DNumeric)

instance (F.FromField (f (g a))) => F.FromField (Compose f g a) where
   fromField = fmap (fmap (fmap (Compose ) )) $ F.fromField

instance F.FromField a => F.FromField (Only a) where
  fromField = fmap (fmap (fmap Only)) F.fromField


fromShowableList foldable = do
    let keyMap = keySetToMap foldable
    n <- FR.numFieldsRemaining
    traverse (FR.fieldWith . renderedType) foldable

keySetToMap ks = M.fromList $  fmap (\(Key k _ t)-> (toStrict $ encodeUtf8 k,t))  (F.toList ks)

instance Show Showable where
  show (Showable a) = T.unpack a
  show (Numeric a) = show a
  show (DNumeric a) = show a
  show (SOptional a) = show a

projectKey
  :: Traversable t => Connection
     -> M.Map (S.Set Key) Table
     -> HashSchema Key Table ->
     ((t Key, (HashSchema Key Table, Table)) -> IO [t Showable],
         QueryT (t Key)
         -> S.Set Key -> (t Key, (HashSchema Key Table, Table)))
projectKey conn baseTables hashGraph = (\(j,(h,i)) -> queryWith_ (fromShowableList j) conn . buildQuery $ i, projectAllKeys baseTables hashGraph )

withConn action = do
  conn <- connectPostgreSQL "user=postgres password=queijo dbname=usda "
  action conn

main :: IO ()
main = do
  let schema = "public"
  conn <- connectPostgreSQL "user=postgres password=queijo dbname=usda "
  inf@(k,baseTables) <- keyTables conn  schema
  connTest <- connectPostgreSQL "user=postgres password=queijo dbname=test"
  traverse (execute_ connTest . fromString . T.unpack . dropTable) baseTables
  traverse (execute_  connTest . fromString . T.unpack . createTable) baseTables

  --print baseTables
  graph <- fmap graphFromPath $ schemaKeys conn  schema inf
  graphAttributes <- fmap graphFromPath $ schemaAttributes conn  schema inf
  let
      g1 = warshall graph
      schema = hashGraph  g1
      q = projectKey conn  baseTables schema
  startGUI defaultConfig (setup q (M.keys baseTables))
  print "END"

