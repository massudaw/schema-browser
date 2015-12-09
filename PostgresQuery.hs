{-# LANGUAGE ConstraintKinds,TypeFamilies ,DeriveTraversable,DeriveFoldable,StandaloneDeriving,RecursiveDo,FlexibleInstances,RankNTypes,NoMonomorphismRestriction,ScopedTypeVariables,UndecidableInstances,FlexibleContexts,OverloadedStrings ,TupleSections, ExistentialQuantification #-}
module PostgresQuery where
import Types
import Control.Monad
import Utils
import GHC.Stack
import Schema
import RuntimeTypes
import Data.Bifunctor
import Query
import Control.Monad.Writer hiding (pass)
import System.Time.Extra
import Patch
import Debug.Trace
import Data.Ord
import Data.Functor.Identity
import qualified  Data.Map as M

import Postgresql
import Data.Tuple
import Data.String

import Control.Applicative
import Control.Monad.IO.Class
import Data.Maybe
import qualified Data.List as L

import Data.Monoid
import Prelude hiding (takeWhile,head)


import qualified Data.Foldable as F
import qualified Data.Text as T
import Data.Text (Text)
import qualified Data.Set as S
import qualified Database.PostgreSQL.Simple.ToField as TF
import qualified Database.PostgreSQL.Simple.FromRow as FR
import Database.PostgreSQL.Simple
-- import Data.GraphViz (preview)


insertPatch
  :: (PatchConstr Key a ,MonadIO m ,Functor m ,TF.ToField (TB Identity Key a ))
     => (TBData Key () -> FR.RowParser (TBData Key a ))
     -> Connection
     -> TBIdx Key a
     -> Table
     -> m (TBIdx Key a )
insertPatch f conn path@(m ,s,i ) t =  if not $ L.null serialAttr
      then do
        let
          iquery :: String
          iquery = T.unpack $ prequery <> " RETURNING ROW(" <>  T.intercalate "," (projKey serialAttr) <> ")"
        liftIO $ print iquery
        out <-  fmap head $ liftIO $ queryWith (f (mapRecord (const ()) serialTB )) conn (fromString  iquery ) directAttr
        let Just (_,_ ,gen) = diff serialTB out -- :: Maybe (TBIdx Key a)
        return (m,getPKM out ,compact (i <> gen ) )
      else do
        let
          iquery = T.unpack prequery
        liftIO $ print iquery
        liftIO $ execute  conn (fromString  iquery ) directAttr
        return path
    where
      prequery =  "INSERT INTO " <> rawFullName t <>" ( " <> T.intercalate "," (projKey directAttr ) <> ") VALUES (" <> T.intercalate "," (fmap (const "?") $ projKey directAttr)  <> ")"
      attrs =  concat $ nonRefTB . create <$> i
      testSerial (k,v ) = (isSerial .keyType $ k) && (isNothing. unSSerial $ v)
      serial f =  filter (all1 testSerial  .f)
      direct f = filter (not.all1 testSerial .f)
      serialAttr = serial aattri attrs
      directAttr = direct aattri attrs
      projKey = fmap (keyValue ._relOrigin) . concat . fmap keyattri
      serialTB = reclist' t (fmap _tb  serialAttr)
      all1 f [] = False
      all1 f i = all f i



deletePatch
  :: (PatchConstr Key a ,TF.ToField (TB Identity Key  a ) ) =>
     Connection ->  TBIdx Key a -> Table -> IO (TBIdx Key a)
deletePatch conn patch@(m ,kold ,_) t = do
    execute conn (fromString $ traceShowId $ T.unpack del) koldPk
    return patch
  where
    equality k = attrValueName k <> "="  <> "?"
    koldPk = uncurry Attr <$> F.toList kold
    pred   =" WHERE " <> T.intercalate " AND " (fmap  equality koldPk)
    del = "DELETE FROM " <> rawFullName t <>   pred


updatePatch
  :: TF.ToField (TB Identity Key Showable) =>
     Connection -> TBData Key Showable -> TBData Key Showable -> Table -> IO (TBIdx Key Showable)
updatePatch conn kv old  t =
    execute conn (fromString $ traceShowId $ T.unpack up)  (skv <> koldPk ) >> return patch
  where
    patch  = justError ("cant diff states" <> (concat $ zipWith differ (show kv) (show old))) $ diff old kv
    kold = getPKM old
    equality k = k <> "="  <> "?"
    koldPk = uncurry Attr <$> F.toList kold
    pred   =" WHERE " <> T.intercalate " AND " (equality . keyValue . fst <$> F.toList kold)
    setter = " SET " <> T.intercalate "," (equality .   attrValueName <$> skv   )
    up = "UPDATE " <> rawFullName t <> setter <>  pred
    skv = unTB <$> F.toList  (_kvvalues $ unTB tbskv)
    tbskv = snd isM
    isM :: TBData Key  Showable
    isM =  justError ("cant diff befor update" <> show (kv,old)) $ diffUpdateAttr kv old

differ = (\i j  -> if i == j then [i]  else "(" <> [i] <> "|" <> [j] <> ")" )

paginate conn t order off size k eqpred = do
    let (que,attr) = case k of
          (Just koldpre) ->
            let
              que =  selectQuery t <> pred <> orderQ
              koldPk :: [TB Identity Key Showable]
              koldPk =  uncurry Attr <$> L.sortBy (comparing ((`L.elemIndex` (fmap fst order)).fst)) koldpre
            in (que,koldPk <> tail (reverse koldPk) <> eqpk )
          Nothing ->
            let
              que =  selectQuery t <> pred <> orderQ
            in (que,eqpk)
    let quec = fromString $ T.unpack $ "SELECT *,count(*) over () FROM (" <> que <> ") as q " <> offsetQ <> limitQ
    print (quec,attr)
    v <- uncurry (queryWith (withCount (fromRecord (unTlabel' t)) ) conn) (quec,attr)
    print (maybe 0 (\c-> c - off ) $ safeHead ( fmap snd v :: [Int]))
    return ((maybe 0 (\c-> c - off ) $ safeHead ( fmap snd v :: [Int])), fmap fst v)
  where pred = maybe "" (const " WHERE ") (fmap (fmap snd)   k <> fmap (concat . fmap  (fmap TB1 .F.toList . snd)) eqpred) <> T.intercalate " AND " (maybe [] (const $ pure $ generateComparison (first (justLabel t) <$> order)) k <> (maybe [] pure $ eqquery <$> eqpred))
        equality (pred,k) = inattr k <> pred <> "?"
        eqquery :: [(Text,TB Identity Key a)] -> Text
        eqquery eqpred = T.intercalate " AND " (equality . second (firstTB (justLabel t)) <$> eqpred)
        eqpk :: [TB Identity Key Showable]
        eqpk =  maybe [] ( L.sortBy (comparing ((`L.elemIndex` (fmap fst order)). inattr )))  (fmap snd <$> eqpred)
        offsetQ = " OFFSET " <> T.pack (show off)
        limitQ = " LIMIT " <> T.pack (show size)
        orderQ = " ORDER BY " <> T.intercalate "," ((\(l,j)  -> l <> " " <> showOrder j ) . first (justLabel t) <$> order)



data View
  = View
  { tree :: TB3Data (Labeled Text) Key ()
  , viewOrder :: [(Key,Order)]
  , viewProjection :: [Key]
  , pagination :: (Int,Int,Int,Maybe [(Key,FTB Showable)])
  }

justLabel :: TB3Data (Labeled Text ) Key () -> Key -> Text
justLabel t =  justError "cant find label" .getLabels t

-- tableType :: TB1 () -> Text


getLabels t k =  M.lookup  k (mapLabels label' t)
    where label' (Labeled l (Attr k _)) =  (k,l )
          label' (Labeled l (IT k tb )) = (lattr k, l <> " :: " <> tableType tb)
          label' (Unlabeled (Attr k _)) = (k,keyValue k)
          label' (Unlabeled (IT k _)) = (lattr k,keyValue $ lattr k )
          lattr =_tbattrkey . labelValue .getCompose


mapLabels label' t =  M.fromList $ fmap (label'. getCompose.labelValue.getCompose) (getAttr $ joinNonRef' t)


-- Generate SORT Order

generateSort v = T.intercalate "," (generateSort' <$> v)
generateSort' (k,v) =  k <> " " <>   showOrder v

-- Generate Comparison Operator

generateComparison ((k,v):[]) = k <>  dir v <> "?"
  where dir Asc = ">"
        dir Desc = "<"
generateComparison ((k,v):xs) = "case when " <> k <>  "=" <> "? OR "<> k <> " is null  then " <>  generateComparison xs <> " else " <> k <>  dir v <> "?" <>" end"
  where dir Asc = ">"
        dir Desc = "<"

-- High level db operations

insertMod :: InformationSchema ->  TBData Key Showable -> TransactionM (Maybe (TableModification (TBIdx Key Showable)))
insertMod inf j  = liftIO$ do
  let
      table = lookTable inf (_kvname (fst  j))
  kvn <- insertPatch fromRecord (conn  inf) (patch j) table
  let mod =  TableModification Nothing table kvn
  Just <$> logTableModification inf mod


deleteMod :: InformationSchema ->  TBData Key Showable -> TransactionM (Maybe (TableModification (TBIdx Key Showable)))
deleteMod inf j@(meta,_) = liftIO$ do
  let patch =  (tableMeta table, getPKM j,[])
      table = lookTable inf (_kvname (fst  j))
  deletePatch (conn inf)  patch table
  Just <$> logTableModification inf (TableModification Nothing table patch)

updateMod :: InformationSchema -> TBData Key Showable -> TBData Key Showable -> TransactionM (Maybe (TableModification (TBIdx Key Showable)))
updateMod inf kv old = liftIO$ do
  let table = lookTable inf (_kvname (fst  old ))
  patch <- updatePatch (conn  inf) kv  old  table
  let mod =  TableModification Nothing table patch
  Just <$> logTableModification inf mod

selectAll
  ::
     InformationSchema
     -> TableK Key
     -> Maybe PageToken
     -> Int
     -> [(Key, Order)]
     -> [(T.Text, Column Key Showable)]
     -> TransactionM  (Int,
           [(KVMetadata Key,
             Compose
               Identity (KV (Compose Identity (TB Identity))) Key Showable)])
selectAll inf table i  j k st = do
      let
          unref (TableRef i) = i
          tbf =  tableView (tableMap inf) table
      liftIO $ print (tableName table,selectQuery tbf )
      let m = tbf
      (t,v) <- liftIO$ duration  $ paginate (conn inf) m k 0 j (fmap unref i) (nonEmpty st)
      mapM_ (tellRefs inf  ) (snd v)
      liftIO$ print (tableName table,t)
      return v

tellRefs  ::  InformationSchema ->TBData Key Showable ->  TransactionM ()
tellRefs  inf (m,k) = mapM_ (tellRefsAttr . unTB ) $ F.toList  (_kvvalues $ unTB k)
  where tellRefsAttr (FKT l k t) = void $ do
            tell ((\m@(k,v) -> TableModification Nothing (lookTable inf (_kvname k)) . patch $ m) <$> F.toList t)
            mapM_ (tellRefs inf) $ F.toList t
        tellRefsAttr (Attr _ _ ) = return ()
        tellRefsAttr (IT _ t ) = void $ mapM (tellRefs inf) $ F.toList t

loadDelayed :: InformationSchema -> TBData Key () -> TBData Key Showable -> IO (Maybe (TBIdx Key Showable))
loadDelayed inf t@(k,v) values@(ks,vs)
  | S.null $ _kvdelayed k = return Nothing
  | L.null delayedattrs  = return Nothing
  | otherwise = do
       let
           whr = T.intercalate " AND " ((\i-> (keyValue i) <>  " = ?") <$> (_kvpk k) )
           table = justError "no table" $ M.lookup (S.fromList $ _kvpk k) (pkMap inf)
           delayedTB1 =  (ks,) . _tb $ KV ( filteredAttrs)
           delayed =  mapKey' (kOptional . ifDelayed . ifOptional) (mapValue' (const ()) delayedTB1)
           str = "SELECT " <> explodeRecord (relabelT' runIdentity Unlabeled delayed) <> " FROM " <> showTable table <> " WHERE " <> whr
       print str
       is <- queryWith (fromRecord delayed) (conn inf) (fromString $ T.unpack str) (fmap unTB $ F.toList $ _kvvalues $  runIdentity $ getCompose $ tbPK' (tableNonRef' values))
       case is of
            [] -> errorWithStackTrace "empty query"
            [i] ->return $ fmap (\(i,j,a) -> (i,getPKM (ks,vs),a)) $ diff delayedTB1(mapKey' (kOptional.kDelayed.unKOptional) . mapFValue' (LeftTB1 . Just . DelayedTB1 .  unSOptional ) $ i  )
            _ -> errorWithStackTrace "multiple result query"
  where
    delayedattrs = concat $ fmap (keyValue . (\(Inline i ) -> i)) .  F.toList <$> M.keys filteredAttrs
    filteredAttrs = M.filterWithKey (\key v -> S.isSubsetOf (S.map _relOrigin key) (_kvdelayed k) && (all (maybe False id) $ fmap (fmap (isNothing .unSDelayed)) $ fmap unSOptional $ kattr $ v)  ) (_kvvalues $ unTB vs)

connRoot dname = (fromString $ "host=" <> host dname <> " port=" <> port dname  <> " user=" <> user dname <> " dbname=" <> dbn  dname <> " password=" <> pass dname ) -- <> " sslmode= require" )



postgresOps = SchemaEditor updateMod insertMod deleteMod (\i j p g s o-> (\(l,i) -> (fmap TB1 i,Just $ TableRef  (filter (flip L.elem (fmap fst s) . fst ) $  getPK $ TB1 $ last i) ,l)) <$> selectAll i j p (fromMaybe 200 g) s o ) (\_ _ _ _ _ -> return ([],Nothing,0)) (\inf table -> liftIO . loadDelayed inf (unTlabel' $ tableView (tableMap inf) table ))
