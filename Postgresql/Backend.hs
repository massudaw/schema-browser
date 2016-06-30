{-# LANGUAGE FlexibleContexts,TypeFamilies ,NoMonomorphismRestriction,OverloadedStrings ,TupleSections #-}
module Postgresql.Backend where

import Types
import qualified Types.Index as G
import Step.Common
import Step.Host
import Safe
import Control.Monad
import Postgresql.Printer
import Postgresql.Parser
import Utils
import Control.Monad.Reader
import GHC.Stack
import Schema
import RuntimeTypes
import Data.Bifunctor
import Query
import Control.Monad.Writer hiding (pass)
import System.Time.Extra
import Types.Patch
import Debug.Trace
import Data.Ord
import Data.Functor.Identity
import qualified  Data.Map as M

import Data.Tuple
import Data.String

import Control.Applicative
import Data.Maybe
import qualified Data.List as L

import Prelude hiding (takeWhile,head)

import qualified Data.Foldable as F
import qualified Data.Text as T
import Data.Text (Text)
import qualified Data.Set as S
import qualified Database.PostgreSQL.Simple.FromRow as FR
import Database.PostgreSQL.Simple

insertPatch
  :: (MonadIO m ,Functor m )
     => (TBData PGKey () -> FR.RowParser (TBData PGKey Showable ))
     -> Connection
     -> TBIdx PGKey Showable
     -> TableK PGKey
     -> m (TBIdx PGKey Showable )
insertPatch f conn path@(m ,s,i ) t =  liftIO$ if not $ L.null serialAttr
      then do
        let
          iquery :: String
          iquery = T.unpack $ prequery <> " RETURNING ROW(" <>  T.intercalate "," (projKey serialAttr) <> ")"
        out <-  fmap safeHead $ liftIO $ queryWith (f (mapRecord (const ()) serialTB )) conn (fromString  iquery ) directAttr
        let Just (_,_ ,gen) =  join $ diff serialTB <$> out
            comp = compact (i <> gen)
        return (m, G.getIndex (justError "no out insert" out) ,comp )
      else do
        let
          iquery = T.unpack prequery
        print iquery
        execute  conn (fromString  iquery ) directAttr
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
  ::
     Connection ->  TBIdx PGKey Showable -> Table -> IO (TBIdx PGKey Showable)
deletePatch conn patch@(m ,G.Idex kold ,_) t = do
    execute conn (fromString $ traceShowId $ T.unpack del) koldPk
    return patch
  where
    equality k = attrValueName k <> "="  <> "?"
    koldPk = uncurry Attr <$> M.toList kold
    pred   =" WHERE " <> T.intercalate " AND " (fmap  equality koldPk)
    del = "DELETE FROM " <> rawFullName t <>   pred

applyPatch
  ::
     Connection -> TBIdx PGKey Showable -> IO (TBIdx PGKey Showable)
applyPatch conn patch@(m,G.Idex kold,skv)  =
    execute conn (fromString $ traceShowId $ T.unpack up)  (fmap attrPatchValue skv <> koldPk ) >> return patch
  where
    equality k = k <> "="  <> "?"
    koldPk = uncurry Attr <$> M.toList kold
    attrPatchName (PAttr k _) = keyValue k
    attrPatchValue (PAttr  k v) = Attr k (create v) :: TB Identity PGKey Showable
    pred   =" WHERE " <> T.intercalate " AND " (equality . keyValue . fst <$> M.toList kold)
    setter = " SET " <> T.intercalate "," (equality .   attrPatchName <$> skv   )
    up = "UPDATE " <> kvfullname m <> setter <>  pred


updatePatch
  ::
     Connection -> TBData PGKey Showable -> TBData PGKey Showable -> Table -> IO (TBIdx PGKey Showable)
updatePatch conn kv old  t =
    execute conn (fromString $ traceShowId $ T.unpack up)  (skv <> koldPk ) >> return patch
  where
    patch  = justError ("cant diff states" <> (concat $ zipWith differ (show kv) (show old))) $ diff old kv
    kold = M.toList $ getPKM old
    equality k = k <> "="  <> "?"
    koldPk = uncurry Attr <$> kold
    pred   =" WHERE " <> T.intercalate " AND " (equality . keyValue . fst <$> kold)
    setter = " SET " <> T.intercalate "," (equality .   attrValueName <$> skv   )
    up = "UPDATE " <> rawFullName t <> setter <>  pred
    skv = unTB <$> F.toList  (_kvvalues $ unTB tbskv)
    tbskv = snd isM
    isM :: TBData PGKey  Showable
    isM =  justError ("cant diff befor update" <> show (kv,old)) $ diffUpdateAttr kv old

differ = (\i j  -> if i == j then [i]  else "(" <> [i] <> "|" <> [j] <> ")" )

paginate inf t order off size koldpre wherepred = do
    let (que,attr) =
            let
              que =  selectQuery t <> pred <> orderQ
            in (que, ordevalue <>  predvalue )
    let quec = fromString $ T.unpack $ "SELECT *,count(*) over () FROM (" <> que <> ") as q " <> offsetQ <> limitQ
    print quec
    v <- uncurry (queryWith (withCount (fromRecord (unTlabel' t)) ) (conn inf ) ) (quec, maybe [] (fmap (firstTB (recoverFields inf)))  attr)
    print (maybe 0 (\c-> c - off ) $ safeHead ( fmap snd v :: [Int]))
    return ((maybe 0 (\c-> c - off ) $ safeHead ( fmap snd v :: [Int])), fmap fst v)
  where pred = maybe "" (\i -> " WHERE " <> T.intercalate " AND " i )  ( orderquery <> predquery)
        equality ("IN",k) = inattr k <> " IN " <> " (select unnest(?) )"
        equality (i,k) = " ? " <> i <> inattr k
        (orderquery , ordevalue) =
          let
            oq = (const $ pure $ generateComparison (first (justLabel t) <$> order)) <$> koldpre
            koldPk :: Maybe [TB Identity Key Showable]
            koldPk =  (\k -> uncurry Attr <$> L.sortBy (comparing ((`L.elemIndex` (fmap fst order)).fst)) k ) <$> koldpre
            pkParam =  koldPk <> (tail .reverse <$> koldPk)
          in (oq,pkParam)
        (predquery , predvalue ) = case traceShowId wherepred of
              LegacyPredicate lpred ->
                let
                  eqquery :: [(Text,TB Identity Key a)] -> [Text]
                  eqquery eqpred =  (equality . second (firstTB (justLabel t)) <$> eqpred)
                  eqspred = L.sortBy (comparing ((`L.elemIndex` (fmap fst order)). inattr .snd) )  <$> eqpred
                  eqpk :: Maybe [TB Identity Key Showable]
                  eqpk =  (fmap snd <$> eqspred)
                  eqpred = nonEmpty lpred
                in (eqquery <$> eqspred , eqpk)
              WherePredicate wpred -> printPred t wpred


        offsetQ = " OFFSET " <> T.pack (show off)
        limitQ = " LIMIT " <> T.pack (show size)
        orderQ = " ORDER BY " <> T.intercalate "," ((\(l,j)  -> l <> " " <> showOrder j ) . first (justLabel t) <$> order)

printPred :: Show b => TB3Data (Labeled Text)  Key b ->  BoolCollection (Access Text,Text,FTB Showable) -> (Maybe [Text],Maybe [Column Key Showable])
printPred t (PrimColl (a,e,i)) =
                     let idx = indexFieldL a t
                         opvalue i@"is not null" =  [i]
                         opvalue i@"is null" =  [i]
                         opvalue  i = (\v -> i <> " ? " <> inferParamType e (keyType (fst v))) <$> idx
                         opparam "is not null" =  Nothing
                         opparam "is null" =  Nothing
                         opparam _ = Just $ flip Attr i .fst <$> (idx )

                     in (Just $ zipWith (\i j -> i <> " " <> j) (snd <$> idx) (opvalue e) ,opparam e )
printPred t (OrColl wpred) =
                let
                  w = unzip . fmap (printPred  t) <$> nonEmpty wpred
                in (pure . (\i -> " (" <> i <> ") ") . T.intercalate " OR " <$> join (nonEmpty. concat . catMaybes . fst <$> w) , concat . catMaybes . snd <$> w )
printPred t (AndColl wpred) =
                let
                  w = unzip . fmap (printPred  t) <$> nonEmpty wpred
                in (pure . (\i -> " (" <> i <> ") ") . T.intercalate " AND " <$>  join (nonEmpty . concat . catMaybes .fst <$> w) , concat . catMaybes . snd <$> w )


inferParamType e (KOptional i) = inferParamType e i
inferParamType "<@" (Primitive (AtomicPrim PDate )) = ":: daterange"
inferParamType "<@" (Primitive (AtomicPrim PPosition )) = ":: point3range"
inferParamType "<@" (Primitive (AtomicPrim (PTimestamp i ) )) = case i of
                                                                  Just i -> ":: tsrange"
                                                                  Nothing -> ":: tstzrange"
inferParamType _ _ = ""


data View
  = View
  { tree :: TB3Data (Labeled Text) Key ()
  , viewOrder :: [(Key,Order)]
  , viewProjection :: [Key]
  , pagination :: (Int,Int,Int,Maybe [(Key,FTB Showable)])
  }

justLabel :: TB3Data (Labeled Text ) Key () -> Key -> Text
justLabel t k =  justError ("cant find label"  <> show k <> " - " <> show t).getLabels t $ k



findFKL  l v =  M.lookup (S.fromList l) $ M.mapKeys (S.map (keyString. _relOrigin)) $ _kvvalues $ unLB v
findAttrL l v =  M.lookup (S.fromList $ fmap Inline l) $ M.mapKeys (S.map (fmap keyString)) $ _kvvalues $ unLB v

unLB (Compose (Labeled l v )) = v
unLB (Compose (Unlabeled v )) = v

indexFieldL :: Show a => Access Text -> TB3Data (Labeled Text) Key a -> [(Key,Text)]
indexFieldL p@(IProd b l) v = case  findAttrL  l  (snd v) of
                                Just i -> [utlabel i]
                                Nothing -> case unLB<$>  findFKL l (snd v) of
                                    Just (FKT ref _ _) ->  (\l -> utlabel . justError ("no attr" <> show (ref,l)) . L.find ((==[l]).  fmap (keyValue . _relOrigin). keyattr ) $ unkvlist ref ) <$>l
                                    Nothing -> errorWithStackTrace ("no fkt" <> show (p,snd v))

indexFieldL n@(Nested ix@(IProd b l) nt) v =  concat . fmap (indexFieldL nt) .  F.toList . _fkttable.  unLB $ justError "no nested" $ findFKL l (snd v)
indexFieldL (Many nt ) v =  concat $ flip indexFieldL v <$> nt
indexFieldL (ISum nt ) v =  concat $ flip indexFieldL v <$> nt
indexFieldL i v = errorWithStackTrace (show (i,v))

utlabel = tlabel' . getCompose

tlabel' (Labeled l (Attr k _)) =  (k,l)
tlabel' (Labeled l (IT k tb )) =  (k,l <> " :: " <> tableType tb)
tlabel' (Unlabeled (Attr k _)) = (k,keyValue k)
tlabel' (Unlabeled (IT k v)) =  (k,label $ getCompose $ snd (justError "no it label" $ safeHead (F.toList v)))


getLabels t k =  M.lookup  k (mapLabels label' t)
    where label' (Labeled l (Attr k _)) =  (k,l )
          label' (Labeled l (IT k tb )) = (k, l <> " :: " <> tableType tb)
          label' (Unlabeled (Attr k _)) = (k,keyValue k)
          label' (Unlabeled (IT k v)) = (k, label $ getCompose $ snd (justError "no it label" $ safeHead (F.toList v))  )


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

insertMod :: TBData Key Showable -> TransactionM (Maybe (TableModification (TBIdx Key Showable)))
insertMod j  = do
  inf <- ask
  liftIO $ do
    let
      table = lookTable inf (_kvname (fst  j))
    kvn <- insertPatch (fmap (mapKey' (recoverFields inf)) . fromRecord . (mapKey' (typeTrans inf))) (conn  inf) (patch $ mapKey' (recoverFields inf) j) (mapTableK (recoverFields inf ) table)
    let mod =  TableModification Nothing table (firstPatch (typeTrans inf) $ kvn)
    --Just <$> logTableModification inf mod
    return $ Just  mod


deleteMod :: TBData Key Showable -> TransactionM (Maybe (TableModification (TBIdx Key Showable)))
deleteMod j@(meta,_) = do
  inf <- ask
  log <- liftIO $  do
    let
      patch =  (tableMeta table, G.getIndex  j,[])
      table = lookTable inf (_kvname (fst  j))
    deletePatch (conn inf)  (firstPatch (recoverFields inf) patch) table
    -- Just <$> logTableModification inf (TableModification Nothing table  patch)
    return (TableModification Nothing table  patch)
  tell  (maybeToList $ Just log)
  return $ Just log

updateMod :: TBData Key Showable -> TBData Key Showable -> TransactionM (Maybe (TableModification (TBIdx Key Showable)))
updateMod kv old = do
  inf <- ask
  liftIO$ do
    let table = lookTable inf (_kvname (fst  old ))
    patch <- updatePatch (conn  inf) (mapKey' (recoverFields inf) kv )(mapKey' (recoverFields inf) old ) table
    let mod =  TableModification Nothing table (firstPatch (typeTrans inf) patch)
    -- Just <$> logTableModification inf mod
    return $ Just mod

patchMod :: TBIdx Key Showable -> TransactionM (Maybe (TableModification (TBIdx Key Showable)))
patchMod patch@(m,_,_) = do
  inf <- ask
  liftIO $ do
    let table = lookTable inf (_kvname m )
    patch <- applyPatch (conn  inf) (firstPatch (recoverFields inf ) patch )
    let mod =  TableModification Nothing table (firstPatch (typeTrans inf) patch)
    -- Just <$> logTableModification inf mod
    return (Just mod)


selectAll
  ::
     TableK Key
     -> Int
     -> Maybe PageToken
     -> Int
     -> [(Key, Order)]
     -> WherePredicate
     -> TransactionM  (Int,
           [(KVMetadata Key,
             Compose
               Identity (KV (Compose Identity (TB Identity))) Key Showable)])
selectAll table offset i  j k st = do
      inf <- ask
      let
          unref (TableRef i) = Just i
          unref (HeadToken ) = Nothing
          tbf =  tableView (tableMap inf) table
      let m = tbf
      (t,v) <- liftIO$ duration  $ paginate inf m k offset j (join $ fmap unref i) st
      mapM_ (tellRefs ) (snd v)
      return v

tellRefs  ::  TBData Key Showable ->  TransactionM ()
tellRefs  (m,k) = do
    inf <- ask
    let
        tellRefsAttr (FKT l k t) = void $ do
            tell ((\m@(k,v) -> TableModification Nothing (lookTable inf (_kvname k)) . patch $ m) <$> F.toList t)
            mapM_ (tellRefs ) $ F.toList t
        tellRefsAttr (Attr _ _ ) = return ()
        tellRefsAttr (IT _ t ) = void $ mapM (tellRefs ) $ F.toList t
    mapM_ (tellRefsAttr . unTB ) $ F.toList  (_kvvalues $ unTB k)

loadDelayed :: InformationSchema -> TBData Key () -> TBData Key Showable -> IO (Maybe (TBIdx Key Showable))
loadDelayed inf t@(k,v) values@(ks,vs)
  | L.null $ _kvdelayed k = return Nothing
  | L.null delayedattrs  = return Nothing
  | otherwise = do
       let
           whr = T.intercalate " AND " ((\i-> (keyValue i) <>  " = ?") <$> (_kvpk k) )
           table = justError "no table" $ M.lookup (S.fromList $ _kvpk k) (pkMap inf)
           delayedTB1 =  (ks,) . _tb $ KV ( filteredAttrs)
           delayed =  mapKey' (kOptional . ifDelayed . ifOptional) (mapValue' (const ()) delayedTB1)
           str = "SELECT " <> explodeRecord (relabelT' runIdentity Unlabeled delayed) <> " FROM " <> showTable table <> " WHERE " <> whr
       print str
       is <- queryWith (fromRecord delayed) (conn inf) (fromString $ T.unpack str) (fmap (firstTB (recoverFields inf) .unTB) $ F.toList $ _kvvalues $  runIdentity $ getCompose $ tbPK' (tableNonRef' values))
       case is of
            [] -> errorWithStackTrace "empty query"
            [i] ->return $ fmap (\(i,j,a) -> (i,G.getIndex (ks,vs),a)) $ diff delayedTB1(mapKey' (kOptional.kDelayed.unKOptional) . mapFValue' (LeftTB1 . Just . DelayedTB1 .  unSOptional ) $ i  )
            _ -> errorWithStackTrace "multiple result query"
  where
    delayedattrs = concat $ fmap (keyValue . (\(Inline i ) -> i)) .  F.toList <$> M.keys filteredAttrs
    filteredAttrs = M.filterWithKey (\key v -> S.isSubsetOf (S.map _relOrigin key) (S.fromList $ _kvdelayed k) && (all (maybe False id) $ fmap (fmap (isNothing .unSDelayed)) $ fmap unSOptional $ kattr $ v)  ) (_kvvalues $ unTB vs)

connRoot dname = (fromString $ "host=" <> host dname <> " port=" <> port dname  <> " user=" <> user dname <> " dbname=" <> dbn  dname <> " password=" <> pass dname ) -- <> " sslmode= require" )



postgresOps = SchemaEditor updateMod patchMod insertMod deleteMod (\ j off p g s o-> (\(l,i) -> (i,(TableRef . filter (flip L.elem (fmap fst s) . fst ) .  M.toList . getPKM <$> lastMay i) ,l)) <$> selectAll  j (fromMaybe 0 off) p (fromMaybe 200 g) s o )  (\table j -> do
    inf <- ask
    liftIO . loadDelayed inf (unTlabel' $ tableView (tableMap inf) table ) $ j ) mapKeyType undefined undefined logTableModification
