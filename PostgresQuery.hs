{-# LANGUAGE ConstraintKinds,TypeFamilies ,DeriveTraversable,DeriveFoldable,StandaloneDeriving,RecursiveDo,FlexibleInstances,RankNTypes,NoMonomorphismRestriction,ScopedTypeVariables,UndecidableInstances,FlexibleContexts,OverloadedStrings ,TupleSections, ExistentialQuantification #-}
module PostgresQuery where
import Types
import Control.Monad
import Utils
import Data.Bifunctor
import Query
import Patch
import Debug.Trace
import Data.Ord
import Data.Functor.Identity
import qualified  Data.Map as M

import Postgresql
import Data.Tuple
-- import Schema
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
        let Just (_,_ ,gen) = difftable serialTB out
        return $ (m,getPKM out ,compactAttr (i <> gen))
      else do
        let
          iquery = T.unpack prequery
        liftIO $ print iquery
        liftIO $ execute  conn (fromString  iquery ) directAttr
        return path
    where
      prequery =  "INSERT INTO " <> rawFullName t <>" ( " <> T.intercalate "," (projKey directAttr ) <> ") VALUES (" <> T.intercalate "," (fmap (const "?") $ projKey directAttr)  <> ")"
      attrs =  concat $ nonRefTB . createAttr <$> i
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
    patch  = justError ("cant diff states" <> (concat $ zipWith differ (show kv) (show old))) $ difftable old kv
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
              que =  selectQuery (TB1 t) <> pred <> orderQ
              koldPk :: [TB Identity Key Showable]
              koldPk =  uncurry Attr <$> L.sortBy (comparing ((`L.elemIndex` (fmap fst order)).fst)) koldpre
            in (que,koldPk <> tail (reverse koldPk) <> eqpk )
          Nothing ->
            let
              que =  selectQuery (TB1 t) <> pred <> orderQ
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




