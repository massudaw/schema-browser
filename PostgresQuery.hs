{-# LANGUAGE ConstraintKinds,TypeFamilies ,DeriveTraversable,DeriveFoldable,StandaloneDeriving,RecursiveDo,FlexibleInstances,RankNTypes,NoMonomorphismRestriction,ScopedTypeVariables,UndecidableInstances,FlexibleContexts,OverloadedStrings ,TupleSections, ExistentialQuantification #-}
module PostgresQuery where
import Types
import Control.Monad
import Utils
import Query
import Patch
import Debug.Trace
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
import Prelude hiding (takeWhile)


import qualified Data.Foldable as F
import qualified Data.Text.Lazy as T
import Data.Text.Lazy (Text)
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
        return $ (m,s,compactAttr (i <> gen))
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
    patch  = justError ("cant diff states" <> show (kv,old)) $ difftable old kv
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



selectQueryWherePK
  :: (MonadIO m ,Functor m ,TF.ToField (TB Identity Key Showable ))
     => (TBData Key () -> FR.RowParser (TBData Key Showable ))
     -> Connection
     -> TB3Data (Labeled Text) Key ()
     -> Text
     -> [(Key,FTB Showable )]
     -> m (TBData Key Showable )
selectQueryWherePK f conn t rel kold =  do
        liftIO$ print que
        liftIO $ head <$> queryWith (f (unTlabel' t) ) conn que koldPk
  where pred = " WHERE " <> T.intercalate " AND " (equality . label . getCompose <$> fmap (labelValue.getCompose) (getPKAttr $ joinNonRef' t))
        que = fromString $ T.unpack $ selectQuery (TB1 t) <> pred
        equality k = k <> rel   <> "?"
        koldPk :: [TB Identity Key Showable ]
        koldPk = (\(Attr k _) -> Attr k (justError ("no value for key " <> show k) $ M.lookup k (M.fromList kold)) ) <$> fmap (labelValue .getCompose.labelValue.getCompose) (getPKAttr $ joinNonRef' t)


selectQueryWhere
  :: (MonadIO m ,Functor m )
--      => (TBData Key () -> FR.RowParser (TBData Key Showable ))
     => Connection
     -> TB3Data (Labeled Text) Key ()
     -> Text
     -> [(Key,FTB Showable )]
     -> m [TBData Key Showable]
selectQueryWhere  conn t rel kold =  do
        liftIO$ print que
        let filterRec = filterTB1' ( not . (`S.isSubsetOf`  (S.fromList (fst <$> kold))) . S.fromList . fmap _relOrigin.  keyattr )
        liftIO  $ fmap filterRec <$> queryWith (fromRecord ( unTlabel' t) ) conn que koldPk
  where pred = " WHERE " <> T.intercalate " AND " (equality . label <$> filter ((`S.isSubsetOf` (S.fromList (fst <$> kold))). S.singleton . keyAttr . labelValue ) ( fmap (getCompose.labelValue.getCompose) (getAttr $ joinNonRef' t)))
        que = fromString $ T.unpack $ selectQuery (TB1 t) <> pred
        equality k = k <> rel   <> "?"
        koldPk :: [TB Identity Key Showable ]
        koldPk = catMaybes $ (\(Attr k _) -> Attr k <$> ( M.lookup k (M.fromList kold)) ) <$> fmap (labelValue .getCompose.labelValue.getCompose) (getAttr $ joinNonRef' t)

paginate  conn t order off size Nothing = do
        liftIO$ print que
        liftIO $ queryWith_ (fromRecord (unTlabel' t) ) conn que
  where
        limitQ = " LIMIT " <> T.pack (show size)
        offsetQ = " OFFSET " <> T.pack (show off)
        orderQ = " ORDER BY " <> T.intercalate "," ((\(l,j)  -> l <> " " <> showOrder j ) <$> lookLabels t order)
        que = fromString $ T.unpack $ selectQuery (TB1 t) <> orderQ <> offsetQ <> limitQ

paginate  conn t order off size (Just kold) = do
        liftIO$ print que
        liftIO $ queryWith (fromRecord (unTlabel' t) ) conn que (koldPk <> reverse koldPk)
  where pred = " WHERE " <> generateComparison (lookLabels t order)
        offsetQ = " OFFSET " <> T.pack (show off)
        limitQ = " LIMIT " <> T.pack (show size)
        orderQ = " ORDER BY " <> T.intercalate "," ((\(l,j)  -> l <> " " <> showOrder j ) <$> lookLabels t order)
        que = fromString $ T.unpack $ selectQuery (TB1 t) <> pred <> orderQ <> offsetQ <> limitQ
        koldPk :: [TB Identity Key Showable ]
        koldPk = catMaybes $ (\(Attr k _) -> Attr k <$>(  M.lookup k (M.fromList kold)))  <$> fmap (labelValue .getCompose.labelValue.getCompose) (getAttr $ joinNonRef' t)

lookLabels t kold  =  catMaybes $ label' <$> fmap (getCompose.labelValue.getCompose) (getAttr $ joinNonRef' t)
    where label' (Labeled l (Attr k _)) =  (l,) <$>  ( M.lookup k (M.fromList kold))
          label' (Unlabeled (Attr k _)) = (keyValue k,) <$> ( M.lookup k (M.fromList kold))



generateSort v = T.intercalate "," (generateSort' <$> v)
generateSort' (k,v) =  k <> " " <>   showOrder v

generateComparison [] = "false"
generateComparison ((k,v):xs) = "case when " <> k <>  "=" <> "?" <> " then " <>  generateComparison xs <> " else " <> k <>  dir v <> "?" <>" end"
  where dir Asc = ">"
        dir Desc = "<"
