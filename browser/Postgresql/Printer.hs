{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
module Postgresql.Printer
  (selectQuery
  ,tableType
  ,explodeRecord
  ,expandBaseTable
  ,createTable
  ,dropTable
  )
  where

import Query
import Debug.Trace
import Data.Ord
import Types.Index (TBIndex(..))
import Data.String
import Step.Host (findFK,findAttr,findFKAttr)
import Step.Common
import NonEmpty (NonEmpty(..))
import Data.Functor.Apply
import Data.Bifunctor
import qualified Data.Foldable as F
import qualified Data.Traversable as Tra
import Data.Maybe
import Data.Monoid hiding (Product)

import qualified Data.Text as T

import Utils

import Prelude hiding (head)
import Control.Monad
import Control.Applicative
import Data.Functor.Identity
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad.Writer
import Data.Text (Text)
import GHC.Stack

import Types
import Types.Inference




--
-- Patch CRUD Postgresql Operations
--



dropTable :: Table -> Text
dropTable r= "DROP TABLE "<> rawFullName r


-- createTable :: Table -> Text
createTable r@(Raw _ sch _ _ _ _ tbl _ _ _ pk _ fk inv attr _) = "CREATE TABLE " <> rawFullName r  <> "\n(\n\t" <> T.intercalate ",\n\t" commands <> "\n)"
  where
    commands = (renderAttr <$> S.toList attr ) <> [renderPK] <> fmap renderFK (S.toList fk)
    renderAttr k = keyValue k <> " " <> renderTy (keyType k) <> if  (isKOptional (keyType k)) then "" else " NOT NULL"
    renderKeySet pk = T.intercalate "," (fmap keyValue (S.toList pk ))
    renderTy (KOptional ty) = renderTy ty <> ""
    renderTy (KSerial ty) = renderTy ty <> ""
    renderTy (KInterval ty) = renderTy ty <> ""
    renderTy (KArray ty) = renderTy ty <> "[] "
    renderTy (Primitive ty ) = ty
    -- renderTy (InlineTable s ty ) = s <> "." <> ty
    renderPK = "CONSTRAINT " <> tbl <> "_PK PRIMARY KEY (" <>  renderKeySet (S.fromList pk) <> ")"
    -- renderFK (Path origin (FKJoinTable  ks (_,table)) ) = "CONSTRAINT " <> tbl <> "_FK_" <> table <> " FOREIGN KEY " <>  renderKeySet origin <> ") REFERENCES " <> table <> "(" <> renderKeySet end <> ")  MATCH SIMPLE  ON UPDATE  NO ACTION ON DELETE NO ACTION"
    renderFK (Path origin _  ) = ""



expandInlineTable ::  TB3  (Labeled Text) Key  () -> Text ->  Text
expandInlineTable tb@(TB1 (meta, Compose (Labeled t ((KV i))))) pre=
  let
    query = "(SELECT " <>  T.intercalate "," (aliasKeys  <$> (filter (not .isFun) $ fmap getCompose (sortPosition name) ))  <> ") as " <> t
    name =  tableAttr tb
    isFun  (Labeled a (Fun _ _ _ )) = True
    isFun  _ = False
    aliasKeys (Labeled  a (Attr n    _ ))  =  "(" <> pre <> ")." <> keyValue n <> " as " <> a
       -- aliasKeys (Labeled  a (Fun n f fs ))  =  "" -- f <> "(" "(" <> t <> ")." <> keyValue n <> " as " <> a
   in query
expandInlineTable tb _ = errorWithStackTrace (show tb)


expandInlineArrayTable ::  TB3  (Labeled Text) Key  () -> Text ->  Text
expandInlineArrayTable tb@(TB1 (meta, Compose (Labeled t ((KV i))))) pre =
   let query = "(SELECT " <>  T.intercalate "," (aliasKeys  . getCompose <$>   sortPosition name)  <> ",row_number() over () as arrrow FROM UNNEST(" <> pre <> ") as ix ) " <> t
       name =  tableAttr tb
       aliasKeys (Labeled  a (Attr n    _ ))  =  "(ix)." <> keyValue n <> " as " <> a
   in query

sortPosition = L.sortBy (comparing (maximum . fmap (keyPosition ._relOrigin) .keyattr))

expandBaseTable ::  TB3  (Labeled Text) Key  () ->  Text
expandBaseTable tb@(TB1 (meta, Compose (Labeled t ((KV i))))) =
  let
     query = "(SELECT " <>  T.intercalate "," (aliasKeys  . getCompose <$> ( sortPosition name)) <> " FROM " <> aliasTable <> ") as " <> t
     name =  tableAttr tb
     aliasTable = kvMetaFullName meta <> " as " <> t
     aliasKeys (Labeled  a (Attr n    _ ))  =  t <> "." <> keyValue n <> " as " <> a
     aliasKeys (Labeled a (IT n _ ))  = t <> "." <> keyValue n <> " as " <> a
     aliasKeys _  = ""
   in query


getInlineRec (TB1 t) = getInlineRec' t

getInlineRec' tb = L.filter (\i -> match $  unComp i) $ attrs
  where attrs = F.toList $ _kvvalues $ unComp (snd tb)
        match (Attr _ _ ) = False
        match (IT _ i ) = isTableRec i
        match (FKT _ _ i ) = False


expandTable ::  TB3  (Labeled Text) Key  () -> Writer [Text] Text
expandTable (DelayedTB1 (Just tb)) = expandTable tb
expandTable tb
  | isTableRec tb = do
      expandFKMutRecursive tb
      return $ tlabel tb
        {-  | isFilled (getInlineRec tb) = do
      expandInlineRecursive tb
      return $ tlabel tb-}
  | otherwise = return $ expandBaseTable  tb



--- Note [InlinableRec]
-- when some base table has a recursive inlinable field we need to
-- open the table reach the recursive attr, perform a with recursive query
-- with field and index tagging , then recover the base table
-- for example :
--  def :
--  rec_root ( id serial , rec_test :: rec_test)
--  rec_test ( tag tag , rec_test:: rec_test)
--  procedure :
--   open(id,iter,tag,rec_test) (expand rec_root with iter 0 and open the recursive field) (iter over the recursive field)
--   close(id,iter,tag,rec_test) (get max iter) (iterate until last item)
--   final(id,rec_test) join rec_root where iter = 0 and replace rec_field with (row (tag,rec_test))
--

expandInlineRecursive
  :: MonadWriter [Text] m =>
       TB3
              (Labeled Text) Key  ()
                   -> m ()
expandInlineRecursive tbase =
    let
     top = do
        res <- mapM with (getInlineRec tbase)
        let
            pret = fmap (\(i,_) -> i) res
            tRecf = fmap (\(_,i) -> i) res
        tell [rret <> " as (select " <>  attrsf tRecf <> " from " <> T.intercalate " natural join " (expandBaseTable tbase : fmap (<> "close") pret) <> " where iter = 0)"]
     rret = (label $ getCompose $ snd (unTB1 tbase))
     attrsf tRecf =  T.intercalate "," (map (\e -> maybe e explode $ L.find ((e == ).snd) tRecf)  nonrecb )
      where
       explode = (\(tRec ,tRecf)-> "ROW(" <> T.intercalate "," (F.toList tRec) <> ") as " <> tRecf)
       nonrecb =  explodeDelayed  undefined (\i -> "ROW(" <> i <> ")")  "," (const id  ) . getCompose <$> m
              where m = F.toList $ _kvvalues $ labelValue $ getCompose $  snd $ unTB1 $ tfil
                    tfil =   tbFilterE (\m e -> not $ S.member e (S.fromList $ fmap S.fromList $ topRec  $ _kvrecrels m)) <$> tbase
     with inlineEl  = tell [open,close] >> return (pret,(M.insert (S.fromList $ keyattri (labelValue $ getCompose $ inlineEl)) tRec  nonrecM  ,tRecf))
       where
         tr = _fkttable . unComp $ inlineEl
         t = TB1 (head $ F.toList tr)
         open = pret <> "open(" <> T.intercalate "," tbpk  <> ",iter," <> attrs "" <> ") as ("  <> openbase <> " union all " <> openrec <> ")"
           where
              openbase = "select " <> T.intercalate "," tbpk  <>" ,0," <> attrs "" <> " FROM " <> expandBaseTable tbase <> (fst (runWriter ((expandJoin True [] . Unlabeled. labelValue.  getCompose ) inlineEl)))
              openrec = "select " <> T.intercalate "," tbpk  <> ",iter +1, (" <> label (getCompose $snd $ unTB1 v) <> ").* from " <> pret <>"open " <> head (fst (runWriter (Tra.traverse (expandJoin True [] .Unlabeled. labelValue.getCompose ) (getInlineRec t )))) <> "   where " <> T.intercalate " AND " (fmap (<> " is not null ") tpk)
         close = pret <> "close(" <> T.intercalate "," tbpk  <> ",iter," <> attrs  "" <>") as ( " <> closebase <> " union all " <> closerec <>  ")"
           where
             closebase ="select " <> T.intercalate "," tbpk  <> ",iter," <> T.intercalate "," (F.toList $ M.insert recKey ("null :: record") nonrecM ) <> " from " <> pret <>"open natural join (select " <> T.intercalate "," tbpk  <> ",max(iter) as iter from " <> pret <>"open group by " <> T.intercalate "," tbpk  <> ") as max"
             closerec ="select c." <> T.intercalate "," tbpk  <> ",o.iter," <> T.intercalate "," (F.toList $ M.insert recKey ("row(" <>attrs "c." <>" )") $ fmap ("o." <>) nonrecM) <> " from " <> pret <>"close c join " <> pret <>"open o on " <> joinPk tbpk <> " and c.iter -1 = o.iter"

         pret = (label $ getCompose $ snd (unTB1 t))

         joinPk  tbpk = "(" <> T.intercalate "," (fmap ("o." <>)  tbpk ) <>  ")=(" <> T.intercalate "," (fmap ("c." <>)  tbpk  )<> ")"
         recKey = (S.fromList $ keyattri (labelValue $ getCompose $ inlineEl))
         attrs pre =  T.intercalate "," (fmap (pre <>) $ F.toList (M.insert  recKey tRec  nonrecM ))
         nonrecM =  (explodeDelayed undefined (\i -> "ROW(" <> i <> ")")  "," (const id  )) . getCompose <$> m
            where m =  _kvvalues $ labelValue $ getCompose $  snd $ unTB1 $ tfil
                  tfil =   tbFilterE (\m e -> not $ S.member e (S.fromList $ fmap S.fromList $ topRec  $ _kvrecrels m)) <$> t
         tRec =  (explodeDelayed undefined(\i -> "ROW(" <> i <> ")")  "," (const id ) ) $ Labeled (label $ getCompose $ snd $head $ F.toList v) (Attr l (TB1 ()))
         tRecf  =  label $ getCompose $ inlineEl
         IT l v =  labelValue $ getCompose $ head $ concat $ F.toList $  labelValue $ getCompose $  snd $  joinNonRef' $  unTB1 tnfil
         tpk =  (explodeDelayed undefined(\i -> "ROW(" <> i <> ")")  "," (const id ) ) .getCompose <$> m
            where m =  F.toList $ _kvvalues $ labelValue $ getCompose $  snd $ head $ F.toList $ tfilpk
         tbpk =  (explodeDelayed undefined(\i -> "ROW(" <> i <> ")")  "," (const id ) ) .getCompose <$> m
            where m =  F.toList $ _kvvalues $ labelValue $ getCompose $  tbPK $ tbase
         tfilpk  =  tbFilterE (\m e -> not $ S.member e (S.fromList $ fmap S.fromList $ topRec $  _kvrecrels m)) <$> v
         tnfil =   tbFilterE (\m e -> S.member e (S.fromList $ fmap S.fromList $ topRec $ _kvrecrels m)) <$> t
    in top


topRec = join . join . fmap unMutRec

expandFKMutRecursive
  :: MonadWriter [Text] m =>
     FTB
       (KVMetadata (Key),
        Compose
          (Labeled Text)
          (KV (Compose (Labeled Text) (TB (Labeled Text))))
          Key
          ())
     -> m ()
expandFKMutRecursive t=
    let
      query  =  tname <> "(" <> T.intercalate "," (tnonRec <> tRec <> (("f"<>) <$>  tRec ) <> (label <$> l)) <> ") as  ( SELECT "  <> T.intercalate "," (tnonRec<> tRec <> tRec <> (const "null :: record" <$> l)) <>" FROM (select * from " <> expandBaseTable t <>  (fst (runWriter (expandQuery' False (unlabelIT $ first (\t -> t {_kvrecrels =[] }  ) tnonRecA)))) <> ") as " <> tname <> " UNION ALL " <> recpart <> ")"
      recpart = "(SELECT " <> T.intercalate "," (fmap ("sg." <>) ( tnonRec <> tRec) <> (fmap recflags idx) <> (recfield <$> idx) ) <> " FROM "<> tname <> " sg " <> T.concat (recpoint <$> idx ) <> " WHERE " <> T.intercalate " OR "(recwhere <$> idx ) <> " UNION ALL " <> recpart2 <> ")"
          where idx= [0..length tRec -1]
      recpart2 = "SELECT sg.* FROM "<> tname <> " sg " <> T.concat (recpoint <$> idx) <> " WHERE " <> T.intercalate " OR " (T.intercalate " and " (recwhere3 <$> idx) : (recwhere2 <$> idx))
          where idx= [0..length tRec -1]
      recflags l = "case when " <> tnn <>" is null or " <> T.intercalate " or " (fmap (\i -> tn <> "f" <> i <> " is not null ")  tRec) <> " then "<> "sg.f" <> tRec !! l <> " else null end"
          where tn = tnn <> "."
                tnn = "t" <> T.pack (show l)
      recfield ix = "case when " <> tn <> head tnonRec <> " is not null then  ROW(" <> T.intercalate "," (fmap (tn <>)  tRec2  <> (fmap (explodeRowSg tn . snd) itv)) <> ") else sg." <>  label (l !! ix) <> " end"
          where tn = "t" <> T.pack (show ix) <> "."
      recpoint l =  " LEFT JOIN " <> tname <> " as " <> tn <> " ON " <>  tn <> "." <>   head tnonRec <> "=" <> "sg.f" <> (tRec !! l)
          where tn = "t" <> T.pack (show l)
      recwhere l =  "(" <> (tn <> head tnonRec <> " is not null and " ) <> T.intercalate " and " (fmap (\i -> tn <> "f" <> i <> " is null ")  tRec) <> ")"
          where tn = "t" <> T.pack (show l) <> "."
      recwhere2 l =  "(" <> T.intercalate " and " (((\i -> tn i <> head tnonRec <> " is null " ) <$> idx)   <>  (fmap (\i -> tn l <> "f" <> i <> " is not null ")  tRec)) <> ")"
          where tn l = "t" <> T.pack (show l) <> "."
                idx= L.delete l [0..length tRec -1]
      recwhere3 l =  "(" <> tn l  <> head tnonRec <> " is not null and "    <> T.intercalate " or " (fmap (\i -> tn l <> "f" <> i <> " is not null ")  tRec) <> ")"
          where tn l = "t" <> T.pack (show l) <> "."
      top = tbasen <> " as (select " <> T.intercalate "," (tRec2  <> ((\(l,v) -> explodeDelayed undefined(\i -> "ROW(" <> i <> ")")  "," (const id) v <> " as " <> l ) <$> itv  ))  <> " from " <> tname <> " WHERE " <> pred   <>") "
          where pred = T.intercalate " and " (fmap (\i -> "f" <> i <> " is null ")  tRec)



      explodeRowSg l = explodeDelayed  undefined(\i -> "ROW(" <> i <> ")")  "," (const (l <> ))
      tname = (label $ getCompose $ snd (unTB1 t)) <> "pre"
      tbasen = (label $ getCompose $ snd (unTB1 t))
      tnonRec ,tRec :: [Text]
      tnonRec =  (explodeDelayed undefined id   "," (const id  )) . getCompose <$> m
        where m = flattenNonRec (_kvrecrels $ fst $ unTB1 t) (unTB1 t)
      tnonRecA =  (unTB1 t)
      tRec =   (explodeDelayed undefined (\i -> "ROW(" <> i <> ")")  "," (const id ) ) .getCompose <$> l
        where l = concat $ fmap (unkvlist . _tbref .labelValue . getCompose ).  L.filter (isFKT .labelValue .getCompose) $ flattenRec (fmap (fmap (fmap S.fromList)) $_kvrecrels $ fst $ unTB1 t) (unTB1 t)
              isFKT (FKT _ _ _) = True
              isFKT i = False
      tRec2 =  (explodeDelayed undefined (\i -> "ROW(" <> i <> ")")  "," (const id ) ) .getCompose <$> l
          where l = F.toList $ _kvvalues $ labelValue $ getCompose $  snd $ unTB1 $ tfil
      itv =   fmap (\i -> case getCompose i of
                                      Labeled lit (IT i itv) -> (lit,Unlabeled $ IT i (unlabelIT <$> itv))
                                      Labeled lit (FKT ref rel  itv) -> (lit,Labeled lit( FKT ref rel itv))) $ F.toList $   _kvvalues $ labelValue $ getCompose $  snd $ unTB1 tnfil


      l = fmap getCompose $   flattenRec (fmap (fmap (fmap S.fromList)) $ _kvrecrels $ fst $ unTB1 t) (unTB1 t)
      tfil =   tbFilterE (\m e -> not $ S.member e (S.fromList $ fmap S.fromList $ topRec $ _kvrecrels m)) <$> t
      tnfil =   tbFilterE (\m e -> S.member e (S.fromList $ fmap S.fromList $ topRec $ _kvrecrels m)) <$> t
    in tell [query,top]


selectQuery
  :: (KVMetadata Key,
      Compose
        (Labeled Text)
        (KV (Compose (Labeled Text) (TB (Labeled Text))))
        Key
        ())
     -> Maybe (TBIndex Key Showable)
     -> [(Key, Order)]
     -> WherePredicate
     -> (Text,Maybe [TB Identity Key Showable])
selectQuery t koldpre order wherepred = (,ordevalue <> predvalue) $ if L.null (snd withDecl )
    then fst withDecl
    else "WITH RECURSIVE " <> T.intercalate "," ( snd withDecl ) <> fst withDecl
  where withDecl = runWriter tableQuery
        tableQuery = do
            tname <- expandTable (TB1 t)
            tquery <- if isTableRec (TB1 t) || isFilled (getInlineRec (TB1 t)) then return "" else expandQuery False (TB1 t)
            return $ "SELECT " <> explodeRow (TB1 t) <> " FROM " <>  tname <>  tquery <> pred <> orderQ
        (predquery , predvalue ) = case wherepred of
              WherePredicate wpred -> printPred t wpred
        pred = maybe "" (\i -> " WHERE " <> T.intercalate " AND " i )  ( orderquery <> predquery)
        (orderquery , ordevalue) =
          let
            unIndex (Idex i ) = M.toList i
            oq = (const $ pure $ generateComparison (first (justLabel t) <$> order)) . unIndex<$> koldpre
            koldPk :: Maybe [TB Identity Key Showable]
            koldPk =  (\k -> uncurry Attr <$> L.sortBy (comparing ((`L.elemIndex` (fmap fst order)).fst)) k ) . unIndex <$> koldpre
            pkParam =  koldPk <> (tail .reverse <$> koldPk)
         in (oq,pkParam)
        orderQ = " ORDER BY " <> T.intercalate "," ((\(l,j)  -> l <> " " <> showOrder j ) . first (justLabel t) <$> order)

generateComparison ((k,v):[]) = k <>  dir v <> "?"
  where dir Asc = ">"
        dir Desc = "<"
generateComparison ((k,v):xs) = "case when " <> k <>  "=" <> "? OR "<> k <> " is null  then " <>  generateComparison xs <> " else " <> k <>  dir v <> "?" <>" end"
  where dir Asc = ">"
        dir Desc = "<"



isFilled =  not . L.null

expandQuery left (ArrayTB1 (t:| _) ) =  expandQuery left t
expandQuery left (LeftTB1 (Just t)) =  expandQuery left t
expandQuery left (DelayedTB1 (Just t)) = return ""--  expandQuery left t
expandQuery left (TB1 t)
--    | isTableRec t  || isFilled (getInlineRec t)  = return "" -- expandTable t
    | otherwise   = expandQuery' left t

expandQuery' left t@(meta, m) = foldr (liftA2 mappend) (return "") (expandJoin left (F.toList (_kvvalues . labelValue . getCompose $ m) ) .getCompose <$> F.toList (_kvvalues . labelValue . getCompose $ m))

tableType (ArrayTB1 (i :| _ )) = tableType i <> "[]"
tableType (LeftTB1 (Just i)) = tableType i
tableType (TB1 (m,_)) = kvMetaFullName  m

unLB (Compose (Labeled _ l)) = l
unLB (Compose (Unlabeled  l)) = l

allAttr :: FTB  (KVMetadata Key,
                      Compose
                        (Labeled Text)
                        (KV (Compose (Labeled Text) (TB (Labeled Text))))
                        Key
                        ()) -> Bool
allAttr (TB1 (i,k)) = F.all (isAttr . unLB ) (_kvvalues $ unLB  k)
  where isAttr (Attr _ _) = True
        isAttr _ = False

look :: Key -> [Labeled Text ((TB (Labeled Text)) Key ())] ->  Labeled Text ((TB (Labeled Text)) Key ())
look ki i = justError ("missing FK on " <> show (ki,keyAttr . labelValue <$> i )  ) $ (\j-> L.find (\v -> keyAttr (labelValue v) == j) i  ) ki

expandJoin :: Bool -> [Compose (Labeled Text) (TB (Labeled Text)) Key ()] -> Labeled Text (TB (Labeled Text) Key ()) -> Writer [Text] Text
expandJoin left env (Unlabeled  (IT i (LeftTB1 (Just tb) )))
    = expandJoin True env $ Unlabeled (IT i tb)
expandJoin left env (Labeled l (IT i (LeftTB1 (Just tb) )))
    = expandJoin True env $ Labeled l (IT i tb)
expandJoin left env (Labeled l (IT a (ArrayTB1 (tb :| _ ) )))
    = do
    tjoin <- expandQuery left tb
    return $ jt <> " JOIN LATERAL (SELECT array_agg(" <> explodeRow tb <> "  order by arrrow ) as " <> label tas <> " FROM " <> expandInlineArrayTable tb l <> tjoin <> " )  as p" <>  label tas <> " ON true"
        where
          tas = getTas tb
          getTas (DelayedTB1 (Just tb))  = getTas tb
          getTas (TB1  (_,Compose tas)) = tas
          jt = if left then " LEFT" else ""
expandJoin left env (Labeled l (IT a tb)) =  do
     tjoin <- expandQuery left tb
     return $ " JOIN LATERAL "<> expandInlineTable  tb  l  <> " ON true "   <>  tjoin
-- expandJoin left env (Labeled _ (IT i tb )) = return ""
     -- expandQuery left tb
     -- tjoin <- expandQuery left tb
     -- return $ " JOIN LATERAL "<> expandInlineTable (label $ getCompose i) tb  <> " ON true "   <>  tjoin
expandJoin left env (Labeled _ (Fun _ _ _ )) = return ""
expandJoin left env (Labeled _ (Attr _ _ )) = return ""
expandJoin left env (Unlabeled  (Attr _ _ )) = return ""
expandJoin left env (Unlabeled (FKT i rel (LeftTB1 (Just tb)))) = expandJoin True env (Unlabeled (FKT i rel tb))
expandJoin left env (Labeled l (FKT i rel (LeftTB1 (Just tb)))) = expandJoin True env (Labeled l (FKT i rel tb))
expandJoin left env (Labeled l (FKT _ ks (ArrayTB1 (tb :| _))))
    = do
    query <- hasArray ( L.find (isArray. keyType ._tbattrkey . labelValue )  (look (_relRoot <$> ks) (fmap getCompose $ concat $ fmap nonRef env)))
    return $ jt <> " JOIN LATERAL (select * from ( SELECT " <>  query  <> "  ) as " <>  label tas  <>  (if left then "" else " WHERE " <> l <> " is not null " ) <> " ) as " <>  label tas <> " ON true "
      where
          hasArray (Just _)  =  do
            ttable <- expandTable (fmap (first (\t -> t {_kvrecrels = []})) tb)
            tjoin <- expandQuery left tb
            return $ "array_agg(" <> explodeRow  tb <> " order by arrrow) as " <> l <> " FROM ( SELECT * FROM (SELECT *,row_number() over () as arrrow FROM UNNEST(" <> label (justError "no array rn rel" $ L.find (isArray. keyType ._tbattrkey . labelValue )  (look (_relRoot <$> ks) (fmap getCompose $ concat $ fmap nonRef env)))  <> ") as arr) as z1 "  <> jt  <> " JOIN " <> ttable <> " ON " <>  label (head $ look  [ _relTarget $ justError "no array in rel" $ L.find (isArray. keyType . _relRoot ) ks] (fmap getCompose $ F.toList   (tableAttr tb))) <> " = arr" <> nonArrayJoin  <> " ) as z1 " <> tjoin
          hasArray Nothing =   do
            ttable <- expandTable tb
            tjoin <- expandQuery left tb
            return $ "array_agg(" <> explodeRow  tb <> " ) as " <> l <> " FROM " <> ttable <>   tjoin <> " WHERE true " <>  nonArrayJoin
          nonArrayJoin = if L.null nonArrayRel then "" else " AND " <> joinOnPredicate nonArrayRel (fmap getCompose $ concat $ fmap nonRef  env ) (fmap getCompose $ F.toList   (tableAttr tb))
            where
              nonArrayRel = L.filter (not . isArray . keyType . _relOrigin) ks
          tas = getTas tb
          getTas (DelayedTB1 (Just tb))  = getTas tb
          getTas (TB1  (_,Compose tas)) = tas
          look :: [Key] -> [Labeled Text ((TB (Labeled Text)) Key ())] ->  [Labeled Text ((TB (Labeled Text)) Key ())]
          look ki i = justError ("missing FK on " <> show (ki,ks ,keyAttr . labelValue <$> i )  ) $ allMaybes $ fmap (\j-> L.find (\v -> keyAttr (labelValue v) == j) i  ) ki
          jt = if left then " LEFT" else ""
expandJoin left env (Unlabeled (FKT _ rel tb)) = do
    tname <- expandTable tb
    tjoin <- if isTableRec tb
      then  return ""
      else expandQuery left tb
    return $ jt <> " JOIN " <> tname <> " ON " <> joinOnPredicate rel (fmap getCompose $ concat $ fmap nonRef env) (fmap getCompose $ F.toList (tableAttr tb)) <> tjoin
    where
      jt = if left then " LEFT" else ""

expandJoin left env (Labeled l (FKT i rel tb)) =  foldr (liftA2 mappend) (return "") $ (expandJoin left env . getCompose ) <$> unkvlist i

joinOnPredicate :: [Rel Key] -> [Labeled Text ((TB (Labeled Text))  Key ())] -> [Labeled Text ((TB (Labeled Text))  Key ())] -> Text
joinOnPredicate ks m n =  T.intercalate " AND " $ (\(Rel l op r) ->  intersectionOp (keyType . keyAttr . labelValue $ l) op (keyType . keyAttr . labelValue $ r) (label l)  (label r )) <$> fkm
    where fkm  = (\rel -> Rel (look (_relRoot rel ) m) (_relOperator rel) (look (_relTarget rel ) n)) <$>  ks
          look ki i = justError ("missing FK on " <> show (ki,ks ,keyAttr . labelValue <$> i )) $ (\j-> L.find (\v -> keyAttr (labelValue v) == j) i  ) ki

inner :: Text -> Text -> Text -> Text
inner b l m = l <> b <> m

intersectionOp :: (Eq b,Show b,Show (KType (Prim KPrim b ))) => KType (Prim KPrim b)-> BinaryOperator -> KType (Prim KPrim b)-> (Text -> Text -> Text)
intersectionOp i op (KOptional j) = intersectionOp i op j
intersectionOp (KOptional i) op j = intersectionOp i op j
intersectionOp (Primitive j) op (KArray (Primitive i) )
  | isPrimReflexive i j = (\i j  -> i <> renderBinary op <> "(" <> j <> ")" )
  | otherwise = errorWithStackTrace $ "wrong type intersectionOp * - {*} " <> show j <> " /= " <> show i
intersectionOp i op j = inner (renderBinary op)





explodeRow ::TB3 (Labeled Text) Key () -> Text
explodeRow = explodeRow'  (\i -> "ROW(" <> i <> ")")  "," (const id)
explodeRecord :: TB3Data (Labeled Text) Key () -> Text
explodeRecord  = explodeRow''   (\i -> "ROW("<> i <> ")")  "," (const id)


leafDel True i = " case when " <> i <> " is not null then true else null end  as " <> i
leafDel False i = " case when " <> i <> " is not null then true else null end  as " <> i

explodeRow' block  assoc  leaf (DelayedTB1 (Just tbd@(TB1 (i,tb)))) = "(true)"
explodeRow' block assoc leaf (LeftTB1 (Just tb) ) = explodeRow' block assoc leaf tb
explodeRow' block assoc leaf (ArrayTB1 (tb:|_) ) = explodeRow' block assoc leaf tb
explodeRow' block assoc leaf (TB1 i ) = explodeRow'' block assoc leaf i

explodeRow'' block assoc leaf  t@((m ,Compose (Unlabeled (KV tb)))) = block (T.intercalate assoc (fmap (explodeDelayed t block assoc leaf .getCompose)  $ sortPosition $F.toList  tb  ))
explodeRow'' block assoc leaf  t@((m ,Compose (Labeled l (KV tb)))) = sel (T.intercalate assoc (fmap (explodeDelayed t block assoc leaf .getCompose)  $ sortPosition $ F.toList  tb  ))
  where sel i = "(select p" <> l <> " from (select " <> i<>  ") as p" <> l <> ")"

replaceexpr :: Expr -> [Text]  -> Text
replaceexpr k ac = go k
  where
    go :: Expr -> Text
    go (Function i e) = i <> "(" <> T.intercalate ","  (go   <$> e) <> ")"
    go (Value i ) = (ac !! i )


explodeDelayed tb block assoc leaf (Labeled l (Fun k (ex,a)  _ )) =  replaceexpr ex $ fmap (\i -> explodeDelayed tb block assoc leaf $ indexLabel i tb) a -- leaf (isArray (keyType k)) l
explodeDelayed _ block assoc leaf (Labeled l (Attr k  _ ))
  | isKDelayed (keyType k) = leafDel (isArray (keyType k)) l
  | otherwise =  leaf (isArray (keyType k)) l
explodeDelayed _ block assoc leaf (Labeled l (Attr k  _ ))
  | isKDelayed (keyType k) = leafDel (isArray (keyType k)) l
  | otherwise =  leaf (isArray (keyType k)) l
explodeDelayed _ block assoc leaf (Unlabeled (Attr k  _ )) = leaf (isArray (keyType k))  (keyValue k)

explodeDelayed _ block assoc leaf (Unlabeled (IT  n t )) =  explodeRow'  block assoc leaf t
explodeDelayed rec block assoc leaf (Labeled l (IT  k (LeftTB1 (Just tb  )))) = explodeDelayed rec block assoc leaf (Labeled l (IT k tb))
explodeDelayed _ block assoc leaf (Labeled l (IT  _ (ArrayTB1 tb ) )) = leaf False m
  where m = label $ getCompose $ snd $  head $ concat $ fmap F.toList $ tb
explodeDelayed _ block assoc leaf (Labeled l (IT  _ t  )) = explodeRow'  block assoc leaf t
explodeDelayed tbenv  block assoc leaf (Labeled l (FKT ref  _ _ )) = case unkvlist ref of
             [] -> leaf False l
             i -> T.intercalate assoc (explodeDelayed tbenv block assoc leaf . getCompose <$> i) <> assoc <> leaf False l
explodeDelayed tb block assoc leaf (Unlabeled (FKT ref rel t )) = case unkvlist ref of
             [] -> explodeRow' block assoc leaf t
             i -> T.intercalate assoc (explodeDelayed tb block assoc leaf .getCompose <$> i) <> assoc <> explodeRow' block assoc leaf t



printPred :: TB3Data (Labeled Text)  Key ()->  BoolCollection (Access Key ,AccessOp Showable ) -> (Maybe [Text],Maybe [Column Key Showable])
printPred t (PrimColl (a,e)) = (Just $ catMaybes $ fmap fst idx,Just $ catMaybes $ fmap snd idx)
  where
    idx = indexFieldL e [] a t

printPred t (OrColl wpred) =
                let
                  w = unzip . fmap (printPred  t) <$> nonEmpty wpred
                in (pure . (\i -> " (" <> i <> ") ") . T.intercalate " OR " <$> join (nonEmpty. concat . catMaybes . fst <$> w) , concat . catMaybes . snd <$> w )
printPred t (AndColl wpred) =
                let
                  w = unzip . fmap (printPred  t) <$> nonEmpty wpred
                in (pure . (\i -> " (" <> i <> ") ") . T.intercalate " AND " <$>  join (nonEmpty . concat . catMaybes .fst <$> w) , concat . catMaybes . snd <$> w )

renderType (KInterval t) =
  case t of
    Primitive (AtomicPrim (PInt i)) ->  case i of
      4 -> "int4range"
      8 -> "int8range"
    Primitive (AtomicPrim PDate) -> "daterange"
    Primitive (AtomicPrim PDouble) -> "floatrange"
    Primitive (AtomicPrim (PTimestamp i)) -> case i of
      Just i -> "tsrange"
      Nothing -> "tstzrange"
    i -> Nothing
renderType (Primitive (RecordPrim (s,t)) ) = Just $ s <> "." <> t
renderType (Primitive (AtomicPrim t) ) =
  case t  of
    PDouble -> "double precision"
    PText -> "character varying"
    PInt v -> case v of
      4 -> "integer"
      8 -> "bigint"
    PDate -> "date"
    PTimestamp v -> case v of
      Just i -> "timestamp without time zone"
      Nothing -> "timestamp with time zone"
    i -> Nothing
renderType (KArray i) = (<>"[]") <$> renderType i
renderType (KOptional i) =renderType i
renderType (KSerial i) =renderType i
renderType (KDelayed i) =renderType i

-- inferParamType e i |traceShow (e,i) False = undefined

instance IsString (Maybe T.Text) where
  fromString i = Just (fromString i)

inferParamType op i = maybe "" (":: " <>) $ renderType $ inferOperatorType op i

justLabel :: TB3Data (Labeled Text ) Key () -> Key -> Text
justLabel t k =  justError ("cant find label"  <> show k <> " - " <> show t).getLabels t $ k

indexLabel  :: Show a =>
    Access Key
    -> TB3Data (Labeled Text) Key a
    -> (Labeled Text (TB (Labeled Text) Key a))
indexLabel p@(IProd b l) v =
    case findAttr l v of
      Just i -> getCompose i
      Nothing -> errorWithStackTrace "no fk"
indexLabel  n@(Nested ix@(IProd b l) (Many [nt])) v =
    case getCompose $ justError "no nested" $ findFK l v of
      Unlabeled i -> indexLabel  nt.head . F.toList . _fkttable $ i
      Labeled i _ -> errorWithStackTrace "cant index"
indexLabel  (Many [nt]) v = flip (indexLabel ) v $ nt
-- indexLabel  (ISum [nt]) v = flip (indexLabel ) v <$> nt
indexLabel  i v = errorWithStackTrace (show (i, v))




indexFieldL
    ::  AccessOp Showable
    -> [Text]
    -> Access Key
    -> TB3Data (Labeled Text) Key ()
    -> [(Maybe Text, Maybe (TB Identity Key Showable))]
-- indexFieldL e c p v | traceShow (e,c,p) False = undefined
indexFieldL e c p@(IProd b l) v =
    case findAttr l v of
      Just i -> [utlabel  e c i]
      Nothing ->
            case
                   fmap getCompose $ findFK l v of

                Just (Unlabeled i) ->
                    case i of
                        (FKT ref _ _) ->
                            (\l ->
                                  utlabel e c.
                                  justError ("no attr" <> show (ref, l)) .
                                  L.find
                                      ((== [l]) .
                                       fmap (_relOrigin) . keyattr) $
                                  unkvlist ref) <$>
                            l
                        i -> errorWithStackTrace "no fk"
    -- Don't support filtering from labeled queries yet just check if not null for all predicates
    -- TODO: proper check  accessing the term
                Just (Labeled i _) -> [(Just (i <> " is not null"), Nothing)]
                Nothing -> case findFKAttr l v of
                             Just i -> [utlabel e  c i]
                             Nothing  -> errorWithStackTrace ("no fk attr" <> show (l,v))

indexFieldL e c n@(Nested ix@(IProd b l) nt) v =
    case getCompose $ justError "no nested" $ findFK l v of
        Unlabeled i ->
          concat . fmap (indexFieldL e c nt) . F.toList . _fkttable $ i
        Labeled l (IT k fk) -> (indexFieldL e c nt  $ head (F.toList fk ))
        Labeled l a -> {-->
          let
            go (ArrayTB1 (i:| _)) =
              concat . fmap (indexFieldL e (c ++["p" <> m]) nt) . F.toList $ i
            go (LeftTB1 (Just i)) = go i
            go (TB1 i) =  indexFieldL e c nt   i
            go i = errorWithStackTrace (show i)

            m = label $ getCompose $ snd $  head $ F.toList (_fkttable a)
         in go (_fkttable a)
          -- -} [(Just (l <> " is not null"), Nothing)]

indexFieldL e c (Many nt) v = concat $ flip (indexFieldL e c) v <$> nt
indexFieldL e c (ISum nt) v = concat $ flip (indexFieldL e c) v <$> nt
indexFieldL e c i v = errorWithStackTrace (show (i, v))

utlabel (Right  e) c a = result
  where
    idx = tlabel' . getCompose $ a
    opvalue  ref i  =  T.intercalate "." (c ++ [ref])  <> " is " <> renderUnary i
    result =  ( Just $  (opvalue (snd $ idx) e)   ,Nothing)
utlabel (Left (value,e)) c a = result
  where
    idx = tlabel' . getCompose $ a
    operator i = errorWithStackTrace (show i)
    opvalue ref (AnyOp i)  = " ? " <> renderBinary i <>  " ANY( " <> T.intercalate "." (c ++ [ref]) <>  ")"
    opvalue ref (Flip (AnyOp (AnyOp Equals)))  = T.intercalate "." (c ++ [ref]) <> " " <>  "<@@" <>  " ANY( ? " <>  inferParamType e (KArray $ keyType (fst idx)) <> ")"
    opvalue ref (Flip (AnyOp i))  = T.intercalate "." (c ++ [ref]) <> " " <> renderBinary (Flip i) <>  " ANY( ? " <>  inferParamType e (KArray $ keyType (fst idx)) <> ")"
    opvalue ref  i = (\v ->  " ? " <> inferParamType (Flip i) (keyType (fst idx)) <> renderBinary i <>  T.intercalate "." (c ++ [ref]) ) $ idx
    opparam _ = Just $ Attr (fst idx ) value
    result =  ( Just $  (opvalue (snd $ idx) e)   ,opparam e )

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


