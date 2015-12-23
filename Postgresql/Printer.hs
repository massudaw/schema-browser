{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RankNTypes #-}

module Postgresql.Printer
  (selectQuery
  ,tableType
  ,explodeRecord
  ,createTable
  ,dropTable
  )
  where

import Query
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
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad.Writer
import Data.Text (Text)

import Types




--
-- Patch CRUD Postgresql Operations
--



dropTable r= "DROP TABLE "<> rawFullName r


createTable r@(Raw sch _ _ _ _ tbl _ _ pk _ fk inv attr) = "CREATE TABLE " <> rawFullName r  <> "\n(\n\t" <> T.intercalate ",\n\t" commands <> "\n)"
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
    renderFK (Path origin (FKJoinTable _ ks table) end) = "CONSTRAINT " <> tbl <> "_FK_" <> table <> " FOREIGN KEY " <>  renderKeySet origin <> ") REFERENCES " <> table <> "(" <> renderKeySet end <> ")  MATCH SIMPLE  ON UPDATE  NO ACTION ON DELETE NO ACTION"
    renderFK (Path origin _  end) = ""



expandInlineTable ::  Text -> TB3  (Labeled Text) Key  () ->  Text
expandInlineTable pre tb@(TB1 (meta, Compose (Labeled t ((KV i))))) =
   let query = "(SELECT " <>  T.intercalate "," (aliasKeys  . getCompose <$> name)  <> ") as " <> t
       name =  tableAttr tb
       aliasKeys (Labeled  a (Attr n    _ ))  =  "(" <> pre <> ")." <> keyValue n <> " as " <> a
   in query

expandInlineArrayTable ::  Text -> TB3  (Labeled Text) Key  () ->  Text
expandInlineArrayTable pre tb@(TB1 (meta, Compose (Labeled t ((KV i))))) =
   let query = "(SELECT " <>  T.intercalate "," (aliasKeys  . getCompose <$> name)  <> ",row_number() over () as arrrow FROM UNNEST(" <> pre  <> ") as ix ) "
       name =  tableAttr tb
       aliasKeys (Labeled  a (Attr n    _ ))  =  "(ix)." <> keyValue n <> " as " <> a
   in query

expandBaseTable ::  TB3  (Labeled Text) Key  () ->  Text
expandBaseTable tb@(TB1 (meta, Compose (Labeled t ((KV i))))) =
   let query = "(SELECT " <>  T.intercalate "," (aliasKeys  . getCompose <$> name) <> " FROM " <> aliasTable <> ") as " <> t
       name =  tableAttr tb
       aliasTable = kvMetaFullName meta <> " as " <> t
       aliasKeys (Labeled  a (Attr n    _ ))  =  t <> "." <> keyValue n <> " as " <> a
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
  | isFilled (getInlineRec tb) = do
      expandInlineRecursive tb
      return $ tlabel tb
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
       nonrecb =  explodeDelayed (\i -> "ROW(" <> i <> ")")  "," (const id  ) . getCompose <$> m
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
         nonrecM =  (explodeDelayed (\i -> "ROW(" <> i <> ")")  "," (const id  )) . getCompose <$> m
            where m =  _kvvalues $ labelValue $ getCompose $  snd $ unTB1 $ tfil
                  tfil =   tbFilterE (\m e -> not $ S.member e (S.fromList $ fmap S.fromList $ topRec  $ _kvrecrels m)) <$> t
         tRec =  (explodeDelayed (\i -> "ROW(" <> i <> ")")  "," (const id ) ) .getCompose $ l
         tRecf  =  label $ getCompose $ inlineEl
         IT l v =  labelValue $ getCompose $ head $ concat $ F.toList $  labelValue $ getCompose $  snd $  joinNonRef' $  unTB1 tnfil
         tpk =  (explodeDelayed (\i -> "ROW(" <> i <> ")")  "," (const id ) ) .getCompose <$> m
            where m =  F.toList $ _kvvalues $ labelValue $ getCompose $  snd $ head $ F.toList $ tfilpk
         tbpk =  (explodeDelayed (\i -> "ROW(" <> i <> ")")  "," (const id ) ) .getCompose <$> m
            where m =  F.toList $ _kvvalues $ labelValue $ getCompose $  tbPK $ tbase
         tfilpk  =  tbFilterE (\m e -> not $ S.member e (S.fromList $ fmap S.fromList $ topRec $  _kvrecrels m)) <$> v
         tnfil =   tbFilterE (\m e -> S.member e (S.fromList $ fmap S.fromList $ topRec $ _kvrecrels m)) <$> t
    in top


topRec = join . join . fmap unMutRec


expandFKMutRecursive t=
    let
      query  =  tname <> "(" <> T.intercalate "," (tnonRec <> tRec <> (("f"<>) <$>  tRec ) <> (label <$> l)) <> ") as  ( SELECT "  <> T.intercalate "," (tnonRec<> tRec <> tRec <> (const "null :: record" <$> l)) <>" FROM (select * from " <> expandBaseTable t <>  (fst (runWriter (expandQuery' False (fmap unlabelIT $ TB1 $(first (\t -> t {_kvrecrels =[] }  )) tnonRecA)))) <> ") as " <> tname <> " UNION ALL " <> recpart <> ")"
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
      top = tbasen <> " as (select " <> T.intercalate "," (tRec2  <> ((\(l,v) -> explodeDelayed (\i -> "ROW(" <> i <> ")")  "," (const id) v <> " as " <> l ) <$> itv  ))  <> " from " <> tname <> " WHERE " <> pred   <>") "
          where pred = T.intercalate " and " (fmap (\i -> "f" <> i <> " is null ")  tRec)



      explodeRowSg l = explodeDelayed  (\i -> "ROW(" <> i <> ")")  "," (const (l <> ))
      tname = (label $ getCompose $ snd (unTB1 t)) <> "pre"
      tbasen = (label $ getCompose $ snd (unTB1 t))
      tnonRec ,tRec :: [Text]
      tnonRec =  (explodeDelayed id   "," (const id  )) . getCompose <$> m
        where m = flattenNonRec (_kvrecrels $ fst $ unTB1 t) (unTB1 t)
      tnonRecA =  (unTB1 t)
      tRec =   (explodeDelayed (\i -> "ROW(" <> i <> ")")  "," (const id ) ) .getCompose <$> l
        where l = concat $ fmap (_tbref .labelValue . getCompose ).  L.filter (isFKT .labelValue .getCompose) $ flattenRec (fmap (fmap (fmap S.fromList)) $_kvrecrels $ fst $ unTB1 t) (unTB1 t)
              isFKT (FKT _ _ _) = True
              isFKT i = False
      tRec2 =  (explodeDelayed (\i -> "ROW(" <> i <> ")")  "," (const id ) ) .getCompose <$> l
          where l = F.toList $ _kvvalues $ labelValue $ getCompose $  snd $ unTB1 $ tfil
      itv =   fmap (\i -> case getCompose i of
                                      Labeled lit (IT i itv) -> (lit,Unlabeled $ IT i (unlabelIT <$> itv))
                                      Labeled lit (FKT ref rel  itv) -> (lit,Labeled lit( FKT ref rel itv))) $ F.toList $   _kvvalues $ labelValue $ getCompose $  snd $ unTB1 tnfil


      l = fmap getCompose $   flattenRec (fmap (fmap (fmap S.fromList)) $ _kvrecrels $ fst $ unTB1 t) (unTB1 t)
      tfil =   tbFilterE (\m e -> not $ S.member e (S.fromList $ fmap S.fromList $ topRec $ _kvrecrels m)) <$> t
      tnfil =   tbFilterE (\m e -> S.member e (S.fromList $ fmap S.fromList $ topRec $ _kvrecrels m)) <$> t
    in tell [query,top]


selectQuery r = if L.null (snd withDecl )
    then fst withDecl
    else "WITH RECURSIVE " <> T.intercalate "," ( snd withDecl ) <> fst withDecl
  where withDecl = runWriter tableQuery
        t = TB1 r
        tableQuery = do
            tname <- expandTable t
            tquery <- if isTableRec t || isFilled (getInlineRec t) then return "" else expandQuery False t
            return $ "SELECT " <> explodeRow t <> " FROM " <>  tname <>  tquery

isFilled =  not . L.null

expandQuery left (DelayedTB1 (Just t)) = return ""--  expandQuery left t
expandQuery left t@(TB1 (meta, m))
--    | isTableRec t  || isFilled (getInlineRec t)  = return "" -- expandTable t
    | otherwise   = expandQuery' left t

expandQuery' left t@(TB1 (meta, m)) = foldr1 (liftA2 mappend) (expandJoin left (F.toList (_kvvalues . labelValue . getCompose $ m) ) .getCompose <$> F.toList (_kvvalues . labelValue . getCompose $ m))

tableType (ArrayTB1 (i :| _ )) = tableType i <> "[]"
tableType (LeftTB1 (Just i)) = tableType i
tableType (TB1 (m,_)) = kvMetaFullName  m


expandJoin :: Bool -> [Compose (Labeled Text) (TB (Labeled Text)) Key ()] -> Labeled Text (TB (Labeled Text) Key ()) -> Writer [Text] Text
expandJoin left env (Labeled l (IT i (LeftTB1 (Just tb) )))
    = expandJoin True env $ Labeled l (IT i tb)
expandJoin left env (Labeled l (IT i (ArrayTB1 (tb :| _ ) )))
    = do
    tjoin <- expandQuery left tb
    return $ jt <> " JOIN LATERAL (SELECT array_agg(" <> (explodeRow tb {-<> (if allAttr tb then  " :: " <> tableType tb else "")-} ) <> "  order by arrrow ) as " <> l <> " FROM " <> expandInlineArrayTable tname tb <> label tas <> tjoin <> " )  as " <>  label tas <> " ON true"
        where
          tas = getTas tb
          getTas (DelayedTB1 (Just tb))  = getTas tb
          getTas (TB1  (_,Compose tas)) = tas
          tname = label $ getCompose i
          jt = if left then " LEFT" else ""
expandJoin left env (Unlabeled (IT i tb)) =  do
     tjoin <- expandQuery left tb
     return $ " JOIN LATERAL "<> expandInlineTable (label $ getCompose i) tb  <> " ON true "   <>  tjoin
expandJoin left env (Labeled _ (IT i tb )) = return ""
     -- expandQuery left tb
     -- tjoin <- expandQuery left tb
     -- return $ " JOIN LATERAL "<> expandInlineTable (label $ getCompose i) tb  <> " ON true "   <>  tjoin
expandJoin left env (Labeled _ (Attr _ _ )) = return ""
expandJoin left env (Unlabeled  (Attr _ _ )) = return ""
expandJoin left env (Unlabeled (FKT i rel (LeftTB1 (Just tb)))) = expandJoin True env (Unlabeled (FKT i rel tb))
expandJoin left env (Labeled l (FKT i rel (LeftTB1 (Just tb)))) = expandJoin True env (Labeled l (FKT i rel tb))
expandJoin left env (Labeled l (FKT _ ks (ArrayTB1 (tb :| _))))
    = do
    query <- hasArray ( L.find (isArray. keyType ._tbattrkey . labelValue )  (look (_relOrigin <$> ks) (fmap getCompose $ concat $ fmap nonRef env)))
    return $ jt <> " JOIN LATERAL (select * from ( SELECT " <>  query  <> "  ) as " <>  label tas  <>  (if left then "" else " WHERE " <> l <> " is not null " ) <> " ) as " <>  label tas <> " ON true "
      where
          hasArray (Just _)  =  do
            ttable <- expandTable (fmap (first (\t -> t {_kvrecrels = []})) tb)
            tjoin <- expandQuery left tb
            return $ "array_agg(" <> explodeRow  tb <> " order by arrrow) as " <> l <> " FROM ( SELECT * FROM (SELECT *,row_number() over () as arrrow FROM UNNEST(" <> label (justError "no array rn rel" $ L.find (isArray. keyType ._tbattrkey . labelValue )  (look (_relOrigin <$> ks) (fmap getCompose $ concat $ fmap nonRef env)))  <> ") as arr) as z1 "  <> jt  <> " JOIN " <> ttable <> " ON " <>  label (head $ look  [ _relTarget $ justError "no array in rel" $ L.find (isArray. keyType . _relOrigin ) ks] (fmap getCompose $ F.toList   (tableAttr tb))) <> " = arr" <> nonArrayJoin  <> " ) as z1 " <> tjoin
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

expandJoin left env (Labeled l (FKT i rel tb)) =  foldr1 (liftA2 mappend) $ (expandJoin left env . getCompose ) <$> i
-- expandJoin left env i = errorWithStackTrace (show ("expandJoin",i))

joinOnPredicate :: [Rel Key] -> [Labeled Text ((TB (Labeled Text))  Key ())] -> [Labeled Text ((TB (Labeled Text))  Key ())] -> Text
joinOnPredicate ks m n =  T.intercalate " AND " $ (\(Rel l op r) ->  intersectionOp (mapKType . keyType . keyAttr . labelValue $ l) op (mapKType .keyType . keyAttr . labelValue $ r) (label l)  (label r )) <$> fkm
    where fkm  = (\rel -> Rel (look (_relOrigin rel ) m) (_relOperator rel) (look (_relTarget rel ) n)) <$>  ks
          look ki i = justError ("missing FK on " <> show (ki,ks ,keyAttr . labelValue <$> i )) $ (\j-> L.find (\v -> keyAttr (labelValue v) == j) i  ) ki





explodeRow :: TB3 (Labeled Text) Key () -> Text
explodeRow = explodeRow'  (\i -> "ROW(" <> i <> ")")  "," (const id)
explodeRecord :: TB3Data (Labeled Text) Key () -> Text
explodeRecord  = explodeRow''   (\i -> "ROW(" <> i <> ")")  "," (const id)


leafDel True i = " case when " <> i <> " is not null then true else null end "
leafDel False i = " case when " <> i <> " is not null then true else null end "

explodeRow' block  assoc  leaf (DelayedTB1 (Just tbd@(TB1 (i,tb)))) = "(true)"
explodeRow' block assoc leaf (LeftTB1 (Just tb) ) = explodeRow' block assoc leaf tb
explodeRow' block assoc leaf (ArrayTB1 (tb:|_) ) = explodeRow' block assoc leaf tb
explodeRow' block assoc leaf (TB1 i ) = explodeRow'' block assoc leaf i

explodeRow'' block assoc leaf  ((m ,Compose (Unlabeled (KV tb)))) = block (T.intercalate assoc (fmap (explodeDelayed block assoc leaf .getCompose)  $ F.toList  tb  ))
explodeRow'' block assoc leaf  ((m ,Compose (Labeled l (KV tb)))) = block (T.intercalate assoc (fmap (explodeDelayed block assoc leaf .getCompose)  $ F.toList  tb  ))

explodeDelayed block assoc leaf (Labeled l (Attr k  _ ))
  | isKDelayed (keyType k) = leafDel (isArray (keyType k)) l
  | otherwise =  leaf (isArray (keyType k)) l
explodeDelayed block assoc leaf (Unlabeled (Attr k  _ )) = leaf (isArray (keyType k))  (keyValue k)

explodeDelayed block assoc leaf (Unlabeled (IT  n t )) =  explodeRow'  block assoc leaf t
explodeDelayed block assoc leaf (Labeled l (IT  _ tb  )) = leaf False l
explodeDelayed block assoc leaf (Labeled l (FKT i  _ tb  )) = case i of
             [] -> leaf False l
             i -> T.intercalate assoc (F.toList $ (explodeDelayed block assoc leaf . getCompose ) <$> i) <> assoc <> leaf False l
explodeDelayed block assoc leaf (Unlabeled (FKT i rel t )) = case i of
             [] -> explodeRow' block assoc leaf t
             i -> T.intercalate assoc (F.toList $ (explodeDelayed block assoc leaf .getCompose) <$> i) <> assoc <> explodeRow' block assoc leaf t




