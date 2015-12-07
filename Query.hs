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

module Query where

import qualified Control.Lens as Le
import Data.Functor.Apply
import Data.Bifunctor
import Data.Time.LocalTime
import Data.Unique
import Data.Functor.Identity
import Data.Ord
import qualified Data.Poset as P
import qualified Data.Foldable as F
-- import Data.Traversable (mapAccumL)
import qualified Data.Traversable as Tra
import Data.Maybe
import qualified Data.Interval as Interval
import Data.Monoid hiding (Product)

import qualified Data.Text as T
import qualified Data.ExtendedReal as ER

import Utils

import Debug.Trace

import Prelude hiding (head)
import Control.Monad
import System.IO.Unsafe
import Control.Applicative
import Data.List (intercalate)
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Set (Set)
import Data.Map (Map)
import Control.Monad.State
import Control.Monad.Writer
import Data.Text (Text)
import GHC.Stack

import Types



transformKey (KSerial i)  (KOptional j) (SerialTB1 v)  | i == j = LeftTB1  v
transformKey (KOptional i)  (KSerial j) (LeftTB1 v)  | i == j = SerialTB1 v
transformKey (KOptional j) l (LeftTB1  v)
    | isJust v = transformKey j l (fromJust v)
    | otherwise = errorWithStackTrace "no transform optional nothing"
transformKey (KSerial j)  l (SerialTB1 v)
    | isJust v = transformKey j l (fromJust v)
    | otherwise =  DelayedTB1 Nothing
transformKey l@(Primitive _)  (KOptional j ) v  = LeftTB1 $ Just (transformKey l j v)
transformKey l@(Primitive _)  (KSerial j ) v   = SerialTB1 $ Just (transformKey l j v)
transformKey l@(Primitive _)  (KArray j ) v | j == l  = ArrayTB1 $ pure v
transformKey ki kr v | ki == kr = v
transformKey ki kr  v = errorWithStackTrace  ("No key transform defined for : " <> show ki <> " " <> show kr <> " " <> show v )

description  = rawDescription

atTables f t = f t


renderAliasedKey (v ,(t,k)) a = rawName t <> "." <> keyValue k <> " AS " <> a

isKDelayed (KDelayed i) = True
isKDelayed (KSerial i) = isKDelayed i
isKDelayed (KOptional i) = isKDelayed i
isKDelayed (KInterval i) = isKDelayed i
isKDelayed (KArray i)  = isKDelayed i
isKDelayed _ = False


isKOptional (KOptional i) = True
isKOptional (KSerial i) = isKOptional i
isKOptional (KInterval i) = isKOptional i
isKOptional (Primitive _) = False
isKOptional (KArray i)  = isKOptional i
-- isKOptional i = errorWithStackTrace (show ("isKOptional",i))



getPrim i@(Primitive _ ) = i
getPrim (KOptional j) =  getPrim j
getPrim (KDelayed j) =  getPrim j
getPrim (KSerial j) =  getPrim j
getPrim (KArray j) =  getPrim j
getPrim (KInterval j) =  getPrim j

inner b l m = l <> b <> m

-- Operators
pkOp (KOptional j ) i  (LeftTB1 l) k  = maybe False id (pkOp i j k <$> l)
pkOp (KSerial j ) i  (SerialTB1 l) k  = maybe False id (pkOp i j k <$> l)
pkOp i (KOptional j ) k (LeftTB1 l) = maybe False id (pkOp i j k <$> l)
pkOp i (KSerial j ) k (SerialTB1 l) = maybe False id (pkOp i j k <$> l)
pkOp (KArray i) (KArray j) (ArrayTB1 k) (ArrayTB1 l) | i == j = not $ S.null $ S.intersection (S.fromList (F.toList k)) (S.fromList (F.toList  l ))
pkOp (KInterval i) (KInterval j) (IntervalTB1 k) (IntervalTB1 l)| i == j  = not $ Interval.null $ Interval.intersection  k l
pkOp (Primitive i ) (Primitive j ) k l  | i == j = k == l
pkOp a b c d = errorWithStackTrace (show (a,b,c,d))

pkOpSet i l = (\i -> if L.null i then False else L.all id i) $ zipWith (\(a,b) (c,d)->  pkOp (keyType a)  (keyType c) b d) (L.sortBy (comparing fst ) i) (L.sortBy (comparing fst) l)


intersectionOp :: (Eq b,Show (KType (Prim KPrim b ))) => KType (Prim KPrim b)-> Text -> KType (Prim KPrim b)-> (Text -> Text -> Text)
intersectionOp (KOptional i) op (KOptional j) = intersectionOp i op j
intersectionOp i op (KOptional j) = intersectionOp i op j
intersectionOp (KOptional i) op j = intersectionOp i op j
intersectionOp (KInterval i) op (KInterval j )  = inner op
intersectionOp (KArray i) op  (KArray j )  = inner op
intersectionOp (KInterval i) op j
    | getPrim i == getPrim j =  inner op
    | otherwise = errorWithStackTrace $ "wrong type intersectionOp " <> show i <> " /= " <> show j
intersectionOp i op (KInterval j)
    | getPrim i == getPrim j = inner "<@"
    | otherwise = errorWithStackTrace $ "wrong type intersectionOp " <> show i <> " /= " <> show j
intersectionOp (KArray i ) op  j
    | i == getPrim j = (\j i -> i <> " IN (select * from unnest("<> j <> ") ) ")
    | otherwise = errorWithStackTrace $ "wrong type intersectionOp {*} - * " <> show i <> " /= " <> show j
intersectionOp j op (KArray i )
    | getPrim i == getPrim j = (\i j  -> i <> " IN (select * from unnest("<> j <> ") ) ")
    | otherwise = errorWithStackTrace $ "wrong type intersectionOp * - {*} " <> show j <> " /= " <> show i
intersectionOp i op j = inner op

showTable t  = rawSchema t <> "." <> rawName t


findPKM (LeftTB1 i ) =  join $ fmap (findPKM ) i
findPKM i  = Just $ concat . fmap (\i -> zip (keyattr i) (kattr i )) .F.toList . _kvvalues . unTB . tbPK $ i


diffUpdateAttr :: TBData Key Showable -> TBData Key Showable -> Maybe (TBData Key Showable)
diffUpdateAttr  kv kold@(t,_ )  =  fmap ((t,) . _tb . KV ) .  allMaybesMap  $ liftF2 (\i j -> if i == j then Nothing else Just i) (unKV . snd . tableNonRef'  $ kv ) (unKV . snd . tableNonRef' $ kold )

attrValue :: (Ord a,Show a) => TB Identity Key a -> FTB a
attrValue (Attr _  v)= v
attrValue i = errorWithStackTrace $ " no attr value instance " <> show i

attrType :: (Ord a,Show a) => TB Identity Key a -> KType (Prim (Text,Text) (Text,Text))
attrType (Attr i _)= keyType i
attrType (IT i _) = overComp attrType i
attrType i = errorWithStackTrace $ " no attr value instance " <> show i

attrValueName :: (Ord a,Show a) => TB Identity Key a -> Text
attrValueName (Attr i _ )= keyValue i
attrValueName (IT i  _) = overComp attrValueName i
attrValueName i = errorWithStackTrace $ " no attr value instance " <> show i

type TBValue = TB1 (Key,Showable)
type TBType = TB1 Key

--
-- Patch CRUD Postgresql Operations
--

unSComposite (ArrayTB1 i) = i
unSComposite i = errorWithStackTrace ("unSComposite " <> show i)


dropTable r= "DROP TABLE "<> rawFullName r

rawFullName = showTable

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


allKVRec :: Ord f => TB2 f Showable -> [FTB Showable]
allKVRec (DelayedTB1 i) = maybe mempty allKVRec i
allKVRec (LeftTB1 i) = maybe mempty allKVRec i
allKVRec (ArrayTB1 i) = mconcat $ allKVRec <$> i
allKVRec  t@(TB1 (m, e))=  concat $  F.toList (go . unTB <$> (_kvvalues $ unTB $ eitherDescPK t))
  where
        go  (FKT _  _ tb) =  allKVRec  tb
        go  (IT  _ tb) = allKVRec tb
        go  (Attr _ a) = [a]


tableToKV r =   do
   ((rawPK r)) <> (rawDescription r)  <>(S.toList (rawAttrs r))

labelTable :: Table -> State ((Int, Map Int Table), (Int, Map Int Key)) (Labeled Text Table,TB3Data (Labeled Text)  Key  () )
labelTable i = do
   t <- tname i
   name <- Tra.traverse (\k-> (S.singleton (Inline k),) <$> kname t k ) (tableToKV i)
   return (t, (tableMeta i,) $ Compose $ Labeled (label t) $ KV $ M.fromList $ fmap Compose <$> name)

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

unComp :: (Show (g k a) ,F.Foldable f ) => Compose f g k a -> g k a
unComp = head . F.toList . getCompose

isTableRec tb = isTableRec'  (unTB1 tb )
isTableRec' tb = not $ L.null $ _kvrecrels (fst  tb )

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

isPairReflexive (Primitive i ) op (KInterval (Primitive j)) | i == j = False
isPairReflexive (Primitive j) op  (KArray (Primitive i) )  | i == j = False
isPairReflexive (KInterval i) op (KInterval j)
  | i == j && op == "<@" = False
  | i == j && op == "=" = True
isPairReflexive (Primitive i ) op (Primitive j) | i == j = True
isPairReflexive (KOptional i ) op  j = isPairReflexive i op j
isPairReflexive i op (KSerial j) = isPairReflexive i op j
isPairReflexive (KSerial i) op j = isPairReflexive i op j
isPairReflexive (KArray i )  op  (KArray j)
  | i == j  && op == "<@" = False
  | i == j  && op == "=" = True
isPairReflexive (KArray i )  op  j = True
isPairReflexive i op  j = errorWithStackTrace $ "isPairReflexive " <> show i <> " - "<> show  j

filterNotReflexive ks = L.filter (notReflexiveRel ks) ks
filterReflexive ks = L.filter (reflexiveRel ks) ks

notReflexiveRel ks = not . reflexiveRel ks
reflexiveRel ks
  | any (isArray . keyType . _relOrigin) ks =  (isArray . keyType . _relOrigin)
  | all (isJust . keyStatic . _relOrigin) ks = ( isJust . keyStatic. _relOrigin)
  | any (isJust . keyStatic . _relOrigin) ks = ( isNothing . keyStatic. _relOrigin)
  | any (\j -> not $ isPairReflexive (mapKType $ keyType (_relOrigin  j) ) (_relOperator j ) (mapKType $ keyType (_relTarget j) )) ks =  const False
  | otherwise = (\j-> isPairReflexive (mapKType $ keyType (_relOrigin  j) ) (_relOperator j ) (mapKType $ keyType (_relTarget j) ))

isInlineRel (Inline _ ) =  True
isInlineRel i = False

isReflexive (Path i r@(FKJoinTable _ ks _ )  t)
  |  not (t `S.isSubsetOf` (S.fromList $ fmap _relTarget ks ))  = False
  |  otherwise = isPathReflexive  r
isReflexive (Path _ l _ ) = isPathReflexive l

isPathReflexive (FKJoinTable _ ks _)
  | otherwise   = all id $ fmap (\j-> isPairReflexive (mapKType $ keyType (_relOrigin  j) ) (_relOperator j ) (mapKType $ keyType (_relTarget j) )) ks
isPathReflexive (FKInlineTable _)= True
isPathReflexive (RecJoin _ i ) = isPathReflexive i



allRec'
  :: Map Text Table
     -> Table
     -> TBData Key ()
allRec' i t = unTlabel' $ tableView  i t

tableView  invSchema r = fst $ flip runState ((0,M.empty),(0,M.empty)) $ do
  when (L.null $ rawPK r) (fail $ "cant generate ast for table " <> T.unpack (tableName r ) <> " the pk is null")
  (t,ks) <- labelTable r
  tb <- recurseTB invSchema (rawFKS r) False [] ks
  return  $ tb

tableViewNR invSchema r = fst $ flip runState ((0,M.empty),(0,M.empty)) $ do
  when (L.null $ rawPK r) (fail $ "cant generate ast for table " <> T.unpack (tableName r )<> " the pk is null")
  (t,ks) <- labelTable r
  tb <- recurseTB invSchema (S.filter (all isInlineRel. F.toList .pathRelRel)$ rawFKS r) False [] ks
  return  $ TB1 tb


rootPaths' invSchema r = (\(i,j) -> (unTlabel i,j ) ) $ fst $ flip runState ((0,M.empty),(0,M.empty)) $ do
  when (L.null $ rawPK r) (fail $ "cant generate ast for table " <> T.unpack (tableName r )<> " the pk is null")
  (t,ks) <- labelTable r
  tb <- recurseTB invSchema (rawFKS r ) False [] ks
  return ( TB1 tb , selectQuery $ tb )


allAttr i =  all allAttr' $ F.toList i
allAttr' (_,i) = all (isAttr .labelValue . getCompose) $ F.toList $ _kvvalues (labelValue $ getCompose i)
    where isAttr (Attr _ _ ) = True
          isAttr (IT k e)  = allAttr e
          isAttr _ = False

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


      pret = tname <> "."

      explodeRowSg l = explodeDelayed  (\i -> "ROW(" <> i <> ")")  "," (const (l <> ))
      tname = (label $ getCompose $ snd (unTB1 t)) <> "pre"
      tbasen = (label $ getCompose $ snd (unTB1 t))
      tnonRec ,tRec :: [Text]
      tnonRec =  (explodeDelayed id   "," (const id  )) . getCompose <$> m
        where m = flattenNonRec (_kvrecrels $ fst $ unTB1 t) (unTB1 t)
      tnonRecA =  (unTB1 t)
      tpk =  (explodeDelayed (\i -> "ROW(" <> i <> ")")  "," (const id ) ) .getCompose <$> m
        where m =  F.toList $  _kvvalues $ labelValue $ getCompose $   tfilpk
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
      tfilpk =   tbPK  t
      tnfil =   tbFilterE (\m e -> S.member e (S.fromList $ fmap S.fromList $ topRec $ _kvrecrels m)) <$> t
    in tell [query,top]

tlabel t = (label $ getCompose $ snd (unTB1 t))

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

tableType (ArrayTB1 [i]) = tableType i <> "[]"
tableType (LeftTB1 (Just i)) = tableType i
tableType (TB1 (m,_)) = kvMetaFullName  m


expandJoin :: Bool -> [Compose (Labeled Text) (TB (Labeled Text)) Key ()] -> Labeled Text (TB (Labeled Text) Key ()) -> Writer [Text] Text
expandJoin left env (Unlabeled (IT i (LeftTB1 (Just tb) )))
    = expandJoin True env $ Unlabeled (IT i tb)
expandJoin left env (Labeled l (IT i (LeftTB1 (Just tb) )))
    = expandJoin True env $ Labeled l (IT i tb)
expandJoin left env (Labeled l (IT i (ArrayTB1 [tb] )))
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
expandJoin left env (Labeled l (FKT _ ks (ArrayTB1 [tb])))
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
expandJoin left env i = errorWithStackTrace (show ("expandJoin",i))

joinOnPredicate :: [Rel Key] -> [Labeled Text ((TB (Labeled Text))  Key ())] -> [Labeled Text ((TB (Labeled Text))  Key ())] -> Text
joinOnPredicate ks m n =  T.intercalate " AND " $ (\(Rel l op r) ->  intersectionOp (mapKType . keyType . keyAttr . labelValue $ l) op (mapKType .keyType . keyAttr . labelValue $ r) (label l)  (label r )) <$> fkm
    where fkm  = (\rel -> Rel (look (_relOrigin rel ) m) (_relOperator rel) (look (_relTarget rel ) n)) <$>  ks
          look ki i = justError ("missing FK on " <> show (ki,ks ,keyAttr . labelValue <$> i )) $ (\j-> L.find (\v -> keyAttr (labelValue v) == j) i  ) ki

loadOnlyDescriptions (TB1 (kv ,m) ) = _kvpk kv

dumbKey n = Key n  Nothing [] 0 Nothing (unsafePerformIO newUnique) (Primitive (AtomicPrim ("pg_catalog","integer") ))

recursePath
  :: Bool->  RecState Key
     -> [(Set (Rel Key), Labeled Text (TB (Labeled Text) Key ()))]
     -> [(Set (Rel Key), Labeled Text (TB (Labeled Text) Key ()))]
     -> Map Text Table
     -> Path (Set Key) SqlOperation
     -> State
          ((Int, Map Int Table), (Int, Map Int Key))
          (Compose (Labeled Text) (TB (Labeled Text)) Key ())
recursePath isLeft isRec vacc ksbn invSchema (Path ifk jo@(FKInlineTable t ) e)
    | isArrayRel ifk  {-&& not (isArrayRel e )-}=   do
          tas <- tname nextT
          let knas = dumbKey (rawName nextT)
          kas <- kname tas  knas
          let
          (_,ksn) <-  labelTable  nextT
          tb <- fun ksn
          let
              ref = (\i -> Compose . justError ("cant find " ). fmap snd . L.find ((== S.singleton (Inline i)) . fst )$ ksbn ) $ head (S.toList ifk )
          return $  Compose $ Labeled (label $ kas) $ IT ref   (mapOpt $ mapArray $ TB1 tb )
    | otherwise = do
          (_,ksn) <-  labelTable nextT
          tb <-fun ksn
          lab <- if isTableRec' tb
            then do
              tas <- tname nextT
              let knas = dumbKey (rawName nextT)
              kas <- kname tas  knas
              return $ Labeled (label kas)
            else return  Unlabeled
          let
            ref = (\i -> Compose . justError ("cant find " ). fmap snd . L.find ((== S.singleton (Inline i)) . fst )$ ksbn ) $ head (S.toList ifk )
          return $ ( Compose $ lab $ IT  ref  (mapOpt $ TB1 tb)   )
    where
        nextLeft =  isLeft || isLeftRel ifk
        mapArray i =  if isArrayRel ifk then ArrayTB1 [i] else i
        mapOpt i = if isLeftRel ifk then  LeftTB1 $ Just  i else i
        nextT = justError ("recursepath lookIT "  <> show t <> " " <> show invSchema) (M.lookup t invSchema)
        fun =  recurseTB invSchema (rawFKS nextT) nextLeft isRec

recursePath isLeft isRec vacc ksbn invSchema (Path ifk jo@(FKJoinTable w ks tn) e)
    | S.size ifk   < S.size e =   do
          (t,ksn) <- labelTable nextT
          tb <-fun ksn
          tas <- tname nextT
          let knas = dumbKey(rawName nextT)
          kas <- kname tas  knas
          return $ Compose $ Labeled (label $ kas) (FKT [] ks  (mapOpt $ ArrayTB1 [ TB1 tb]  ))
    | isArrayRel ifk && not (isArrayRel e) =   do
          (t,ksn) <- labelTable nextT
          tb <-fun ksn
          tas <- tname nextT
          let knas = dumbKey (rawName nextT)
          kas <- kname tas  knas
          return $ Compose $ Labeled (label $ kas) (FKT (fmap (\i -> Compose . justError ("cant find " ). fmap snd . L.find ((== S.singleton (Inline i)) . fst )$ ksbn ) (_relOrigin <$> (filter (\i -> not $ S.member i (S.unions $ fmap fst vacc)) $  filterReflexive ks) ))  ks  (mapOpt $ mapArray $ TB1 tb  ))
    | otherwise = do
          (t,ksn) <- labelTable nextT
          tb@(m,Compose r)  <-fun ksn
          lab <- if not  . L.null $ isRec
            then do
              tas <- tname nextT
              let knas = dumbKey (rawName nextT)
              kas <- kname tas  knas
              return $ Labeled (label kas)
            else return  Unlabeled
          return $ Compose $ lab $ FKT (fmap (\i -> Compose . justError ("cant find " ). fmap snd . L.find ((== S.singleton (Inline i)) . fst )$ ksbn ) (_relOrigin <$> filter (\i -> not $ S.member (_relOrigin i) (S.map _relOrigin $ S.unions $ fmap fst vacc)) (filterReflexive ks)))  ks (mapOpt $ TB1 tb)
  where
        nextT = (\(Just i)-> i) (M.lookup tn (invSchema))
        nextLeft = any (isKOptional.keyType) (S.toList ifk) || isLeft
        mapArray i =  if isArrayRel ifk then ArrayTB1 [i] else i
        mapOpt i = if isLeftRel  ifk then  LeftTB1 $ Just  i else i
        fun =   recurseTB invSchema (rawFKS nextT) nextLeft isRec

recursePath isLeft isRec vacc ksbn invSchema jo@(Path ifk (RecJoin l f) e)
    = recursePath isLeft (fmap (\(b,c) -> if mAny (\c -> L.null c) c  then (b,b) else (b,c)) $  isRec  ) vacc ksbn invSchema (Path ifk f e)

recurseTB :: Map Text Table -> Set (Path (Set Key ) SqlOperation ) -> Bool -> RecState Key  -> TB3Data (Labeled Text) Key () -> StateT ((Int, Map Int Table), (Int, Map Int Key)) Identity (TB3Data (Labeled Text) Key ())
recurseTB invSchema  fks' nextLeft isRec (m, kv) =  (if L.null isRec then m else m  ,) <$>
    (\kv -> case kv of
      (Compose (Labeled l kv )) -> do
         i <- fun kv
         return (Compose (Labeled l i));
      (Compose (Unlabeled kv)) -> do
         i<- fun kv
         return (Compose (Unlabeled i))) kv
    where
      fun =  (\kv -> do
          let
              items = _kvvalues kv
              fkSet:: S.Set Key
              fkSet =   S.unions . fmap (S.fromList . fmap _relOrigin . (\i -> if all isInlineRel i then i else filterReflexive i ) . S.toList . pathRelRel ) $ filter isReflexive  $ S.toList fks'
              nonFKAttrs :: [(S.Set (Rel Key) ,TBLabel  ())]
              nonFKAttrs =  M.toList $  M.filterWithKey (\i a -> not $ S.isSubsetOf (S.map _relOrigin i) fkSet) items
          pt <- foldl (\acc  fk ->  do
                  vacc <- acc
                  let relFk =pathRelRel fk
                      lastItem =   L.filter cond isRec
                      cond (_,l) = mAny (\l-> L.length l == 1  && ((== relFk ). S.fromList. last $ l)) l
                  if L.length lastItem < 2
                  then   do
                    i <- fmap (relFk,) . recursePath nextLeft ( fmap (fmap (L.drop 1 ))  <$> L.filter (\(_,i) -> mAny (\i -> (S.fromList .concat . maybeToList . safeHead $ i) == relFk ) i ) (isRec <> fmap (\i -> (i,i) ) (_kvrecrels m))) vacc ( (M.toList $  fmap getCompose items )) invSchema $ fk
                    return (fmap getCompose i:vacc)
                  else return vacc
                  ) (return []) $ P.sortBy (P.comparing pathRelRel) (F.toList $ fks' )
          return (   KV $ M.fromList $ nonFKAttrs <> (fmap (fmap Compose ) pt)))

mAny f (MutRec i) = L.any f i


type RecState k = [(MutRec [[Rel k]],MutRec [[Rel k]])]

isLeftRel ifk = any (isKOptional.keyType) (S.toList ifk)
isArrayRel ifk = any (isArray.keyType) (S.toList ifk)


eitherDescPK :: (Functor f,F.Foldable f,Ord k) =>TB3 f k a -> Compose f (KV  (Compose f (TB f ))) k a
eitherDescPK i@(TB1 (kv, _)  )
  | not ( null ( _kvdesc kv) ) =  if L.null (F.toList $ tbDesc i) then tbPK i else tbDesc i
  | otherwise = tbPK i


tbDesc :: (Functor f,Ord k)=>TB3 f k a -> Compose f (KV  (Compose f (TB f ))) k a
tbDesc  =  tbFilter  (\kv k -> (S.isSubsetOf (S.map _relOrigin k) (S.fromList $ _kvdesc kv ) ))

tbPK :: (Functor f,Ord k)=>TB3 f k a -> Compose f (KV  (Compose f (TB f ))) k a
tbPK = tbFilter  (\kv k -> (S.isSubsetOf (S.map _relOrigin k) (S.fromList $ _kvpk kv ) ))


tbPK' :: (Ord k)=>TBData k a -> Compose Identity  (KV  (Compose Identity (TB Identity  ))) k a
tbPK' = tbFilter'  (\kv k -> (S.isSubsetOf (S.map _relOrigin k) (S.fromList $ _kvpk kv ) ))

tbUn :: (Functor f,Ord k) =>   Set k -> TB3 f k a ->  Compose f (KV  (Compose f (TB f ))) k a
tbUn un (TB1 (kv,item)) =  (\kv ->  mapComp (\(KV item)->  KV $ M.filterWithKey (\k _ -> pred kv k ) $ item) item ) un
  where pred kv k = (S.isSubsetOf (S.map _relOrigin k) kv )

tbAttr :: (Functor f,Ord k) =>  TB3 f k a ->  Compose f (KV  (Compose f (TB f ))) k a
tbAttr  =  tbFilter  (\kv k -> not (S.isSubsetOf (S.map _relOrigin k) (S.fromList (_kvpk kv) <> (S.fromList (_kvdesc kv ))) ))

tbFilter' pred (kv,item) =  mapComp (\(KV item)->  KV $ M.filterWithKey (\k _ -> pred kv k ) $ item) item
tbFilterE  pred (kv,item) =  (kv,mapComp (\(KV item)->  KV $ M.filterWithKey (\k _ -> pred kv k ) $ item) item)

tbFilter :: (Functor f,Ord k) =>  ( KVMetadata k -> Set (Rel k) -> Bool) -> TB3 f k a ->  Compose f (KV  (Compose f (TB f ))) k a
tbFilter pred (TB1 i) = tbFilter' pred i
tbFilter pred (LeftTB1 (Just i)) = tbFilter pred i
tbFilter pred (ArrayTB1 ([i])) = tbFilter pred i
tbFilter pred (DelayedTB1 (Just i)) = tbFilter pred i





mkKey i = do
  (c,m) <- snd <$> get
  let next = (c+1,M.insert (c+1) i m)
  modify (\(j,_) -> (j,next))
  return (c+1,i)

mkTable i = do
  (c,m) <- fst <$> get
  let next = (c+1,M.insert (c+1) i m)
  modify (\(_,j) -> (next,j))
  return (c+1)

aliasKeys (t,Labeled  a (Attr n   _ ))  = label t <> "." <> keyValue n <> " as " <> a


aliasTable (Labeled t r) = showTable r <> " as " <> t
kname :: Labeled Text Table -> Key -> QueryRef (Labeled Text (TB (Labeled Text) Key () ))
kname t i = do
  n <- mkKey i
  return $ (Labeled ("k" <> (T.pack $  show $ fst n)) (Attr i (TB1 ())) )




tname :: Table -> QueryRef (Labeled Text Table)
tname i = do
  n <- mkTable i
  return $ Labeled ("t" <> (T.pack $  show n)) i


markDelayed True (TB1 (m,v)) = TB1 . (m,) $ mapComp (KV . M.mapWithKey (\k v -> mapComp (recurseDel (if S.isSubsetOf (S.map _relOrigin k) ((S.fromList $ _kvpk m) <> (S.fromList $ _kvdesc m) ) then False else True)) v  ). _kvvalues ) v
markDelayed False (TB1 (m,v)) = TB1 . (m,) $ mapComp (KV . fmap (mapComp (recurseDel False)) . _kvvalues) v
markDelayed i (LeftTB1 j) = LeftTB1 $ (markDelayed  i)<$> j
markDelayed i (ArrayTB1 j) = ArrayTB1 $ (markDelayed  i)<$> j


makeTB1Delayed (LeftTB1 i ) =  LeftTB1 $ makeTB1Delayed <$> i
makeTB1Delayed (ArrayTB1 i ) =  ArrayTB1 $ makeTB1Delayed <$> i
makeTB1Delayed i  =  DelayedTB1 $ Just (markDelayed True i)

makeDelayed (KOptional i) = KOptional $ makeDelayed i
makeDelayed (KArray i ) = KArray $ makeDelayed i
makeDelayed i  = KDelayed i


forceDesc rec (ArrayTB1 m ) = ArrayTB1 $ forceDesc rec <$> m
forceDesc rec (LeftTB1 m ) = LeftTB1 $ forceDesc rec <$> m
forceDesc rec (DelayedTB1 (Just m) ) = forceDesc rec m
forceDesc rec (TB1 (m,v)) =  TB1 . (m,) $ mapComp (KV . M.mapWithKey (\k v -> mapComp ((if S.isSubsetOf (S.map _relOrigin k) (S.fromList (_kvpk m ) <> (S.fromList $ _kvdesc m) ) then forceDel True   else forceDel False  )) v   ). _kvvalues ) v
forceDel rec t =
            case t of
              Attr k v ->  Attr (alterKeyType forceDAttr k) v
              IT k v -> IT (mapComp (forceDel rec) k) (forceDesc True v)
              FKT k rel v -> FKT (mapComp (forceDel rec) <$> k)  rel ((if rec then forceDesc False else id ) v)

forceDTB1  v = go v
  where
    go v = case v of
      LeftTB1 i -> LeftTB1 $ go <$> i
      ArrayTB1 i -> ArrayTB1 $ go <$> i
      DelayedTB1 (Just i) -> i
      i -> i

forceDAttr v = go v
  where
    go v = case v of
      (KOptional i) -> KOptional $ go i
      (KArray i ) -> KArray $ go i
      (KDelayed i ) -> i
      i -> i


alterKeyType f  = Le.over keyTypes f

recurseDel False a@(Attr k v) = a
recurseDel True a@(Attr k v) = Attr (alterKeyType makeDelayed k ) v
recurseDel False a@(IT k v ) = IT k $ markDelayed  False v
recurseDel True a@(IT k v ) = IT (mapComp (recurseDel True ) k )  (makeTB1Delayed v)
recurseDel False a@(FKT  k rel v ) = FKT k rel $ markDelayed  True v
recurseDel True (FKT  k rel v ) = FKT (mapComp (recurseDel True ) <$> k )  rel  (makeTB1Delayed v)


explodeRow :: TB3 (Labeled Text) Key () -> Text
explodeRow = explodeRow'  (\i -> "ROW(" <> i <> ")")  "," (const id)
explodeRecord :: TB3Data (Labeled Text) Key () -> Text
explodeRecord  = explodeRow''   (\i -> "ROW(" <> i <> ")")  "," (const id)
explodeLabel :: Labeled Text (TB (Labeled Text) Key () ) -> Text
explodeLabel = explodeDelayed (\i -> "ROW(" <> i <> ")")  "," (const id)


leafDel True i = " case when " <> i <> " is not null then true else null end "
leafDel False i = " case when " <> i <> " is not null then true else null end "

explodeRow' block  assoc  leaf (DelayedTB1 (Just tbd@(TB1 (i,tb)))) = "(true)"
explodeRow' block assoc leaf (LeftTB1 (Just tb) ) = explodeRow' block assoc leaf tb
explodeRow' block assoc leaf (ArrayTB1 [tb] ) = explodeRow' block assoc leaf tb
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

isTB1Array (DelayedTB1 (Just tb) ) = isTB1Array tb
isTB1Array (LeftTB1 (Just tb)) = isTB1Array tb
isTB1Array (ArrayTB1 [tb]) = True
isTB1Array _ = False


isTB1Delayed (DelayedTB1 _ ) = True
isTB1Delayed (LeftTB1 (Just tb)) = isTB1Delayed tb
isTB1Delayed (ArrayTB1 [tb]) = isTB1Delayed tb
isTB1Delayed _ = False

unTlabel' ((m,kv) )  = (m,) $ overLabel (\(KV kv) -> KV $ fmap (Compose . Identity .unlabel.getCompose ) $   kv) kv
unTlabel  = fmap unTlabel'

unlabel (Labeled l (IT tn t) ) = (IT (relabel tn) (unTlabel t ))
unlabel (Unlabeled (IT tn t) ) = (IT (relabel tn) (unTlabel t ))
unlabel (Labeled l (FKT i fkrel t) ) = (FKT (fmap relabel i) fkrel (unTlabel  t ))
unlabel (Unlabeled (FKT i fkrel t) ) = (FKT (fmap relabel i) fkrel (unTlabel t))
unlabel (Labeled l (Attr k i )) = Attr k i

relabel = Compose . Identity . unlabel.getCompose

-- alterComp :: (f k a -> g d b ) -> Compose (Labeled Text) f  k a -> Compose (f Identityg d b
overLabel f = Compose .  Identity . f . labelValue  .getCompose




-- interval' i j = Interval.interval (ER.Finite i ,True) (ER.Finite j , True)
inf' = (\(ER.Finite i) -> i) . Interval.lowerBound
sup' = (\(ER.Finite i) -> i) . Interval.upperBound


_unTB1 (TB1 (m,i) ) =  i
_unTB1 (LeftTB1 (Just i )) = _unTB1 i
_unTB1 (DelayedTB1 (Just i )) = _unTB1 i
_unTB1 i =  errorWithStackTrace $ show ("untb1":: String,i)

instance P.Poset (FKey (KType Text))where
  compare  = (\i j -> case compare (i) (j) of
                      EQ -> P.EQ
                      LT -> P.LT
                      GT -> P.GT )



inlineName (KOptional i) = inlineName i
inlineName (KArray a ) = inlineName a
inlineName (Primitive (RecordPrim (s, i)) ) = i

inlineFullName (KOptional i) = inlineFullName i
inlineFullName (KArray a ) = inlineFullName a
inlineFullName (Primitive (RecordPrim (s, i)) ) = s <> "." <> i

relabeling :: (forall a . f a -> a ) -> (forall a . a -> p a ) -> TB f k a -> TB p k a
relabeling p l (Attr k i ) = (Attr k i)
relabeling p l (IT i tb ) = IT ((Compose.  l . relabeling p l . p . getCompose ) i) (relabelT p l tb)

relabelT :: (forall a . f a -> a ) -> (forall a . a -> p a ) -> TB3 f k a -> TB3 p k a
relabelT p l =  fmap (relabelT' p l)

relabelT' :: (forall a . f a -> a ) -> (forall a . a -> p a ) -> TB3Data f k a -> TB3Data p k a
relabelT' p l (m ,Compose j) =  (m,Compose $ l (KV $ fmap (Compose.  l . relabeling p l . p . getCompose ) (_kvvalues $ p j)))

backFKRef
  :: (Show (f Key ),Show a, Functor f) =>
     M.Map Key Key
     -> f Key
     -> TB2 Key a
     -> f (Compose Identity (TB f1) Key a)
backFKRef relTable ifk = fmap (_tb . uncurry Attr). reorderPK .  concat . fmap aattr . F.toList .  _kvvalues . unTB . _unTB1
  where
        reorderPK l = fmap (\i -> justError (show ("reorder wrong" :: String, ifk ,relTable , l,i))  $ L.find ((== i).fst) (catMaybes (fmap lookFKsel l) ) )  ifk
        lookFKsel (ko,v)=  (\kn -> (kn ,transformKey (mapKType $ keyType ko ) (mapKType $ keyType kn) v)) <$> knm
          where knm =  M.lookup ko relTable


postgresLiftPrim =
  [(Primitive (AtomicPrim PBounding ), KInterval (Primitive (AtomicPrim PPosition)))]

postgresLiftPrimConv =
  [((Primitive (AtomicPrim PBounding ), KInterval (Primitive (AtomicPrim PPosition)) ), ((\(TB1 (SBounding (Bounding i) )) -> IntervalTB1 (fmap   (TB1. SPosition ) i)) , (\(IntervalTB1 i) -> TB1 $ SBounding $ Bounding $ (fmap (\(TB1 (SPosition i)) -> i)) i)))]

postgresPrim =
  [("character varying",PText)
  ,("name",PText)
  ,("character_data",PText)
  ,("varchar",PText)
  ,("text",PText)
  ,("character",PText)
  ,("char",PText)
  ,("bpchar",PText)
  ,("sql_identifier" , PText)
  ,("base64url",PText)
  ,("session",PSession)
  ,("bytea",PBinary)
  ,("pdf",PMime "application/pdf")
  ,("ofx",PMime "application/x-ofx")
  ,("jpg",PMime "image/jpg")
  ,("email",PMime "text/plain")
  ,("html",PMime "text/html")
  ,("dynamic",PDynamic)
  ,("double precision",PDouble)
  ,("numeric",PDouble)
  ,("float8",PDouble)
  ,("int4",PInt)
  ,("cnpj",PCnpj)
  ,("cpf",PCpf)
  ,("int8",PInt)
  ,("integer",PInt)
  ,("bigint",PInt)
  ,("cardinal_number",PInt)
  ,("smallint",PInt)
  ,("boolean",PBoolean)
  ,("bool",PBoolean)
  ,("timestamptz",PTimestamp Nothing)
  ,("timestamp",PTimestamp (Just utc))
  ,("timestamp with time zone",PTimestamp Nothing)
  ,("timestamp without time zone",PTimestamp (Just utc))
  ,("interval", PInterval)
  ,("date" ,PDate)
  ,("time",PDayTime)
  ,("time with time zone" , PDayTime)
  ,("time without time zone" , PDayTime)
  ,("POINT3",PPosition)
  ,("LINESTRING3",PLineString)
  ,("box3d",PBounding)
  ]

type PGType = (Text,Text)
type PGRecord = (Text,Text)

ktypeLift :: Ord b => KType (Prim KPrim b) -> Maybe (KType (Prim KPrim b))
ktypeLift i = (M.lookup i (M.fromList postgresLiftPrim ))

ktypeRec v@(KOptional i) = ktypeLift v <|> ktypeRec i
ktypeRec v@(KArray i) = ktypeLift v <|> ktypeRec i
ktypeRec v@(KInterval i) = ktypeLift v <|> ktypeRec i
ktypeRec v@(KSerial i) = ktypeLift v <|> ktypeRec i
ktypeRec v@(KDelayed i) = ktypeLift v <|> ktypeRec i
ktypeRec v@(Primitive i ) = ktypeLift v

mapKType i = fromMaybe (fmap textToPrim i) $ ktypeRec (fmap textToPrim i)
mapKTypeM i = ktypeLift (fmap textToPrim i)

textToPrim :: Prim (Text,Text) (Text,Text) -> Prim KPrim (Text,Text)
textToPrim (AtomicPrim (s,i)) = case  M.lookup i (M.fromList postgresPrim) of
  Just k -> AtomicPrim k -- $ fromMaybe k (M.lookup k (M.fromList postgresLiftPrim ))
  Nothing -> errorWithStackTrace $ "no conversion for type " <> (show i)
textToPrim (RecordPrim i) =  (RecordPrim i)

preconversion i =  join $ (\t -> M.lookup (i,t) (M.fromList postgresLiftPrimConv)) <$> ktypeLift  i

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



interPointPost rel ref tar = interPoint (fmap (fmap (fmap (mapKType ))) rel) (fmap (firstTB (fmap (mapKType ))) ref) (fmap (firstTB (fmap (mapKType ))) tar)
