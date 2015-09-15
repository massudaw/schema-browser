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
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RankNTypes #-}

module Query where

import Data.Functor.Apply
import Data.Unique
import Data.Functor.Identity
import Data.Ord
import qualified Data.Poset as P
import qualified Data.Foldable as F
import Data.Traversable (mapAccumL)
import qualified Data.Traversable as Tra
import Data.Maybe
import qualified Data.Interval as Interval
import Data.Monoid hiding (Product)

import qualified Data.Text.Lazy as T
import qualified Data.ExtendedReal as ER

import GHC.Int
import Utils

import Database.PostgreSQL.Simple
import Database.PostgreSQL.Simple.Internal
import Database.PostgreSQL.Simple.ToField

import Control.Monad
import GHC.Exts (fromString)
import System.IO.Unsafe
import Control.Applicative
import Data.List (intercalate)
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Set (Set)
import Data.Map (Map)
import Control.Monad.State
import Data.Text.Lazy(Text)
import Debug.Trace
import GHC.Stack

import Types


textToPrim "character varying" = PText
textToPrim "name" = PText
textToPrim "varchar" = PText
textToPrim "text" = PText
textToPrim "bytea" = PBinary
textToPrim "pdf" = PMime "application/pdf"
textToPrim "ofx" = PMime "application/x-ofx"
textToPrim "jpg" = PMime "image/jpg"
textToPrim "character" = PText
textToPrim "char" = PText
textToPrim "double precision" = PDouble
textToPrim "numeric" = PDouble
textToPrim "float8" = PDouble
textToPrim "int4" = PInt
textToPrim "cnpj" = PCnpj
textToPrim "sql_identifier" =  PText
textToPrim "cpf" = PCpf
textToPrim "int8" = PInt
textToPrim "integer" = PInt
textToPrim "bigint" = PInt
textToPrim "cardinal_number" = PInt
textToPrim "boolean" = PBoolean
textToPrim "smallint" = PInt
textToPrim "timestamp without time zone" = PTimestamp
textToPrim "timestamp with time zone" = PTimestamp
textToPrim "interval" = PInterval
textToPrim "date" = PDate
textToPrim "time" = PDayTime
textToPrim "time with time zone" = PDayTime
textToPrim "time without time zone" = PDayTime
textToPrim "POINT" = PPosition
textToPrim "LINESTRING" = PLineString
textToPrim "box3d" = PBounding
textToPrim i = error $ "no case for type " <> T.unpack i


isSerial (KSerial _) = True
isSerial _ = False

isPrim (Primitive i) = True
isPrim i = False

isOptional (KOptional _) = True
isOptional _ = False

isArray :: KType i -> Bool
isArray (KArray _) = True
isArray (KOptional i) = isArray i
isArray _ = False


showableDef (KOptional i) = Just $ LeftTB1 (showableDef i)
showableDef (KSerial i) = Just $ SerialTB1 (showableDef i)
showableDef (KArray i ) = Nothing -- Just (SComposite Vector.empty)
showableDef i = Nothing

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

renderShowable :: FTB Showable -> String
renderShowable (LeftTB1 i ) = maybe "" renderShowable i
renderShowable (DelayedTB1 i ) =  maybe "<NotLoaded>" (\i -> "<Loaded| " <> renderShowable i <> "|>") i
renderShowable (SerialTB1 i ) = maybe "" renderShowable i
renderShowable (ArrayTB1 i)  = intercalate "," $ F.toList $ fmap renderShowable i
renderShowable (IntervalTB1 i)  = showInterval renderShowable i
renderShowable (TB1  i) = renderPrim i

renderPrim :: Showable -> String
renderPrim (SText a) = T.unpack a
renderPrim (SNumeric a) = show a
renderPrim (SBoolean a) = show a
renderPrim (SDouble a) = show a
renderPrim (STimestamp a) = show a
renderPrim (SLineString a ) = show a
renderPrim (SBounding a ) = show a
renderPrim (SDate a) = show a
renderPrim (SDayTime a) = show a
renderPrim (SBinary _) = show "<Binary>"
renderPrim (SPosition a) = show a
renderPrim (SPInterval a) = show a


showInterval f i | i == Interval.empty = show i
showInterval f (Interval.Interval (ER.Finite i,j) (ER.Finite l,m) ) = ocl j <> f i <> "," <> f l <> ocr m
  where
    ocl j = if j then "[" else "("
    ocr j = if j then "]" else ")"


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
isKOptional (InlineTable _ _) = False
isKOptional (KArray i)  = isKOptional i
isKOptional (KEither _ _) = False
isKOptional i = errorWithStackTrace (show i)



getPrim i@(Primitive _ ) = textToPrim <$> i
getPrim (KOptional j) =  getPrim j
getPrim (KDelayed j) =  getPrim j
getPrim (KSerial j) =  getPrim j
getPrim (KArray j) =  getPrim j
getPrim (KInterval j) =  getPrim j

inner b l m = l <> b <> m

-- Operators
intersectPred p@(Primitive _) op  (KInterval i) j (IntervalTB1 l )  | p == i =  Interval.member j l
intersectPred p@(KInterval j) "<@" (KInterval i) (IntervalTB1 k)  (IntervalTB1  l)  =  Interval.isSubsetOf k  l
intersectPred p@(KInterval j) "@>" (KInterval i) (IntervalTB1 k)  (IntervalTB1 l) =  flip Interval.isSubsetOf k l
intersectPred p@(KInterval j) "=" (KInterval i) (IntervalTB1 k)  (IntervalTB1 l)   =  k == l
intersectPred p@(KArray j) "<@" (KArray i) (ArrayTB1 k)  (ArrayTB1 l )   =  S.fromList (F.toList k) `S.isSubsetOf` S.fromList  (F.toList l)
intersectPred p@(KArray j) "@>" (KArray i) (ArrayTB1 k)  (ArrayTB1 l )   =  S.fromList (F.toList l) `S.isSubsetOf` S.fromList  (F.toList k)
intersectPred p@(KArray j) "=" (KArray i) (ArrayTB1 k)  (ArrayTB1 l )   =  k == l
intersectPred p@(Primitive _) op (KArray i) j (ArrayTB1 l )  | p == i =  elem j l
intersectPred p1@(Primitive _) op  p2@(Primitive _) j l   | p1 == p2 =  case op of
                                                                             "=" -> j ==  l
                                                                             "<" -> j < l
                                                                             ">" -> j > l
                                                                             ">=" -> j >= l
                                                                             "<=" -> j <= l
                                                                             "/=" -> j /= l

intersectPred p1 op  (KSerial p2) j (SerialTB1 l)   | p1 == p2 =  maybe False (j ==) l
intersectPred p1 op (KOptional p2) j (LeftTB1 l)   | p1 == p2 =  maybe False (j ==) l
intersectPred p1@(KOptional i ) op p2 (LeftTB1 j) l  =  maybe False id $ fmap (\m -> intersectPred i op p2 m l) j
intersectPred p1 op p2 j l   = error ("intersectPred = " <> show p1 <> show p2 <>  show j <> show l)

pkOp (KOptional j ) i  (LeftTB1 l) k  = maybe False id (pkOp i j k <$> l)
pkOp (KSerial j ) i  (SerialTB1 l) k  = maybe False id (pkOp i j k <$> l)
pkOp i (KOptional j ) k (LeftTB1 l) = maybe False id (pkOp i j k <$> l)
pkOp i (KSerial j ) k (SerialTB1 l) = maybe False id (pkOp i j k <$> l)
pkOp (KArray i) (KArray j) (ArrayTB1 k) (ArrayTB1 l) | i == j = not $ S.null $ S.intersection (S.fromList (F.toList k)) (S.fromList (F.toList  l ))
pkOp (KInterval i) (KInterval j) (IntervalTB1 k) (IntervalTB1 l)| i == j  = not $ Interval.null $ Interval.intersection  k l
pkOp (Primitive i ) (Primitive j ) k l  | i == j = k == l
pkOp a b c d = errorWithStackTrace (show (a,b,c,d))

pkOpSet i l = (\i -> if L.null i then False else L.all id i) $ zipWith (\(a,b) (c,d)-> pkOp (keyType a)  (keyType c) b d) (L.sortBy (comparing fst ) i) (L.sortBy (comparing fst) l)


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
    | fmap textToPrim i == getPrim j = (\j i -> i <> " IN (select * from unnest("<> j <> ") ) ")
    | otherwise = errorWithStackTrace $ "wrong type intersectionOp {*} - * " <> show i <> " /= " <> show j
intersectionOp j op (KArray i )
    | getPrim i == getPrim j = (\i j  -> i <> " IN (select * from unnest("<> j <> ") ) ")
    | otherwise = errorWithStackTrace $ "wrong type intersectionOp * - {*} " <> show j <> " /= " <> show i
intersectionOp i op j = inner op

showTable t  = rawSchema t <> "." <> rawName t

delete
  :: ToField (TB Identity Key  Showable)  =>
     Connection ->  TB1 (Showable) -> Table -> IO GHC.Int.Int64
delete conn kold t = execute conn (fromString $ traceShowId $ T.unpack del) koldPk
  where
    equality k = attrValueName k <> "="  <> "?"
    koldPk = runIdentity . getCompose <$> F.toList (_kvvalues . unTB . tbPK $ tableNonRef kold)
    pred   =" WHERE " <> T.intercalate " AND " (fmap  equality koldPk)
    del = "DELETE FROM " <> rawFullName t <>   pred

findPKM (LeftTB1 i ) =  join $ fmap (findPKM ) i
findPKM i  = Just $ concat . fmap (\i -> zip (keyattr i) (kattr i )) .F.toList . _kvvalues . unTB . tbPK $ i

updateAttr
  :: ToField (TB Identity Key Showable) =>
     Connection -> TB1  Showable -> TB1 Showable -> Table -> IO GHC.Int.Int64
updateAttr conn kv kold t = execute conn (fromString $ traceShowId $ T.unpack up)  (skv <> koldPk)
  where
    equality k = attrValueName k <> "="  <> "?"
    koldPk = runIdentity . getCompose <$> F.toList ( _kvvalues . unTB $ tbPK (tableNonRefK kold))
    pred   =" WHERE " <> T.intercalate " AND " (equality <$> koldPk)
    setter = " SET " <> T.intercalate "," (equality <$> skv )
    up = "UPDATE " <> rawFullName t <> setter <>  pred
    skv = runIdentity .getCompose <$> F.toList  (_kvvalues $ unTB tbskv)
    (TB1 (_,tbskv)) = isM
    isM :: TB3 Identity Key  Showable
    isM =  justError ("cant diff befor update" <> show (kv,kold)) $ diffUpdateAttr kv kold

diffUpdateAttr :: TB1 Showable -> TB1 Showable -> Maybe (TB1 Showable)
diffUpdateAttr  kv kold@(TB1 (t,_) ) =  fmap (TB1 .(t,) . _tb . KV ) .  allMaybesMap  $ liftF2 (\i j -> if i == j then Nothing else Just i) (_kvvalues . unTB . _unTB1 . tableNonRefK  $ kv ) (_kvvalues . unTB . _unTB1 . tableNonRefK $ kold )

attrValue :: (Ord a,Show a) => TB Identity Key a -> FTB a
attrValue (Attr _  v)= v
attrValue i = errorWithStackTrace $ " no attr value instance " <> show i

attrType :: (Ord a,Show a) => TB Identity Key a -> KType Text
attrType (Attr i _)= keyType i
attrType (IT i _) = overComp attrType i
attrType i = errorWithStackTrace $ " no attr value instance " <> show i

attrValueName :: (Ord a,Show a) => TB Identity Key a -> Text
attrValueName (Attr i _ )= keyValue i
attrValueName (IT i  _) = overComp attrValueName i
attrValueName i = errorWithStackTrace $ " no attr value instance " <> show i

type TBValue = TB1 (Key,Showable)
type TBType = TB1 Key


insertAttr
  :: (MonadIO m
     ,Functor m
     ,ToField (TB Identity Key Showable))
     => (TB2 Key () -> RowParser (TB2 Key Showable) )
     -> Connection
     -> TB3 Identity Key Showable
     -> Table
     -> m (TB3 Identity  Key Showable)
insertAttr f conn krec  t = if not (L.null pkList)
              then   do
        let iquery = T.unpack $ "INSERT INTO " <> rawFullName t <>" ( " <> T.intercalate "," (fmap attrValueName  kva) <> ") VALUES (" <> T.intercalate "," (fmap (const "?") kva) <> ")" <> " RETURNING ROW(" <>  T.intercalate "," (attrValueName <$> pkList ) <> ")"
        liftIO $ print iquery
        out :: TB1 Showable <-  fmap head $ liftIO $ queryWith (f (  TB1 . (tableMeta t,) . _tb $  KV (M.fromList $ fmap (\i -> (S.singleton $ Inline $ keyAttr i,Compose (Identity i))) (fmap (const ()) <$> pkList )))) conn (fromString  iquery ) (  kva)
        return $ mapTB1 (mapComp (\case{ (Attr k' v')-> maybe (Attr k' v')    unTB $ fmap snd $ getCompose $ unTB $ findTB1 (overComp (\case{Attr nk nv ->nk == k'; i-> False} )) out; i-> i} ) ) krec
              else liftIO $ execute conn (fromString $ traceShowId $ T.unpack $ "INSERT INTO " <> rawFullName t <>" ( " <> T.intercalate "," (fmap attrValueName kva) <> ") VALUES (" <> T.intercalate "," (fmap (const "?") kva) <> ")"   )  kva >> return krec
  where pkList :: [ TB Identity Key Showable]
        pkList =    L.filter pred  . fmap (runIdentity. getCompose) $ (F.toList $ _kvvalues $ unTB $ tbPK $ tableNonRefK krec )
        pred i = (isSerial . attrType $ i) && (isNothing . unSSerial .attrValue $ i )
        kva = L.filter (not . pred) $ fmap (runIdentity . getCompose) $ F.toList (_kvvalues $ unTB k)
        (TB1 (_,k) ) = tableNonRefK krec


unSComposite (ArrayTB1 i) = i
unSComposite i = errorWithStackTrace ("unSComposite " <> show i)


dropTable r= "DROP TABLE "<> rawFullName r

rawFullName = showTable

createTable r@(Raw sch _ _ _ tbl _ _ pk _ fk attr) = "CREATE TABLE " <> rawFullName r  <> "\n(\n\t" <> T.intercalate ",\n\t" commands <> "\n)"
  where
    commands = (renderAttr <$> S.toList attr ) <> [renderPK] <> fmap renderFK (S.toList fk)
    renderAttr k = keyValue k <> " " <> renderTy (keyType k) <> if  (isKOptional (keyType k)) then "" else " NOT NULL"
    renderKeySet pk = T.intercalate "," (fmap keyValue (S.toList pk ))
    renderTy (KOptional ty) = renderTy ty <> ""
    renderTy (KSerial ty) = renderTy ty <> ""
    renderTy (KInterval ty) = renderTy ty <> ""
    renderTy (KArray ty) = renderTy ty <> "[] "
    renderTy (Primitive ty ) = ty
    renderTy (InlineTable s ty ) = s <> "." <> ty
    renderPK = "CONSTRAINT " <> tbl <> "_PK PRIMARY KEY (" <>  renderKeySet pk <> ")"
    renderFK (Path origin (FKJoinTable _ ks table) end) = "CONSTRAINT " <> tbl <> "_FK_" <> table <> " FOREIGN KEY " <>  renderKeySet origin <> ") REFERENCES " <> table <> "(" <> renderKeySet end <> ")  MATCH SIMPLE  ON UPDATE  NO ACTION ON DELETE NO ACTION"
    renderFK (Path origin _  end) = ""


keyOptional (k,v) = (kOptional k ,LeftTB1 $ Just v)

unKeyOptional (k  ,(LeftTB1 v) ) = fmap (unKOptional k,) v

kOptional (Key a  c m n d e) = Key a  c m  n d (KOptional e)
kDelayed (Key a  c m n d e) = Key a  c m  n d (KDelayed e)

unKOptional ((Key a  c m n d (KOptional e))) = (Key a  c m n d e )
unKOptional ((Key a  c m n d (e@(Primitive _)))) = (Key a  c m n d e )
unKOptional i = errorWithStackTrace ("unKOptional" <> show i)

unKDelayed ((Key a  c m n d (KDelayed e))) = (Key a  c m n d e )
unKDelayed i = errorWithStackTrace ("unKDelayed" <> show i)

unKArray (Key a  c d m n (KArray e)) = Key a  c d  m n e
unKArray (Key a  c d m n e) = Key a  c d  m n e
-- unKArray (Key a  c d m (KOptional (KArray e) )) = Key a  c d m e



unIntercalate :: ( Char -> Bool) -> String -> [String]
unIntercalate pred s                 =  case dropWhile pred s of
                                "" -> []
                                s' -> w : unIntercalate pred s''
                                      where (w, s'') =
                                             break pred s'

data Tag = TAttr | TPK

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
   (S.toList (rawPK r)) <> (rawDescription r)  <>(S.toList (rawAttrs r))


preLabelTable :: Text -> Table ->  (TB3 (Labeled Text)  Key () )
preLabelTable t i =
   let v = fmap (\k -> (S.singleton (Inline k),Compose $ Labeled ( "(" <> t <> ")." <> keyValue k ) (Attr k (TB1 ()) )) ) (tableToKV i)
   in (TB1 . (tableMeta i,) $ Compose $ Labeled t $KV $ M.fromList $ v )


labelTable :: Table -> State ((Int, Map Int Table), (Int, Map Int Key)) (Labeled Text Table,TB3 (Labeled Text)  Key  () )
labelTable i = do
   t <- tname i
   name <- Tra.traverse (\k-> (S.singleton (Inline k),) <$> kname t k ) (tableToKV i)
   return (t,TB1 . (tableMeta i,) $ Compose $ Labeled (label t) $ KV $ M.fromList $ fmap Compose <$> name)

expandTable ::  TB3  (Labeled Text) Key  () -> Text
expandTable tb@(TB1 (meta, Compose (Labeled t ((KV i)))  ))  =
   let query = "(SELECT " <>  T.intercalate "," (aliasKeys  . getCompose <$> name) <> " FROM " <> aliasTable <> ") as " <> t
       name =  tableAttr tb
       aliasTable = kvMetaFullName meta  <> " as " <> t
       aliasKeys (Labeled  a (Attr n    _ ))  = t <> "." <> keyValue n <> " as " <> a
   in query
expandTable (DelayedTB1 (Just tb)) = expandTable tb
expandTable tb = errorWithStackTrace (show tb)


isPairReflexive (Primitive i ) op (KInterval (Primitive j)) | i == j = False
isPairReflexive (Primitive j) op  (KArray (Primitive i) )  | i == j = False
isPairReflexive (KInterval i) op (KInterval j)
  | i == j && op == "<@" = False
  | i == j && op == "=" = True
isPairReflexive (Primitive i ) op (Primitive j) | i == j = True
isPairReflexive (KOptional i ) op  j = isPairReflexive i op j
isPairReflexive i op (KSerial j) = isPairReflexive i op j
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
  | any (\j -> not $ isPairReflexive (textToPrim <$> keyType (_relOrigin  j) ) (_relOperator j ) (textToPrim <$> keyType (_relTarget j) )) ks =  const False
  | otherwise = (\j-> isPairReflexive (textToPrim <$> keyType (_relOrigin  j) ) (_relOperator j ) (textToPrim <$> keyType (_relTarget j) ))

isInlineRel (Inline _ ) =  True
isInlineRel i = False


isPathReflexive (FKJoinTable _ ks _)
  = all id $ fmap (\j-> isPairReflexive (textToPrim <$> keyType (_relOrigin  j) ) (_relOperator j ) (textToPrim <$> keyType (_relTarget j) )) ks
isPathReflexive (FKInlineTable _)= True
isPathReflexive (FKEitherField _ )= False
isPathReflexive (RecJoin i ) = isPathReflexive i

isPathEither (FKJoinTable _ ks _) = False
isPathEither (FKInlineTable _)= False
isPathEither (FKEitherField _ )= True
isPathEither (RecJoin i ) = isPathEither i


allRec'
  :: Map Text Table
     -> Table
     -> TB1 ()
allRec' i t = unTlabel $ tableView  i t

tableView  invSchema r = fst $ flip runState ((0,M.empty),(0,M.empty)) $ do
  (t,ks) <- labelTable r
  tb <- recurseTB invSchema r False ks
  return  tb

rootPaths' invSchema r = (\(i,j) -> (unTlabel i,j ) ) $ fst $ flip runState ((0,M.empty),(0,M.empty)) $ do
  (t,ks) <- labelTable r
  tb <- recurseTB invSchema r False ks
  return ( tb , selectQuery tb )

-- keyAttr :: Show b  => TB Identity b a -> b
keyAttr (Attr i _ ) = i
keyAttr i = errorWithStackTrace $ "cant find keyattr " <> (show i)


selectQuery t = "SELECT " <> explodeRow t <> " FROM " <> expandTable t <> expandQuery False  t

expandQuery left (DelayedTB1 (Just t)) = ""--  expandQuery left t
expandQuery left t@(TB1 (meta, m))
    = foldr1 mappend (expandJoin left (F.toList (_kvvalues . labelValue . getCompose $ m) ) .getCompose <$> F.toList (_kvvalues . labelValue . getCompose $ m))


expandJoin :: Bool -> [Compose (Labeled Text) (TB (Labeled Text)) Key ()] -> Labeled Text (TB (Labeled Text) Key ()) -> Text
expandJoin left env (Unlabeled (IT i (LeftTB1 (Just tb) )))
    = expandJoin True env $ Unlabeled (IT i tb)
expandJoin left env (Labeled l (IT i (LeftTB1 (Just tb) )))
    = expandJoin True env $ Labeled l (IT i tb)
expandJoin left env (Labeled l (IT i (ArrayTB1 [tb] )))
    = jt <> " JOIN LATERAL (SELECT array_agg(" <> explodeRow  tb  <> "  order by arrrow ) as " <> l <> " FROM  (SELECT * FROM (SELECT *,row_number() over () as arrrow FROM UNNEST(" <> tname  <> ") as arr) as arr ) " <> label tas <> expandQuery left tb <> " )  as " <>  label tas <> " ON true"
        where
          tas = getTas tb
          getTas (DelayedTB1 (Just tb))  = getTas tb
          getTas (TB1  (_,Compose tas)) = tas
          tname = label $ getCompose i
          jt = if left then " LEFT" else ""
expandJoin left env (Labeled l (IT i tb)) = expandQuery left tb
expandJoin left env (Unlabeled  (IT _ tb )) = expandQuery left tb
expandJoin left env (Labeled _ (Attr _ _ )) = ""
expandJoin left env (Unlabeled  (Attr _ _ )) = ""
expandJoin left env (Unlabeled (FKT i rel (LeftTB1 (Just tb)))) = expandJoin True env (Unlabeled (FKT i rel tb))
expandJoin left env (Labeled l (FKT i rel (LeftTB1 (Just tb)))) = expandJoin True env (Labeled l (FKT i rel tb))
expandJoin left env (Labeled l (FKT _ ks (ArrayTB1 [tb])))
    = jt <> " JOIN LATERAL (select * from ( SELECT " <>  hasArray ( L.find (isArray. keyType ._tbattrkey . labelValue )  (look (_relOrigin <$> ks) (fmap getCompose $ concat $ fmap nonRef env))) <> "  ) as " <>  label tas  <>  (if left then "" else " WHERE " <> l <> " is not null " ) <> " ) as " <>  label tas <> " ON true "
      where
          hasArray (Just _)  =  "array_agg(" <> explodeRow  tb <> " order by arrrow) as " <> l <> " FROM ( SELECT * FROM (SELECT *,row_number() over () as arrrow FROM UNNEST(" <> label (justError "no array in rel" $ L.find (isArray. keyType ._tbattrkey . labelValue )  (look (_relOrigin <$> ks) (fmap getCompose $ concat $ fmap nonRef env)))  <> ") as arr) as z1 "  <> jt  <> " JOIN " <> expandTable tb <> " ON " <>  label (head $ look  [ _relTarget $ justError "no array in rel" $ L.find (isArray. keyType . _relOrigin ) ks] (fmap getCompose $ F.toList   (tableAttr tb))) <> " = arr " <> nonArrayJoin  <> " ) as z1 " <> expandQuery left tb
          hasArray Nothing = "array_agg(" <> explodeRow  tb <> " ) as " <> l <> " FROM " <> expandTable tb <>   expandQuery left tb <> " WHERE true " <>  nonArrayJoin
          nonArrayJoin = if L.null nonArrayRel then "" else " AND " <> joinOnPredicate nonArrayRel (fmap getCompose $ concat $ fmap nonRef  env ) (fmap getCompose $ F.toList   (tableAttr tb))
            where
              nonArrayRel = L.filter (not . isArray . keyType . _relOrigin) ks
          tas = getTas tb
          getTas (DelayedTB1 (Just tb))  = getTas tb
          getTas (TB1  (_,Compose tas)) = tas
          look :: [Key] -> [Labeled Text ((TB (Labeled Text)) Key ())] ->  [Labeled Text ((TB (Labeled Text)) Key ())]
          look ki i = justError ("missing FK on " <> show (ki,ks ,keyAttr . labelValue <$> i )  ) $ allMaybes $ fmap (\j-> L.find (\v -> keyAttr (labelValue v) == j) i  ) ki
          jt = if left then " LEFT" else ""
expandJoin left env (Unlabeled (FKT _ rel tb))
  = jt <> " JOIN " <> expandTable tb <> " ON " <> joinOnPredicate rel (fmap getCompose $ concat $ fmap nonRef env) (fmap getCompose $ F.toList (tableAttr tb)) <> expandQuery left tb
    where
      jt = if left then " LEFT" else ""

expandJoin left env i = errorWithStackTrace (show i)

joinOnPredicate :: [Rel Key] -> [Labeled Text ((TB (Labeled Text))  Key ())] -> [Labeled Text ((TB (Labeled Text))  Key ())] -> Text
joinOnPredicate ks m n =  T.intercalate " AND " $ (\(Rel l op r) ->  intersectionOp (keyType . keyAttr . labelValue $ l) op (keyType . keyAttr . labelValue $ r) (label l)  (label r )) <$> fkm
    where fkm  = (\rel -> Rel (look (_relOrigin rel ) m) (_relOperator rel) (look (_relTarget rel ) n)) <$>  ks
          look ki i = justError ("missing FK on " <> show (ki,ks ,keyAttr . labelValue <$> i )) $ (\j-> L.find (\v -> keyAttr (labelValue v) == j) i  ) ki

loadOnlyDescriptions (TB1 (kv ,m) ) = _kvpk kv

recursePath
  :: Bool
     -> [(Set (Rel Key), Labeled Text (TB (Labeled Text) Key ()))]
     -> [(Set (Rel Key), Labeled Text (TB (Labeled Text) Key ()))]
     -> Map Text Table
     -> Path (Set Key) SqlOperation
     -> State
          ((Int, Map Int Table), (Int, Map Int Key))
          (Compose (Labeled Text) (TB (Labeled Text)) Key ())
recursePath isLeft vacc ksbn invSchema (Path ifk jo@(FKInlineTable t ) e)
    | isArrayRel ifk  {-&& not (isArrayRel e )-}=   do
          tas <- tname nextT
          let knas = Key (rawName nextT) Nothing 0 Nothing (unsafePerformIO newUnique) (Primitive "integer" )
          kas <- kname tas  knas
          let
              ksn = preLabelTable ( label tas )  nextT
          tb <- fun ksn
          let
              ref = (\i -> Compose . justError ("cant find " ). fmap snd . L.find ((== S.singleton (Inline i)) . fst )$ ksbn ) $ head (S.toList ifk )
          return $  Compose $ Labeled (label $ kas) $ IT ref   (mapOpt $ mapArray tb )
    | otherwise = do
          let tname = head $ fmap (\i -> label . justError ("cant find " ). fmap snd . L.find ((== S.singleton (Inline i)) . fst )$ ksbn ) (S.toList ifk )
              ksn = preLabelTable tname   nextT
          tb <-fun ksn
          let
            ref = (\i -> Compose . justError ("cant find " ). fmap snd . L.find ((== S.singleton (Inline i)) . fst )$ ksbn ) $ head (S.toList ifk )
          return $ ( Compose $ Unlabeled $ IT  ref  (mapOpt tb)   )
    where
        nextLeft =  isLeft || isLeftRel ifk
        mapArray i =  if isArrayRel ifk then ArrayTB1 [i] else i
        mapOpt i = if isLeftRel ifk then  LeftTB1 $ Just  i else i
        nextT = justError ("recursepath lookIT "  <> show t <> " " <> show invSchema) (M.lookup t invSchema)
        fun =  recurseTB invSchema nextT nextLeft


recursePath isLeft vacc ksbn invSchema (Path ifk jo@(FKJoinTable w ks tn) e)
    | S.size ifk   < S.size e =   do
          (t,ksn) <- labelTable nextT
          tb <-fun ksn
          tas <- tname nextT
          let knas = (Key (rawName nextT) Nothing 0 Nothing (unsafePerformIO newUnique)  (Primitive "integer" ))
          kas <- kname tas  knas
          return $ Compose $ Labeled (label $ kas) (FKT [] ks  (mapOpt $ ArrayTB1 [ tb]  ))
    | isArrayRel ifk && not (isArrayRel e) =   do
          (t,ksn) <- labelTable nextT
          tb <-fun ksn
          tas <- tname nextT
          let knas = (Key (rawName nextT) Nothing 0 Nothing (unsafePerformIO newUnique)  (Primitive "integer" ))
          kas <- kname tas  knas
          return $ Compose $ Labeled (label $ kas) (FKT (fmap (\i -> Compose . justError ("cant find " ). fmap snd . L.find ((== S.singleton (Inline i)) . fst )$ ksbn ) (_relOrigin <$> (filter (\i -> not $ S.member i (S.unions $ fmap fst vacc)) $  filterReflexive ks) ))  ks  (mapOpt $ mapArray $ tb  ))
    | otherwise = do
          (t,ksn) <- labelTable nextT
          tb <-fun ksn
          return $ Compose $ Unlabeled $ FKT (fmap (\i -> Compose . justError ("cant find " ). fmap snd . L.find ((== S.singleton (Inline i)) . fst )$ ksbn ) (_relOrigin <$> filter (\i -> not $ S.member (_relOrigin i) (S.map _relOrigin $ S.unions $ fmap fst vacc)) (filterReflexive ks)))  ks (mapOpt $ tb)
  where
        nextT = (\(Just i)-> i) (M.lookup tn (invSchema))
        nextLeft = any (isKOptional.keyType) (S.toList ifk) || isLeft
        mapArray i =  if isArrayRel ifk then ArrayTB1 [i] else i
        mapOpt i = if isLeftRel  ifk then  LeftTB1 $ Just  i else i
        fun =   recurseTB invSchema nextT nextLeft

isLeftRel ifk = any (isKOptional.keyType) (S.toList ifk)
isArrayRel ifk = any (isArray.keyType) (S.toList ifk)

pathRelRel :: Path (Set Key ) SqlOperation -> Set (Rel Key)
pathRelRel (Path _ (FKJoinTable _ rel  _ ) _ ) = S.fromList rel
pathRelRel (Path r (FKInlineTable  _   )  _ ) = S.map Inline r
pathRelRel (Path r (FKEitherField _    )  _ ) = S.map Inline r

pathRel (Path _ rel _ ) = rel
pathRelRef (Path ifk _ _ ) = ifk
pathRelStore (Path _ _ ifk ) = ifk

eitherDescPK :: (Functor f,Ord k) =>TB3 f k a -> Compose f (KV  (Compose f (TB f ))) k a
eitherDescPK i@(TB1 (kv, _)  )
  | not ( null ( _kvdesc kv) ) =  tbDesc i
  | otherwise = tbPK i


tbDesc :: (Functor f,Ord k)=>TB3 f k a -> Compose f (KV  (Compose f (TB f ))) k a
tbDesc  =  tbFilter  (\kv k -> (S.isSubsetOf (S.map _relOrigin k) (S.fromList $ _kvdesc kv ) ))

tbPK :: (Functor f,Ord k)=>TB3 f k a -> Compose f (KV  (Compose f (TB f ))) k a
tbPK = tbFilter  (\kv k -> (S.isSubsetOf (S.map _relOrigin k) (_kvpk kv ) ))

tbUn :: (Functor f,Ord k) =>   Set k -> TB3 f k a ->  Compose f (KV  (Compose f (TB f ))) k a
tbUn un (TB1 (kv,item)) =  (\kv ->  mapComp (\(KV item)->  KV $ M.filterWithKey (\k _ -> pred kv k ) $ item) item ) un
  where pred kv k = (S.isSubsetOf (S.map _relOrigin k) kv )

tbAttr :: (Functor f,Ord k) =>  TB3 f k a ->  Compose f (KV  (Compose f (TB f ))) k a
tbAttr  =  tbFilter  (\kv k -> not (S.isSubsetOf (S.map _relOrigin k) (_kvpk kv <> (S.fromList (_kvdesc kv ))) ))

tbFilter :: (Functor f,Ord k) =>  ( KVMetadata k -> Set (Rel k) -> Bool) -> TB3 f k a ->  Compose f (KV  (Compose f (TB f ))) k a
tbFilter pred (TB1 (kv,item)) =  mapComp (\(KV item)->  KV $ M.filterWithKey (\k _ -> pred kv k ) $ item) item
tbFilter pred (LeftTB1 (Just i)) = tbFilter pred i
tbFilter pred (ArrayTB1 ([i])) = tbFilter pred i
tbFilter pred (DelayedTB1 (Just i)) = tbFilter pred i
f = errorWithStackTrace ""

recurseTB :: Map Text Table -> Table -> Bool -> TB3 (Labeled Text) Key () -> StateT ((Int, Map Int Table), (Int, Map Int Key)) Identity (TB3 (Labeled Text) Key ())
recurseTB invSchema  nextT nextLeft ksn@(TB1 (m, kv) ) =  TB1 . (m,) <$>
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
              fkSet =  S.unions . fmap (S.fromList . fmap _relOrigin . (\i -> if all isInlineRel i then i else filterReflexive i ) . S.toList . pathRelRel ) $ filter (isPathReflexive . pathRel) $ S.toList (rawFKS nextT)
              nonFKAttrs :: [(S.Set (Rel Key) ,TBLabel  ())]
              nonFKAttrs =  M.toList $  M.filterWithKey (\i a -> not $ S.isSubsetOf (S.map _relOrigin i) fkSet) items
          pt <- foldl (\acc  fk ->  do
                  vacc <- acc
                  i <- fmap (pathRelRel fk,) . recursePath nextLeft vacc ( (M.toList $  fmap getCompose items )) invSchema $ fk
                  return (fmap getCompose i:vacc)
                  ) (return []) $ P.sortBy (P.comparing pathRelRel) (F.toList $ rawFKS nextT)
          return (   KV $ M.fromList $ nonFKAttrs <> (fmap (fmap Compose ) pt)))




unAttr (Attr _ i) = i
unAttr i = errorWithStackTrace $ "cant find attr" <> (show i)

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


markDelayed True (TB1 (m,v)) = TB1 . (m,) $ mapComp (KV . M.mapWithKey (\k v -> mapComp (recurseDel (if S.isSubsetOf (S.map _relOrigin k) (_kvpk m <> (S.fromList $ _kvdesc m) ) then False else True)) v  ). _kvvalues ) v
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
forceDesc rec (TB1 (m,v)) =  TB1 . (m,) $ mapComp (KV . M.mapWithKey (\k v -> mapComp ((if S.isSubsetOf (S.map _relOrigin k) (_kvpk m <> (S.fromList $ _kvdesc m) ) then forceDel True   else forceDel False  )) v   ). _kvvalues ) v
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


alterKeyType f (Key a b c d m e) = (Key a b c d m (f e))

recurseDel False a@(Attr k v) = a
recurseDel True a@(Attr k v) = Attr (alterKeyType makeDelayed k ) v
recurseDel False a@(IT k v ) = IT k $ markDelayed  False v
recurseDel True a@(IT k v ) = IT (mapComp (recurseDel True ) k )  (makeTB1Delayed v)
recurseDel False a@(FKT  k rel v ) = FKT k rel $ markDelayed  True v
recurseDel True (FKT  k rel v ) = FKT (mapComp (recurseDel True ) <$> k )  rel  (makeTB1Delayed v)


explodeRow :: TB3 (Labeled Text) Key () -> Text
explodeRow = explodeRow'  (\i -> "ROW(" <> i <> ")")  "," (const id)
explodeLabel :: Labeled Text (TB (Labeled Text) Key () ) -> Text
explodeLabel = explodeDelayed (\i -> "ROW(" <> i <> ")")  "," (const id)


leafDel True i = " case when " <> i <> " is not null then true else null end "
leafDel False i = " case when " <> i <> " is not null then true else null end "

explodeRow' block  assoc  leaf (DelayedTB1 (Just tbd@(TB1 (i,tb)))) = "(true)"

explodeRow' block assoc leaf (LeftTB1 (Just tb) ) = explodeRow' block assoc leaf tb
explodeRow' block assoc leaf (ArrayTB1 [tb] ) = explodeRow' block assoc leaf tb
explodeRow' block assoc leaf (TB1 (m ,Compose (Labeled _ (KV tb)))) = block (T.intercalate assoc (fmap (explodeDelayed block assoc leaf .getCompose)  $ F.toList  tb  ))
explodeRow' block assoc leaf  (TB1 (m ,Compose (Unlabeled (KV tb)))) = block (T.intercalate assoc (fmap (explodeDelayed block assoc leaf .getCompose)  $ F.toList  tb  ))

explodeDelayed block assoc leaf (Labeled l (Attr k  _ ))
  | isKDelayed (keyType k) = leafDel (isArray (keyType k)) l
  | otherwise =  leaf (isArray (keyType k)) l
explodeDelayed block assoc leaf (Unlabeled (Attr k  _ )) = leaf (isArray (keyType k))  (keyValue k)

explodeDelayed block assoc leaf (Unlabeled (IT  n t )) =  explodeRow'  block assoc leaf t
explodeDelayed block assoc leaf (Labeled l (IT  _ tb  )) = l
explodeDelayed block assoc leaf (Labeled l (FKT i  _ tb  )) = case i of
             [] -> l
             i -> T.intercalate assoc (F.toList $ (explodeDelayed block assoc leaf . getCompose ) <$> i) <> assoc <> l
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

unTlabel (TB1 (m,kv) )  = TB1 . (m,) $ overLabel (\(KV kv) -> KV $ fmap (Compose . Identity .unlabel.getCompose ) $   kv) kv
unTlabel (LeftTB1 kv)  = LeftTB1 $ fmap unTlabel kv
unTlabel (ArrayTB1 kv)  = ArrayTB1 $ fmap unTlabel kv
unTlabel (DelayedTB1 kv)  = DelayedTB1 $ fmap unTlabel kv

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


unSOptional (LeftTB1 i) = i
unSOptional i = traceShow ("unSOptional No Pattern Match SOptional-" <> show i) (Just i)

unSDelayed (DelayedTB1 i) = i
unSDelayed i = traceShow ("unSDelayed No Pattern Match" <> show i) Nothing

unSSerial (SerialTB1 i) = i
unSSerial i = traceShow ("unSSerial No Pattern Match SSerial-" <> show i) Nothing

unRSOptional (LeftTB1 i) = join $ fmap unRSOptional i
unRSOptional i = traceShow ("unRSOptional No Pattern Match SOptional-" <> show i) Nothing

unRSOptional2 (LeftTB1 i) = join $ unRSOptional2 <$> i
unRSOptional2 i   = Just i

unRSOptional' (LeftTB1 i) = join $ unRSOptional' <$> i
unRSOptional' (SerialTB1 i )  = join $ unRSOptional' <$> i
unRSOptional' i   = Just i

_unTB1 (TB1 (m,i) ) =  i
_unTB1 (LeftTB1 (Just i )) = _unTB1 i
_unTB1 (DelayedTB1 (Just i )) = _unTB1 i
_unTB1 i =  errorWithStackTrace $ show i

instance P.Poset (FKey (KType Text))where
  compare  = (\i j -> case compare (i) (j) of
                      EQ -> P.EQ
                      LT -> P.LT
                      GT -> P.GT )

makeOpt (Key a  c d m n ty) = (Key a  c d m n (KOptional ty))


inlineName (KOptional i) = inlineName i
inlineName (KArray a ) = inlineName a
inlineName (InlineTable _ i) = i
inlineName (KEither _ i) = i

inlineFullName (KOptional i) = inlineFullName i
inlineFullName (KArray a ) = inlineFullName a
inlineFullName (InlineTable s i) = s <> "." <> i

isKEither (KOptional i ) = isKEither i
isKEither (KArray i ) = isKEither i
isKEither (KEither _ i) = True
isKEither _ = False

isInline (KOptional i ) = isInline i
isInline (KArray i ) = isInline i
isInline (InlineTable _ i) = True
isInline _ = False

relabeling :: (forall a . f a -> a ) -> (forall a . a -> p a ) -> TB f k a -> TB p k a
relabeling p l (Attr k i ) = (Attr k i)
relabeling p l (IT i tb ) = IT ((Compose.  l . relabeling p l . p . getCompose ) i) (relabelT p l tb)

relabelT :: (forall a . f a -> a ) -> (forall a . a -> p a ) -> TB3 f k a -> TB3 p k a
relabelT p l (TB1 (m ,Compose j)) =  (TB1  (m,Compose $ l (KV $ fmap (Compose.  l . relabeling p l . p . getCompose ) (_kvvalues $ p j))))


