{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor #-}
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
import Data.Bifunctor
import Data.Unique
import Data.Functor.Identity
import qualified Data.Vector as Vector
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
import GHC.Exts
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

isReflexive (FKT _  r _ _ ) = r
isReflexive _ = True

_unlb1 ( TB1  m i ) = fmap getCompose i

unlb1 ( TB1  m i ) = fmap getCompose (_kvvalues $ labelValue $ getCompose $ i)
unlb1 ( LeftTB1  (Just i ) ) = unlb1 i
unlb1 ( ArrayTB1  [i ] ) = unlb1 i


isSerial (KSerial _) = True
isSerial _ = False

isPrim (Primitive i) = True
isPrim i = False

isOptional (KOptional _) = True
isOptional _ = False

isArray (KArray _) = True
isArray (KOptional i) = isArray i
isArray _ = False



showableDef (KOptional i) = Just $ SOptional (showableDef i)
showableDef (KSerial i) = Just $ SSerial (showableDef i)
showableDef (KArray i ) = Nothing -- Just (SComposite Vector.empty)
showableDef i = Nothing

transformKey (KSerial i)  (KOptional j) (SSerial v)  | i == j = (SOptional v)
transformKey (KOptional i)  (KSerial j) (SOptional v)  | i == j = (SSerial v)
transformKey (KOptional j) l (SOptional v)
    | isJust v = transformKey j l (fromJust v)
    | otherwise = error "no transform optional nothing"
transformKey (KSerial j)  l (SSerial v)
    | isJust v = transformKey j l (fromJust v)
    | otherwise = error "no transform serial nothing"
-- transformKey (KOptional j)  l@(Primitive _ ) (SOptional v) | j == l  && isJust v = (\(Just i)-> i) v
transformKey l@(Primitive _)  (KOptional j ) v | j == l  = SOptional $ Just v
transformKey l@(Primitive _)  (KSerial j ) v | j == l  = SSerial $ Just v
transformKey ki kr v | ki == kr = v
transformKey ki kr  v = error  ("No key transform defined for : " <> show ki <> " " <> show kr <> " " <> show v )

description  = rawDescription

atTables f t = f t

renderShowable :: Showable -> String
renderShowable (SOptional i ) = maybe "" renderShowable i
renderShowable (SSerial i ) = maybe "" renderShowable i
renderShowable (SInterval i)  = showInterval i
renderShowable (SComposite i)  = unlines $ F.toList $ fmap renderShowable i
renderShowable i = shw i
   where
    shw (SText a) = T.unpack a
    shw (SNumeric a) = show a
    shw (SBoolean a) = show a
    shw (SDouble a) = show a
    shw (STimestamp a) = show a
    shw (SLineString a ) = show a
    shw (SBounding a ) = show a
    shw (SDate a) = show a
    shw (SDayTime a) = show a
    shw (SSerial a) = show a
    shw (SBinary _) = show "<Binary>"
    shw (SDelayed  i ) = maybe "<NotLoaded>" (\i -> "<Loaded| " <> shw i <> "|>") i
    shw (SPosition a) = show a
    shw (SOptional a) = show a
    shw (SInterval a) = showInterval a
    shw (SPInterval a) = show a
    shw (SComposite a) = intercalate "," $ F.toList (fmap shw a)

showInterval i | i == Interval.empty = show i
showInterval (Interval.Interval (ER.Finite i,j) (ER.Finite l,m) ) = ocl j <> renderShowable i <> "," <> renderShowable l <> ocr m
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

fullTableName = T.intercalate "_" . fmap (\k -> keyValue k <> (T.pack $ show $ hashUnique (keyFastUnique k))) . S.toList


getPrim i@(Primitive _ ) = textToPrim <$> i
getPrim (KOptional j) =  getPrim j
getPrim (KSerial j) =  getPrim j
getPrim (KArray j) =  getPrim j
getPrim (KInterval j) =  getPrim j

inner b l m = l <> b <> m

intersectPred p@(Primitive _ ) (KInterval i) j (SInterval l )  | p == i =  Interval.member j l
intersectPred p@(KInterval j ) (KInterval i) (SInterval k)  (SInterval l )   =  Interval.isSubsetOf k  l
intersectPred p@(KArray j ) (KArray i) (SComposite k)  (SComposite l )   =  S.fromList (F.toList k) `S.isSubsetOf` S.fromList  (F.toList l)
intersectPred p@(Primitive _ ) (KArray i) j (SComposite l )  | p == i =  Vector.elem j l
intersectPred p1@(Primitive _ ) p2@(Primitive _) j l   | p1 == p2 =  j ==  l
intersectPred p1 (KSerial p2 ) j (SSerial l)   | p1 == p2 =  maybe False (j ==) l
intersectPred p1 (KOptional p2 ) j (SOptional l)   | p1 == p2 =  maybe False (j ==) l
intersectPred p1@(KOptional i ) p2 (SOptional j) l  =  maybe False id $ fmap (\m -> intersectPred i p2 m l) j
intersectPred p1 p2 j l   = error ("intersectPred = " <> show p1 <> show p2 <>  show j <> show l)


pkOp (KSerial j ) i  (SSerial l) k  = maybe False id (pkOp i j k <$> l)
pkOp i (KSerial j ) k (SSerial l) = maybe False id (pkOp i j k <$> l)
pkOp (KInterval i) (KInterval j) (SInterval k) (SInterval l)| i == j  = not $ Interval.null $ Interval.intersection  k l
pkOp (KArray i) (KArray j) (SComposite k) (SComposite l) | i == j = not $ S.null $ S.intersection (S.fromList (F.toList k)) (S.fromList (F.toList  l ))
pkOp (Primitive i ) (Primitive j ) k l  | i == j = k == l
pkOp a b c d = errorWithStackTrace (show (a,b,c,d))

pkOpSet i l = L.all id $ zipWith (\(a,b) (c,d)-> pkOp (keyType a)  (keyType c) b d)  i l


intersectionOp (KOptional i) (KOptional j) = intersectionOp i j
intersectionOp i (KOptional j) = intersectionOp i j
intersectionOp (KOptional i) j = intersectionOp i j
intersectionOp (KInterval i) (KInterval j )  = inner " <@ "
intersectionOp (KArray i) (KArray j )  = inner " <@ "
intersectionOp (KInterval i) j
    | getPrim i == getPrim j =  inner " @> "
    | otherwise = error $ "wrong type intersectionOp " <> show i <> " /= " <> show j
intersectionOp i (KInterval j)
    | getPrim i == getPrim j = inner " <@ "
    | otherwise = error $ "wrong type intersectionOp " <> show i <> " /= " <> show j
intersectionOp (KArray i ) j
    | fmap textToPrim i == getPrim j = (\j i -> i <> " IN (select * from unnest("<> j <> ") ) ")
    | otherwise = error $ "wrong type intersectionOp {*} - * " <> show i <> " /= " <> show j
intersectionOp j (KArray i )
    | getPrim i == getPrim j = (\ i j  -> i <> " IN (select * from unnest("<> j <> ") ) ")
    | otherwise = error $ "wrong type intersectionOp * - {*} " <> show j <> " /= " <> show i
intersectionOp i j = inner " = "

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
    (TB1 _ (tbskv)) = isM
    isM :: TB3 Identity Key  Showable
    isM =  justError "cant diff befor update" $ diffUpdateAttr kv kold

diffUpdateAttr :: TB1 Showable -> TB1 Showable -> Maybe (TB1 Showable)
diffUpdateAttr  kv kold@(TB1 t _ ) =  fmap ((TB1  t ) . _tb . KV ) .  allMaybesMap  $ liftF2 (\i j -> if i == j then Nothing else Just i) (_kvvalues . unTB . _unTB1 . tableNonRefK  $ kv ) (_kvvalues . unTB . _unTB1 . tableNonRefK $ kold )


attrType :: Show a => TB Identity Key a -> KType Text
attrType (Attr i _)= keyType i
attrType (IT i _) = overComp attrType i
attrType i = errorWithStackTrace $ " no attr value instance " <> show i

attrValueName :: Show a => TB Identity Key a -> Text
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
        out <-  fmap head $ liftIO $ queryWith (f (fmap (const ()) $ TB1 (tableMeta t) $ _tb $  KV (M.fromList $ fmap (\i -> (S.singleton $ keyAttr i,Compose (Identity i))) pkList ))) conn (fromString  iquery ) (  kva)
        return $ mapTB1 (mapComp (\case{ (Attr k' v')-> maybe (Attr k' v') (runIdentity . getCompose )  $ fmap snd $ getCompose $ unTB $ findTB1 (overComp (\case{Attr nk nv ->nk == k'; i-> False} )) out; i-> i} ) ) krec
              else liftIO $ execute conn (fromString $ traceShowId $ T.unpack $ "INSERT INTO " <> rawFullName t <>" ( " <> T.intercalate "," (fmap attrValueName kva) <> ") VALUES (" <> T.intercalate "," (fmap (const "?") kva) <> ")"   )  kva >> return krec
  where pkList :: [ TB Identity Key Showable]
        pkList =   L.filter (isSerial . attrType ) . fmap (runIdentity. getCompose) $ (F.toList $ _kvvalues $ unTB $ tbPK $ tableNonRefK krec )
        kva = L.filter (not . isSerial . attrType ) $ fmap (runIdentity . getCompose) $ F.toList (_kvvalues $ unTB k)
        (TB1 _ k ) = tableNonRefK krec



fakeKey n t = Key n Nothing (unsafePerformIO newUnique) t

unSComposite (SComposite i) = i
unSComposite i = errorWithStackTrace ("unSComposite " <> show i)



isEmptyShowable (SOptional Nothing ) = True
isEmptyShowable (SSerial Nothing ) = True
isEmptyShowable i = False



dropTable r= "DROP TABLE "<> rawFullName r

rawFullName = showTable

createTable r@(Raw sch _ _ _ tbl _ pk _ fk attr) = "CREATE TABLE " <> rawFullName r  <> "\n(\n\t" <> T.intercalate ",\n\t" commands <> "\n)"
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


keyOptional (k,v) = (kOptional k ,SOptional $ Just v)

unKeyOptional (k  ,(SOptional v) ) = fmap (unKOptional k,) v

kOptional (Key a  c d e) = Key a  c d (KOptional e)
kDelayed (Key a  c d e) = Key a  c d (KDelayed e)

unKOptional ((Key a  c d (KOptional e))) = (Key a  c d e )
unKOptional i = errorWithStackTrace ("unKOptional" <> show i)

unKDelayed ((Key a  c d (KDelayed e))) = (Key a  c d e )
unKDelayed i = errorWithStackTrace ("unKDelayed" <> show i)

unKArray (Key a  c d (KArray e)) = Key a  c d e
unKArray (Key a  c d (KOptional (KArray e) )) = Key a  c d e



unIntercalate :: ( Char -> Bool) -> String -> [String]
unIntercalate pred s                 =  case dropWhile pred s of
                                "" -> []
                                s' -> w : unIntercalate pred s''
                                      where (w, s'') =
                                             break pred s'

data Tag = TAttr | TPK

allKVRec :: TB1 Showable -> [Showable]
allKVRec (LeftTB1 i) = maybe mempty allKVRec i
allKVRec (ArrayTB1 i) = mconcat $ allKVRec <$> i
allKVRec  t@(TB1 m e)=  concat $  F.toList (go . unTB <$> (_kvvalues $ unTB $ eitherDescPK t))
  where
        go  (FKT _ _ _ tb) =  allKVRec  tb
        go  (TBEither _ _  tbr) =  maybe [] id $ go . unTB <$>  tbr
        go  (IT  _ tb) = allKVRec tb
        go  (Attr _ a) = [a]


tableToKV r =   do
   (S.toList (rawPK r)) <> (maybeToList (rawDescription r))  <>(S.toList (rawAttrs r))


preLabelTable :: Text -> Table ->  (TB3 (Labeled Text)  Key () )
preLabelTable t i =
   let v = fmap (\k -> (S.singleton k,Compose $ Labeled ( "(" <> t <> ")." <> keyValue k ) (Attr k () )) ) (tableToKV i)
   in (TB1 (tableMeta i) $ Compose $ Labeled t $KV $ M.fromList $ v )


labelTable :: Table -> State ((Int, Map Int Table), (Int, Map Int Key)) (Labeled Text Table,TB3 (Labeled Text)  Key  () )
labelTable i = do
   t <- tname i
   name <- Tra.traverse (\k-> (S.singleton k,) <$> kname t k ) (tableToKV i)
   return (t,TB1 (tableMeta i) $ Compose $ Labeled (label t) $ KV $ M.fromList $ fmap Compose <$> name)

expandTable ::  TB3  (Labeled Text) Key  () -> Text
expandTable tb@(TB1 meta (Compose (Labeled t ((KV i)))  ))  =
   let query = "(SELECT " <>  T.intercalate "," (aliasKeys  . getCompose <$> name) <> " FROM " <> aliasTable <> ") as " <> t
       name =  tableAttr tb
       aliasTable = kvMetaFullName meta  <> " as " <> t
       aliasKeys (Labeled  a (Attr (Key n   _ _ _) _ ))  = t <> "." <> n <> " as " <> a
   in query
expandTable tb = errorWithStackTrace (show tb)


-- lb1 = TB1 . (fmap Compose)

isPairReflexive (Primitive i ) (KInterval (Primitive j)) | i == j = False
isPairReflexive (Primitive j) (KArray (Primitive i) )  | i == j = False
isPairReflexive (KInterval i) (KInterval j)  | i == j = False
isPairReflexive (Primitive i ) (Primitive j) | i == j = True
isPairReflexive (KOptional i ) j = isPairReflexive i j
-- isPairReflexive i (KOptional j) = isPairReflexive i j
isPairReflexive i (KSerial j) = isPairReflexive i j
isPairReflexive (KArray i )   (KArray j) | i == j = False
isPairReflexive (KArray i )   j = True
isPairReflexive i j = error $ "isPairReflexive " <> show i <> " - "<> show  j

isPathReflexive (FKJoinTable _ ks _)
  = all id $ fmap (\(i,j)-> isPairReflexive (textToPrim <$> keyType i ) (textToPrim <$> keyType j)) ks
isPathReflexive (FKInlineTable _)= True
isPathReflexive (FKEitherField _ _)= False

isPathEither (FKJoinTable _ ks _) = False
isPathEither (FKInlineTable _)= False
isPathEither (FKEitherField _ _)= True


intersectionOpK i j = intersectionOp (keyType i ) (keyType j)

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
  return ( tb , selectQuery tb ) -- "SELECT " <> explodeRow tb <>  (" FROM " <> q ) <> js)

kattrl = kattrli .  labelValue . getCompose
kattrli (Attr i _ ) = [i]
kattrli (FKT i _ _ _ ) =  (L.concat $ kattrl  <$> i)
kattrli (IT i  _ ) =  kattrl i

-- keyAttr :: Show b  => TB Identity b a -> b
keyAttr (Attr i _ ) = i
keyAttr i = errorWithStackTrace $ "cant find keyattr " <> (show i)


selectQuery t = "SELECT " <> explodeRow t <> " FROM " <> expandTable t <> expandQuery False  t

expandQuery left t@(TB1 meta m)
    =  foldr1 mappend (expandJoin left .getCompose <$> F.toList (_kvvalues $ labelValue $ getCompose $ m))


expandJoin :: Bool -> Labeled Text (TB (Labeled Text) Key ()) -> Text
expandJoin left (Unlabeled (IT i (LeftTB1 (Just tb) )))
    = expandJoin True $ Unlabeled (IT i tb)
expandJoin left (Labeled l (IT i (LeftTB1 (Just tb) )))
    = expandJoin True $ Labeled l (IT i tb)
expandJoin left (Labeled l (IT i (ArrayTB1 [tb] )))
    = jt <> " JOIN LATERAL (SELECT array_agg(" <> explodeRow  tb  <> "  order by arrrow ) as " <> l <> " FROM  (SELECT * FROM (SELECT *,row_number() over () as arrrow FROM UNNEST(" <> tname  <> ") as arr) as arr ) "<> label tas <> expandQuery left tb <> " )  as " <>  label tas <> " ON true"
        where
          (TB1 _ (Compose tas )) = tb
          tname = label $ getCompose i
          jt = if left then " LEFT" else ""
expandJoin left (Labeled l (IT i tb)) = expandQuery left tb
expandJoin left (Unlabeled  (IT _ tb )) = expandQuery left tb
expandJoin left (Labeled _ (Attr _ _ )) = ""
expandJoin left (Unlabeled  (Attr _ _ )) = ""
expandJoin left (Unlabeled (TBEither l kj j )) = foldr1 mappend (expandJoin left .getCompose <$>  kj )
expandJoin left (Unlabeled (FKT i refl rel (LeftTB1 (Just tb)))) = expandJoin True (Unlabeled (FKT i refl rel tb))
expandJoin left (Labeled l (FKT i refl rel (LeftTB1 (Just tb)))) = expandJoin True (Labeled l (FKT i refl rel tb))
expandJoin left (Labeled l (FKT i refl ks (ArrayTB1 [ tb])))
    = jt <> " JOIN LATERAL (SELECT " <> "array_agg(" <> explodeRow  tb <> " order by arrrow) as " <> l <> " FROM ( SELECT * FROM (SELECT *,row_number() over () as arrrow FROM UNNEST(" <> label (head (look (fst <$> ks) ( fmap getCompose $ concat $ fmap nonRef i ) ))  <> ") as arr) as z1 "  <> jt  <> " JOIN "<> expandTable tb   <> " ON " <>  label (head (look (snd <$> ks) ((fmap getCompose $ F.toList   (tableAttr tb) )) )) <> " = arr ) as z1 " <> expandQuery left tb  <>   "  ) as " <>  label tas  <> " ON true "
      where
          (TB1 _ (Compose tas )) = tb
          look ki i = justError ("missing FK on " <> show (ki,ks ,keyAttr . labelValue <$> i )  ) $ allMaybes $ fmap (\j-> L.find (\v -> keyAttr (labelValue v) == j) i  ) ki
          jt = if left then " LEFT" else ""
expandJoin left (Unlabeled (FKT i refl rel tb))
    =  jt <> " JOIN " <> expandTable tb <> " ON " <> joinOnPredicate rel (fmap getCompose $ concat $ fmap nonRef  i) (fmap getCompose $ F.toList   (tableAttr tb) ) <> expandQuery left tb
    where
          jt = if left then " LEFT" else ""
expandJoin left (Labeled l (FKT i refl rel tb))
    = " JOIN " <> expandTable tb <> " ON " <> joinOnPredicate rel (fmap getCompose $ concat $ fmap nonRef  i) (fmap getCompose $ tableAttr tb)

expandJoin left i = errorWithStackTrace (show i)

joinOnPredicate ks m n =  T.intercalate " AND " . fmap (\(l,r)->  intersectionOpK (keyAttr . labelValue $ l) (keyAttr . labelValue $ r) (label l)  (label r )) $  fkm m n
    where fkm m n = zip (look (fst <$> ks) m) (look (snd <$> ks) n)
          look ki i = justError ("missing FK on " <> show (ki,ks ,keyAttr . labelValue <$> i )  ) $ allMaybes $ fmap (\j-> L.find (\v -> keyAttr (labelValue v) == j) i  ) ki



recursePath'
  :: Bool
     -> [(Set Key, Labeled Text (TB (Labeled Text) Key ()))]
     -> Map Text Table
     -> Path (Set (FKey (KType Text))) SqlOperation
     -> State
          ((Int, Map Int Table), (Int, Map Int Key))
          (Compose (Labeled Text) (TB (Labeled Text)) Key ())
recursePath' isLeft ksbn invSchema (Path _ jo@(FKEitherField o l) _) = do
   let findAttr =(\i -> Compose . justError ("cant find " ). fmap snd . L.find ((== S.singleton i) . fst  )$ ksbn )
   return $ (Compose $ Unlabeled $  TBEither  o (findAttr <$> l )  Nothing)

recursePath' isLeft ksbn invSchema (Path ifk jo@(FKInlineTable t ) e)
    | isArrayRel ifk  {-&& not (isArrayRel e )-}=   do
          tas <- tname nextT
          let knas = Key (rawName nextT) Nothing (unsafePerformIO newUnique) (Primitive "integer" )
          kas <- kname tas  knas
          let
              tname = head $ fmap (\i -> label . justError ("cant find " ). fmap snd . L.find ((== S.singleton i) . fst )$ ksbn ) (S.toList ifk )
              ksn = preLabelTable ( label tas )  nextT
          tb <- fun ksn
          let
              ref = (\i -> Compose . justError ("cant find " ). fmap snd . L.find ((== S.singleton i) . fst )$ ksbn ) $ head (S.toList ifk )
          return $  Compose $ Labeled (label $ kas) $ IT ref   (mapOpt $ mapArray tb )
    | otherwise = do
          let tname = head $ fmap (\i -> label . justError ("cant find " ). fmap snd . L.find ((== S.singleton i) . fst )$ ksbn ) (S.toList ifk )
              ksn = preLabelTable tname   nextT
          tb <-fun ksn
          let
            ref = (\i -> Compose . justError ("cant find " ). fmap snd . L.find ((== S.singleton i) . fst )$ ksbn ) $ head (S.toList ifk )
          return $ ( Compose $ Unlabeled $ IT  ref  (mapOpt tb)   )
    where
        nextLeft =  isLeft || isLeftRel ifk
        mapArray i =  if isArrayRel ifk then ArrayTB1 [i] else i
        mapOpt i = if isLeftRel ifk then  LeftTB1 $ Just  i else i
        nextT = justError ("recursepath lookIT "  <> show t <> " " <> show invSchema) (M.lookup t invSchema)
        fun =  recurseTB invSchema nextT nextLeft

recursePath' isLeft ksbn invSchema (Path ifk jo@(FKJoinTable w ks tn) e)
    | isArrayRel ifk && not (isArrayRel e) =   do
          (t,ksn) <- labelTable nextT
          tb <-fun ksn
          tas <- tname nextT
          let knas = (Key (rawName nextT) Nothing (unsafePerformIO newUnique) (Primitive "integer" ))
          kas <- kname tas  knas
          return $ Compose $ Labeled (label $ kas) (FKT (fmap (\i -> Compose . justError ("cant find " ). fmap snd . L.find ((== S.singleton i) . fst )$ ksbn ) (S.toList ifk )) (isPathReflexive jo ) ks  (mapOpt $ mapArray tb  ))

    | otherwise = do
          (t,ksn) <- labelTable nextT
          let pksn = getCompose <$> F.toList (_kvvalues $ labelValue $ getCompose $ tbPK ksn)
          tb <-fun ksn
          return $ Compose $ Unlabeled $ FKT (fmap (\i -> Compose . justError ("cant find " ). fmap snd . L.find ((== S.singleton i) . fst )$ ksbn ) (S.toList ifk )) (isPathReflexive jo ) ks (mapOpt tb)
  where
        nextT = (\(Just i)-> i) (M.lookup tn (invSchema))
        nextLeft = any (isKOptional.keyType) (S.toList ifk) || isLeft
        mapArray i =  if isArrayRel ifk then ArrayTB1 [i] else i
        mapOpt i = if isLeftRel  ifk then  LeftTB1 $ Just  i else i
        fun =   recurseTB invSchema nextT nextLeft

isLeftRel ifk = any (isKOptional.keyType) (S.toList ifk)
isArrayRel ifk = any (isArray.keyType) (S.toList ifk)

pathRel (Path _ rel _ ) = rel
pathRelRef (Path ifk _ _ ) = ifk
pathRelStore (Path _ _ ifk ) = ifk

eitherDescPK :: (Functor f,Ord k) =>TB3 f k a -> Compose f (KV  (Compose f (TB f ))) k a
eitherDescPK i@(TB1 kv  _  )
  | not ( S.null ( _kvdesc kv) ) =  tbDesc i
  | otherwise = tbPK i


tbDesc :: (Functor f,Ord k)=>TB3 f k a -> Compose f (KV  (Compose f (TB f ))) k a
tbDesc  =  tbFilter  (\kv k -> (S.isSubsetOf k (_kvdesc kv ) ))

tbPK :: (Functor f,Ord k)=>TB3 f k a -> Compose f (KV  (Compose f (TB f ))) k a
tbPK = tbFilter  (\kv k -> (S.isSubsetOf k (_kvpk kv ) ))

tbAttr :: (Functor f,Ord k) =>  TB3 f k a ->  Compose f (KV  (Compose f (TB f ))) k a
tbAttr  =  tbFilter  (\kv k -> not (S.isSubsetOf k (_kvpk kv <> _kvdesc kv ) ))

tbFilter :: (Functor f,Ord k) =>  ( KVMetadata k -> Set k -> Bool) -> TB3 f k a ->  Compose f (KV  (Compose f (TB f ))) k a
tbFilter pred (TB1 kv item) =  mapComp (\(KV item)->  KV $ M.filterWithKey (\k _ -> pred kv k ) $ item) item

recurseTB :: Map Text Table -> Table -> Bool -> TB3 (Labeled Text) Key () -> StateT ((Int, Map Int Table), (Int, Map Int Key)) Identity (TB3 (Labeled Text) Key ())
recurseTB invSchema  nextT nextLeft ksn@(TB1 m kv ) =  (TB1 m) <$>
    (\kv -> case kv of
      (Compose (Labeled l kv )) -> do
         i <- fun kv
         return (Compose (Labeled l i));
      (Compose (Unlabeled kv)) -> do
         i<- fun kv
         return (Compose (Unlabeled i))) kv

    where fun =  (\kv -> do
                  let
                      items = _kvvalues kv
                      fkSet = traceShow (_kvname m) $ S.unions $ fmap pathRelRef $ filter ( isPathReflexive . pathRel) $ S.toList (rawFKS nextT)
                      eitherSet = S.unions $ fmap pathRelRef $ filter ( isPathEither . pathRel) $  S.toList (rawFKS nextT)
                      nonFKAttrs :: [(S.Set Key,TBLabel  ())]
                      nonFKAttrs =  M.toList $  M.filterWithKey (\i a -> not $ S.isSubsetOf i fkSet) items
                      itemSet :: S.Set Key
                      itemSet = S.unions (M.keys items)
                  pt <- mapM (\fk -> fmap (((pathRelRef fk,))) . recursePath' nextLeft (M.toList $  fmap getCompose items ) invSchema $ fk ) (filter (not. isPathEither . pathRel) (F.toList $ rawFKS nextT ))
                  let
                      nonEitherAttrs = filter (\(k,i) -> not $ S.isSubsetOf k eitherSet) (nonFKAttrs <> pt )
                  pt2 <- mapM (\fk -> fmap (((pathRelRef fk,))) .recursePath' nextLeft (fmap (fmap getCompose) $ nonFKAttrs<> pt ) invSchema$ fk ) (filter ( isPathEither . pathRel) $ F.toList $ rawFKS nextT )
                  return (   KV $ M.fromList $ (\i->traceShow (fmap fst i) i ) $ nonEitherAttrs <> pt2) )



unTB = runIdentity . getCompose
_tb = Compose . Identity

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

aliasKeys (t,Labeled  a (Attr (Key n   _ _ _) _ ))  = label t <> "." <> n <> " as " <> a


aliasTable (Labeled t r) = showTable r <> " as " <> t
kname :: Labeled Text Table -> Key -> QueryRef (Labeled Text (TB (Labeled Text) Key () ))
kname t i = do
  n <- mkKey i
  return $ (Labeled ("k" <> (T.pack $  show $ fst n)) (Attr i ()) )




tname :: Table -> QueryRef (Labeled Text Table)
tname i = do
  n <- mkTable i
  return $ Labeled ("t" <> (T.pack $  show n)) i


explodeLabel :: Labeled Text (TB (Labeled Text) Key () ) -> Text
explodeLabel (Labeled l (Attr k  _ ))
  | isKDelayed (keyType k) = "case when " <> l <> " is not null then true else null end"
  | otherwise =  l
explodeLabel (Unlabeled (TBEither _  l  _ )) = "ROW(" <> T.intercalate "," (explodeLabel.getCompose<$>  l) <> ")"
explodeLabel (Unlabeled (IT  n t )) =  explodeRow  t
explodeLabel (Labeled l (IT  _ _  )) =  l
explodeLabel (Labeled l (FKT i _ _ _ )) = T.intercalate "," (( F.toList $ (explodeLabel. getCompose ) <$> i)) <> "," <> l
explodeLabel (Unlabeled (FKT i refl rel t )) = T.intercalate "," (( F.toList $ (explodeLabel.getCompose) <$> i)) <> "," <> explodeRow t

explodeRow (LeftTB1 (Just tb) ) = explodeRow tb
explodeRow (ArrayTB1 [tb] ) = explodeRow tb
explodeRow (TB1 m (Compose (Labeled _ (KV tb)))) = "ROW(" <> (T.intercalate ","  (fmap (explodeLabel.getCompose)  $ F.toList  tb  )) <> " )"
explodeRow (TB1 m (Compose (Unlabeled (KV tb)))) = "ROW(" <> (T.intercalate ","  (fmap (explodeLabel.getCompose)  $ F.toList  tb  )) <> " )"

unTlabel (TB1 m kv )  = TB1 m $ overLabel (\(KV kv) -> KV $ fmap (Compose . Identity .unlabel.getCompose ) $   kv) kv
unTlabel (LeftTB1 kv)  = LeftTB1 $ fmap unTlabel kv
unTlabel (ArrayTB1 kv)  = ArrayTB1 $ fmap unTlabel kv

unlabel (Labeled l (IT tn t) ) = (IT (relabel tn) (unTlabel t ))
unlabel (Unlabeled (IT tn t) ) = (IT (relabel tn) (unTlabel t ))
unlabel (Unlabeled (TBEither  n l  b ) ) = TBEither n (relabel <$> l)   (fmap relabel b)
unlabel (Labeled l (FKT i refl fkrel t) ) = (FKT (fmap relabel i) refl fkrel (unTlabel  t ))
unlabel (Unlabeled (FKT i refl fkrel t) ) = (FKT (fmap relabel i) refl fkrel (unTlabel t))
unlabel (Labeled l (Attr k i )) = Attr k i

relabel = Compose . Identity . unlabel.getCompose

-- alterComp :: (f k a -> g d b ) -> Compose (Labeled Text) f  k a -> Compose (f Identityg d b
overLabel f = Compose .  Identity . f . labelValue  .getCompose




-- interval' i j = Interval.interval (ER.Finite i ,True) (ER.Finite j , True)
inf' = (\(ER.Finite i) -> i) . Interval.lowerBound
sup' = (\(ER.Finite i) -> i) . Interval.upperBound


unSOptional (SOptional i) = i
unSOptional i = traceShow ("unSOptional No Pattern Match SOptional-" <> show i) Nothing

unSDelayed (SDelayed i) = i
unSDelayed i = traceShow ("unSDelayed No Pattern Match" <> show i) Nothing

unSSerial (SSerial i) = i
unSSerial i = traceShow ("unSSerial No Pattern Match SSerial-" <> show i) Nothing

unRSOptional (SOptional i) = join $ fmap unRSOptional i
unRSOptional i = traceShow ("unRSOptional No Pattern Match SOptional-" <> show i) Nothing

unRSOptional2 (SOptional i) = join $ unRSOptional' <$> i
unRSOptional2 i   = Just i

unRSOptional' (SOptional i) = join $ unRSOptional' <$> i
unRSOptional' (SSerial i )  = join $ unRSOptional' <$>i
unRSOptional' i   = Just i

_unTB1 (TB1 m i ) =  i
_unTB1 (LeftTB1 (Just i )) = _unTB1 i
_unTB1 i =  errorWithStackTrace $ show i


allMaybes i | F.all (const False) i  = Nothing
allMaybes i = if F.all isJust i
        then Just $ fmap (justError "wrong invariant allMaybes") i
        else Nothing

makeOpt (Key a  c d ty) = (Key a  c d (KOptional ty))

zipWithTF g t f = snd (mapAccumL map_one (F.toList f) t)
    where map_one (x:xs) y = (xs, g y x)


inlineName (KOptional i) = inlineName i
inlineName (KArray a ) = inlineName a
inlineName (InlineTable _ i) = i

inlineFullName (KOptional i) = inlineFullName i
inlineFullName (KArray a ) = inlineFullName a
inlineFullName (InlineTable s i) = s <> "." <> i

isInline (KOptional i ) = isInline i
isInline (KArray i ) = isInline i
isInline (InlineTable _ i) = True
isInline _ = False


