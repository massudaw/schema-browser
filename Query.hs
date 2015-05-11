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

module Query where

import Warshal
import Control.Lens.TH
import Data.Tuple
import Data.Functor.Apply
import Data.Functor.Compose
import Data.Functor.Identity
import Data.Typeable
import Data.Distributive
import Data.Vector(Vector)
import qualified Data.Vector as Vector
import Data.Functor.Classes
import qualified Data.Foldable as F
import Data.Foldable (Foldable)
import Data.Traversable (mapAccumL)
import qualified Data.Traversable as Tra
import Data.Char ( isAlpha )
import Data.Maybe
import qualified Data.Interval as Interval
import Data.Monoid hiding (Product)
import Data.Functor.Product
import Data.Bifunctor

import qualified Data.Text.Lazy as T
import qualified Data.ByteString as BS
import qualified Data.ExtendedReal as ER

import GHC.Int

import Data.Traversable(Traversable)
import Database.PostgreSQL.Simple
import Database.PostgreSQL.Simple.Time
import Database.PostgreSQL.Simple.ToField

import Data.Time
import Control.Monad
import GHC.Exts
import System.IO.Unsafe
import Data.Tuple
import Control.Applicative
import Data.List ( nubBy,nub, sort,intercalate,sortBy,isInfixOf )
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Map (Map)
import Data.Set (Set)
import Control.Monad.State
import Control.Monad.State.Class
import System.Environment ( getArgs )
import Text.Parsec hiding(label,State)
import Text.Parsec.String
import Text.Printf ( printf )
import Data.Text.Lazy(Text)
import Debug.Trace
import GHC.Stack

import Data.Unique
import Types


textToPrim "character varying" = PText
textToPrim "name" = PText
textToPrim "varchar" = PText
textToPrim "text" = PText
textToPrim "pdf" = PMime "application/pdf"
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
textToPrim "interval" = PInterval
textToPrim "date" = PDate
textToPrim "POINT" = PPosition
textToPrim "LINESTRING" = PLineString
textToPrim "box3d" = PBounding
textToPrim i = error $ "no case for type " <> T.unpack i

isReflexive (FKT _  r _ _ ) = r
isReflexive (AKT _  r _ _ ) = r
isReflexive _ = True

_unlb1 ( TB1  i ) = fmap getCompose i

unlb1 ( TB1  i ) = fmap getCompose i


isSerial (KSerial _) = True
isSerial _ = False
isPrim (Primitive i) = True
isPrim i = False
isOptional (KOptional _) = True
isOptional _ = False
isArray (KArray _) = True
isArray (KOptional i) = isArray i
isArray _ = False


attrInputSet (Metric k ) = [k]
attrInputSet (Operator l k n r ) = concat $ [attrInputSet l, attrInputSet r]
attrInputSet (Fun args k ) = concat $ attrInputSet <$> args
attrInputSet (Agg (Aggregate args k) ) = concat $ attrInputSet <$> args

attrName (Metric k ) = maybe (keyValue k ) id (keyAlias k)
attrName (Operator l k n r ) = attrName l  <> n <>  attrName r
attrName (Fun args n ) =  T.concat (fmap attrName args) <>  n
attrName (Agg (Aggregate args n)) = T.concat (fmap attrName args) <>  n

renderAttribute :: KAttribute -> Text
renderAttribute (Metric s ) = keyValue s
renderAttribute (Operator l k n r ) = renderAttribute l <>  " " <> k <> " " <> renderAttribute r
-- renderAttribute (Prod m1 m2 ) =  renderAttribute m1 <> "*" <> renderAttribute m2
renderAttribute (Fun arg n ) = n <> "(" <> T.intercalate "," (renderAttribute <$> arg) <>")"
renderAttribute a@(Agg m2  ) = renderAggr renderAttribute m2 <> " as " <> attrName a
  where renderAggr f (Aggregate l s )  = s  <> "(" <> T.intercalate ","  (fmap f l)  <> ")"


showableDef (KOptional i) = Just $ SOptional (showableDef i)
showableDef (KSerial i) = Just $ SSerial (showableDef i)
showableDef (KArray i ) = Just (SComposite Vector.empty)
showableDef i = Nothing

transformKey (KSerial i)  (KOptional j) (SSerial v)  | i == j = (SOptional v)
transformKey (KOptional i)  (KSerial j) (SOptional v)  | i == j = (SSerial v)
transformKey (KOptional j)  l@(Primitive _) (SOptional v)
    | isJust v = transformKey j l (fromJust v)
    | otherwise = error "no transform optional nothing"
transformKey (KSerial j)  l@(Primitive _) (SSerial v)
    | isJust v = transformKey j l (fromJust v)
    | otherwise = error "no transform serial nothing"
-- transformKey (KOptional j)  l@(Primitive _ ) (SOptional v) | j == l  && isJust v = (\(Just i)-> i) v
transformKey l@(Primitive _)  (KOptional j ) v | j == l  = SOptional $ Just v
transformKey l@(Primitive _)  (KSerial j ) v | j == l  = SSerial $ Just v
transformKey ki kr v | ki == kr = v
transformKey ki kr  v = error  ("No key transform defined for : " <> show ki <> " " <> show kr <> " " <> show v )


-- Pretty Print Filter
renderFilter (table ,name,Category i) = tableName table <> "." <> keyValue name <> " IN( " <>  T.intercalate "," (fmap (\s -> "'" <> T.pack (renderShowable $ head (_pkKey s)) <> "'" ) $ S.toList i) <> ")"
renderFilter (table ,name,And i) =  T.intercalate " AND "  (fmap (renderFilter . (table ,name,)) i)
-- renderFilter (table ,name,RangeFilter i) =  tableName table <> "." <> keyValue name <> " BETWEEN " <> T.intercalate " AND "  (fmap (\s -> "'" <> T.pack (renderShowable$ head (_pkKey s)) <> "'" ) [Interval.inf i,Interval.sup i])

description (Raw _ _ _ desc _ _ ) = desc

atTables f t@(Raw _ _ _ _ _ _ ) = f t
atTables f (Filtered _ t ) = atTables f t
atTables f (Project _ t ) = atTables f t
atTables f (Reduce _ _ t ) = atTables f t
atTables f (Limit t _) = atTables f t
atTables f (Base _ p ) = from p
  where from (From t _) = atTables f t
        from (Join ty t _ p) = atTables f t <> from p
        from (SplitJoin _ t  _ p) = atTables f t <> from p

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
  -- shw (SSerial a) = maybe " " ((" "<>) . shw) a
  shw (SSerial a) = show a
  shw (SBinary a) = show "<Binary>"
  shw (SPosition a) = show a
  shw (SOptional a) = show a
  -- shw (SOptional a) = maybe "  " (("  "<>). shw) a
  shw (SInterval a) = showInterval a
  shw (SPInterval a) = show a
  shw (SComposite a) = intercalate "," $ F.toList (fmap shw a)

showInterval i | i == Interval.empty = show i
showInterval (Interval.Interval (ER.Finite i,j) (ER.Finite l,m) ) = ocl j <> renderShowable i <> "," <> renderShowable l <> ocr m
    where
      ocl j = if j then "[" else "("
      ocr j = if j then "]" else ")"



normalizing = atBase (\(Raw _ _ t _ _ _ )-> t)



alterTableName f = atBase (\(Raw s t p i j l )-> (Raw s (f t)  p i j l))
tablesName = atBase (\(Raw _ t _ _ _ _ )-> S.singleton t)


renderAliasedKey (PathRoot  ,v)  a = renderNamespacedKeySet v <> " AS " <> a
  where renderNamespacedKeySet (t,k) = tableName t <> "." <> keyValue k
renderAliasedKey (v ,(t,k)) a = tableName t <> "." <> keyValue k <> " AS " <> a


isKOptional (KOptional i) = True
isKOptional (KSerial i) = isKOptional i
isKOptional (KInterval i) = isKOptional i
isKOptional (Primitive _) = False
isKOptional (KArray i)  = isKOptional i

-- transform a multiple intersecting join in independent ones
splitJoins j@(From p r ) = j
splitJoins j@(Join ty b r p) = case hasSplit of
                                     True -> Join ty b r (splitJoins p)
                                     False ->  SplitJoin ty b   mapK (splitJoins p)
      where
        mapK :: [(Set Key,[(Table,Set (Key, Key))])]
        mapK = M.toList $ M.fromListWith (<>) $ fmap (fmap pure) $ concat $ concat $ fmap snd $ M.toList mapkPre
        mapkPre :: Map (Set Key) ([[(Set Key,(Table,Set (Key,Key)))]])
        mapkPre = fmap (fmap (\(i,j)-> fmap (i,) j) . M.toList . M.fromListWith (<>)) groupJoins
        groupJoins ::  Map (Set Key) [(Set Key,[(Table,Set (Key,Key))])]
        groupJoins =  M.fromListWith (<>) ((\f@(t,a)-> ( S.map snd a , [( S.map fst a , [( t , a )] )] )) <$> S.toList r)
        -- hasSplit ::  Map (Set Key) [(Set Key,[(Table,Set (Key,Key))])]
        hasSplit =   all (\i -> length (snd i) <2) $ M.toList $  M.fromListWith (<>) ((\f@(t,a)-> (  ( S.map snd a , [( t , a )] ) )) <$> S.toList r)
splitJoins j = j


aliasJoin b@(Base k1 p) = zipWith (\i (j,l)-> (j,(i,l))) (T.pack . ("v" <> ). show <$> [0..]) aliasMap
  where
    aliasMap =  fmap (\i -> ( (\(p,(t,k))-> (p,k))i,i)) attrs
    attrs = S.toList $ allAttrs' b

fullTableName = T.intercalate "_" . fmap (\k -> keyValue k <> (T.pack $ show $ hashUnique (keyFastUnique k))) . S.toList


getPrim i@(Primitive _ ) = textToPrim <$> i
getPrim (KOptional j) =  getPrim j
getPrim (KSerial j) =  getPrim j
getPrim (KArray j) =  getPrim j
getPrim (KInterval j) =  getPrim j

inner b l m = l <> b <> m

intersectPred p@(Primitive _ ) (KInterval i) j (SInterval l )  | p == i =  Interval.member j l
intersectPred p@(Primitive _ ) (KArray i) j (SComposite l )  | p == i =  Vector.elem j l
intersectPred p1@(Primitive _ ) p2@(Primitive _) j l   | p1 == p2 =  j ==  l
intersectPred p1@(KOptional i ) p2 (SOptional j) l  =  maybe False id $ fmap (\m -> intersectPred i p2 m l) j
intersectPred p1 p2 j l   = error ("intersectPred = " <> show p1 <> show p2 <>  show j <> show l)



intersectionOp (KOptional i) (KOptional j) = intersectionOp i j
intersectionOp i (KOptional j) = intersectionOp i j
intersectionOp (KOptional i) j = intersectionOp i j
intersectionOp (KInterval i) (KInterval j )  = inner " = "
intersectionOp (KArray i) (KArray j )  = inner " = "
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

-- Generate a sql query from the AST
showTable :: Table -> Text
showTable (Filtered f t) = filterTable (fmap (\(k,f) -> (t,k,f) ) f ) t
  where
      filterTable [] b =  showTable b
      filterTable filters b =  "(SELECT *  FROM " <> showTable b <>  " WHERE " <> T.intercalate " AND " (fmap renderFilter filters)  <> ") as " <> ( tableName b )
showTable (Raw s t _ _  _ _) = fst s <> "." <> t
showTable b@(Base k1 p) = " from (SELECT " <> T.intercalate ","  ((\(a,p)-> renderAliasedKey p a) . snd <$> attrs )  <> joinQuerySet p <>") as " <> tableName b
  where
    attrs = aliasJoin b
    joinQuerySet (From b _) =  " FROM " <>  showTable b
    joinQuerySet (SplitJoin t b  r p) =  F.foldl' joinType (joinQuerySet p) r
        where joinType  l ir@(_,r)
                | any (isKOptional . keyType) (concat $ fmap fst . S.toList .  snd <$> r ) = l <> " LEFT JOIN " <> joinPredicate2 b ir
                | otherwise =  l <> " JOIN " <> joinPredicate2 b ir
              joinPredicate2 b (i,r)  = showTable b <> " AS " <> tempName  <> " ON " <> T.intercalate " AND " (fmap (\(t,fs) -> T.intercalate " AND " $ fmap (\f-> intersectionOp ( keyType (fst f)) (keyType (snd f)) (tableName t <> "." <> keyValue (fst f)) (tempName <> "." <> keyValue (snd f))) $ S.toList fs )  r )
                where tempName = tableName b <> fullTableName  i
    joinQuerySet (Join ty b  r p)  = joinType (joinQuerySet p)  r
        where
            joinType  l ir
                | ty == JLeft = l <> " LEFT JOIN " <> joinPredicate b ir
                | otherwise =  l <> " JOIN " <> joinPredicate b ir
            joinPredicate  b  r  = showTable b <> " ON " <> T.intercalate " AND " (fmap (\(t,fs) -> T.intercalate " AND " $ fmap (\f-> intersectionOp (keyType (fst f)) (keyType (snd f)) (tableName t <> "." <> keyValue (fst f) ) (tableName b <> "." <> keyValue (snd f)) )  $ S.toList fs )  $ S.toList r )

showTable (Project s t)
  |  F.all (const False) s  = "(SELECT " <>  showTable t  <> ") as " <> tableName t
  | otherwise = "(SELECT " <> T.intercalate ","  (F.toList $ attrName <$> s)  <>  showTable t  <> ") as " <> tableName t
showTable (Reduce j t p) =  "(SELECT " <> T.intercalate "," (fmap keyValue (S.toList j)  <> fmap (renderAttribute.Agg )  (S.toList t ) )   <> " FROM " <>   showTable p  <> " GROUP BY " <> T.intercalate "," (fmap keyValue (S.toList j)) <> " ) as " <> tableName p
showTable (Limit t v) = showTable t <> " LIMIT " <> T.pack (show v)

delete
  :: ToField b =>
     Connection ->  [(Key, b)] -> Table -> IO GHC.Int.Int64
delete conn kold t@(Raw sch tbl pk _ _ _) = execute conn (fromString $ traceShowId $ T.unpack del) (fmap snd koldPk)
  where
    koldM = M.fromList kold
    equality (k,_)= keyValue k <> "="  <> "?"
    memberPK k = S.member (keyValue $ fst k) (S.fromList $ fmap  keyValue $ S.toList  pk)
    koldPk = filter memberPK kold
    pred   =" WHERE " <> T.intercalate " AND " (fmap  equality koldPk)
    del = "DELETE FROM " <> rawFullName t <>   pred


update
  :: ToField b =>
     Connection -> [(Key, b)] -> TB1 (Key, b) -> Table -> IO (GHC.Int.Int64,TableModification b)
update conn kv kold t@(Raw sch tbl pk _ _ _) = fmap (,TableModification Nothing t (Edit (Just skv) kold  )) $ execute conn (fromString $ traceShowId $ T.unpack up)  (fmap snd skv <> fmap snd koldPk)
  where
    koldM = M.fromList (F.toList kold)
    equality (k,_)= keyValue k <> "="  <> "?"
    memberPK k = S.member (keyValue $ fst k) (S.fromList $ fmap  keyValue $ S.toList  pk)
    koldPk = filter memberPK (F.toList kold)
    pred   =" WHERE " <> T.intercalate " AND " (fmap  equality koldPk)
    setter = " SET " <> T.intercalate "," (fmap equality skv )
    up = "UPDATE " <> rawFullName t <> setter <>  pred
    skv = nubBy (\(i,j) (k,l) -> i == k)  kv

insertPK f conn kva t@(Raw sch tbl pk  _ _ attr ) = case pkListM of
                                                      Just reti ->  fmap ( zip pkList . head) $ liftIO $ queryWith (f $ Metric <$> pkList) conn (fromString $ traceShowId $ T.unpack $ "INSERT INTO " <> rawFullName t <>" ( " <> T.intercalate "," (fmap (keyValue . fst) kv) <> ") VALUES (" <> T.intercalate "," (fmap (const "?") kv) <> ")" <> " RETURNING " <>  T.intercalate "," (keyValue <$> reti )  ) (fmap snd  kv)
                                                      Nothing ->   liftIO $ execute conn (fromString $ traceShowId $ T.unpack $ "INSERT INTO " <> rawFullName t <>" ( " <> T.intercalate "," (fmap (keyValue . fst) kv) <> ") VALUES (" <> T.intercalate "," (fmap (const "?") kv) <> ")"   ) (fmap snd  kv) >> return []
  where pkList = S.toList $ S.filter (isSerial . keyType )  pk
        pkListM= case pkList of
                  [] -> Nothing
                  i -> Just i
        kv = nub $ filter (\(k,_) -> memberPK k || memberAttr k || memberDesc k) $    kva
        memberPK k = S.member (keyValue k) (S.fromList $ fmap  keyValue $ S.toList $ S.filter (not . isSerial . keyType ) pk)
        memberAttr k = S.member (keyValue k) (S.fromList $ fmap  keyValue $ S.toList attr)
        memberDesc k = S.member (keyValue k) (S.map keyValue $ maybe S.empty S.singleton $ rawDescription t )

getKey  (Raw sch tbl pk desc fk attr) k =  M.lookup k table
  where table = M.fromList $ fmap (\i-> (keyValue i, i)) $ S.toList (pk <> attr)

isEmptyShowable (SOptional Nothing ) = True
isEmptyShowable (SSerial Nothing ) = True
isEmptyShowable i = False


insert conn kva t@(Raw sch tbl pk desc _ attr ) = execute conn (fromString $ traceShowId $ T.unpack $ "INSERT INTO " <> rawFullName t  <>" ( " <> T.intercalate "," (fmap (keyValue . fst) kv) <> ") VALUES (" <> T.intercalate "," (fmap (const "?") kv) <> ")") (fmap snd kv)
  where kv = filter (\(k,_) -> S.member k (maybe S.empty S.singleton desc )|| S.member k pk || S.member k attr ) $ filter ( not . isSerial . keyType . fst)  kvb
        kvb = catMaybes $ fmap (\i-> fmap (,snd i) . getKey t . keyValue . fst $ i  ) kva

dropTable r@(Raw sch tbl _ _ _ _ )= "DROP TABLE "<> rawFullName r

rawFullName (Raw (sch,tt) tbl _ _ _ _) = sch <> "." <> tbl

createTable r@(Raw sch tbl pk _ fk attr) = "CREATE TABLE " <> rawFullName r  <> "\n(\n\t" <> T.intercalate ",\n\t" commands <> "\n)"
  where commands = (renderAttr <$> S.toList attr ) <> [renderPK] <> fmap renderFK (S.toList fk)
        renderAttr k = keyValue k <> " " <> renderTy (keyType k) <> if  (isKOptional (keyType k)) then "" else " NOT NULL"
        renderKeySet pk = T.intercalate "," (fmap keyValue (S.toList pk ))
        renderTy (KOptional ty) = renderTy ty <> ""
        renderTy (KSerial ty) = renderTy ty <> ""
        renderTy (KInterval ty) = renderTy ty <> ""
        renderTy (KArray ty) = renderTy ty <> "[] "
        renderTy (Primitive ty ) = ty
        renderTy (InlineTable ty ) = ty
        renderPK = "CONSTRAINT " <> tbl <> "_PK PRIMARY KEY (" <>  renderKeySet pk <> ")"
        renderFK (Path origin (FKJoinTable _ ks table) end) = "CONSTRAINT " <> tbl <> "_FK_" <> table <> " FOREIGN KEY " <>  renderKeySet origin <> ") REFERENCES " <> table <> "(" <> renderKeySet end <> ")  MATCH SIMPLE  ON UPDATE  NO ACTION ON DELETE NO ACTION"
        renderFK (Path origin _  end) = ""

joinPath (Path i (FKJoinTable _ ks ll ) j) (Just p) = Just $ addJoin  ll (S.fromList ks)  p
joinPath (Path i (FetchTable ll ) j) (Just p) = Just $ addJoin  ll ((S.fromList $ zip (S.toList i) (S.toList j)))  p
-- joinPath (Path i (FetchTable ll) j) Nothing  =  Just $ From ll   (i `S.union` j)
joinPath (ComposePath i (l,ij,k) j ) m = F.foldl' (flip joinPath)  m  ((S.toList l)  <> ( S.toList k))

joinPathL (Path i (FKJoinTable ll  ks _ ) j) (Just p) = Just $ addJoin  ll (S.fromList $ fmap swap ks)  p
joinPathL (Path i (FetchTable ll ) j) (Just p) = Just $ addJoin  ll ((S.fromList $ zip (S.toList i) (S.toList j)))  p
joinPathL (ComposePath i (l,ij,k) j ) m = F.foldr joinPathL  m  ((S.toList l)  <> ( S.toList k))

makeOpt (Key a b c d ty) = (Key a b c d (KOptional ty))

addJoin
  :: Table
  -> Set (Key, Key) -> JoinPath Key Table -> JoinPath Key Table
addJoin tnew f p = case mapPath tnew  f p of
            -- Add new case
            Left (Left accnew) -> case any (isKOptional . keyType) (concat $ fmap fst . S.toList .  snd <$> S.toList accnew) of
                             True ->  Join JLeft tnew  accnew  p
                             False ->  Join JInner tnew accnew  p
            -- Just update with new joins
            Left (Right i) -> i
            Right i -> i
    where
        filterFst JInner t elem=  if S.null filtered then Nothing else Just (t,filtered)
          where filtered = S.filter ((`S.member` (S.map (snd.snd) $ allAttrs' t)) . fst ) elem
        filterFst JLeft t elem=  if S.null filtered then Nothing else Just (t,filtered)
          where filtered = S.map (\(i,j) -> (makeOpt i ,j) )$ S.filter ((`S.member` (S.map (snd.snd) $ allAttrs' t)) . fst ) elem

        --mapPath :: (Show a,Show b,Ord b,Ord a) => a -> Set b -> JoinPath b a -> Either (Set (a,b)) (JoinPath b a)
        mapPath tnew f (From t   s ) =  if tablesName tnew `S.isSubsetOf`  tablesName t
                then  Right $ From t  snew
                else  Left $ Left $ maybe S.empty S.singleton   (filterFst JInner t f)
            where snew =  s `S.union` (S.map snd f)
        mapPath tnew f (Join ty t clause p ) = res
            where  res = case mapPath tnew  f p  of
                    Right pnew  -> case (filterFst ty t f) of
                        Just i -> Right $ Join ty t  (i `S.insert` clause )  pnew
                        Nothing -> Right $ Join ty t  clause pnew
                    Left (Right (Join ty1 t1 clause1 p1 )) ->
                        Left $ Right (Join ty1 t1 (maybe clause1 (`S.insert` clause1) (filterFst ty t f))(Join ty t clause p1))
                    Left (Left accnew) -> if tablesName tnew `S.isSubsetOf`  tablesName t
                        then Left $  Right $ Join ty t  (clause `S.union` accnew ) p
                        else Left $ case filterFst ty t f of
                                    Just i -> Left $ S.insert i accnew
                                    Nothing -> Left accnew




addFilterTable [] b = b
addFilterTable ff b@(Filtered fi _ ) = Filtered (fi<>ff) b
addFilterTable ff b = Filtered ff b

-- Label each table with filter clauses
specializeJoin
  :: Map Key Filter
    -> JoinPath Key Table
    -> (Map Key Filter,JoinPath Key Table )
specializeJoin f (From t s) =  (M.fromList ff , From (addFilterTable ff t) s)
    where ff = catMaybes  (fmap (\ i -> fmap (i,). (flip M.lookup) f $ i) (fmap (snd . snd) $ S.toList $ allAttrs' t))
specializeJoin f (Join ty t r p) =  (ms1,Join ty (addFilterTable ff t) r sp)
    where (ms,sp) = specializeJoin f p
          ff = catMaybes  (fmap (\ i -> fmap (i,). flip M.lookup f  $ i) (fmap (snd . snd) $ S.toList $ allAttrs' t))
          ms1 = foldr (\(i,j) s -> M.insert i  j s) ms ff

specializeJoin f i = error $ "specializeJoin " <> show f <> " --- "<> show i

addPath
  :: Monad m => [Path (Set Key) (SqlOperation Table) ]
  -> QueryT m ()
addPath  p = do
  (schema,Base k j ) <- get
  put (schema,Base k ((\(Just i)-> i) $ F.foldl' (flip joinPathL) (Just j) p))


type HashQuery =  HashSchema (Set Key) (SqlOperation Table)
type PathQuery = Path (Set Key) (SqlOperation Table)

createFilter
  :: Map Key Filter
  ->  HashQuery
  -> Table
  -> (Map Key Filter, Table)
createFilter filters schema (Base k j) = (m,Base k spec)
    where
      path = queryHash (fmap S.singleton $ M.keys  filters)  schema k
      Just join =  foldr joinPath (Just j) (concat $ catMaybes path)
      (m,spec) = specializeJoin filters join
createFilter filters schema (Project a t) = fmap (Project a) (createFilter filters schema t)
createFilter filters schema (Reduce  k a t) = fmap (Reduce k a) (createFilter filters schema t)


predicate
  :: Monad m =>[(Key,Filter)]
     -> QueryT m ()
predicate filters = do
  (schema,table) <- get
  put (schema, snd  $ createFilter (M.fromList filters) schema table)


unIntercalate :: ( Char -> Bool) -> String -> [String]
unIntercalate pred s                 =  case dropWhile pred s of
                                "" -> []
                                s' -> w : unIntercalate pred s''
                                      where (w, s'') =
                                             break pred s'

data Tag = TAttr | TPK

allKVRec  (TB1 (KV (PK k d) e ))= F.foldr zipPK (KV (PK [] []) []) $ (go TPK (\i -> KV (PK i []) []) . runIdentity . getCompose  <$> k) <> (go TAttr (\i-> KV (PK [] i) [] ) . runIdentity . getCompose <$> d) <> ( go TAttr (\i-> KV (PK [] []) i) . runIdentity . getCompose <$> e)
  where zipPK (KV (PK i j) k) (KV (PK m n) o) = KV (PK (i <> m) (j <> n)) (k <> o )
        go  TAttr l (FKT _ _ _ tb) =  l $ F.toList $ allKVRec  tb
        go  TPK l (FKT _ _ _ tb) =  allKVRec  tb
        go  TAttr l (IT  _ tb) =  l $ F.toList $ allKVRec  tb
        go  TPK l (IT  _ tb) =  allKVRec  tb
        go  TAttr l (IAT _  tb) = l $ concat $  F.toList . allKVRec <$> tb
        -- go  TPK l (AKT _ _ _ tb) = concat $  allKVRec <$> tb
        go  TAttr l (AKT _ _ _ tb) = l $ concat $  F.toList . allKVRec <$> tb
        go  _ l (Attr a) = l [a]


allPKRec  (TB1 (KV (PK k d) i ))=  F.foldr zipPK (PK [] []) $ (go (flip PK []) . runIdentity . getCompose <$> k) <> (go (PK []) . runIdentity . getCompose <$> d)
  where zipPK (PK i j) (PK m n) = (PK (i <> m) (j <> n))
        go l (Attr a) = l [a]


allAliasedRec i t = tb1Rec False PathRoot i t

tb1Rec isOpt p  invSchema ta@(Raw _ _ k desc fk attr) =
  let
      baseCase = KV (PK (fun k) (fun (S.fromList $ F.toList desc)))  (fun (maybe attr (`S.delete` attr) desc))
      leftFst True keys = fmap (fmap (\((Key a al b c  e) ) -> ( Key a al b c  (KOptional e)))) keys
      leftFst False keys = keys
      fun items = fmap (Compose . Identity  ) $ (fmap (Attr . (p,)) $ F.toList $ items `S.difference` fkSet ) <> (fkCase invSchema isOpt p <$> filter (\(Path ifk _ _) -> ifk `S.isSubsetOf` items ) (F.toList fk) )
      fkSet = S.unions $  fmap (\(Path ifk _ _) -> ifk)  $S.toList fk
  in leftFst isOpt  $ TB1 baseCase


fkCase invSchema isOpt p (Path ifk (FKJoinTable bt kv nt)  o ) = FKT  (Compose . Identity . Attr. (p,) <$>S.toList ifk) True kv (tb1Rec isOptional (aliasKeyValue ifk ) invSchema ((\(Just i)-> i) (M.lookup nt  invSchema )))
            where isOptional = any (isKOptional . keyType ) (F.toList ifk)
                  bindMap = M.fromList $ fmap swap kv
                  aliasKeyValue k =  (PathCons $ S.map (,p) k)
                  substBind k = case M.lookup k bindMap of
                                    Just i -> i
                                    Nothing -> k

recursePath invSchema (Path i (FetchTable t) e)  = Path i (FetchTable nextT) e : recursePaths invSchema nextT
  where nextT@(Raw _ _ _ _ fk _ ) = (\(Just i)-> i) (M.lookup t (invSchema))
recursePath invSchema (Path i (FKJoinTable w ks t) e)  = Path i (FKJoinTable backT ks nextT) e : recursePaths invSchema nextT
  where nextT@(Raw _ _ _ _ fk _ ) = (\(Just i)-> i) (M.lookup t (invSchema))
        backT = (\(Just i)-> i) (M.lookup w (invSchema))


recursePaths invSchema (Raw _ _ _ _ fk _ )  = concat $ recursePath invSchema <$> S.toList fk


rawLPK t@(Labeled b i ) = (t,) . (\i -> Labeled (keyValue i) (Attr i) ) <$> S.toList (rawPK i)

tableToKV r =   do
  KV (PK (S.toList (rawPK r)) (maybeToList (rawDescription r)) ) (S.toList (rawAttrs r))

labelTable :: Table -> State ((Int, Map Int Table), (Int, Map Int Key)) (Labeled Text Table,FTB1 (Compose (Labeled Text) (TB (Labeled Text) )) Key,Text)
labelTable i = do
   t <- tname i
   name <- Tra.traverse ( kname t) (tableToKV i)
   let query = "(SELECT " <>  T.intercalate "," (F.toList $ aliasKeys <$> name) <> " FROM " <> aliasTable t <> ") as " <> label t
   return (t,TB1 $ fmap (Compose. snd) $ name,query)

lb1 = TB1 . (fmap Compose)

isPairReflexive (Primitive i ) (KInterval (Primitive j)) | i == j = False
isPairReflexive (Primitive j) (KArray (Primitive i) )   = False
isPairReflexive (Primitive i ) (Primitive j) | i == j = True
isPairReflexive (KOptional i ) j = isPairReflexive i j
isPairReflexive i  (KOptional j) = isPairReflexive i j
isPairReflexive i  (KSerial j) = isPairReflexive i j
isPairReflexive (KArray i )   j = True
isPairReflexive i j = error $ "isPairReflexive " <> show i <> " - "<> show  j

isPathReflexive (FKJoinTable _ ks _)
  = all id $ fmap (\(i,j)-> isPairReflexive (textToPrim <$> keyType i ) (textToPrim <$> keyType j)) ks
isPathReflexive (FKInlineTable _)= True

intersectionOpK i j = intersectionOp (keyType i ) (keyType j)


recursePath' isLeft (ksbn,bn) invSchema (Path ifk jo@(FKInlineTable t ) e)
    | any (isArray . keyType ) (S.toList ifk)  =   do
          (bt,ksb,bq) <- labelTable backT
          return $ ( [Compose $ Labeled ""  $ IAT (fmap (\i -> Compose . justError ("cant find " ). L.find ((== i) . unAttr. labelValue  )$ ksbn) (S.toList ifk )) [ksb]  ]  ,"")
    | otherwise = do
          (bt,ksb,bq) <- labelTable backT
          return $ ( [Compose $ Labeled ""  $ IT (fmap (\i -> Compose . justError ("cant find " ). L.find ((== i) . unAttr. labelValue  )$ ksbn) (S.toList ifk ))  ksb  ]  ,"")
    where
        backT = (\(Just i)-> i) (M.lookup t (invSchema))

recursePath' isLeft (ksbn,bn) invSchema (Path ifk jo@(FKJoinTable w ks tn) e)
    | any (isArray . keyType . fst) (ks)  =   do
          (bt,ksb,bq) <- labelTable backT
          let pksb = (_pkKey $ _kvKey $ unlb1 ksb )
          (nt,ksn@(TB1 (KV (PK npk ndesc) nattr)),nq) <- labelTable nextT
          let pksn = (_pkKey $ _kvKey $ unlb1 ksn )
          let nkv pk desc attr = (mapOpt $ TB1 (KV (PK (fst pk) (fst desc)) (fst attr)), foldl mappend "" $ snd pk <> snd desc <> snd attr)
          (tb,q) <-liftA3 nkv (fun ksn nt $ fmap getCompose npk) (fun ksn nt $ fmap getCompose ndesc) (fun ksn nt $ fmap getCompose nattr)
          tas <- tname nextT
          let knas =(Key (tableName nextT) Nothing Nothing (unsafePerformIO newUnique) (Primitive "integer" ))
          kas <- kname tas  knas
          let relLabel = fkm (F.toList $ unlb1 $ ksb) (F.toList $ unlb1 ksn)
          let jt = if nextLeft  then " LEFT JOIN " else " JOIN "
              query =  jt <> "(SELECT " <> T.intercalate "," (label <$> pksb) <> "," <> "array_agg((" <> (T.intercalate ","  (fmap explodeLabel $ (F.toList $ unlb1 $ tb ) )) <> " )order by arrrow) as " <> label (snd kas) <> " FROM " <> bq <> (jt <> " LATERAL ( SELECT * FROM (SELECT *,row_number() over () as arrrow FROM UNNEST(" <> label (head (look (fst <$> ks) (F.toList$ unlb1 ksb) ))  <> ") as arr) as z1 "  <> jt <> nq  <> " ON " <>  label (head (look (snd <$> ks) (F.toList $ unlb1 ksn) )) <> " = arr ) as z1 ON true " <>  q <>   " GROUP BY " <>  T.intercalate "," (label <$> pksb ) <> ") as " <>  label tas  <> " ON " <>  joinLPredicate (zip ksbn pksb))
          return $ ([Compose $ Labeled (label $ snd kas) (AKT (fmap (\i -> Compose . justError ("cant find " ). L.find ((== i) . unAttr. labelValue  )$ ksbn) (S.toList ifk )) (isPathReflexive jo ) ks  [tb  ]) ] , query)

    | otherwise = do
          (nt,ksn@(TB1 (KV (PK npk ndesc) nattr)),nq) <- labelTable nextT
          let pksn = (_pkKey $ _kvKey $ unlb1 ksn )
              nkv pk desc attr = (mapOpt $ TB1 (KV (PK (fst pk) (fst desc)) (fst attr)), foldl mappend "" $ snd pk <> snd desc <> snd attr)
          (tb,q) <-liftA3 nkv (fun ksn nt $ fmap getCompose npk) (fun ksn nt $ fmap getCompose ndesc) (fun ksn nt $ fmap getCompose nattr)
          let jt = if nextLeft  then " LEFT JOIN " else " JOIN "
          return $ ( [Compose $ Labeled ""  $ FKT (fmap (\i -> Compose . justError ("cant find " ). L.find ((== i) . unAttr. labelValue  )$ ksbn) (S.toList ifk )) (isPathReflexive jo ) ks tb  ]  ,(jt <> nq <> " ON "  <> joinLPredicate (fkm ksbn pksn) <>  q))
  where nextT@(Raw _ _ _ _ fk _ ) = (\(Just i)-> i) (M.lookup tn (invSchema))
        backT = (\(Just i)-> i) (M.lookup w (invSchema))
        joinLPredicate   =   T.intercalate " AND " . fmap (\(l,r)->  intersectionOpK (unAttr . labelValue $ l) (unAttr . labelValue $ r) (label l)  (label r ))
        fkSet = S.unions $ fmap (\(Path ifk _ _) -> ifk)$ filter (\(Path _ ifk  _) -> isPathReflexive ifk)  $ S.toList (rawFKS nextT)
        nextLeft = any (isKOptional.keyType.fst) ks || isLeft
        fkm m n = zip (look (fst <$> ks) m) (look (snd <$> ks) n)
        look ki i = justError ("missing FK on " ) $ allMaybes $ fmap (\j-> L.find (\v -> unAttr (labelValue v) == j) i  ) ki
        mapOpt = fmap (\i -> if any (isKOptional.keyType.fst) ks then  makeOpt i else i)
        fun ksn nt items =  do
                  let attrs :: [TBLabel  Key]
                      attrs = fmap Compose $ filter (\i -> not $ S.member (unAttr.labelValue $ i) fkSet) items
                      itemSet :: S.Set Key
                      itemSet = S.fromList $ fmap (unAttr.labelValue) items
                  pt <- mapM (recursePath' nextLeft (F.toList .unlb1 $ ksn ,nt) invSchema) (filter (\(Path ifk jo  _) ->  ifk `S.isSubsetOf`  itemSet ) (F.toList $ rawFKS nextT ))
                  return (attrs <> (concat $ fst <$> pt), snd <$> pt)


unTB = runIdentity . getCompose
_tb = Compose . Identity

unAttr (Attr i) = i
unAttr i = errorWithStackTrace $ "cant find attr" -- <> (show i)

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

aliasKeys (t,Labeled  a (Attr (Key n _  _ _ _)))  = label t <> "." <> n <> " as " <> a

nonAliasKeys (t,Labeled a (Attr (Key n _  _ _ _)))  = label t <> "." <> n

aliasTable (Labeled t r) = showTable r <> " as " <> t

kname :: Labeled Text Table -> Key -> QueryRef (Labeled Text Table ,Labeled Text (TB (Labeled Text) Key))
kname t i = do
  n <- mkKey i
  return $ (t,Labeled ("k" <> (T.pack $  show $ fst n)) (Attr i) )

tname :: Table -> QueryRef (Labeled Text Table)
tname i = do
  n <- mkTable i
  return $ Labeled ("t" <> (T.pack $  show n)) i

explodeLabel :: Labeled Text (TB (Labeled Text) Key) -> Text
explodeLabel (Labeled l (Attr _)) = l
explodeLabel (Labeled l (FKT i refl rel t )) = T.intercalate "," (( F.toList $ (explodeLabel.getCompose) <$> i)) <> ",(" <> T.intercalate "," (( F.toList $ fmap explodeLabel $ unlb1 t))  <> ")"
explodeLabel (Labeled l (IT i t )) = T.intercalate "," (( F.toList $ (explodeLabel.getCompose) <$> i))--  <> ",(" <> T.intercalate "," (( F.toList $ fmap explodeLabel $ unlb1 t))  <> ")"
explodeLabel (Labeled l (IAT i t )) = T.intercalate "," (( F.toList $ (explodeLabel.getCompose) <$> i))--  <> ",(" <> T.intercalate "," (( F.toList $ fmap explodeLabel $ unlb1 t))  <> ")"
explodeLabel (Labeled l (AKT i _ _ _ )) = T.intercalate "," (( F.toList $ (explodeLabel. getCompose ) <$> i)) <> "," <> l

unTlabel kv  = TB1 $ fmap (Compose . Identity .unlabel) $ unlb1 kv
unlabel (Labeled l (FKT i refl fkrel t) ) = (FKT (fmap relabel i) refl fkrel (unTlabel t ))
unlabel (Labeled l (IT i t) ) = (IT (fmap relabel i) (unTlabel t ))
unlabel (Labeled l (IAT i [t]) ) = (IAT (fmap relabel i) [unTlabel t ])
unlabel (Labeled l (AKT i refl fkrel [t]) ) = (AKT (fmap relabel i) refl fkrel [unTlabel t])
unlabel (Labeled l (Attr i )) = Attr i

relabel = Compose . Identity . unlabel.getCompose

type TBLabel =  Compose (Labeled Text) (TB (Labeled Text))
type TBIdent =  Compose Identity  (TB Identity )
allRec'
  :: Map Text Table
     -> Table
     -> TB1
          Key
allRec' i t = unTlabel $ fst $ rootPaths' i t

rootPaths' invSchema r@(Raw _ _ _ _ fk _ ) = fst $ flip runState ((0,M.empty),(0,M.empty)) $ do
  (t,ks@(TB1 (KV (PK npk ndesc) nattr)),q) <- labelTable r
  let fkSet = traceShowId $ S.unions $ fmap (\(Path ifk _ _) -> ifk)$ traceShowId $ filter (\(Path _ ifk  _) -> isPathReflexive ifk) $ S.toList fk
      fun items =  do
                  let attrs :: [TBLabel Key]
                      attrs = fmap Compose $ filter (\i -> not $ S.member (unAttr.labelValue $ i) fkSet) items
                      itemSet :: S.Set Key
                      itemSet = S.fromList $ fmap (unAttr.labelValue) items
                  pt <- mapM (recursePath' False (F.toList .unlb1 $ ks ,t) invSchema) (filter (\(Path ifk jo _)-> ifk `S.isSubsetOf`  itemSet ) (F.toList fk ))
                  return (attrs <> (concat $ fst <$> pt), snd <$> pt)
      nkv pk desc attr = (TB1 (KV (PK (fst pk) (fst desc)) (fst attr)), foldl mappend "" $ snd pk <> snd desc <> snd attr)
  (tb,js) <-liftA3 nkv (fun $ fmap getCompose npk) (fun $ fmap getCompose ndesc) (fun $ fmap getCompose nattr)
  return ( tb , "SELECT (" <> T.intercalate "," (fmap explodeLabel $ (F.toList $ unlb1 tb))  <> (") FROM " <> q ) <> js)




projectAllRec'
     :: Monad m => Map Text Table ->  QueryT m (TB1 KAttribute)
projectAllRec' invSchema =  do
  (schema,table@(Base _ t  )) <- get
  let
      ta@(Raw _ _ k _ _ _ ) = atBase id table
      path = ( recursePaths invSchema ta)
      table1 = Base k $ splitJoins  ((\(Just i)-> i) $ F.foldl' (flip joinPath) (Just t)  ( recursePaths invSchema ta))
      attrs =  Metric . alterName <$> (allAliasedRec invSchema ta )
      aliasMap =   fmap fst $ M.fromList $ aliasJoin table1
      alterName ak@(p,Key k al a b c ) = (Key k (Just $ justError ("lookupAlias "  <> show ak <> " " <> show aliasMap   <> " -- paths " <> show path <> T.unpack (showTable table1 )  ) $ M.lookup ak aliasMap ) a b c )
  put (schema,Project (F.toList attrs )  table1 )
  return  attrs


justError e (Just i) = i
justError e  _ = error e

getTableKV (Raw _ _ pk desc _ attrs) = KV (PK (F.toList pk) (F.toList desc) ) (F.toList desc )

projectTableAttrs
     :: Monad m => Table -> QueryT m (KV  KAttribute)
projectTableAttrs r@(Raw _ _ pk desc _ _) =  do
  (schema,Base k  table) <- get
  let
      table1 = Base k $ splitJoins table
      kv =  fmap (\i-> Metric $ alterName . (\(Just i)-> i) $ F.find (\k-> i == snd k ) (M.keys aliasMap) ) $ getTableKV r
      aliasMap =  M.fromList $ aliasJoin  table1
      alterName ak@(p,Key k al a b c ) = (Key k (Just $ fst $ justError ("lookupAlias "  <> show ak <> " " <> show aliasMap  <> T.unpack (showTable table1 )  ) $ M.lookup ak aliasMap ) a b c )
  put (schema,Limit (Project (F.toList kv) $ table1) 500)
  return kv



allAttrs' :: Table -> Set (AliasPath Key,(Table,Key))
allAttrs' r@(Raw _ _ _ _ _ _) = S.map ((PathRoot,) . (r,)) $ rawKeys r
allAttrs' (Limit p _ ) = allAttrs' p
allAttrs' (Filtered _ p) = allAttrs' p
allAttrs' (Base _ p) =  snd $  from allAttrs' p
  where from f (From t pk ) = (sm1,ft)
          where ft = f t
                sm1 =  foldr (\i m -> M.insert (snd $ snd i) PathRoot m ) M.empty (S.toList ft)
        from f s@(SplitJoin _ t  rel p) =  (sm1 , (foldr (<>) sp $ fmap (\(n,_) -> S.map (\(_,(ta,k))-> (pth  n,(alterTableName (<> fullTableName n  ) ta,k))) (f t) ) rel )  <> sp)
          where
                (sm,sp) = from f p
                sm1 =  foldr (\(n,_) m -> foldr (\i mi -> M.insert   (snd $ snd i) (pth  n) mi ) m  (S.toList ft) ) sm rel
                pth n = PathCons (S.map (\nk -> (nk,(justError $ "allAttrs' pathSplit KEY " <> (T.unpack $ showKey nk ) )$ M.lookup nk sm) ) n )
                ft = f t
        from f (Join ty t r p) = (sm1,S.map (\(_,(ta,k))-> (pth ,(ta,k))) ft  <>   sp)
          where n = S.map (justError "allAttrs' filterSet") $ S.filter isJust $ S.map (\i -> M.lookup i  (M.fromList $ concat $ fmap (fmap swap . S.toList .snd) $ S.toList r) ) pk
                (sm,sp) = from f p
                sm1 =  foldr (\i m -> M.insert (snd $ snd i) pth  m ) sm (S.toList ft)
                pth = PathCons (S.map (\nk -> (nk,(justError "allAttrs' pathLeft") (M.lookup nk sm)) ) n )
                ft = f t
                pk = atBase (\(Raw _ _ p _ _ _) -> p) t

rawKeys r = (rawPK r ) <> (maybe S.empty S.singleton (rawDescription r) ) <> (rawAttrs r)

newtype QueryT m a
  = QueryT {runQueryT :: StateT  (HashQuery, Table)  m a} deriving(Functor,Applicative,Monad,MonadState (HashQuery, Table) )

runQuery t =  runState (runQueryT t)

pathLabel (ComposePath i (p1,p12,p2) j) = T.intercalate "," $  fmap pathLabel (S.toList p1) <> fmap pathLabel (S.toList p2)
pathLabel (Path i t j) = tableName t

zipWithTF g t f = snd (mapAccumL map_one (F.toList f) t)
    where map_one (x:xs) y = (xs, g y x)
          -- map_one [] y = ([] , [] )


groupSplit f = fmap (\i-> (f $ head i , i)) . groupWith f

-- interval' i j = Interval.interval (ER.Finite i ,True) (ER.Finite j , True)
inf' = (\(ER.Finite i) -> i) . Interval.lowerBound
sup' = (\(ER.Finite i) -> i) . Interval.upperBound


unSOptional (SOptional i) = i
unSOptional i = traceShow ("unSOptional No Pattern Match SOptional-" <> show i) Nothing

unSSerial (SSerial i) = i
unSSerial i = traceShow ("unSSerial No Pattern Match SSerial-" <> show i) Nothing

unRSOptional (SOptional i) = join $ fmap unRSOptional i
unRSOptional i = traceShow ("unRSOptional No Pattern Match SOptional-" <> show i) Nothing

unRSOptional' (SOptional i) = join $ unRSOptional' <$> i
unRSOptional' (SSerial i )  = join $ unRSOptional' <$>i
unRSOptional' i   = Just i

allMaybes i | F.all (const False) i  = Nothing
allMaybes i = if F.all isJust i
        then Just $ fmap (justError "wrong invariant allMaybes") i
        else Nothing


