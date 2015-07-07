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
import Data.Functor.Compose
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
import Data.Void

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
import Data.Map (Map)
-- import Data.Set (Set)
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

_unlb1 ( TB1  i ) = fmap getCompose i

unlb1 ( TB1  i ) = fmap getCompose i
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
    shw (SPosition a) = show a
    shw (SOptional a) = show a
    shw (SInterval a) = showInterval a
    shw (SPInterval a) = show a
    shw (SEitherR a) = renderShowable a
    shw (SEitherL a) = renderShowable a
    shw (SComposite a) = intercalate "," $ F.toList (fmap shw a)

showInterval i | i == Interval.empty = show i
showInterval (Interval.Interval (ER.Finite i,j) (ER.Finite l,m) ) = ocl j <> renderShowable i <> "," <> renderShowable l <> ocr m
    where
      ocl j = if j then "[" else "("
      ocr j = if j then "]" else ")"


renderAliasedKey (v ,(t,k)) a = rawName t <> "." <> keyValue k <> " AS " <> a


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
intersectPred p@(Primitive _ ) (KArray i) j (SComposite l )  | p == i =  Vector.elem j l
intersectPred p1@(Primitive _ ) p2@(Primitive _) j l   | p1 == p2 =  j ==  l
intersectPred p1 (KSerial p2 ) j (SSerial l)   | p1 == p2 =  maybe False (j ==) l
intersectPred p1 (KOptional p2 ) j (SOptional l)   | p1 == p2 =  maybe False (j ==) l
intersectPred p1@(KOptional i ) p2 (SOptional j) l  =  maybe False id $ fmap (\m -> intersectPred i p2 m l) j
intersectPred p1 p2 j l   = error ("intersectPred = " <> show p1 <> show p2 <>  show j <> show l)


intersectionOp (KOptional i) (KOptional j) = intersectionOp i j
intersectionOp i (KOptional j) = intersectionOp i j
intersectionOp (KOptional i) j = intersectionOp i j
intersectionOp (KInterval i) (KInterval j )  = inner " <@ "
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

showTable t  = rawSchema t <> "." <> rawName t

delete
  :: ToField (TB Identity Key (Showable))  =>
     Connection ->  TB1 (Showable) -> Table -> IO GHC.Int.Int64
delete conn kold t = execute conn (fromString $ traceShowId $ T.unpack del) koldPk
  where
    equality k = attrValueName k <> "="  <> "?"
    koldPk = runIdentity . getCompose <$> F.toList (_pkKey $ _kvKey $ _unTB1 $ tableNonRef kold)
    pred   =" WHERE " <> T.intercalate " AND " (fmap  equality koldPk)
    del = "DELETE FROM " <> rawFullName t <>   pred

updateAttr
  :: ToField (TB Identity Key Showable) =>
     Connection -> TB1  Showable -> TB1 Showable -> Table -> IO (GHC.Int.Int64,TableModification Showable)
updateAttr conn kv kold t = fmap (,TableModification Nothing t (EditTB  kv  kold  )) $ execute conn (fromString $ traceShowId $ T.unpack up)  (skv <> koldPk)
  where
    equality k = attrValueName k <> "="  <> "?"
    koldPk = runIdentity . getCompose <$> F.toList (_pkKey $ _kvKey $ _unTB1 $ tableNonRefK kold)
    pred   =" WHERE " <> T.intercalate " AND " (equality <$> koldPk)
    setter = " SET " <> T.intercalate "," (equality <$> skv )
    up = "UPDATE " <> rawFullName t <> setter <>  pred
    skv = runIdentity . getCompose <$> F.toList (_unTB1 $ tableNonRefK kv)


attrType (Attr i _)= keyType i
attrType (IT i _) = keyType  i
attrType i = error $ " no attr value instance " <> show i

attrValueName (Attr i _ )= keyValue i
attrValueName (IT i  _) = keyValue i
attrValueName i = error $ " no attr value instance " <> show i

type TBValue = TB1 (Key,Showable)
type TBType = TB1 Key


insertAttr
  :: (MonadIO m
     ,Functor m
     ,ToField (TB Identity Key Showable))
     => (TB2 Key () -> RowParser (TB2 Key Showable) )
     -> Connection
     -> TB2 Key Showable
     -> Table
     -> m (TB2 Key Showable)
insertAttr f conn krec  t = if not (L.null pkList)
              then   do
        let iquery = T.unpack $ "INSERT INTO " <> rawFullName t <>" ( " <> T.intercalate "," (fmap attrValueName  kva) <> ") VALUES (" <> T.intercalate "," (fmap (const "?") kva) <> ")" <> " RETURNING ROW(" <>  T.intercalate "," (attrValueName . runIdentity . getCompose <$> pkList ) <> ")"
        liftIO $ print iquery
        out <-  fmap head $ liftIO $ queryWith (f (fmap (const ()) $ TB1 $ KV (PK pkList []) [])) conn (fromString  iquery ) (  kva)
        return $ mapTB1 (mapComp (\case{ (Attr k' v')-> maybe (Attr k' v') (runIdentity . getCompose )  $ findTB1 (overComp (\case{Attr nk nv ->nk == k'; i-> False} )) out; i-> i} ) ) krec
              else liftIO $ execute conn (fromString $ traceShowId $ T.unpack $ "INSERT INTO " <> rawFullName t <>" ( " <> T.intercalate "," (fmap attrValueName kva) <> ") VALUES (" <> T.intercalate "," (fmap (const "?") kva) <> ")"   )  kva >> return krec
  where pkList =   L.filter (isSerial . attrType . runIdentity . getCompose ) (_pkKey . _kvKey $ k )
        kva = L.filter (not . isSerial . attrType ) $ fmap (runIdentity . getCompose)  $ F.toList k
        (TB1 k ) = tableNonRefK krec

tableNonRefK (ArrayTB1 i) = ArrayTB1 $ tableNonRefK <$> i
tableNonRefK (LeftTB1 i ) = LeftTB1 $ tableNonRefK <$> i
tableNonRefK (TB1 (KV (PK l m ) n)  )  = TB1 (KV (PK (fun l) (fun m) ) (fun n))
  where
        nonRef i@(Attr _ _ ) = [Compose $ Identity $ i]
        nonRef (FKT i True _ _ ) = i
        -- Fix Either expansion
        nonRef (TBEither n kj j ) =  maybe (addDefault <$> kj) (\j -> fmap (\i -> if i == (fmap (const ()) j ) then j else addDefault i) kj) j
        nonRef (FKT i False _ _ ) = []
        nonRef it@(IT j k ) = [Compose $ Identity $ (IT   j (tableNonRefK k )) ]
        fun  = concat . fmap (nonRef . runIdentity . getCompose)

optionalAttr
  :: Compose
       Identity
       (TB f (FKey (KType a), Showable))
       (FKey (KType a1), Showable)
     -> Compose
          Identity
          (TB f (FKey (KType a), Showable))
          (FKey (KType a1), Showable)
optionalAttr  (Compose (Identity ((Attr k i )))) = Compose . Identity . Attr (keyOptional k) $ keyOptional i
optionalAttr  (Compose (Identity ((IT  rel j  )))) = Compose . Identity $  IT  rel (LeftTB1 $ Just $ j )

addDefault (Compose (Identity (Attr k i))) = Compose (Identity (Attr k (SOptional Nothing)))
addDefault (Compose (Identity (IT  rel j ))) = Compose (Identity (IT  rel (LeftTB1 Nothing)  ))

overComp f =  f . runIdentity . getCompose
mapComp f =  Compose. Identity . f . runIdentity . getCompose

tableNonRef (ArrayTB1 i) = ArrayTB1 $ tableNonRef <$> i
tableNonRef (LeftTB1 i ) = LeftTB1 $ tableNonRef <$> i
tableNonRef (TB1 (KV (PK l m ) n)  )  = TB1 (KV (PK (fun l) (fun m) ) (fun n))
  where
        nonRef i@(Attr _ _ ) = [Compose $ Identity $ i]
        nonRef (TBEither n l j ) = [Compose $ Identity $  TBEither n l  (overComp (head . nonRef) <$> j ) ]
        nonRef (FKT i True _ _ ) = i
        nonRef (FKT i False _ _ ) = []
        nonRef it@(IT j k ) = [Compose $ Identity $ (IT  j (tableNonRef k )) ]
        fun  = concat . fmap (overComp nonRef )

fakeKey n t = Key n Nothing (unsafePerformIO newUnique) t

unSComposite (SComposite i) = i
unSComposite i = errorWithStackTrace ("unSComposite " <> show i)

unSEitherR (SEitherR r) = Just r
unSEitherR (SEitherL r) = Nothing
unSEitherL (SEitherL r) = Just r
unSEitherL (SEitherR r) = Nothing



isEmptyShowable (SOptional Nothing ) = True
isEmptyShowable (SSerial Nothing ) = True
isEmptyShowable i = False



dropTable r= "DROP TABLE "<> rawFullName r

rawFullName = showTable

createTable r@(Raw sch _ _ tbl _ pk _ fk attr) = "CREATE TABLE " <> rawFullName r  <> "\n(\n\t" <> T.intercalate ",\n\t" commands <> "\n)"
  where commands = (renderAttr <$> S.toList attr ) <> [renderPK] <> fmap renderFK (S.toList fk)
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

unKOptional ((Key a  c d (KOptional e))) = (Key a  c d e )
unKOptional i = errorWithStackTrace ("unKOptional " <> show i)

unKArray (Key a  c d (KArray e)) = Key a  c d e
unKArray (Key a  c d (KOptional (KArray e) )) = Key a  c d e



unIntercalate :: ( Char -> Bool) -> String -> [String]
unIntercalate pred s                 =  case dropWhile pred s of
                                "" -> []
                                s' -> w : unIntercalate pred s''
                                      where (w, s'') =
                                             break pred s'

data Tag = TAttr | TPK

allKVRec (LeftTB1 i) = maybe mempty allKVRec i
allKVRec (ArrayTB1 i) = mconcat $ allKVRec <$> i
allKVRec  (TB1 (KV (PK k d) e ))= F.foldr zipPK (KV (PK [] []) []) $ (go TPK (\i -> KV (PK i []) []) . runIdentity . getCompose  <$> k) <> (go TAttr (\i-> KV (PK [] i) [] ) . runIdentity . getCompose <$> d) <> ( go TAttr (\i-> KV (PK [] []) i) . runIdentity . getCompose <$> e)
  where zipPK (KV (PK i j) k) (KV (PK m n) o) = KV (PK (i <> m) (j <> n)) (k <> o )
        go  TAttr l (FKT _ _ _ tb) =  l $ F.toList $ allKVRec  tb
        go  TPK l (FKT _ _ _ tb) =  allKVRec  tb
        go  i l (TBEither _ _  tbr) =  maybe mempty id $ go i l . runIdentity . getCompose <$>  tbr
        go  TAttr l (IT  _ tb) =  l $ F.toList $ allKVRec  tb
        go  TPK l (IT  _ tb) =  allKVRec  tb
        go  _ l (Attr _ a) = l [a]


allPKRec  (TB1 (KV (PK k d) i ))=  F.foldr zipPK (PK [] []) $ (go (flip PK []) . runIdentity . getCompose <$> k) <> (go (PK []) . runIdentity . getCompose <$> d)
  where zipPK (PK i j) (PK m n) = (PK (i <> m) (j <> n))
        go l (Attr _ a) = l [a]


tableToKV r =   do
  KV (PK (S.toList (rawPK r)) (maybeToList (rawDescription r)) ) (S.toList (rawAttrs r))

preLabelTable :: Text -> Table ->  (FTB1 (Compose (Labeled Text) (TB (Labeled Text) Key )) () )
preLabelTable t i =
   let v = fmap (\k -> Labeled (t <> "." <> keyValue k ) (Attr k () ) ) (tableToKV i)
   in (TB1 $ Compose <$> v )


labelTable :: Table -> State ((Int, Map Int Table), (Int, Map Int Key)) (Labeled Text Table,FTB1 (Compose (Labeled Text) (TB (Labeled Text) Key )) () ,Text)
labelTable i = do
   t <- tname i
   name <- Tra.traverse ( kname t) (tableToKV i)
   let query = "(SELECT " <>  T.intercalate "," (F.toList $ aliasKeys . (t,)<$> name) <> " FROM " <> aliasTable t <> ") as " <> label t
   return (t,TB1 $ Compose <$> name,query)

lb1 = TB1 . (fmap Compose)

isPairReflexive (Primitive i ) (KInterval (Primitive j)) | i == j = False
isPairReflexive (Primitive j) (KArray (Primitive i) )   = False
isPairReflexive (Primitive i ) (Primitive j) | i == j = True
isPairReflexive (KOptional i ) j = isPairReflexive i j
isPairReflexive i (KOptional j) = isPairReflexive i j
isPairReflexive i (KSerial j) = isPairReflexive i j
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
     -> TB1
          ()
allRec' i t = fst $ rootPaths' i t

rootPaths' invSchema r = (\(i,j) -> (unTlabel i,j ) ) $ fst $ flip runState ((0,M.empty),(0,M.empty)) $ do
  (t,ks@(TB1 (KV (PK npk ndesc) nattr)),q) <- labelTable r
  let
      fun =  recurseTB invSchema r False ks
      nkv pk desc attr = (TB1 (KV (PK (fst pk) (fst desc)) (fst attr)), foldl mappend "" $ snd pk <> snd desc <> snd attr)
  (tb,js) <-liftA3 nkv (fun $ fmap getCompose npk) (fun $ fmap getCompose ndesc) (fun $ fmap getCompose nattr)
  return ( tb , "SELECT ROW(" <> T.intercalate "," (fmap explodeLabel $ (F.toList $ unlb1 tb))  <> (") FROM " <> q ) <> js)

kattrl = kattrli .  labelValue . getCompose
kattrli (Attr i _ ) = [i]
kattrli (FKT i _ _ _ ) =  (L.concat $ kattrl  <$> i)
kattrli (IT i  _ ) =  [i]

-- keyAttr :: Show b  => TB Identity b a -> b
keyAttr (Attr i _ ) = i
keyAttr i = errorWithStackTrace $ "cant find keyattr" <> (show i)

recursePath' isLeft ksbn invSchema (Path _ jo@(FKEitherField o l) _) = do
   let findAttr =(\i -> Compose . justError ("cant find " ). L.find ((== [i]) . kattrl  . Compose )$ ksbn)
   return $ ([Compose $ Unlabeled $  TBEither  o (findAttr <$> l )  Nothing ],"")

recursePath' isLeft ksbn invSchema (Path ifk jo@(FKInlineTable t ) e)
    | isArrayRel ifk =   do
          tas <- tname nextT
          let knas =(Key (rawName nextT) Nothing (unsafePerformIO newUnique) (Primitive "integer" ))
          kas <- kname tas  knas
          let jt = if nextLeft then " LEFT JOIN " else " JOIN "
              tname = head $ fmap (\i -> label . justError ("cant find " ). L.find ((== i) . keyAttr . labelValue  )$ ksbn) (S.toList ifk )
              ksn@(TB1 (KV (PK npk ndesc) nattr)) = preLabelTable ( "(" <> label tas <> ")")  nextT
              nkv pk desc attr = (TB1 (KV (PK (fst pk) (fst desc)) (fst attr)), foldl mappend "" $ snd pk <> snd desc <> snd attr)
          (tb,q) <-liftA3 nkv (fun ksn $ fmap getCompose npk) (fun ksn $ fmap getCompose ndesc) (fun ksn $ fmap getCompose nattr)
          let query = jt <> " LATERAL (SELECT array_agg(ROW(" <> (T.intercalate ","  (fmap explodeLabel $ (F.toList $ unlb1 $ tb ) )) <> " ) order by arrrow ) as " <> label kas <> " FROM  (SELECT * FROM (SELECT *,row_number() over () as arrrow FROM UNNEST(" <> tname  <> ") as arr) as arr ) "<> label tas <> q <> " )  as " <>  label tas <> " ON true"
          return $ ( [Compose $ Labeled (label $ kas) $ IT (head $ S.toList ifk)  (mapOpt $ mapArray tb ) ]  ,query )
    | otherwise = do
          let tname = head $ fmap (\i -> label . justError ("cant find " ). L.find ((== i) . keyAttr . labelValue  )$ ksbn) (S.toList ifk )
              ksn@(TB1 (KV (PK npk ndesc) nattr)) = preLabelTable ( "(" <> tname <> ")")  nextT
              nkv pk desc attr = (TB1 (KV (PK (fst pk) (fst desc)) (fst attr)), foldl mappend "" $ snd pk <> snd desc <> snd attr)
          (tb,q) <-liftA3 nkv (fun ksn $ fmap getCompose npk) (fun ksn $ fmap getCompose ndesc) (fun ksn $ fmap getCompose nattr)
          return $ ( [Compose $ Unlabeled $ IT  (head $ S.toList ifk) (mapOpt tb) ]  ,q)
    where
        nextLeft =  isLeft || isLeftRel ifk
        mapArray i =  if isArrayRel ifk then ArrayTB1 [i] else i
        mapOpt i = if isLeftRel ifk then  LeftTB1 $ Just  i else i
        nextT = justError ("recursepath lookIT "  <> show t <> " " <> show invSchema) (M.lookup t invSchema)
        fun =  recurseTB invSchema nextT nextLeft

recursePath' isLeft ksbn invSchema (Path ifk jo@(FKJoinTable w ks tn) e)
    | isArrayRel  ifk   =   do
          (nt,ksn@(TB1 (KV (PK npk ndesc) nattr)),nq) <- labelTable nextT
          let
              nkv pk desc attr = ( TB1 (KV (PK (fst pk) (fst desc)) (fst attr)), foldl mappend "" $ snd pk <> snd desc <> snd attr)
          (tb,q) <-liftA3 nkv (fun ksn $ fmap getCompose npk) (fun ksn $ fmap getCompose ndesc) (fun ksn $ fmap getCompose nattr)

          tas <- tname nextT
          let knas =(Key (rawName nextT) Nothing (unsafePerformIO newUnique) (Primitive "integer" ))
          kas <- kname tas  knas
          let jt = if nextLeft  then " LEFT JOIN " else " JOIN "
              query =  jt <> " LATERAL (SELECT " <> "array_agg(ROW(" <> (T.intercalate ","  (fmap explodeLabel $ (F.toList $ unlb1 $ tb ) )) <> " )order by arrrow) as " <> label (kas) <> " FROM ( SELECT * FROM (SELECT *,row_number() over () as arrrow FROM UNNEST(" <> label (head (look (fst <$> ks) (ksbn) ))  <> ") as arr) as z1 "  <> jt <> nq  <> " ON " <>  label (head (look (snd <$> ks) (F.toList $ unlb1 ksn) )) <> " = arr ) as z1 " <>  q <>   "  ) as " <>  label tas  <> " ON true "
          return $ ([Compose $ Labeled (label $ kas) (FKT (fmap (\i -> Compose . justError ("cant find " ). L.find ((== i) . keyAttr . labelValue  )$ ksbn) (S.toList ifk )) (isPathReflexive jo ) ks  (mapOpt $ mapArray tb  )) ] , query)

    | otherwise = do
          (nt,ksn@(TB1 (KV (PK npk ndesc) nattr)),nq) <- labelTable nextT
          let pksn = (_pkKey $ _kvKey $ unlb1 ksn )
              nkv pk desc attr = (mapOpt $ TB1 (KV (PK (fst pk) (fst desc)) (fst attr)), foldl mappend "" $ snd pk <> snd desc <> snd attr)
          (tb,q) <-liftA3 nkv (fun ksn $ fmap getCompose npk) (fun ksn $ fmap getCompose ndesc) (fun ksn $ fmap getCompose nattr)
          let jt = if nextLeft  then " LEFT JOIN " else " JOIN "
          return ([Compose $ Unlabeled $ FKT (fmap (\i -> Compose . justError ("cant find " ). L.find ((== i) . keyAttr . labelValue  )$ ksbn) (S.toList ifk )) (isPathReflexive jo ) ks tb]  , jt <> nq <> " ON "  <> joinLPredicate (fkm ksbn pksn) <> q )
  where
        joinLPredicate   =   T.intercalate " AND " . fmap (\(l,r)->  intersectionOpK (keyAttr . labelValue $ l) (keyAttr . labelValue $ r) (label l)  (label r ))
        fkm m n = zip (look (fst <$> ks) m) (look (snd <$> ks) n)
        look ki i = justError ("missing FK on " <> show (ki,ks ,keyAttr . labelValue <$> i )  ) $ allMaybes $ fmap (\j-> L.find (\v -> keyAttr (labelValue v) == j) i  ) ki
        nextT = (\(Just i)-> i) (M.lookup tn (invSchema))
        nextLeft = any (isKOptional.keyType) (S.toList ifk) || isLeft
        mapArray i =  if isArrayRel ifk then ArrayTB1 [i] else i
        mapOpt i = if isLeftRel  ifk then  LeftTB1 $ Just  i else i
        fun =  recurseTB invSchema nextT nextLeft

isLeftRel ifk = any (isKOptional.keyType) (S.toList ifk)
isArrayRel ifk = any (isArray.keyType) (S.toList ifk)

pathRel (Path _ rel _ ) = rel
pathRelRef (Path ifk _ _ ) = ifk
pathRelStore (Path _ _ ifk ) = ifk

recurseTB invSchema  nextT nextLeft ksn items =  do
                  let
                      fkSet = S.unions $ fmap pathRelRef $ filter ( isPathReflexive . pathRel) $ S.toList (rawFKS nextT)
                      eitherSet = S.unions $ fmap pathRelRef $ filter ( isPathEither . pathRel) $  S.toList (rawFKS nextT)
                      nonFKAttrs :: [TBLabel  () ]
                      nonFKAttrs = fmap Compose $ filter (\i -> not $ S.member (keyAttr .labelValue $ i) fkSet) items
                      itemSet :: S.Set Key
                      itemSet = S.fromList $ fmap (keyAttr .labelValue) items
                  pt <- mapM (recursePath' nextLeft (F.toList .unlb1 $ ksn ) invSchema) (filter (\(Path ifk jo  _) ->  ifk `S.isSubsetOf`  itemSet ) $ filter (not. isPathEither . pathRel) (F.toList $ rawFKS nextT ))
                  let
                      nonEitherAttrs = filter (\i -> not $ S.isSubsetOf (S.fromList $ kattrl $ i) eitherSet) (nonFKAttrs <> (concat $  fst <$> pt) )
                  pt2 <- mapM (recursePath' nextLeft (fmap getCompose $ nonFKAttrs<> (concat $  fst <$> pt) ) invSchema) (filter (\(Path ifk jo  _) ->  ifk `S.isSubsetOf`  itemSet ) $ filter (isPathEither . pathRel) (F.toList $ rawFKS nextT ))
                  return (nonEitherAttrs <> (concat $ fst <$> pt2), snd <$> pt)



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
explodeLabel (Labeled l (Attr _ _)) = l
explodeLabel (Unlabeled (TBEither _  l  _ )) = "ROW(" <> T.intercalate "," (explodeLabel.getCompose<$>  l) <> ")"
explodeLabel (Unlabeled (IT  n t )) =  "ROW(" <> T.intercalate "," (( F.toList $ fmap explodeLabel $ unlb1 t))  <> ")"
explodeLabel (Labeled l (IT  _ _  )) =  l
explodeLabel (Labeled l (FKT i _ _ _ )) = T.intercalate "," (( F.toList $ (explodeLabel. getCompose ) <$> i)) <> "," <> l
explodeLabel (Unlabeled (FKT i refl rel t )) = T.intercalate "," (( F.toList $ (explodeLabel.getCompose) <$> i)) <> ", ROW(" <> T.intercalate "," (( F.toList $ fmap explodeLabel $ unlb1 t))  <> ")"

unTlabel (TB1 kv)  = TB1 $ fmap (Compose . Identity .unlabel) $ fmap getCompose kv
unTlabel (LeftTB1 kv)  = LeftTB1 $ fmap unTlabel kv
unTlabel (ArrayTB1 kv)  = ArrayTB1 $ fmap unTlabel kv
unlabel (Labeled l (IT tn t) ) = (IT tn (unTlabel t ))
unlabel (Unlabeled (IT tn t) ) = (IT tn (unTlabel t ))
unlabel (Unlabeled (TBEither  n l  b ) ) = TBEither n (relabel <$> l)   (fmap relabel b)
unlabel (Labeled l (FKT i refl fkrel t) ) = (FKT (fmap relabel i) refl fkrel (unTlabel t ))
unlabel (Unlabeled (FKT i refl fkrel t) ) = (FKT (fmap relabel i) refl fkrel (unTlabel t))
unlabel (Labeled l (Attr k i )) = Attr k i

relabel = Compose . Identity . unlabel.getCompose

type TBLabel =  Compose (Labeled Text) (TB (Labeled Text) Key)
type TBIdent =  Compose Identity  (TB Identity Key )



-- interval' i j = Interval.interval (ER.Finite i ,True) (ER.Finite j , True)
inf' = (\(ER.Finite i) -> i) . Interval.lowerBound
sup' = (\(ER.Finite i) -> i) . Interval.upperBound


unSOptional (SOptional i) = i
unSOptional i = traceShow ("unSOptional No Pattern Match SOptional-" <> show i) Nothing

unSSerial (SSerial i) = i
unSSerial i = traceShow ("unSSerial No Pattern Match SSerial-" <> show i) Nothing

unRSOptional (SOptional i) = join $ fmap unRSOptional i
unRSOptional i = traceShow ("unRSOptional No Pattern Match SOptional-" <> show i) Nothing

unRSOptional2 (SOptional i) = join $ unRSOptional' <$> i
unRSOptional2 i   = Just i

unRSOptional' (SOptional i) = join $ unRSOptional' <$> i
unRSOptional' (SSerial i )  = join $ unRSOptional' <$>i
unRSOptional' i   = Just i

_unTB1 (TB1 i ) =  i
_unTB1 (LeftTB1 (Just i )) = _unTB1 i
_unTB1 i =  errorWithStackTrace $ show i


allMaybes i | F.all (const False) i  = Nothing
allMaybes i = if F.all isJust i
        then Just $ fmap (justError "wrong invariant allMaybes") i
        else Nothing

makeOpt (Key a  c d ty) = (Key a  c d (KOptional ty))

zipWithTF g t f = snd (mapAccumL map_one (F.toList f) t)
    where map_one (x:xs) y = (xs, g y x)
