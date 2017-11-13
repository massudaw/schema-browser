{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE UndecidableInstances #-}
module Postgresql.Printer
  (selectQuery
  ,tableType
  ,codegen
  ,expandBaseTable
  ,explodeRecord
  ,renderType
  ,createTable
  ,dropTable
  ,escapeReserved
  )
  where

import Query
import Debug.Trace
import Postgresql.Codegen
import Database.PostgreSQL.Simple
import RuntimeTypes
import qualified Types.Index as G
import qualified Control.Lens as Le
import Postgresql.Types
import Data.Time
import Types.Patch
import Data.Ord
import Types.Index (TBIndex(..),AttributePath(..))
import Data.String
import Step.Host (findFK,findAttr,findFKAttr)
import qualified Data.Interval as I
import Step.Common
import NonEmpty (NonEmpty(..))
import Data.Functor.Apply
import Data.Bifunctor
import qualified Data.Foldable as F
import qualified Data.Traversable as Tra
import Data.Maybe
import System.IO.Unsafe
import Data.Monoid hiding (Product)

import qualified Data.Text as T

import Utils

import Prelude hiding (head)
import Control.Monad
import Control.Monad.RWS
import Control.Applicative
import Data.Functor.Identity
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Text (Text)
import GHC.Stack

import Types
import Types.Inference

--
-- Patch CRUD Postgresql Operations
--

data Relation k
  = RelInline k
  | RelFK [Rel k]
  deriving(Eq,Ord)

data Address k
  = Root (KVMetadata k)
  | TableReference (Relation k) (Address k )
  | AttributeReference k
  deriving(Eq,Ord)


type NameMap = (Int,Int,M.Map (Address Key) Int)
type Codegen = RWS (Address  Key) String NameMap

newTable m = do
  (i,k,j) <- get
  path <- ask
  put (i+1,k,M.insert (Root m) (i+1)  j)
  return (i+1)

tableLabel :: (MonadState
                  (Int, Int, M.Map (Address k) Int)
                  (RWST (Address Key) String NameMap Identity), Ord k) => KVMetadata k -> Codegen Text
tableLabel m = do
  (i,k,j) <- get
  path <- ask
  return $ "t" <> T.pack ( show (justError "no table" (M.lookup (Root m) j )))

deriving instance (Show ((Labeled Text)(TB (Labeled Text)k a )), Show (FTB1 (Labeled Text) k a), Show (FTB a), Show a, Show k) =>Show (TB (Labeled Text)k a)

dropTable :: Table -> Text
dropTable r= "DROP TABLE "<> rawFullName r

-- createTable :: Table -> Text
createTable r = "CREATE TABLE " <> rawFullName r  <> "\n(\n\t" <> T.intercalate ",\n\t" commands <> "\n)"
  where
    commands = (renderAttr <$> S.toList (rawAttrs r) ) <> [renderPK] <> fmap renderFK (S.toList $ rawFKS r)
    renderAttr k = keyValue k <> " " <> render (keyType k) <> if  (isKOptional (keyType k)) then "" else " NOT NULL"
    renderKeySet pk = T.intercalate "," (fmap keyValue (S.toList pk ))
    render (Primitive l ty ) = ty <> renderTy l
      where
        renderTy (KOptional :ty) = renderTy ty <> ""
        renderTy (KSerial :ty) = renderTy ty <> ""
        renderTy (KInterval :ty) = renderTy ty <> ""
        renderTy (KArray :ty) = renderTy ty <> "[] "
    -- renderTy (InlineTable s ty ) = s <> "." <> ty
    renderPK = "CONSTRAINT " <> tableName r<> "_PK PRIMARY KEY (" <>  renderKeySet (S.fromList $ rawPK r) <> ")"
    -- renderFK (Path origin (FKJoinTable  ks (_,table)) ) = "CONSTRAINT " <> tbl <> "_FK_" <> table <> " FOREIGN KEY " <>  renderKeySet origin <> ") REFERENCES " <> table <> "(" <> renderKeySet end <> ")  MATCH SIMPLE  ON UPDATE  NO ACTION ON DELETE NO ACTION"
    renderFK (Path origin _  ) = ""



reservedNames = ["column","table","schema"]

escapeReserved :: T.Text -> T.Text
escapeReserved i = if i `elem` reservedNames then "\"" <> i <> "\"" else i

expandInlineTable :: TB3Data (Labeled Text) Key () -> Text -> Codegen Text
expandInlineTable tb@(meta, _) pre = do
  t <- newTable meta
  let
    query = "(SELECT " <>  T.intercalate "," (aliasKeys  <$> (filter (not .isFun) $ fmap getCompose (sortPosition name) ))  <> ") as t" <> (T.pack (show t))
    name =  tableAttr tb
    isFun  (Labeled a (Fun _ _ _ )) = True
    isFun  _ = False
    aliasKeys (Labeled  a (Attr n    _ ))  =  "(" <> pre <> ")." <> keyValue n <> " as " <> a
  return query


expandInlineArrayTable ::  TB3Data (Labeled Text) Key  () -> Text -> Codegen (Text,Text)
expandInlineArrayTable tb@(meta, KV i) pre = do
   tidx <- newTable meta
   let query = "(SELECT " <>  T.intercalate "," (aliasKeys  . getCompose <$>   sortPosition name)  <> ",row_number() over () as row_number FROM UNNEST(" <> pre <> ") as ix ) " <> t
       name =  tableAttr tb
       t =  "t" <> T.pack (show tidx)
       aliasKeys (Labeled  a (Attr n  _ ))  =  "(ix)." <> keyValue n <> " as " <> a
   return (t,query)

sortPosition = L.sortBy (comparing (maximum . fmap (keyPosition ._relOrigin) .keyattr))

expandBaseTable ::  TB3Data  (Labeled Text) Key  () -> Codegen Text
expandBaseTable tb@(meta, KV i) = do
  tidx <- newTable meta
  let
     query = "(SELECT " <>  T.intercalate "," (aliasKeys  . getCompose <$> ( sortPosition name)) <> " FROM " <> aliasTable <> ") as " <> t
     t =  "t" <> T.pack (show tidx)
     name =  tableAttr tb
     aliasTable = kvMetaFullName meta <> " as " <> t
     aliasKeys (Labeled  a (Attr n    _ ))  =  t <> "." <> keyValue n <> " as " <> a
     aliasKeys (Labeled a (IT n _ ))  = t <> "." <> keyValue n <> " as " <> a
     aliasKeys _  = ""
  return query


getInlineRec' tb = L.filter (\i -> match $  unComp i) $ attrs
  where attrs = F.toList $ _kvvalues  (snd tb)
        match (Attr _ _ ) = False
        match (IT _ i ) = isTableRec' (unTB1 i)


expandTable ::  TB3Data  (Labeled Text) Key  () -> Codegen Text
expandTable tb
  | isTableRec' tb = errorWithStackTrace "no rec support"
  | otherwise = expandBaseTable  tb




codegen t l = traceShowId $ fst $ evalRWS l (Root (fst t)) (0,0,M.empty)

selectQuery
  :: (KVMetadata Key,
        (KV (Compose (Labeled Text) (TB (Labeled Text))))
        Key
        ())
     -> Maybe [I.Extended (FTB Showable)]
     -> [(Key, Order)]
     -> WherePredicate
     -> (Text,Maybe [Either (TB Identity Key Showable) (PrimType ,FTB Showable)])
selectQuery t koldpre order wherepred = (withDecl, (fmap Left <$> ordevalue )<> (fmap Right <$> predvalue))
      where
        withDecl = codegen t (traceShow t tableQuery)
        tableQuery = do
            tname <- expandTable t
            tquery <- expandQuery' False t
            rec <- explodeRecord t
            return $ "SELECT " <> rec <> " FROM " <>  renderRow (tquery (SQLRInline tname)) <> pred <> orderQ
        (predquery , predvalue ) = case wherepred of
              WherePredicate wpred -> printPred t wpred
        pred = maybe "" (\i -> " WHERE " <> T.intercalate " AND " i )  ( orderquery <> predquery)
        (orderquery , ordevalue) =
          let
            unIndex i  = catMaybes $ zipWith  (\i j -> (i,) <$> j) (_kvpk (fst t)) $ fmap unFin  i
            unFin (I.Finite i) = Just i
            unFin j = Nothing
            oq = (\i ->  pure $ generateComparison (first (justLabel t) <$> (filter ((`elem` (fmap fst i)).fst) order))) . unIndex<$> koldpre
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


expandQuery left (ArrayTB1 (t:| _) ) =  expandQuery left t
expandQuery left (LeftTB1 (Just t)) =  expandQuery left t
expandQuery left (TB1 t)
    | otherwise   = expandQuery' left t

expandQuery' left (meta, m) = foldr (\i -> liftA2 (.) (expandJoin left (F.toList (_kvvalues  m) ) i )  ) (return id) (getCompose <$> F.toList (_kvvalues  m))

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

expandJoin :: Bool -> [Compose (Labeled Text) (TB (Labeled Text)) Key ()] -> Labeled Text (TB (Labeled Text) Key ()) -> Codegen (SQLRow -> SQLRow)
-- expandJoin i j k | traceShow (i,j,k) False = undefined
expandJoin left env (Unlabeled  (IT i (LeftTB1 (Just tb) )))
    = expandJoin True env $ Unlabeled (IT i tb)
expandJoin left env (Labeled l (IT i (LeftTB1 (Just tb) )))
    = expandJoin True env $ Labeled l (IT i tb)
expandJoin left env (Labeled l (IT a (ArrayTB1 (tb :| _ ) )))
    = do
    (tas,itb) <- expandInlineArrayTable (unTB1 tb) l
    tjoin <- expandQuery left tb
    r <- explodeRow tb
    let joinc = " (SELECT array_agg(" <> r <> "  order by row_number) as " <> tas <> (renderRow  $ tjoin (SQLRInline $ " FROM " <>  itb )) <> " )  as p" <>  tas
    return $ (\row -> SQLRJoin row JTLateral jt (SQLRInline joinc) Nothing)
        where
          jt = if left then JDLeft  else JDNormal
expandJoin left env (Labeled l (IT a (TB1 tb))) =  do
     tjoin <- expandQuery' left tb
     itable <- expandInlineTable  tb  l
     return $  tjoin . (\row -> SQLRJoin row JTLateral jt  (SQLRInline itable) Nothing)
        where
          jt = if left then JDLeft  else JDNormal
expandJoin left env v = return id

joinOnPredicate :: [Rel Key] -> [Labeled Text ((TB (Labeled Text))  Key ())] -> [Labeled Text ((TB (Labeled Text))  Key ())] -> Text
joinOnPredicate ks m n =  T.intercalate " AND " $ (\(Rel l op r) ->  intersectionOp (keyType . keyAttr . labelValue $ l) op (keyType . keyAttr . labelValue $ r) (label l)  (label r )) <$> fkm
    where fkm  = (\rel -> Rel (look (_relRoot rel ) m) (_relOperator rel) (look (_relTarget rel ) n)) <$>  ks
          look ki i = justError ("missing FK on " <> show (ki,ks ,keyAttr . labelValue <$> i )) $ (\j-> L.find (\v -> keyAttr (labelValue v) == j) i  ) ki

inner :: Text -> Text -> Text -> Text
inner b l m = l <> b <> m

intersectionOp :: (Eq b,Show b,Show (KType (Prim KPrim b ))) => KType (Prim KPrim b)-> BinaryOperator -> KType (Prim KPrim b)-> (Text -> Text -> Text)
intersectionOp i op (Primitive (KOptional :xs) j) = intersectionOp i op (Primitive xs j)
intersectionOp (Primitive (KOptional :xs) i) op j = intersectionOp (Primitive xs i)  op j
intersectionOp (Primitive [] j) op (Primitive (KArray :_) i )
  | isPrimReflexive i j = (\i j  -> i <> renderBinary op <> "(" <> j <> ")" )
  | otherwise = errorWithStackTrace $ "wrong type intersectionOp * - {*} " <> show j <> " /= " <> show i
intersectionOp i op j = inner (renderBinary op)





explodeRow :: TB3 (Labeled Text) Key () -> Codegen Text
explodeRow = explodeRow'
explodeRecord :: TB3Data (Labeled Text) Key () -> Codegen Text
explodeRecord  = explodeRow''

block  = (\i -> "ROW(" <> i <> ")")
assoc = ","
leaf = const id

leafDel True i = " case when " <> i <> " is not null then true else null end  as " <> i
leafDel False i = " case when " <> i <> " is not null then true else null end  as " <> i

explodeRow' (LeftTB1 (Just tb) ) = explodeRow' tb
explodeRow' (ArrayTB1 (tb:|_) ) = explodeRow' tb
explodeRow' (TB1 i ) = explodeRow'' i

-- explodeRow'' t@(m ,KV tb) = do
-- block . T.intercalate assoc <$> (traverse (explodeDelayed t .getCompose)  $ traceShowId $ sortPosition $F.toList  tb  )
explodeRow'' t@(m ,KV tb) = sel . T.intercalate assoc <$> (traverse (explodeDelayed t .getCompose)  $ traceShowId $ sortPosition $F.toList  tb  )
  where sel i = "(select p" <> (_kvname m) <> " from (select " <> i<>  ") as p" <> (_kvname m) <> ")"

replaceexpr :: Expr -> [Text]  -> Text
replaceexpr k ac = go k
  where
    go :: Expr -> Text
    go (Function i e) = i <> "(" <> T.intercalate ","  (go   <$> e) <> ")"
    go (Value i ) = (ac !! i )

explodeDelayed tb (Labeled l (Fun k (ex,a)  _ )) =  replaceexpr ex <$> traverse (\i -> explodeDelayed tb $ indexLabel i tb) a -- leaf (isArray (keyType k)) l
explodeDelayed _ (Labeled l (Attr k  _ ))
  | isKDelayed (keyType k) = return $ leafDel (isArray (keyType k)) l
  | otherwise =  return $ leaf (isArray (keyType k)) l
explodeDelayed _ (Labeled l (Attr k  _ ))
  | isKDelayed (keyType k) = return $ leafDel (isArray (keyType k)) l
  | otherwise =  return $ leaf (isArray (keyType k)) l
explodeDelayed _ (Unlabeled (Attr k  _ )) =return $  leaf (isArray (keyType k))  (keyValue k)

explodeDelayed _ (Unlabeled (IT  n t )) =  explodeRow' t
explodeDelayed rec (Labeled l (IT  k (LeftTB1 (Just tb  )))) = explodeDelayed rec (Labeled l (IT k tb))
explodeDelayed _ (Labeled l (IT  _ (ArrayTB1 (TB1 tb :| _) ) )) = do
  m <- tableLabel (fst $ tb)
  return $ leaf False m
explodeDelayed _ (Labeled l (IT  _ t  )) = explodeRow' t
explodeDelayed tbenv  (Labeled l (FKT ref  _ _ )) = case unkvlist ref of
             [] -> return $ leaf False l
             i -> (\v -> T.intercalate assoc v <> assoc <> leaf False l) <$> traverse (explodeDelayed tbenv . getCompose) i
explodeDelayed tb (Unlabeled (FKT ref rel t )) = case unkvlist ref of
             [] -> explodeRow' t
             i -> (\v l -> T.intercalate assoc v <> assoc <> l ) <$> traverse (explodeDelayed tb .getCompose ) i <*> explodeRow' t


printPred :: TB3Data (Labeled Text)  Key ()->  BoolCollection (Access Key ,AccessOp Showable ) -> (Maybe [Text],Maybe [(PrimType,FTB Showable)])
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

renderType (Primitive (KInterval :xs) t ) =
  case t of
    (AtomicPrim (PInt i)) ->  case i of
      4 -> "int4range"
      8 -> "int8range"
    (AtomicPrim (PTime (PDate))) -> "daterange"
    (AtomicPrim (PTime (PTimestamp i))) -> case i of
      Just i -> "tsrange"
      Nothing -> "tstzrange"
    (AtomicPrim (PGeom ix i)) ->
       case ix of
            2 ->  "box2d"
            3 ->  "box3d"

    (AtomicPrim PDouble) -> "floatrange"
    i -> Nothing
renderType (Primitive [] (RecordPrim (s,t)) ) = Just $ s <> "." <> t
renderType (Primitive [] (AtomicPrim t) ) =
  case t  of
    PBinary -> "bytea"
    PDynamic -> "bytea"
    PDouble -> "double precision"
    PDimensional _ _ -> "dimensional"
    PText -> "character varying"
    PInt v -> case v of
      2 -> "smallint"
      4 -> "integer"
      8 -> "bigint"
      v -> errorWithStackTrace ("no index" ++ show   v)
    PTime i -> case i of
      PDate -> "date"
      PTimestamp v -> case v of
        Just i -> "timestamp without time zone"
        Nothing -> "timestamp with time zone"
    i -> Nothing
renderType (Primitive (KArray :xs)i) = (<>"[]") <$> renderType (Primitive xs i)
renderType (Primitive (KOptional :xs)i) = renderType (Primitive xs i)
renderType (Primitive (KSerial :xs)i) = renderType (Primitive xs i)
renderType (Primitive (KDelayed :xs)i) = renderType (Primitive xs i)


instance IsString (Maybe T.Text) where
  fromString i = Just (fromString i)

-- inferParamType e i |traceShow ("inferParam"e,i) False = undefined
inferParamType op i = maybe "" (":: " <>) $ renderType $  inferOperatorType op i

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
indexLabel  n@(Nested l (Many [One nt])) v =
  case   findFK (iprodRef <$> l) v of
      Just a ->  case getCompose a of
        Unlabeled i -> indexLabel  nt.head . F.toList . _fkttable $ i
        Labeled i _ -> errorWithStackTrace ("cant index" <> show i)
      Nothing -> errorWithStackTrace ("cant index"<> show l)
-- indexLabel  (ISum [nt]) v = flip (indexLabel ) v <$> nt
indexLabel  i v = errorWithStackTrace (show (i, v))

indexLabelU  (Many [One nt]) v = flip (indexLabel ) v $ nt



indexFieldL
    ::  AccessOp Showable
    -> [Text]
    -> Access Key
    -> TB3Data (Labeled Text) Key ()
    -> [(Maybe Text, Maybe (PrimType ,FTB Showable))]
-- indexFieldL e c p v | traceShow (e,c,p) False = undefined
indexFieldL e c p@(IProd b l) v =
    case findAttr l v of
      Just i -> [utlabel  e c (tlabel' . getCompose $ i)]
      Nothing ->
            case
                   fmap getCompose $ findFK [l] v of

                Just (Unlabeled i) ->
                    case i of
                        (FKT ref _ _) ->
                            (\l ->
                                  utlabel e c.tlabel' . getCompose.
                                  justError ("no attr" <> show (ref, l)) .
                                  L.find
                                      ((== [l]) .
                                       fmap (_relOrigin) . keyattr) $
                                  unkvlist ref) <$>
                                    [l]
                        i -> errorWithStackTrace "no fk"
    -- Don't support filtering from labeled queries yet just check if not null for all predicates
    -- TODO: proper check  accessing the term
                Just (Labeled i _) -> [(Just (i <> " is not null"), Nothing)]
                Nothing -> case findFKAttr [l] v of
                             Just i -> [utlabel e  c (tlabel' . getCompose $i)]
                             Nothing  -> errorWithStackTrace ("no fk attr" <> show (l,v))

indexFieldL e c n@(Nested l nt) v =
  case findFK (iprodRef <$> l) v of
    Just a -> case getCompose a of
        Unlabeled i ->
          concat . fmap (indexFieldLU e c nt) . F.toList . _fkttable $ i
        Labeled l (IT k (LeftTB1 (Just (ArrayTB1 (fk :| _))))) ->  [(Just (l <> " is not null"), Nothing)]
        Labeled l (IT k (ArrayTB1 (fk :| _))) ->  [(Just (l <> " is not null"), Nothing)]
        Labeled l (IT k fk) -> indexFieldLU e c nt  $ head (F.toList fk )
        Labeled l a -> [(Just (l <> " is not null"), Nothing)]

    Nothing -> concat $ (\i -> indexFieldL (Right (Not IsNull)) c i v)<$> l

indexFieldL e c i v = errorWithStackTrace (show (i, v))

indexFieldLU e c (Many nt) v = concat $ flip (indexFieldLU e c) v <$> nt
indexFieldLU e c (ISum nt) v = concat $ flip (indexFieldLU e c) v <$> nt
indexFieldLU e c (One nt) v = flip (indexFieldL e c) v  nt

utlabel (Right  e) c idx = result e idx
  where
    opvalue  ref i  =  T.intercalate "." (c ++ [ref])  <> " is " <> renderUnary i

    result (Not (Not l)) v=  result l v
    result (Not l) v= first (fmap (\i -> "not (" <> i <> ")"))  $ result l v
    result (BinaryConstant b i) v =  utlabel (Left (generateConstant i ,b)) c v
    result (Range  b l) (ty,v) = result l (unKInterval ty,(((if b then "upper" else "lower") <> "(" <> T.intercalate "." (c ++ [v])   <> ")" ) ) )
    result i v =  (Just $  opvalue (snd v) i   ,Nothing )
    unKInterval =alterKeyType (\(Primitive (KInterval :xs) i) -> Primitive xs i)
utlabel (Left (value,e)) c idx = result
  where
    notFlip (Flip i) = False
    notFlip i = True
    operator i = errorWithStackTrace (show i)
    opvalue re  (Flip (Flip i)) = opvalue re i
    opvalue ref (Flip (AnyOp (AnyOp Equals)))  = T.intercalate "." (c ++ [ref]) <> " " <>  "<@@" <>  " ANY( ? " <> ")"
    opvalue ref (AnyOp i)  = case ktypeRec ktypeUnLift  (keyType (fst idx)) of
                              Just _-> T.intercalate "." (c ++ [ref]) <>  unliftOp (AnyOp i) (keyType (fst idx))<>  " ? " <> inferParamType i ( keyType (fst idx))
                              Nothing  ->recoverop (keyType (fst idx))
        where
          recoverop (Primitive (KOptional :xs) i) = recoverop (Primitive xs i)
          recoverop (Primitive (KArray :xs) (AtomicPrim (PGeom ix (PPosition )))) =  " ? "  <> inferParamType (AnyOp i) (keyType (fst idx)) <>  "&&" <>  T.intercalate "." (c ++ [ref])
          recoverop _ =  " ? "  <> inferParamType (AnyOp i) (keyType (fst idx)) <> renderBinary (Flip i) <> " ANY(" <> T.intercalate "." (c ++ [ref])<> ")"
    opvalue ref (Flip (AnyOp i))  = T.intercalate "." (c ++ [ref]) <> renderBinary i <>  " ANY( " <> " ? " <>  ")"
    opvalue ref i =  T.intercalate "." (c ++ [ref]) <>  unliftOp i (keyType (fst idx))<>  " ? " <> inferParamType i ( keyType (fst idx))
    -- opparm ref | traceShow ("opparam",ref) False = undefined
    opparam e = Just $ (inferOperatorType e (keyType  $fst idx ) ,value)
    result =  ( Just $  (opvalue (snd $ idx) e)   ,opparam e )

unliftOp :: BinaryOperator -> PrimType -> Text
unliftOp  op ty =   recurseOp recinf op  recty
  where infered = inferOperatorType op  ty
        recinf = (fromMaybe infered $ ktypeRec ktypeUnLift infered )
        recty = (fromMaybe ty $ktypeRec ktypeUnLift ty)

recurseOp :: PrimType -> BinaryOperator -> PrimType -> Text
recurseOp (Primitive (KOptional :xs) i) o k = recurseOp (Primitive xs i) o k
recurseOp i o (Primitive (KOptional :xs) k) = recurseOp i o (Primitive xs k)
recurseOp i (Flip (Flip o)) k = recurseOp i o k
-- recurseOp i (Flip o)  k = recurseOp k o i
recurseOp i o k | isJust rw =  justError "rw" rw
  where rw = M.lookup (i,o,k)  rewriteOp
recurseOp i o k = renderBinary o

tlabel' (Labeled l (Attr k _)) =  (k,l)
tlabel' (Labeled l (IT k tb )) =  (k,l <> " :: " <> tableType tb)
tlabel' (Unlabeled (Attr k _)) = (k,keyValue k)


getLabels t k =  M.lookup  k (mapLabels label' t)
    where
          label' i | traceShow i  False = undefined
          label' (Labeled l (Attr k _)) =  (k,l )
          label' (Labeled l (IT k tb )) = (k, l <> " :: " <> tableType tb)
          label' (Unlabeled (Attr k _)) = (k,keyValue k)


mapLabels label' t =  M.fromList $ fmap (label'. getCompose) (getAttr $ joinNonRef' t)




