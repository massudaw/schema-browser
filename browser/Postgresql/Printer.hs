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
  ,NameMap
  ,CodegenT
  ,Address(..)
  ,selectRow
  ,lkTB
  ,atTable
  )
  where

import Query
import Debug.Trace
import Postgresql.Codegen
import Database.PostgreSQL.Simple
import RuntimeTypes
import qualified Data.Poset as P
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
  deriving(Eq,Ord,Show)

data Address k
  = Root (KVMetadata k)
  | TableReference (Relation k)
  | AttributeReference k
  deriving(Eq,Ord,Show)


type NameMap = ((Int,M.Map [Address Key] Int),(Int,M.Map [Address Key] Int))
type CodegenT m = RWST [Address Key] String NameMap m
type Codegen = RWST [Address Key] String NameMap Identity


mkKey i = do
  (c,m) <- snd <$> get
  path <- ask
  let next = (c+1,M.insert (path ++ [i]) (c+1) m)
  modify (\(j,_) -> (j,next))
  return (c+1)

mkTable i = do
  (c,m) <- fst <$> get
  path <- ask
  let next = (c+1,M.insert (path ++ [i]) (c+1) m)
  modify (\(_,j) -> (next,j))
  return (c+1)

atTable m = local (++ [Root m])


lkKey i = do
  (c,m) <- snd <$> get
  path <- ask
  return $ M.lookup (path ++ [i]) m

newAttr k = mkKey (AttributeReference k)

lkTB (Attr k _) = do
  a<- lkAttr k
  return $ case a of
    Just a -> "k" <> T.pack (show a)
    Nothing ->  keyValue k

lkTB (IT k _ ) = do
  a <-lkIT k
  return $ case a of
    Just a -> "k" <> T.pack (show a)
    Nothing -> keyValue k

lkTB (FKT  _ rel _ ) = do
  a <- lkFK rel
  return $ case a of
    Just a -> "k" <> T.pack (show a)
    Nothing -> error ""

lkAttr k = lkKey (AttributeReference k)

newIT k = mkKey (TableReference $ RelInline k)
lkIT k = lkKey (TableReference $ RelInline k)

newFK k = mkKey (TableReference $ RelFK k)
lkFK k = lkKey (TableReference $ RelFK k)

newTable m = mkTable (Root m)

tableLabel :: (MonadState
                  (Int, Int, M.Map [Address Key] Int)
                  (RWST [Address Key] String NameMap Identity)) => KVMetadata Key -> Codegen Text
tableLabel m = do
  (i,k,j) <- get
  path <- ask
  return $ "t" <> T.pack (show (justError "no table" (M.lookup (path++[Root m]) j )))


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
    renderFK _ = ""



reservedNames = ["column","table","schema"]

escapeReserved :: T.Text -> T.Text
escapeReserved i = if i `elem` reservedNames then "\"" <> i <> "\"" else i

expandInlineTable :: TBData  Key () -> Text -> Codegen SQLRow
expandInlineTable tb@(meta, _) pre = asNewTable meta $ (\t->  do
  let
    name =  tableAttr tb
    aliasKeys (Attr n    _ )  =  do
      a <- newAttr n
      return $ SQLARename (SQLAIndexAttr (SQLAReference Nothing ("i" <> pre) ) ( keyValue n)) ("k" <>T.pack (show a))
    aliasKeys (IT n _ )  =    do
      a <- newIT  n
      return $ SQLARename (SQLAIndexAttr (SQLAReference Nothing ("i" <> pre )) ( keyValue n)) ("ik"<> T.pack (show a))
  cols <- mapM (aliasKeys )  (sortPosition name)
  return $ SQLRSelect cols Nothing)


expandInlineArrayTable ::  TBData  Key  () -> Text -> Codegen SQLRow
expandInlineArrayTable tb@(meta, KV i) pre = asNewTable meta $ (\t -> do
  let
     rowNumber = SQLARename (SQLAInline "row_number() over ()") "row_number"
     name =  tableAttr tb
     aliasKeys (Attr n    _ )  =  do
       a <- newAttr n
       return $ SQLARename (SQLAIndexAttr (SQLAReference Nothing "ix") ( keyValue n)) ("k" <>T.pack (show a))
     aliasKeys (IT n _ )  =do
       a <- newIT  n
       return $ SQLARename (SQLAIndexAttr (SQLAReference Nothing "ix") ( keyValue n)) ("ik"<> T.pack (show a))
  cols <- mapM (aliasKeys )  (sortPosition name)
  return $ SQLRSelect (cols <> [rowNumber]) (Just $ SQLRRename (SQLRFrom (SQLRUnnest (SQLAReference Nothing  ("i" <> pre)))) "ix" ))

sortPosition = L.sortBy (comparing (maximum . fmap (keyPosition ._relOrigin) .keyattri))

asNewTable meta action = do
  tidx <- newTable meta
  let name =    "t" <> T.pack (show tidx)
  t <- local (++[Root meta]) (action name)
  return $ SQLRRename  t name


expandBaseTable ::  TBData  Key  () -> Codegen SQLRow
expandBaseTable tb@(meta, KV i) = asNewTable meta  (\t -> do
  let
     aliasKeys (at@(Attr n _ )) = do
       a <- newAttr n
       return $ SQLARename (SQLAIndexAttr (SQLAReference Nothing t) ( keyValue n)) ("k"<> T.pack (show a))
     aliasKeys (at@(IT n _ )) = do
       a <- newIT  n
       return $ SQLARename (SQLAIndexAttr (SQLAReference Nothing t) ( keyValue n)) ("ik"<> T.pack (show a))
     name =  tableAttr tb
  cols <- mapM (aliasKeys  )  (sortPosition name)
  return $ SQLRSelect  cols (Just $ SQLRRename (SQLRFrom (SQLRReference (Just $ _kvschema meta) (_kvname meta))) t )
  )


getInlineRec' tb = L.filter (\i -> match $  i) $ attrs
  where attrs = F.toList $ _kvvalues  (snd tb)
        match (Attr _ _ ) = False
        match (IT _ i ) = isTableRec' (unTB1 i)




codegen l =
  case runRWS l [] ((0,M.empty),(0,M.empty)) of
    (q,s,_) -> (q,s)

selectQuery
  :: TBData Key ()
     -> Maybe [I.Extended (FTB Showable)]
     -> [(Key, Order)]
     -> WherePredicate
     -> ((Text,NameMap),Maybe [Either (TB Key Showable) (PrimType ,FTB Showable)])
selectQuery t koldpre order wherepred = (withDecl, (fmap Left <$> ordevalue )<> (fmap Right <$> predvalue))
      where
        withDecl = codegen tableQuery
        tableQuery = do
            tname <- expandBaseTable t
            tquery <- expandQuery' False t
            rec <- explodeRecord t
            return $ "SELECT " <> selectRow "p0" rec <> " FROM " <>  renderRow (tquery tname) <> pred <> orderQ
        (predquery , predvalue ) = case wherepred of
            WherePredicate wpred -> fst $ evalRWS (printPred t wpred) [Root (fst t)] (snd withDecl)
        pred = maybe "" (\i -> " WHERE " <> T.intercalate " AND " i )  (orderquery <> predquery)
        (orderquery , ordevalue) =
          let
            unIndex i  = catMaybes $ zipWith  (\i j -> (i,) <$> j) (_kvpk (fst t)) $ fmap unFin  i
            unFin (I.Finite i) = Just i
            unFin j = Nothing
            oq = (\i ->  pure $ generateComparison (first (justLabel (snd withDecl) t) <$> (filter ((`elem` (fmap fst i)).fst) order))) . unIndex<$> koldpre
            koldPk :: Maybe [TB Key Showable]
            koldPk =  (\k -> uncurry Attr <$> L.sortBy (comparing ((`L.elemIndex` (fmap fst order)).fst)) k ) . unIndex <$> koldpre
            pkParam =  koldPk <> (tail .reverse <$> koldPk)
          in (oq,pkParam)
        orderQ = " ORDER BY " <> T.intercalate "," ((\(l,j)  -> l <> " " <> showOrder j ) . first (justLabel (snd withDecl) t) <$> order)

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

expandQuery' left (meta, m) = atTable meta $ F.foldl (flip (\i -> liftA2 (.) (expandJoin left (F.toList (_kvvalues  m) ) i )  )) (return id) (P.sortBy (P.comparing (RelSort. keyattri )) $  F.toList (_kvvalues  m))

tableType (ArrayTB1 (i :| _ )) = tableType i <> "[]"
tableType (LeftTB1 (Just i)) = tableType i
tableType (TB1 (m,_)) = kvMetaFullName  m




expandJoin :: Bool -> [Column Key ()] -> Column Key () -> Codegen (SQLRow -> SQLRow)
expandJoin left env (IT i (LeftTB1 (Just tb) ))
    = expandJoin True env $ (IT i tb)
expandJoin left env (t@(IT a (ArrayTB1 (tb :| _ ) ))) = do
    l <- lkTB t
    itb <- expandInlineArrayTable (unTB1 tb) l
    tjoin <- expandQuery left tb
    r <- explodeRow tb
    let joinc = " (SELECT array_agg(" <> selectRow "arr" r <> " order by row_number) as " <> l <> " " <> (renderRow  $ tjoin (SQLRFrom  itb )) <> " )  as p" <> l
    return $ (\row -> SQLRJoin row JTLateral jt (SQLRInline joinc) Nothing)
        where
          jt = if left then JDLeft  else JDNormal
expandJoin left env (t@(IT a (TB1 tb))) =  do
     l <- lkTB t
     itable <- expandInlineTable  tb l
     tjoin <- expandQuery' left tb
     return $  tjoin . (\row -> SQLRJoin row JTLateral jt  itable Nothing)
        where
          jt = if left then JDLeft  else JDNormal
expandJoin left env v = return id
  {-
joinOnPredicate :: [Rel Key] -> [Column Key ()] -> [Column Key ()] -> Codegen Text
joinOnPredicate ks m n =  T.intercalate " AND " $ (\(Rel l op r) ->  intersectionOp (keyType . keyAttr . labelValue $ l) op (keyType . keyAttr . labelValue $ r) (label l)  (label r )) <$> fkm
    where fkm  = (\rel -> Rel (look (_relRoot rel ) m) (_relOperator rel) (look (_relTarget rel ) n)) <$>  ks
          look ki i = justError ("missing FK on " <> show (ki,ks ,keyAttr . labelValue <$> i )) $ (\j-> L.find (\v -> keyAttr (labelValue v) == j) i  ) ki
-}
inner :: Text -> Text -> Text -> Text
inner b l m = l <> b <> m

intersectionOp :: (Eq b,Show b,Show (KType (Prim KPrim b ))) => KType (Prim KPrim b)-> BinaryOperator -> KType (Prim KPrim b)-> (Text -> Text -> Text)
intersectionOp i op (Primitive (KOptional :xs) j) = intersectionOp i op (Primitive xs j)
intersectionOp (Primitive (KOptional :xs) i) op j = intersectionOp (Primitive xs i)  op j
intersectionOp (Primitive [] j) op (Primitive (KArray :_) i )
  | isPrimReflexive i j = (\i j  -> i <> renderBinary op <> "(" <> j <> ")" )
  | otherwise = errorWithStackTrace $ "wrong type intersectionOp * - {*} " <> show j <> " /= " <> show i
intersectionOp i op j = inner (renderBinary op)





explodeRow :: TB3 Key () -> Codegen Text
explodeRow = explodeRow'
explodeRecord :: TBData  Key () -> Codegen Text
explodeRecord  = explodeRow''

block  = (\i -> "ROW(" <> i <> ")")
assoc = ","
leaf = id

leafDel i = " case when " <> i <> " is not null then true else null end  as " <> i

explodeRow' (LeftTB1 (Just tb) ) = explodeRow' tb
explodeRow' (ArrayTB1 (tb:|_) ) = explodeRow' tb
explodeRow' (TB1 i ) = explodeRow'' i

-- explodeRow'' t@(m ,KV tb) = do
-- block . T.intercalate assoc <$> (traverse (explodeDelayed t .getCompose)  $ sortPosition $F.toList  tb  )
explodeRow'' t@(m ,KV tb) = atTable m $ T.intercalate assoc <$> (traverse (explodeDelayed t )  $ P.sortBy (P.comparing (RelSort. keyattri ))$ F.toList  tb)

selectRow  l i = "(select rr as " <> l <> " from (select " <> i<>  ") as rr )"

replaceexpr :: Expr -> [Text]  -> Text
replaceexpr k ac = go k
  where
    go :: Expr -> Text
    go (Function i e) = i <> "(" <> T.intercalate ","  (go   <$> e) <> ")"
    go (Value i ) = (ac !! i )

explodeDelayed tb ((Fun k (ex,a)  _ )) =  replaceexpr ex <$> traverse (\i -> explodeDelayed tb $ indexLabel i tb) a -- leaf (isArray (keyType k)) l
explodeDelayed _ t@(Attr k  _ )
  | isKDelayed (keyType k) = do
    l <- lkTB t
    return $ leafDel l
  | otherwise =  do
    l <- lkTB t
    return $ leaf l

explodeDelayed rec ((IT  k (LeftTB1 (Just tb  )))) = do
  explodeDelayed rec ((IT k tb))
explodeDelayed _ (t@(IT  k (ArrayTB1 (TB1 tb :| _) ) )) = do
  l <- lkTB t
  return $ leaf l
explodeDelayed _ (t@(IT  k r  )) = do
   l <- lkTB t
   selectRow l <$> explodeRow' r
{-explodeDelayed tbenv  (Labeled l (FKT ref  _ _ )) = case unkvlist ref of
           [] -> return $ leaf l
           i -> (\v -> T.intercalate assoc v <> assoc <> leaf l) <$> traverse (explodeDelayed tbenv . getCompose) i
-}

printPred :: TBData  Key ()->  BoolCollection (Access Key ,AccessOp Showable ) -> Codegen (Maybe [Text],Maybe [(PrimType,FTB Showable)])
printPred t (PrimColl (a,e)) = do
   idx <- indexFieldL e [] a t
   return (Just $ catMaybes $ fmap fst idx,Just $ catMaybes $ fmap snd idx)

printPred t (OrColl wpred) = do
      w <- fmap unzip <$> traverse (traverse (printPred  t)) (nonEmpty wpred)
      return (pure . (\i -> " (" <> i <> ") ") . T.intercalate " OR " <$> join (nonEmpty. concat . catMaybes . fst <$> w) , concat . catMaybes . snd <$> w )
printPred t (AndColl wpred) = do
      w <- fmap unzip <$> traverse (traverse (printPred  t)) (nonEmpty wpred)
      return (pure . (\i -> " (" <> i <> ") ") . T.intercalate " AND " <$>  join (nonEmpty . concat . catMaybes .fst <$> w) , concat . catMaybes . snd <$> w )

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

justLabel :: NameMap -> TBData Key () -> Key -> Text
justLabel namemap t k = fst $ evalRWS (  getLabels t  k) [Root (fst t)] namemap

indexLabel  :: Show a =>
    Access Key
    -> TBData Key a
    -> (Column  Key a)
indexLabel p@(IProd b l) v =
    case findAttr l v of
      Just i -> i
      Nothing -> errorWithStackTrace "no fk"
indexLabel  i v = errorWithStackTrace (show (i, v))

indexLabelU  (Many [One nt]) v = flip (indexLabel ) v $ nt



indexFieldL
    ::  AccessOp Showable
    -> [Text]
    -> Access Key
    -> TBData Key ()
    -> Codegen [(Maybe Text, Maybe (PrimType ,FTB Showable))]
-- indexFieldL e c p v | traceShow (e,c,p) False = undefined
indexFieldL e c p@(IProd b l) v =
    case findAttr l v of
      Just i -> pure . utlabel  e c <$> tlabel' (i)
      Nothing ->
            case
                   findFK [l] v of

                Just i ->
                    case i of
                        (FKT ref _ _) ->
                          pure . utlabel e c <$> (tlabel' $
                                  justError ("no attr" <> show (ref, l)) .
                                  L.find
                                      ((== [l]) .
                                       fmap (_relOrigin) . keyattr) $
                                  unkvlist ref)

                        i -> errorWithStackTrace "no fk"
    -- Don't support filtering from labeled queries yet just check if not null for all predicates
    -- TODO: proper check  accessing the term
                Just t@(IT k _ ) -> do
                  i <- lkTB t
                  return $ [(Just ("i" <> i <> " is not null"), Nothing)]
                Just t -> do
                  i <- lkTB t
                  return [(Just (i <> " is not null"), Nothing)]
                Nothing -> case findFKAttr [l] v of
                             Just i -> do
                               pure . utlabel e  c <$> tlabel' (i)
                             Nothing  -> errorWithStackTrace ("no fk attr" <> show (l,v))

indexFieldL e c n@(Nested l nt) v =
  case findFK (iprodRef <$> l) v of
    Just a -> case a of
        t@(IT k (LeftTB1 (Just (ArrayTB1 (fk :| _))))) ->  do
          l <- lkTB t
          return [(Just ("i" <> l <> " is not null"), Nothing)]
        t@(IT k (ArrayTB1 (fk :| _))) ->  do
          l <- lkTB t
          return [(Just ("i" <> l <> " is not null"), Nothing)]
        (IT k fk) -> indexFieldLU e c nt  $ head (F.toList fk )
        a -> do
          l <- lkTB a
          return [(Just (l <> " is not null"), Nothing)]

    Nothing -> concat <$> traverse (\i -> indexFieldL (Right (Not IsNull)) c i v) l

indexFieldL e c i v = errorWithStackTrace (show (i, v))

indexFieldLU e c (Many nt) v = concat <$> traverse (flip (indexFieldLU e c) v ) nt
indexFieldLU e c (ISum nt) v = concat <$> traverse (flip (indexFieldLU e c) v ) nt
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

tlabel' t@(Attr k _) =  do
  l <- lkTB t
  return (k,l)
tlabel' t@(IT k tb ) =  do
  l <- lkTB t
  return (k,"i" <> l <> " :: " <> tableType tb)

getLabels :: TBData Key () ->  Key ->  Codegen Text
getLabels t k =   justError ("cant find label"  <> show k <> " - " <> show t) . M.lookup  k <$> (mapLabels label' t)
    where
      label' t@(Attr k _) =  do
        l <- lkTB t
        return (k,l )
      label' t@(IT k tb ) = do
        l <- lkTB t
        return (k, "i" <>  l  <> " :: " <> tableType tb)


mapLabels label' t =  M.fromList <$> traverse (label') (getAttr $ joinNonRef' t)
