{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE UndecidableInstances #-}
module Postgresql.Printer
  (selectQuery
  ,codegen
  ,codegent
  ,runCodegenT
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
  ,loadDelayedQuery
  ,lkTB
  ,atTable
  )
  where

import Utils
import Types
import Types.Inference

import Query

import Postgresql.Sql.Types
import Postgresql.Sql.Printer
import Postgresql.Function
import RuntimeTypes
import qualified Data.Poset as P
import Postgresql.Types
import Data.Ord
import Data.String
import Step.Host (findFK,findAttr)
import NonEmpty (NonEmpty(..))
import Data.Functor.Apply
import Data.Bifunctor
import qualified Data.Foldable as F
import Data.Maybe
import Data.Monoid hiding (Product)

import qualified Data.Text as T


import Control.Monad
import Control.Monad.RWS
import Control.Applicative
import Data.Functor.Identity
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Text (Text)


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
    Nothing ->keyValue  k

lkTB (IT k _ ) = do
  a <-lkIT k
  return $ case a of
    Just a -> "k" <> T.pack (show a)
    Nothing -> keyValue k

lkTB (FKT  _ rel _ ) = do
  a <- lkFK rel
  return $ case a of
    Just a -> "k" <> T.pack (show a)
    Nothing -> error (show rel)

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
    commands = (renderAttr <$>  (rawAttrs r) ) <> [renderPK] <> fmap renderFK ( rawFKS r)
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

expandInlineTable :: KVMetadata Key -> TBData  Key () -> Text -> Codegen SQLRow
expandInlineTable meta tb@( _) pre = asNewTable meta $ (\t->  do
  let
    name =  tableAttr (meta,tb)
    aliasKeys (Attr n    _ )  =  do
      a <- newAttr n
      return $ SQLARename (SQLAIndexAttr (SQLAReference Nothing ("i" <> pre) ) ( keyValue n)) ("k" <>T.pack (show a))
    aliasKeys (IT n _ )  =    do
      a <- newIT  n
      return $ SQLARename (SQLAIndexAttr (SQLAReference Nothing ("i" <> pre )) ( keyValue n)) ("ik"<> T.pack (show a))
  cols <- mapM (aliasKeys )  (sortPosition name)
  return $ SQLRSelect cols Nothing Nothing)


expandInlineArrayTable ::  KVMetadata Key -> TBData  Key  () -> Text -> Codegen SQLRow
expandInlineArrayTable meta tb@( KV i) pre = asNewTable meta $ (\t -> do
  let
     rowNumber = SQLARename (SQLAInline "row_number() over ()") "row_number"
     name =  tableAttr (meta,tb)
     aliasKeys (Attr n    _ )  =  do
       a <- newAttr n
       return $ SQLARename (SQLAIndexAttr (SQLAReference Nothing "ix") ( keyValue n)) ("k" <>T.pack (show a))
     aliasKeys (IT n _ )  =do
       a <- newIT  n
       return $ SQLARename (SQLAIndexAttr (SQLAReference Nothing "ix") ( keyValue n)) ("ik"<> T.pack (show a))
  cols <- mapM (aliasKeys )  (sortPosition name)
  return $ SQLRSelect (cols <> [rowNumber]) (Just $ SQLRRename (SQLRFrom (SQLRUnnest (SQLAReference Nothing  ("i" <> pre)))) "ix" )Nothing)

sortPosition = L.sortBy (comparing (maximum . fmap (keyPosition ._relOrigin) .keyattri))

asNewTable meta action = do
  tidx <- newTable meta
  let name =    "t" <> T.pack (show tidx)
  t <- local (++[Root meta]) (action name)
  return $ SQLRRename  t name


expandBaseTable ::  KVMetadata Key -> TBData  Key  () -> Codegen SQLRow
expandBaseTable meta tb@( KV i) = asNewTable meta  (\t -> do
  let
     aliasKeys (at@(Attr n _ )) = do
       a <- newAttr n
       return $ SQLARename (SQLAIndexAttr (SQLAReference Nothing t) ( keyValue n)) ("k"<> T.pack (show a))
     aliasKeys (at@(IT n _ )) = do
       a <- newIT  n
       return $ SQLARename (SQLAIndexAttr (SQLAReference Nothing t) ( keyValue n)) ("ik"<> T.pack (show a))
     name =  tableAttr (meta,tb)
  cols <- mapM (aliasKeys  )  (sortPosition name)
  return $ SQLRSelect  cols (Just $ SQLRRename (SQLRFrom (SQLRReference (Just $ _kvschema meta) (_kvname meta))) t ) Nothing
  )




codegent l =
  fmap (\(q,s,_) -> (q,s)) $ runRWST l [] ((0,M.empty),(0,M.empty))

runCodegenT env s l =
  fmap (\(q,s,_) -> q) $ runRWST l env s

codegen l =
  case runRWS l [] ((0,M.empty),(0,M.empty)) of
    (q,s,_) -> (q,s)

selectQuery
  :: InformationSchema
  -> KVMetadata Key
  -> TBData Key ()
  -> Maybe [FTB Showable]
  -> [(Key, Order)]
  -> WherePredicate
  -> ((Text,Maybe [(PrimType ,FTB Showable)]),NameMap)
selectQuery inf m t koldpre order (WherePredicate wpred) = codegen tableQuery
      where
        tableQuery = do
          tname <- expandBaseTable m t
          tquery <- expandQuery' inf m False t
          rec <- explodeRecord inf m t
          order <- orderBy
          (predquery,predvalue) <- customPredicate
          (orderquery,ordervalue) <- ordquery
          let pred = maybe "" (\i -> " WHERE " <> T.intercalate " AND " i )  (orderquery <> predquery)
          let orderQ = " ORDER BY " <> T.intercalate "," order
          return  ("SELECT " <> selectRow "p0" rec <> " FROM " <>  renderRow (tquery tname) <> pred <> orderQ,ordervalue <> predvalue)
        customPredicate = atTable m $ printPred inf m t wpred
        orderBy = atTable m $ mapM (\(i,j) -> do
            l <- lkTB (Attr i (TB1 ()))
            return $ l <> " " <> showOrder j ) order
        ordquery =  atTable m $ do
          let
            preds = zip (_kvpk m) <$> koldpre
            orderpreds = (\i -> filter ((`elem` (fmap fst i)).fst) order ) <$> preds
            koldPk :: Maybe [(PrimType,FTB Showable)]
            koldPk =  fmap (fmap (first keyType )) preds
            pkParam =  koldPk <> (tail .reverse <$> koldPk)
          oq <- traverse (traverse (\(i,v) ->  do
            l <- lkTB (Attr i (TB1 ()))
            return $ (l,v) ) ) orderpreds
          return (pure .generateComparison <$> oq,pkParam)

generateComparison ((k,v):[]) = k <>  dir v <> "?"
  where dir Asc = ">"
        dir Desc = "<"
generateComparison ((k,v):xs) = "case when " <> k <>  "=" <> "? OR "<> k <> " is null  then " <>  generateComparison xs <> " else " <> k <>  dir v <> "?" <>" end"
  where dir Asc = ">"
        dir Desc = "<"



expandQuery' inf meta left m = atTable meta $ F.foldl (flip (\i -> liftA2 (.) (expandJoin inf meta left (F.toList (_kvvalues  m) ) i )  )) (return id) (P.sortBy (P.comparing (RelSort. keyattri )) $  F.toList (_kvvalues  m))



expandJoin :: InformationSchema -> KVMetadata Key -> Bool -> [Column Key ()] -> Column Key () -> Codegen (SQLRow -> SQLRow)
expandJoin inf meta left env (IT i (LeftTB1 (Just tb) ))
  = expandJoin inf meta True env $ (IT i tb)
expandJoin inf meta left env (t@(IT a (ArrayTB1 (TB1 tb :| _ ) ))) = do
    l <- lkTB t
    let nmeta = lookSMeta inf r
        r = _keyAtom $ keyType a
    itb <- expandInlineArrayTable nmeta tb l
    tjoin <- expandQuery' inf nmeta left tb
    r <- explodeRecord inf nmeta tb
    let joinc = " (SELECT array_agg(" <> selectRow "arr" r <> " order by row_number) as " <> l <> " " <> (renderRow  $ tjoin (SQLRFrom  itb )) <> " )  as p" <> l
    return $ (\row -> SQLRJoin row JTLateral jt (SQLRInline joinc) Nothing)
        where
          jt = if left then JDLeft  else JDNormal
expandJoin inf meta left env (t@(IT a (TB1 tb))) =  do
     l <- lkTB t
     let nmeta = lookSMeta inf r
         r =_keyAtom $ keyType a
     itable <- expandInlineTable  nmeta tb l
     tjoin <- expandQuery' inf nmeta left tb
     return $  tjoin . (\row -> SQLRJoin row JTLateral jt  itable Nothing)
        where
          jt = if left then JDLeft  else JDNormal
expandJoin inf meta left env v = return id
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
  | otherwise = error $ "wrong type intersectionOp * - {*} " <> show j <> " /= " <> show i
intersectionOp i op j = inner (renderBinary op)




explodeRecord :: InformationSchema -> KVMetadata Key -> TBData  Key () -> Codegen Text
explodeRecord inf m t@(KV tb) = atTable m $ T.intercalate "," <$> (traverse (explodeDelayed inf m t )  $ P.sortBy (P.comparing (RelSort. keyattri ))$ F.toList  tb)

selectRow  l i = "(select rr as " <> l <> " from (select " <> i<>  ") as rr )"

explodeDelayed inf m tb (Fun k (ex,a)  _ )
  = replaceexpr ex <$> traverse (\i-> explodeDelayed inf m tb $ indexLabel i tb) a
explodeDelayed inf m _ t@(Attr k  _ )
  = foldr (=<<) prim (eval<$>kty)
  where
    Primitive kty (AtomicPrim _) = keyType k
    eval KDelayed = \p -> do
      l <- lkTB t
      return $ " case when " <> l <> " is not null then true else null end  as " <> l
    eval _ = return
    prim =  do
      l <- lkTB t
      return  l
explodeDelayed inf m _ t@(IT  k tb  )
  = foldr (=<<) prim (eval<$>kty)
  where
   Primitive kty (RecordPrim r) = keyType k
   eval KArray = \p -> do
    l <- lkTB t
    return  l
   eval _ = return
   prim = do
     l <- lkTB t
     let nmeta = tableMeta $ lookSTable inf r
     selectRow l <$> explodeRecord inf nmeta  (tableNonRef2 $ allRec' (tableMap inf) (lookSTable inf r))


printPred :: InformationSchema -> KVMetadata Key -> TBData  Key ()->  BoolCollection (Access Key ,AccessOp Showable ) -> Codegen (Maybe [Text],Maybe [(PrimType,FTB Showable)])
printPred inf m t (PrimColl (a,e)) = do
  idx <- indexFieldL inf m e [] a t
  return (Just $ catMaybes $ fmap fst idx,Just $ catMaybes $ fmap snd idx)

printPred inf m t (OrColl wpred) = do
      w <- fmap unzip <$> traverse (traverse (printPred inf m  t)) (nonEmpty wpred)
      return (pure . (\i -> " (" <> i <> ") ") . T.intercalate " OR " <$> join (nonEmpty. concat . catMaybes . fst <$> w) , concat . catMaybes . snd <$> w )
printPred inf m t (AndColl wpred) = do
      w <- fmap unzip <$> traverse (traverse (printPred inf m  t)) (nonEmpty wpred)
      return (pure . (\i -> " (" <> i <> ") ") . T.intercalate " AND " <$>  join (nonEmpty . concat . catMaybes .fst <$> w) , concat . catMaybes . snd <$> w )

instance IsString (Maybe T.Text) where
  fromString i = Just (fromString i)


indexFieldL
    :: InformationSchema
    -> KVMetadata Key
    -> AccessOp Showable
    -> [Text]
    -> Access Key
    -> TBData Key ()
    -> Codegen [(Maybe Text, Maybe (PrimType ,FTB Showable))]
indexFieldL inf m e c p@(IProd b l) v =
    case findAttr l v of
      Just i -> pure . utlabel  e c <$> tlabel'  i
      Nothing -> error "not attr"
indexFieldL inf m e c n@(Nested l nt) v =
  case findFK (iprodRef <$> l) v of
    Just a -> case a of
        t@(IT k (LeftTB1 (Just (ArrayTB1 (fk :| _))))) ->  do
          l <- lkTB t
          return [(Just ("i" <> l <> " is not null"), Nothing)]
        t@(IT k (ArrayTB1 (fk :| _))) ->  do
          l <- lkTB t
          return [(Just ("i" <> l <> " is not null"), Nothing)]
        (IT k fk) -> indexFieldLU inf m e c nt  $ head (F.toList fk )
        a -> do
          l <- lkTB a
          return [(Just (l <> " is not null"), Nothing)]

    Nothing -> concat <$> traverse (\i -> indexFieldL inf m (Right (Not IsNull)) c i v) l

indexFieldL inf m e c i v = error (show (i, v))

indexFieldLU inf m e c (Many nt) v = concat <$> traverse (flip (indexFieldLU inf m e c) v ) nt
indexFieldLU inf m e c (ISum nt) v = concat <$> traverse (flip (indexFieldLU inf m e c) v ) nt
indexFieldLU inf m e c (One nt) v = flip (indexFieldL inf m e c) v  nt

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
    operator i = error (show i)
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
tlabel'  t@(IT k tb ) =  do
  l <- lkTB t
  return (k,"i" <> l <> fromMaybe "" (inlineType (keyType k)))

justLabel :: NameMap -> KVMetadata Key -> TBData Key () -> Key -> Text
justLabel namemap meta t k = fst $ evalRWS getLabels  [Root meta] namemap
  where
    getLabels :: Codegen Text
    getLabels =  (fmap  snd . tlabel' ) (justError ("cant find label"  <> show k <> " - " <> show t) $ M.lookup  (S.singleton $ Inline k) $ unKV $ tableNonRef2 t)

loadDelayedQuery
  :: InformationSchema
     -> KVMetadata Key
     -> TBData Key ()
     -> TBData Key ()
     -> RWST [Address Key] String NameMap Identity Text
loadDelayedQuery inf m v delayed= do
  tq <- expandBaseTable m v
  rq <- explodeRecord inf m delayed
  out <- atTable m $ mapM (\i-> do
    v <- lkTB (Attr i (TB1 ()))
    return $   v  <>  " = ?") (_kvpk m)
  let whr = T.intercalate " AND " out
  return $ "select row_to_json(q) FROM (SELECT " <>  selectRow "p0" rq <> " FROM " <> renderRow tq <> " WHERE " <> whr <> ") as q "


