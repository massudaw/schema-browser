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
  ,escapeReserved
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



reservedNames = ["column","table","schema"]
escapeReserved :: T.Text -> T.Text
escapeReserved i = if i `elem` reservedNames then "\"" <> i <> "\"" else i

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
  | isTableRec tb = errorWithStackTrace "no rec support"
  | otherwise = return $ expandBaseTable  tb



topRec = join . join . fmap unMutRec
selectQuery
  :: (KVMetadata Key,
      Compose
        (Labeled Text)
        (KV (Compose (Labeled Text) (TB (Labeled Text))))
        Key
        ())
     -> Maybe (TBIndex Showable)
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
            unIndex (Idex i ) = zip (_kvpk (fst t)) $ F.toList i
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
    case   findFK l v of
      Just a ->  case getCompose a of
        Unlabeled i -> indexLabel  nt.head . F.toList . _fkttable $ i
        Labeled i _ -> errorWithStackTrace ("cant index" <> show i)
      Nothing -> errorWithStackTrace ("cant index"<> show l)
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
  case findFK l v of
    Just a -> case getCompose a of
        Unlabeled i ->
          concat . fmap (indexFieldL e c nt) . F.toList . _fkttable $ i
        Labeled l (IT k (LeftTB1 (Just (ArrayTB1 (fk :| _))))) ->  [(Just (l <> " is not null"), Nothing)]
        Labeled l (IT k (ArrayTB1 (fk :| _))) ->  [(Just (l <> " is not null"), Nothing)]
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

    Nothing -> concat $ (\i -> indexFieldL (Right (Not IsNull)) c (IProd b [i]) v)<$> l

indexFieldL e c (Many nt) v = concat $ flip (indexFieldL e c) v <$> nt
indexFieldL e c (ISum nt) v = concat $ flip (indexFieldL e c) v <$> nt
indexFieldL e c i v = errorWithStackTrace (show (i, v))

utlabel (Right  e) c a = result
  where
    idx = tlabel' . getCompose $ a
    opvalue  ref i@(Range _ l)  =  "(" <> T.intercalate "." (c ++ [ref])   <> ")" <> "i" <> renderUnary i
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


