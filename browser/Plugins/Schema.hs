{-# LANGUAGE FlexibleContexts #-}
module Plugins.Schema where

import Types
import qualified NonEmpty as Non
import Types.Patch
import qualified Data.List as L
import Utils
import Data.Maybe
import Data.Proxy
import Schema
import NonEmpty
import qualified Types.Index as G

import RuntimeTypes
import Control.Applicative
import SchemaQuery

import Data.Typeable
import Data.Text (Text,pack)
import qualified Data.Foldable as F
import qualified Data.Map as M
import Data.Map (Map)
import qualified Data.HashMap.Strict as HM

import Control.Concurrent.STM
import qualified Reactive.Threepenny as R
import Postgresql.Types (PGPrim,PGType)

import System.INotify
-- Dynamic Compilation
import GHC
import GHC.Stack
import GhcMonad (liftIO)
import Packages
import GHC.Paths (libdir)
import Name (getOccString)
import Data.Dynamic (fromDyn,toDyn)
import DynFlags (defaultFatalMessager, defaultFlushOut, PkgConfRef(PkgConfFile))

import Debug.Trace
codeOps = SchemaEditor (error "no ops 1") (error "no ops 2") (\i -> return Nothing ) (error "no ops 4") (\ _ _ _ _ _ _ -> return ([],Nothing ,0)) (\ _ _-> return Nothing )  mapKeyType (error "no ops 6")(error "no ops 7") undefined 200 (\inf -> id {-withTransaction (conn inf)-})  (error "no ops") Nothing

gmailPrim :: HM.HashMap Text KPrim
gmailPrim = HM.fromList
  [("text", PText)
  ,("int", PInt 8)
  ,("plugin", PTypeable (typeRep (Proxy :: Proxy (FPlugins Text))))
  ]

-- Type Conversions
--
gmailLiftPrim :: Ord b => Map (KType (Prim KPrim b)) (KType (Prim KPrim b))
gmailLiftPrim =
  M.fromList []

gmailLiftPrimConv :: Ord b => Map (KType (Prim KPrim b),KType (Prim KPrim b))  ( FTB  Showable -> FTB Showable , FTB Showable -> FTB Showable )
gmailLiftPrimConv =
  M.fromList []




ktypeLift :: Ord b => KType (Prim KPrim b) -> Maybe (KType (Prim KPrim b))
ktypeLift i = (M.lookup i  gmailLiftPrim )

ktypeRec v@(KOptional i) = ktypeLift v <|> ktypeRec i
ktypeRec v@(KArray i) = ktypeLift v <|> ktypeRec i
ktypeRec v@(KInterval i) = ktypeLift v <|> ktypeRec i
ktypeRec v@(KSerial i) = ktypeLift v <|> ktypeRec i
ktypeRec v@(KDelayed i) = ktypeLift v <|> ktypeRec i
ktypeRec v@(Primitive i ) = ktypeLift v

mapKeyType :: FKey (KType PGPrim) -> FKey (KType (Prim KPrim (Text,Text)))
mapKeyType  = fmap mapKType

mapKType :: KType PGPrim -> KType CorePrim
mapKType i = fromMaybe (fmap textToPrim i) $ ktypeRec (fmap textToPrim i)

textToPrim :: Prim PGType  (Text,Text) -> Prim KPrim (Text,Text)
textToPrim (AtomicPrim (s,i,_)) = case  HM.lookup i  gmailPrim of
  Just k -> AtomicPrim k
textToPrim (RecordPrim i) =  (RecordPrim i)
textToPrim i = errorWithStackTrace ("textToPrim : " ++ show i)

code smvar  = indexSchema smvar "code"

list inp
    = case inp of
        ISum i -> Non.fromList i
        Many i -> Non.fromList i

reference i | traceShow i False = undefined
reference (IProd _ k)
  = [ IT "iprod" (LeftTB1 . Just . TB1 .
      tblist . fmap _tb $ [ Attr "key" ((txt ) k )])
    , IT "nested" (LeftTB1 Nothing)]
reference (Nested l nest )
  = [ IT "iprod" (LeftTB1 Nothing)
    , IT "nested" (LeftTB1 . Just .TB1 .
      tblist .fmap _tb $
        [Attr "ref" (array (txt . iprodRef ) (Non.fromList l))
        ,IT "nest" (array (TB1 .tblist . fmap _tb . reference ) ( list nest))]) ]
reference  i = errorWithStackTrace ("no match reference: " ++ show i)

addPlugins iniPlugList smvar = do
  metaschema <- liftIO $code smvar
  let plugins = "plugin_code"
  (_,(_,plug))<- transactionNoLog (meta metaschema) $ selectFrom "plugins" Nothing Nothing [] mempty
  (dbstats,_)<- transactionNoLog metaschema $ selectFrom plugins Nothing Nothing [] mempty
  (event,handle) <- R.newEvent
  let
    row dyn@(FPlugins _ _ (StatefullPlugin _)) =  do
        name <- nameM
        return $ tblist $ fmap _tb [FKT (kvlist $ _tb . Attr "ref" <$> ((fmap (justError "un ". unSOptional' ) . F.toList . getPKM ) name)) [Rel "ref" Equals "oid"]  (TB1 name), Attr "table" (txt (_bounds dyn) ), Attr "plugin" (TB1 $ SHDynamic (HDynamic (toDyn dyn ))) ]
      where nameM =  L.find (flip G.checkPred (WherePredicate (AndColl [PrimColl (keyRef "name",Left (txt (_name dyn ),Equals))]))) (mapKey' keyValue <$> plug)
    row dyn = do
        name <- nameM
        let (inp,out) = pluginStatic dyn
        return $ tblist $ _tb <$> [ FKT (kvlist $ _tb . Attr "ref" <$> ((fmap (justError "un ". unSOptional' ) . F.toList . getPKM ) name)) [Rel "ref" Equals "oid"]  (TB1 name)
                          , Attr "table" (txt (_bounds dyn) )
                          , IT "input" (array (TB1 .tblist . fmap _tb . reference ) (Non.fromList inp))
                          , IT "output" (array (TB1 .tblist . fmap _tb . reference ) (Non.fromList out))
                          , Attr "plugin" (TB1 $ SHDynamic (HDynamic (toDyn dyn ))) ]
      where nameM =  L.find (flip G.checkPred (WherePredicate (AndColl [PrimColl (keyRef "name",Left (txt (_name dyn ),Equals))]))) (mapKey' keyValue <$> plug)
  R.onEventIO event (\dyn -> do
    putPatch (patchVar $ iniRef dbstats) . pure  $ dyn)
  inotify <- liftIO initINotify
  let
    modifyed (Closed i j True ) = do
      putStrLn ("### Modified Plugin: "  ++ show (i,j))
      plugList <- plugListM
      mapM (traverse (handle . PatchRow . patch . liftTable' metaschema "plugin_code") . row ) plugList
      return ()
    modifyed i = return ()
  watch <- liftIO$ addWatch inotify  [CloseWrite] "Plugins.hs" modifyed
  R.registerDynamic (removeWatch watch)
  liftIO $  mapM (traverse (handle . CreateRow .liftTable' metaschema "plugin_code") . row)  iniPlugList
  return  iniPlugList


putString = liftIO . putStrLn

-- |  List all exports of this module
--    and evaluate a symbol from a module DynTest
plugListM :: IO [PrePlugins]
plugListM  = do
  runGhc (Just libdir) $ do
    putString ":::Display exports of modules:::"
    modSums <- initSession ["Plugins"]

    putString ":::Evaluate a name from module Plugins:::"
    importDecl_RdrName <- parseImportDecl "import Plugins "
    importDecl_Run <- parseImportDecl "import RuntimeTypes"
    setContext [ IIDecl importDecl_RdrName
               , IIDecl importDecl_Run]
    dynVal <- dynCompileExpr "plugList :: [PrePlugins]"
    return (fromDyn dynVal [])



-- | Init interactive session and load modules
initSession modStrNames = do
  dflags <- getSessionDynFlags
  setSessionDynFlags $ dflags {
    hscTarget = HscInterpreted
    , ghcLink   = LinkInMemory
    }
  targets <- mapM
              (\modStrName -> do
                  putString modStrName
                  target <- guessTarget ("*"++modStrName++".hs") Nothing
                  return target
              ) modStrNames
  setTargets targets
  addPkgDb  ".stack-work/install/x86_64-linux/ghc-7.10/7.10.3/lib/x86_64-linux-ghc-7.10.3/"

  load LoadAllTargets
  modSums <- mapM
              (\modStrName -> do
                  putString modStrName
                  modSum <- getModSummary $ mkModuleName modStrName
                  return $ ms_mod modSum
              ) modStrNames
  return modSums


-- | Add a package database to the Ghc monad
addPkgDb :: GhcMonad m => FilePath -> m ()
addPkgDb fp = do
  dfs <- getSessionDynFlags
  let pkg  = PkgConfFile fp
  let dfs' = dfs { extraPkgConfs = (pkg:) . extraPkgConfs dfs }
  setSessionDynFlags dfs'
  _ <- liftIO $ initPackages dfs'
  return ()


