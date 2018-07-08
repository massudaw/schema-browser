{-# LANGUAGE GADTs,FlexibleInstances, FlexibleContexts #-}
module Plugins.Schema where

import Types
import qualified NonEmpty as Non
import Types.Patch
import qualified Data.List as L
import Utils
import Control.Monad
import Serializer
import Data.Maybe
import Data.Proxy
import Schema
import NonEmpty hiding(nonEmpty)
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
import qualified Data.Interval as I
import GhcMonad (liftIO)
import Packages
import GHC.Paths (libdir)
import Name (getOccString)
import Data.Dynamic (fromDyn,toDyn)
import DynFlags (defaultFatalMessager, defaultFlushOut, PkgConfRef(PkgConfFile))

import Debug.Trace

codeOps = SchemaEditor (error "no ops 2") (error "no ops 3" ) (error "no ops 4") (error "no ops 5")(\ _ _ _ _ _ _ _ -> return ([],TableRef ((I.NegInf,True) `I.interval` (I.PosInf,True) ),0)) (\ _ _-> return Nothing )  mapKeyType  ((\ a -> liftIO . logTableModification a)) ((\ a -> liftIO . logUndoModification a))400 (\inf -> id {-withTransaction (conn inf)-})  (error "no ops")

gmailPrim :: HM.HashMap Text KPrim
gmailPrim = HM.fromList
  [("text", PText)
  ,("int", PInt 8)
  ,("plugin", PDynamic "plugin")
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

addToken t (Primitive i a) = Primitive (t:i) a

ktypeRec f v@(Primitive (KOptional:xs) i) =   f v <|> fmap (addToken KOptional) (ktypeRec f (Primitive xs i))
ktypeRec f v@(Primitive (KArray :xs) i) =   f v <|> fmap (addToken KArray) (ktypeRec f (Primitive xs i))
ktypeRec f v@(Primitive (KInterval:xs) i) =   f v <|> fmap (addToken KInterval) (ktypeRec f (Primitive xs i))
ktypeRec f v@(Primitive (KSerial :xs) i) = f v <|> fmap (addToken KSerial) (ktypeRec f (Primitive xs i))
ktypeRec f v@(Primitive []  i ) = f v



mapKeyType :: FKey (KType PGPrim) -> FKey (KType (Prim KPrim (Text,Text)))
mapKeyType  = fmap mapKType

mapKType :: KType PGPrim -> KType CorePrim
mapKType i = fromMaybe (fmap textToPrim i) $ ktypeRec ktypeLift (fmap textToPrim i)

textToPrim :: Prim PGType  (Text,Text) -> Prim KPrim (Text,Text)
textToPrim (AtomicPrim (s,i,_)) = case  HM.lookup i  gmailPrim of
  Just k -> AtomicPrim k
textToPrim (RecordPrim i) =  (RecordPrim i)
textToPrim i = error ("textToPrim : " ++ show i)

code smvar  = indexSchema smvar "code"

list' :: Union a -> Maybe (NonEmpty a)
list' (Many inp) = Non.fromList  <$> nonEmpty inp
list' (ISum inp) = Non.fromList  <$> nonEmpty inp

list :: Union a -> NonEmpty a
list = justError "empty union list " . list'

addPlugins iniPlugList smvar = do
  metaschema <- liftIO $ code smvar
  let plugins = "plugin_code"
  (_,(_,TableRep(_,_,plug)))<- transactionNoLog (meta metaschema) $ tableLoaderAll (lookTable (meta metaschema) "plugins") Nothing Nothing [] mempty Nothing
  dbstats <- transactionNoLog metaschema $ selectFrom plugins Nothing Nothing [] mempty
  (event,handle) <- R.newEvent
  let mk = tableMeta $ lookTable (meta metaschema) "plugins"
      m = fmap keyValue mk
  let
    row dyn@(FPlugins _ _ (StatefullPlugin _)) =  do
        name <- nameM
        return $ kvlist $ [FKT (kvlist $ Attr "ref" <$> ((fmap (justError "un ". unSOptional) . F.toList . getPKM m ) name)) [Rel "ref" Equals "oid"]  (TB1 name)
                     ,Attr "table" (txt (_bounds dyn) )
                     ,Attr "plugin" (TB1 $ SDynamic (HDynamic (toDyn dyn ))) ]
          where nameM =  L.find (flip G.checkPred (WherePredicate (AndColl [PrimColl $ fixrel(keyRef "name",Left (txt (_name dyn ),Equals))]))) (mapKey' keyValue <$> plug)
    row dyn = do
        name <- nameM
        let (inp,out) = pluginStatic dyn
        return $ kvlist $ [ FKT (kvlist $ Attr "ref" <$> ((fmap (justError "un ". unSOptional ) . F.toList . getPKM m ) name)) [Rel "ref" Equals "oid"]  (TB1 name)
                     , Attr "table" (txt (_bounds dyn) )
                     , IT "input" (array (TB1 .encodeT ) (list inp))
                     , IT "output" (array (TB1 .encodeT) (list out))
                     , Attr "plugin" (TB1 $ SDynamic (HDynamic (toDyn dyn ))) ]
          where nameM =  L.find (flip G.checkPred (WherePredicate (AndColl [PrimColl $ fixrel (keyRef "name",Left (txt (_name dyn ),Equals))]))) (mapKey' keyValue <$> plug)
  R.onEventIO event (fetchData  (iniRef  dbstats). pure )
  inotify <- liftIO initINotify
  let
    modifyed (Closed i j True ) = do
      putStrLn ("### Modified Plugin: "  ++ show (i,j))
      plugList <- plugListM
      let patchR m i = RowPatch (G.getIndex m i,PatchRow $ patch i)
      mapM (traverse (handle . patchR mk . liftTable' metaschema "plugin_code") . row ) plugList
      return ()
    modifyed i = return ()
  watch <- liftIO$ addWatch inotify  [CloseWrite] "./plugins/Plugins.hs" modifyed
  R.registerDynamic (removeWatch watch)
  liftIO $ mapM (traverse (handle . createRow' (lookMeta metaschema "plugin_code").liftTable' metaschema "plugin_code") . row)  iniPlugList
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
    importDecl_RdrName <- parseImportDecl "import Plugins"
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
  addPkgDb  ".stack-work/install/x86_64-linux-tinfo6-nopie/lts-9.21/8.0.2/lib/x86_64-linux-ghc-8.0.2/"
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
  _ <- liftIO $ initPackages dfs
  return ()


