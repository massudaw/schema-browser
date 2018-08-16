{-# LANGUAGE FlexibleInstances,GADTs #-}
module ClientAccess where

import Control.Monad.Reader
import Data.Bifunctor (first)
import Utils
import Safe
import qualified Data.ExtendedReal as ER
import Graphics.UI.Threepenny hiding (meta)
import Graphics.UI.Threepenny.Internal (wId)
import qualified Data.Interval as Interval
import Data.Interval (Interval)
import Data.Text (Text)
import Data.Time
import qualified NonEmpty as Non
import Reactive.Threepenny
import RuntimeTypes
import Schema
import SchemaQuery
import Data.Maybe
import Serializer
import Step.Common
import Types
import qualified Types.Index as G
import Types.Patch
import qualified Data.Map as M
import qualified Data.Foldable as F

addSchemaIO
  :: Int
     -> InformationSchema
     -> InformationSchema
     -> Int
     -> Dynamic ()
addSchemaIO clientId minf inf six = do
  let cli = lookTable minf "clients"
  dbmeta  <- prerefTable minf cli
  now <- liftIO getCurrentTime
  let new = addSchema clientId  now inf six
      mkPatch = PatchRow . liftPatch minf "clients"
  transactionNoLog minf $
    patchFrom (tableMeta cli) (mkPatch <$>new)
  registerDynamic (void $ do
    now <- liftIO getCurrentTime
    let new = removeSchema clientId  now inf six
    runDynamic $ transactionNoLog minf $
      patchFrom (tableMeta cli) (mkPatch <$>new))



addClientLogin
  :: InformationSchema -> Dynamic (RowPatch Key Showable)
addClientLogin inf =  transactionNoLog inf $ do
    now <- liftIO getCurrentTime
    let
      row = ClientState Nothing (startTime now) []
      obj = liftTable' inf "clients" (encodeT row)
      m = lookMeta inf  "clients"
    lift $ prerefTable inf (lookTable inf "clients")
    liftIO $ print obj
    i <-  fullInsert m obj
    liftIO $ print "inserted"
    lift . registerDynamic . closeDynamic $ do
      now <- liftIO getCurrentTime
      let
        pt = [PAttr (lookKey inf "clients" "up_time") (PInter False (ER.Finite $ PAtom (STime $ STimestamp now) , False))]
      transactionNoLog inf $
        patchFrom m  (head $ index i,PatchRow pt)
      return ()
    return i


trackTable
  :: InformationSchemaKV Key Showable
  -> Int
  -> Table
  -> Int
  -> Int
  -> Dynamic ()
trackTable minf cid table six ix = do
  now <- lift getCurrentTime
  let cpatch = addTable  cid now table six ix
      mkPatch i =  PatchRow . liftPatch minf "clients" <$> i
      cli  = lookTable minf "clients"
      mcli = tableMeta cli
  ref <- prerefTable minf cli
  transactionNoLog minf $
    patchFrom mcli (mkPatch cpatch)
  registerDynamic (void $ do
    now <- getCurrentTime
    let dpatch = removeTable  cid now table six ix
    closeDynamic $ transactionNoLog minf $
      patchFrom mcli (mkPatch dpatch))

atClient idClient =  (G.Idex [LeftTB1 . Just . num $ idClient],)
atSchema  six v = PInline "selection" (POpt $ Just $ PIdx six $ Just$ PAtom v)
atTable tix v = PInline "selection" (POpt $ Just $ PIdx tix $ Just$ PAtom v)
atRow rix v = PInline "selection" (POpt $ Just $ PIdx rix $ Just$ PAtom v)

removeTable :: Int -> UTCTime -> Table -> Int -> Int ->  (TBIndex Showable,TBIdx Text Showable)
removeTable idClient now table  six tix = atClient idClient [atSchema six
     [atTable tix [ PAttr "up_time" ( PInter False (Interval.Finite $ patch(time now),True ))]]]

addTable :: Int -> UTCTime -> Table -> Int -> Int ->  (TBIndex Showable,TBIdx Text Showable)
addTable idClient now table  six tix
  = atClient idClient [atSchema six
     [atTable tix (patch $ encodeT (ClientTableSelection (tableName table) (startTime now) []))]]


addRow idClient now tdi six tix rix
  =  atClient idClient [atSchema six [atTable tix [atRow rix $ patch (encodeT $ createRow now tdi)]]]
removeRow idClient now six tix rix
  =  atClient idClient [atSchema six [atTable tix [atRow rix
            [PAttr "up_time" ( PInter False (Interval.Finite $ patch (time now),True ))]]]]

startTime now = Interval.interval (Interval.Finite now,True) (Interval.PosInf,True)

createRow now tdi = ClientRowSelection (startTime now) (uncurry ClientPK . first keyValue <$>  tdi)

instance DecodeTable ClientPK where
  isoTable = iassoc arr  (identity <$$> prim  "key") (identity <$$> prim "val")
    where arr = IsoArrow (uncurry ClientPK ) (\(ClientPK i j) -> (i,j))

instance DecodeTable ClientRowSelection where
  isoTable = iassoc (isoArrow arr) ( prim  "up_time") (nest "data_index")
    where arr = (uncurry ClientRowSelection , \(ClientRowSelection i j) -> (i,j) )

instance DecodeTable ClientTableSelection where
  isoTable = iassoc3  (isoArrow arr) (identity <$$>prim  "table") (prim "up_time") (nest "selection")
    where arr = (\(i,j,k) -> ClientTableSelection i j k, \(ClientTableSelection i j k ) -> (i,j,k) )

instance DecodeTable ClientSchemaSelection where
  isoTable = iassoc3  (isoArrow arr) (identity <$$>prim  "schema") (prim "up_time") (nest "selection")
    where arr = (\(i,j,k) -> ClientSchemaSelection i j k, \(ClientSchemaSelection i j k ) -> (i,j,k) )

instance DecodeTable ClientState where
  isoTable = iassoc3  (isoArrow arr) (prim"id") (prim "up_time") (nest "selection")
    where arr = (\(i,j,k) -> ClientState i j k  , \(ClientState i j k ) -> (i,j,k) )

instance DecodeTable (AuthCookie User) where
  isoTable = iassoc3
    (isoArrow (\(i,j,k) -> AuthCookie i j k,\(AuthCookie i j k) -> (i,j,k)))
    (identity  <$$> nestJoin [Rel "logged_user" Equals "oid"] isoTable )
    (identity  <$$> prim "cookie")
    (identity  <$$> prim "creation_date")

instance DecodeTable User where
  isoTable = iassoc
    (isoArrow (\(i,j) -> User i j ,\(User i j ) -> (i,j)))
    (identity  <$$> prim "oid")
    (IsoArrow (justError "always Just") Just <$$> prim "usename")

time = TB1  . STime . STimestamp

num = TB1 . SNumeric


data ClientState
  = ClientState
    { client_id ::  Maybe Int
    , client_up_time :: Interval UTCTime
    , schema_selection :: [ClientSchemaSelection]
    }deriving(Eq,Show)

data ClientSchemaSelection
  = ClientSchemaSelection
    { schema_sel :: Int
    , schema_up_time :: Interval UTCTime
    , table_selection :: [ClientTableSelection]
    }deriving(Eq,Show)

data ClientTableSelection
  = ClientTableSelection
    { table_sel :: Text
    , table_up_time :: Interval UTCTime
    , row_selection :: [ClientRowSelection]
    }deriving(Eq,Show)

data ClientRowSelection
  = ClientRowSelection
    { row_up_time :: Interval UTCTime
    , data_index :: Non.NonEmpty  ClientPK
    }deriving(Eq,Show)

data ClientPK
  = ClientPK
    { key :: Text
    , pk_value :: FTB Showable
    }deriving(Eq,Show)

addSchema :: Int -> UTCTime -> InformationSchema -> Int -> (TBIndex Showable,TBIdx Text Showable)
addSchema idClient now inf tix
  = atClient idClient  [atSchema  tix (patch$
       encodeT (ClientSchemaSelection (schemaId inf) (startTime now) []))]


removeSchema :: Int -> UTCTime -> InformationSchema -> Int ->  (TBIndex Showable,TBIdx Text Showable)
removeSchema idClient now inf tix
  = atClient idClient  [atSchema tix [PAttr "up_time" (PInter False (Interval.Finite $ patch(time now),True ))]]


getClient metainf clientId ccli = G.lookup (idex metainf "clients"  [("id",num clientId)]) ccli :: Maybe (TBData Key Showable)

lookClient :: Int -> InformationSchema ->  Dynamic (Tidings (Maybe ClientState))
lookClient clientId metainf = do
  (_,clientState,_)  <- refTables' metainf (lookTable metainf "clients") Nothing (WherePredicate (AndColl [PrimColl $ fixrel (keyRef (lookKey metainf "clients" "id") , Left (num clientId,Equals))]))
  return (fmap (decodeT. mapKey' keyValue). getClient metainf clientId .primary<$> clientState)

indexTable inf (tix,table) = (lookT =<<)
  where
    lookT iv = do
      let tables = table_selection iv
      atMay tables tix

listRows inf table =  maybe []  row_selection


logRowAccess
  :: Show a =>
     Window
     -> (Int, InformationSchemaKV Key Showable)
     -> (Int, TableK (FKey a))
     -> Int
     -> TBIndex Showable
     -> Dynamic ()
logRowAccess w (six,inf) (tix,table) ix (G.Idex row) = do
  let sel =  Non.fromList  (zip (rawPK table) row)
  let lift =  liftPatch minf "clients"
      cli = lookTable minf "clients"
      minf = meta inf
  now <- liftIO getCurrentTime
  let p = lift <$> addRow  (wId w) now  sel  six tix ix
  transactionNoLog minf $ do
    patchFrom (tableMeta cli) (PatchRow <$>p)
  registerDynamic (void $ do
    now <- liftIO getCurrentTime
    let d = lift <$> removeRow (wId w) now  six  tix ix
    runDynamic $ transactionNoLog minf $
      patchFrom (tableMeta cli) (PatchRow<$>d))


activeRows :: [ClientRowSelection] -> [[FTB Showable]]
activeRows =  fmap (F.toList . fmap pk_value . data_index). filter (isNothing . unFin . fst . Interval.upperBound' .  row_up_time)
