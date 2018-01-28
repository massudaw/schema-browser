{-# LANGUAGE GADTs #-}
module ClientAccess where

import Control.Monad.Reader
import Data.Bifunctor (first)
import Safe
import qualified Data.ExtendedReal as ER
import qualified Data.Interval as Interval
import Data.Interval (Interval)
import Data.Text (Text)
import Data.Time
import qualified NonEmpty as Non
import Reactive.Threepenny
import RuntimeTypes
import Schema
import SchemaQuery
import Serializer
import Step.Common
import Types
import qualified Types.Index as G
import Types.Patch

addSchemaIO clientId minf inf six = do
  let cli = lookTable minf "clients"
  dbmeta  <- prerefTable minf cli
  now <- liftIO getCurrentTime
  let new = addSchema clientId  now inf six
      mkPatch = PatchRow . liftPatch minf "clients"
  transactionNoLog minf $ do
    patchFrom (tableMeta cli) (mkPatch <$>new)
  registerDynamic (void $ do
    now <- liftIO getCurrentTime
    let new = removeSchema clientId  now inf six
    runDynamic $ transactionNoLog minf $ do
      patchFrom (tableMeta cli) (mkPatch <$>new))



addClientLogin inf =  transactionNoLog inf $ do
    now <- liftIO getCurrentTime
    let
      row = ClientState Nothing (startTime now) []
      obj = liftTable' inf "clients" (encodeT row)
      m = lookMeta inf  "clients"
    i <-  insertFrom  m obj
    lift . registerDynamic . closeDynamic $ do
      now <- liftIO getCurrentTime
      let
        pt = [PAttr (lookKey inf "clients" "up_time") (PInter False (ER.Finite $ PAtom (STime $ STimestamp now) , False))]
      transactionNoLog inf $ do
        patchFrom m  (index i,PatchRow pt)
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
  transactionNoLog minf $ do
    patchFrom mcli (mkPatch cpatch)
  registerDynamic (void $ do
    now <- getCurrentTime
    let dpatch = removeTable  cid now table six ix
    closeDynamic $ transactionNoLog minf $ do
      patchFrom mcli (mkPatch dpatch))

atClient idClient =  (G.Idex [LeftTB1 $ Just $ num idClient],)
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
    where arr = IsoArrow (\(i,j) -> ClientPK i j ) (\(ClientPK i j) -> (i,j))

instance DecodeTable ClientRowSelection where
  isoTable = iassoc (isoArrow arr) ( prim  "up_time") (nest "data_index")
    where arr = (\(i,j) -> ClientRowSelection i j , \(ClientRowSelection i j) -> (i,j) )

instance DecodeTable ClientTableSelection where
  isoTable = iassoc3  (isoArrow arr) (identity <$$>prim  "table") (prim "up_time") (nest "selection")
    where arr = (\(i,j,k) -> ClientTableSelection i j k, \(ClientTableSelection i j k ) -> (i,j,k) )

instance DecodeTable ClientSchemaSelection where
  isoTable = iassoc3  (isoArrow arr) (identity <$$>prim  "schema") (prim "up_time") (nest "selection")
    where arr = (\(i,j,k) -> ClientSchemaSelection i j k, \(ClientSchemaSelection i j k ) -> (i,j,k) )

instance DecodeTable ClientState where
  isoTable = iassoc3  (isoArrow arr) (prim"id") (prim "up_time") (nest "selection")
    where arr = (\(i,j,k) -> ClientState i j k  , \(ClientState i j k ) -> (i,j,k) )

instance DecodeTable AuthCookies where
  isoTable  = iassoc3 (isoArrow arr)  (identity  <$$> prim "username") (identity  <$$> prim "cookie") (identity  <$$> prim "creation_date")
    where arr = (\(i,j,k) -> AuthCookies i j k,\(AuthCookies i j k) -> (i,j,k))

time = TB1  . STime . STimestamp
num = TB1 . SNumeric

data AuthCookies
  = AuthCookies
  { client :: Text
  , cookie :: Int
  , creation_date :: UTCTime
  } deriving(Eq,Show)

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
  (_,_,clientState,_,_)  <- refTables' metainf (lookTable metainf "clients") Nothing (WherePredicate (AndColl [PrimColl $ fixrel (keyRef (lookKey metainf "clients" "id") , Left (num clientId,Equals))]))
  return (fmap (decodeT. mapKey' keyValue). getClient metainf clientId <$> clientState)

indexTable inf (tix,table) = join . fmap lookT
  where
    lookT iv = do
      let tables = table_selection iv
      atMay tables tix

listRows inf table =  maybe []  row_selection


