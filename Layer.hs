{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE EmptyDataDecls    #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes       #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeFamilies      #-}

import Database.Persist
import           Database.Persist.Postgresql
import           Database.Persist.TH
import           Control.Monad.IO.Class  (liftIO)
import Data.Time
import Data.Functor.Identity


share [mkPersist sqlSettings, mkMigrate "migrateAll"] [persistLowerCase|
Order
    name String
    client ClientId
    local Int
Client
    name String
Operator
    name String
    client ClientId
    local Int
Machine
    name String
    client ClientId
User
    name String
    deriving Show
UserClient
    user ClientId
    client UserId
Service
    time_start UTCTime
    time_end UTCTime
    machine MachineId
    operator Int
    order Int
|]

type family Family f :: *
type instance Family Rational = Int
type instance Family Double = Int


s1 :: ForeignRelation Int Double
s1 = EntityValue 1 1.2

s5 :: ForeignRelation Int Rational
s5 = EntityValue 1 1.0

s2 :: ForeignRelation Double Double
s2 = EntityValue  1.2 2

s3 :: ForeignRelation Rational Rational
s3 = EntityValue  1.0 3

s4 :: ForeignRelation Int (Double,Rational)
s4 =  EntityValue   1  (2.0,3.0)

graph :: ForeignRelation Int  Int
graph = ProductRelation (ForeignRelation s1 s2, ForeignRelation s5 s3) s4


data ForeignRelation i j = forall a b . (Show a , Show b) => ProductRelation (ForeignRelation i a , ForeignRelation i b)  (ForeignRelation j (a,b) )
                         | forall k . Show k => ForeignRelation (ForeignRelation i k ) (ForeignRelation k j )
                         | EntityValue i j

instance (Show i ,Show j) => Show (ForeignRelation i j) where
    show (EntityValue i j ) = "(normal = " ++ show i ++  " , projection = " ++ show j ++ ")"
    show (ProductRelation (m,n) j ) = show (m , n) ++  " -> " ++ show j
    show (ForeignRelation i j ) = "("  ++ show i  ++ ") -> (" ++ show j ++ ")"

connStr = "host=192.168.56.101 dbname=onet user=postgres password=queijo port=5432"

main :: IO ()
main =  withPostgresqlPool connStr 10 $ \pool -> do
  flip runSqlPersistMPool pool $ do
    runMigration migrateAll
{-
    johnId <- insert $ Person "John Doe" $ Just 35
    janeId <- insert $ Person "Jane Doe" Nothing

    insert $ BlogPost "My fr1st p0st" johnId
    insert $ BlogPost "One more for good measure" johnId

    oneJohnPost <- selectList [BlogPostAuthorId ==. johnId] [LimitTo 1]
    liftIO $ print (oneJohnPost :: [Entity BlogPost])

    john <- get johnId
    liftIO $ print (john :: Maybe Person)

    delete janeId
    deleteWhere [BlogPostAuthorId ==. johnId]
    -}

data Layer
    = Layer
    { projections :: [String]
    , base :: [Layer]
    , normalizing :: String
    , styles :: [Style]
    , name :: String}
    | Relation
    { attributes :: [String]
    , normalizing :: String
    , name :: String }
    deriving(Show)

data Style
    = Style
    { geom :: String
    , features :: Feature}
    deriving(Show)

data Feature
    =  Simple
    { single :: Strips }
    | Strips
    { featureParameter :: String
    , strips  :: [Strips]}
    deriving(Show)

data Strips
    = forall a. (Show a ,Num a) => Range
    { init :: a
    , end :: a
    , color :: Int }
    | Plain
    { color :: Int}

instance Show Strips where
    show ( Plain x ) = show x
    show ( Range x y z ) = "Range [" ++ show x ++ "," ++ show y ++ ") :: color " ++ show z
