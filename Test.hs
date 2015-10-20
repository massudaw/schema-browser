module Test where

import Postgresql
import Schema

import Test.Tasty
import Test.Tasty.HUnit

import qualified Data.Text.Lazy as T

main = defaultMain tests

tests :: TestTree
tests = testGroup "Tests" [unitTests,unitTestsIncendio,unitTestsIncendioMeta]

unitTests = testGroup "QueryAllTest"
    $ fmap (\i -> testCase i (testMetaQuery (T.pack i) >> return () )) ["rec_root","rec_root_fk","rec_test_fk","test_inline","view_fks","view_pk"]
unitTestsIncendioMeta = testGroup "QueryAllIncendioMeta"
    $ fmap (\i -> testCase i (testFireMetaQuery (T.pack i) >> return () )) ["view_rec_pk"]
unitTestsIncendio = testGroup "QueryAllIncendio"
    $ fmap (\i -> testCase i (testFireQuery (T.pack i) >> return () )) ["fire_project","pricing","art"]

