{-# LANGUAGE FlexibleInstances, DeriveFunctor  #-}
module Step where

import Query
import Warshal
import Data.Text.Lazy
import Data.Set (Set)

data Step a
  = SAttr (String,(Text, a -> String))
  | SFK (Set Text) [Step a]
  deriving(Show)

instance Show (a -> Maybe Showable) where
  show _ = ""

instance Show (a -> String) where
  show _ = ""

data FKEdit
  = FKEInsertGenerated
  | FKEInsertFind
  | FKEUpdateAttr
  | FKEUpdateFK
  deriving(Show)

data AEdit
  = AEInsert
  | AEUpdate
  deriving(Show)

data TEdit
  = TInsert
  | TUpdate
  | TDelete
  | TGenerated
  deriving(Show)

data TablePlan a = TablePlan TEdit Table [StepPlan a]

data StepPlan a
  = SPAttr AEdit Key a
  | SPFK FKEdit (Path (Set Key) (SqlOperation Table)) [StepPlan a]
  | TBPlan TEdit Table [StepPlan a]
  deriving(Show,Functor)



