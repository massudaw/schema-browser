module Types.Inference
  (inferOperatorType
  ) where

import Types
import GHC.Stack

inferOperatorType ::
										 Show t =>
										 BinaryOperator -> KType t -> KType t
inferOperatorType (Flip (Flip e))  i = inferOperatorType e i
inferOperatorType e (KOptional i) = inferOperatorType e i
inferOperatorType e (KDelayed i) = inferOperatorType e i
inferOperatorType e (KSerial i) = inferOperatorType e i
inferOperatorType Contains  (KInterval i) = i
inferOperatorType (Flip Contains) i = KInterval i
inferOperatorType (AnyOp e ) (KArray i) = inferOperatorType e i
inferOperatorType (Flip (AnyOp e) ) (KArray i) =  KArray (inferOperatorType (Flip e) i)
inferOperatorType Equals i = i
inferOperatorType (Flip Equals) i = i
inferOperatorType IntersectOp i = i
inferOperatorType (Flip IntersectOp ) i = i
inferOperatorType o k = errorWithStackTrace (show (o,k))


