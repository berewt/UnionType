module Main

import Data.Union
import Data.Union.Fix

data ValType a b = Val a

val : Num a => a -> {auto p : Elem (ValType a) xs } -> Fix xs
val x = In $ member (Val x)


data AddType a = Add a a

add : Fix xs -> Fix xs -> {auto p : Elem AddType xs} -> Fix xs
add x y = In $ member (Add x y)

Functor (ValType a) where
  map _ (Val x) = Val x

Functor AddType where
  map func (Add x y) =  Add (func x) (func y)


data Eval = MkEval

Num a => FAlgebra Eval (ValType a) a where
  algebra _ (Val x) = x

FAlgebra Eval AddType Int where
  algebra _ (Add x y) = x + y

eval : ( Functor (wrapUnion fs)
       , FAlgebra Eval (wrapUnion fs) Int)
    => Fix fs -> Int
eval = foldAlgebra (algebra MkEval)
