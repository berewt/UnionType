module Data.Union.Fix

import Data.Union
import public Data.List

%default total
%access public export

data FuncUnion = MkFuncUnion (List (Type -> Type))

inter : FuncUnion -> Type -> Type
inter (MkFuncUnion xs) = Union xs

wrapUnion : List (Type -> Type) -> Type -> Type
wrapUnion = inter . MkFuncUnion

data Fix' : (f : FuncUnion) -> Type where
  In : inter f (Fix' f) -> Fix' f

Fix : List (Type -> Type) -> Type
Fix = Fix' . MkFuncUnion

Algebra : (f : Type -> Type) -> (a: Type) -> Type
Algebra f a = f a -> a

interface FAlgebra (name : Type) (f: Type -> Type) (a : Type) where
  algebra : name -> Algebra f a

FAlgebra name (Union []) a where
  algebra _ = \x => absurd x

(FAlgebra name f a, FAlgebra name (Union fs) a) => FAlgebra name (Union (f::fs)) a where
  algebra n (MemberHere x) = algebra n x
  algebra n (MemberThere x) = algebra n x

foldAlgebra : Functor (inter $ MkFuncUnion f) => Algebra (inter $ MkFuncUnion f) a -> Fix f -> a
foldAlgebra alg l@(In x) = alg $ map (\y => foldAlgebra alg $ assert_smaller l y) x
