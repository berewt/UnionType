module Data.Union.Fix

import Data.Union
import public Data.List

%default total
%access public export

||| The Standard fix point definition
data Fix : (f : (List (Type -> Type))) -> Type where
  In : Union f (Fix f) -> Fix f

||| A type alias for algebras
Algebra : (f : Type -> Type) -> (a: Type) -> Type
Algebra f a = f a -> a

||| The algebra interface.
||| @name The identifier of the algebra that should be use
||| @f The element that should be computed
||| @result The computation result
interface FAlgebra (name : Type) (f: Type -> Type) (result : Type) where
  algebra : name -> Algebra f result

FAlgebra name (Union []) a where
  algebra _ = \x => absurd x

(FAlgebra name f a, FAlgebra name (Union fs) a) => FAlgebra name (Union (f::fs)) a where
  algebra n (MemberHere x) = algebra n x
  algebra n (MemberThere x) = algebra n x

||| Recursively apply an algebra on a Fix element
foldAlgebra : Functor (Union f) => Algebra (Union f) a -> Fix f -> a
foldAlgebra alg l@(In x) = alg $ map (\y => foldAlgebra alg $ assert_smaller l y) x
