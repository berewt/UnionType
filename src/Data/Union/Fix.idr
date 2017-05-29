module Data.Union.Fix

import Data.Union
import public Data.List

%default total
%access public export

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


||| The fix point like for Union
data Fix : (f : (List (Type -> Type))) -> Type where
  In : Union f (Fix f) -> Fix f

||| Recursively apply an algebra on a Fix element
cata : Functor (Union f) => Algebra (Union f) a -> Fix f -> a
cata alg l@(In x) = alg $ map (\y => cata alg $ assert_smaller l y) x


||| A sysnonym for cata
foldFix : Functor (Union f) => Algebra (Union f) a -> Fix f -> a
foldFix = cata


||| Transform a Fix in a bottom-up manner
trans : Functor (Union f) => (Fix f -> Fix f) -> Fix f -> Fix f
trans func = cata (func . In)

||| Query a Fix
query : Foldable (Union f) => (Fix f -> r) -> (r -> r -> r) -> Fix f -> r
query q func l@(In x)
  = foldl (\r,y => func r $ query q func $ assert_smaller l y) (q l) x
