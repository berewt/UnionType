module Data.Union.TypedFix

import Data.Union.Internal.Union2
import public Data.Union.HFunctor
import public Data.List

%default total
%access public export

||| A type alias for algebras
Algebra : (f : (Type -> Type) -> Type -> Type) -> (e : Type -> Type) -> Type
Algebra f e = {w : _} -> f e w -> e w


||| The algebra interface.
||| @name The identifier of the algebra that should be use
||| @f The element that should be computed
||| @e The higher kind type of the union
interface HAlgebra (name : Type) (f : (Type -> Type) -> Type -> Type) (e : Type -> Type) where
  algebra : name -> Algebra f e

HAlgebra name (Union []) e where
  algebra _ = \x => absurd x

(HAlgebra name f e, HAlgebra name (Union fs) e) => HAlgebra name (Union (f::fs)) e where
  algebra name (MemberHere x) = algebra name x
  algebra name (MemberThere x) = algebra name x

||| The fix point like for Union
data Fix : (f : List ((Type -> Type) -> Type -> Type)) -> Type -> Type where
  In : Union f (Fix f) w -> Fix f w

lift : f (Fix fs) w -> {auto prf : Elem f fs} -> Fix fs w
lift x = In $ member x

||| Recursively apply an algebra on a Fix element
cata : HFunctor (Union fs) => (alg : Algebra (Union fs) e) -> Fix fs w -> e w
cata alg l@(In x) = alg $ hmap (\y => cata alg $ assert_smaller l y) x
