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
-- data Fix : (f : List ((Type -> Type) -> Type -> Type)) -> Type -> Type where
--  In : Union f (Fix f) w -> Fix f w
record Fix (f : List ((Type -> Type) -> Type -> Type)) w where
  constructor In
  outFix : Union f (Fix f) w

||| Lift a value into a Fix
lift : f (Fix fs) w -> {auto prf : Elem f fs} -> Fix fs w
lift x = In $ member x

||| Recursively apply an algebra on a Fix element
cata : HFunctor (Union fs) => (alg : Algebra (Union fs) e) -> Fix fs w -> e w
cata alg l@(In x) = alg $ hmap (\y => cata alg $ assert_smaller l y) x

||| A sysnonym for cata
foldFix : HFunctor (Union fs) => (alg : Algebra (Union fs) e) -> Fix fs w -> e w
foldFix = cata

||| Transform a Fix in a bottom-up manner
trans : HFunctor (Union fs) => ({w : _ } -> Fix fs w -> Fix fs w) -> Fix fs w -> Fix fs w
trans func = cata (func . In)


||| Modify the sum type of a fix
mapFix : (HFunctor (Union fs), HFunctor (Union gs))
      => ({e,w : _} -> Union fs e w -> Union gs e w) -> Fix fs w -> Fix gs w
mapFix func = cata (In . hmap In . func . hmap outFix)

generalise : (HFunctor (Union fs), HFunctor (Union gs))
          => Fix fs w -> {auto prf: Sub fs gs} -> Fix gs w
generalise f = mapFix (\x => generalize x) f

generalize : (HFunctor (Union fs), HFunctor (Union gs))
          => Fix fs w -> {auto prf: Sub fs gs} -> Fix gs w
generalize = generalise
