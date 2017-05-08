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
foldFix : Functor (Union f) => Algebra (Union f) a -> Fix f -> a
foldFix alg l@(In x) = alg $ map (\y => foldFix alg $ assert_smaller l y) x


||| The Free Monad like construct for Union
data Term : (f : (List (Type -> Type))) -> Type -> Type where
  Pure : a -> Term f a
  Impure : Union f (Term f a) -> Term f a

Functor (Union f) => Functor (Term f) where
    map func (Pure x) = Pure $ func x
    map func t@(Impure x) = Impure $ map (\y => map func $ assert_smaller t y) x

Functor (Union f) => Applicative (Term f) where
  pure = Pure
  (<*>) (Pure func) x = map func x
  (<*>) t@(Impure func) x = Impure $ map (\y => (assert_smaller t y) <*> x) func

Functor (Union f) => Monad (Term f) where
  (>>=) (Pure x) func = func x
  (>>=) t@(Impure x) func = Impure $ map (\y => (assert_smaller t y) >>= func) x

foldTerm : Functor (Union f) => (a -> b) -> (Union f b -> b) -> Term f a -> b
foldTerm pure imp (Pure x) = pure x
foldTerm pure imp l@(Impure x) = imp $ map (\y => foldTerm pure imp $ assert_smaller l y) x
