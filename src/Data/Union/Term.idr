module Data.Union.Term

import Data.Union
import public Data.List

%default total
%access public export

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


||| Fold a 'Term'
||| @pure The function applied on pure Term
||| @imp  The function applied on impure Term
||| @x    The folded element
foldTerm : Functor (Union f) => (pure : a -> b) -> (imp : Union f b -> b) -> (x : Term f a) -> b
foldTerm pure imp (Pure x) = pure x
foldTerm pure imp l@(Impure x) = imp $ map (\y => foldTerm pure imp $ assert_smaller l y) x
