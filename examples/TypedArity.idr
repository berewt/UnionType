module Main

import public Data.Union.Internal.Union2
import public Data.Union.TypedFix
import public Data.Union.HFunctor

%default total

data Val : (e : Type -> Type) -> (w : Type) -> Type where
  MkVal : w -> Val e w

HFunctor Val where
  hmap _ (MkVal x) = MkVal x

val : a -> {auto p : Elem Val ts} -> Fix ts a
val = lift . MkVal

extract : Fix [Val] a -> a
extract (In (MemberHere (MkVal x))) = x
extract (In (MemberThere x)) = absurd x


data Pair : (e : Type -> Type) -> (w : Type) -> Type where
  MkPair' : e a -> e b -> Pair e (a, b)

HFunctor Pair where
  hmap func (MkPair' x y) = MkPair' (func x) (func y)

pair : Fix ts a -> Fix ts b -> {auto p : Elem Pair ts} -> Fix ts (a, b)
pair x y = lift $ MkPair' x y



data Unary : (op : Type -> Type -> Type) -> (e : Type -> Type) -> (w : Type) -> Type where
  MkUnary : op i o -> e i -> Unary op e o

HFunctor (Unary op) where
  hmap func (MkUnary f x) = MkUnary f (func x)


data Binary : (op : Type -> Type -> Type -> Type) -> (e : Type -> Type) -> (w : Type) -> Type where
  MkBinary : op a b o -> e a -> e b -> Binary op e o

HFunctor (Binary op) where
  hmap func (MkBinary f x y) = MkBinary f (func x) (func y)



data Negate : Type -> Type -> Type where
  MkNegate : Neg a => Negate a a

neg : Neg a => Fix ts a -> {auto p : Elem (Unary Negate) ts} -> Fix ts a
neg = lift . MkUnary MkNegate

data Swap : Type -> Type -> Type where
  MkSwap : Swap (a,b) (b,a)

swap : Fix ts (a,b) -> {auto p : Elem (Unary Swap) ts} -> Fix ts (b,a)
swap = lift . MkUnary MkSwap

data First : Type -> Type -> Type where
  MkFirst : First (a,b) a

first : Fix ts (a,b) -> {auto p : Elem (Unary First) ts} -> Fix ts a
first = lift . MkUnary MkFirst

data Second : Type -> Type -> Type where
  MkSecond : Second (a,b) b

second : Fix ts (a,b) -> {auto p : Elem (Unary Second) ts} -> Fix ts b
second = lift . MkUnary MkSecond


data Arithmetic : Type -> Type -> Type -> Type where
  Add : Num a => Arithmetic a a a
  Subtract : Neg a => Arithmetic a a a
  Mult : Num a => Arithmetic a a a
  Divide : Fractional a => Arithmetic a a a

add : Num a => Fix ts a -> Fix ts a -> {auto p : Elem (Binary Arithmetic) ts} -> Fix ts a
add x y = lift $ MkBinary Add x y

subtract : Neg a => Fix ts a -> Fix ts a -> {auto p : Elem (Binary Arithmetic) ts} -> Fix ts a
subtract x y = lift $ MkBinary Subtract x y

mult : Num a => Fix ts a -> Fix ts a -> {auto p : Elem (Binary Arithmetic) ts} -> Fix ts a
mult x y = lift $ MkBinary Mult x y

divide : Fractional a => Fix ts a -> Fix ts a -> {auto p : Elem (Binary Arithmetic) ts} -> Fix ts a
divide x y = lift $ MkBinary Divide x y




data Eval = MkEval

eval : (HFunctor (Union fs)
       , HAlgebra Eval (Union fs) (Fix [Val])
       ) => {w : _ } -> Fix fs w -> w
eval {fs} {w} = extract . cata (algebra MkEval)


HAlgebra Eval Val (Fix [Val]) where
  algebra _ (MkVal x) = val x

HAlgebra Eval Pair (Fix [Val]) where
  algebra _ (MkPair' x y) = val $ (extract x, extract y)

HAlgebra Eval (Unary Negate) (Fix [Val]) where
  algebra _ (MkUnary MkNegate x) = val $ negate $ extract x

HAlgebra Eval (Unary Swap) (Fix [Val]) where
  algebra _ (MkUnary MkSwap x) = val $ swap $ extract x

HAlgebra Eval (Unary First) (Fix [Val]) where
  algebra _ (MkUnary MkFirst x) = val $ fst $ extract x

HAlgebra Eval (Unary Second) (Fix [Val]) where
  algebra _ (MkUnary MkSecond x) = val $ snd $ extract x


HAlgebra Eval (Binary Arithmetic) (Fix [Val]) where
  algebra _ (MkBinary Add x y) = val $ extract x + extract y
  algebra _ (MkBinary Subtract x y) = val $ extract x - extract y
  algebra _ (MkBinary Mult x y) = val $ extract x * extract y
  algebra _ (MkBinary Divide x y) = val $ extract x / extract y

test : Fix [Val] (Nat, String)
test = val (2, "foo")

test2 : Fix [Val, Pair, Unary Swap] (Nat, String)
test2 = swap (val ("foo", 2))

test3 : Fix [Val, Pair, Unary Swap] (Nat, String)
test3 = swap $ pair (val "foo") (val 2)

test4 : Fix ([Val, Pair] ++ map Unary [Swap, First]) (Nat, String)
test4 = swap $ pair (first (val ("foo", 4))) $ first (val (2, 'c'))

test5 : Fix [Val, Binary Arithmetic] Nat
test5 = add (val 10) (mult (val 3) (val 8))


