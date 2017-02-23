module Main

import Data.Union1

data Fix : (Type -> Type) -> Type where
  In : f (Fix f) -> Fix f

out : Fix f -> f (Fix f)
out (In x) = x

Algebra : (f : Type -> Type) -> (a: Type) -> Type
Algebra f a = f a -> a

foldAlgebra : Functor f => Algebra f a -> Fix f -> a
foldAlgebra func (In x) = func $ map (foldAlgebra func) x

interface FAlgebra (name : Type) (f: Type -> Type) (a : Type) where
  algebra : name -> Algebra f a

FAlgebra name (Union1 []) a where
  algebra _ = \x => absurd x

(FAlgebra name f a, FAlgebra name (Union1 fs) a) => FAlgebra name (Union1 (f::fs)) a where
  algebra n (MemberHere1 x) = algebra n x
  algebra n (MemberThere1 x) = algebra n x

data ValType a = Val Int
data AddType a = Add a a

Fix' : List (Type -> Type) -> Type
Fix' fs = Fix (Union1 fs)


val : Int -> {auto p: Elem ValType fs} -> Fix' fs
val x = In $ member $ Val x

add : Fix' fs -> Fix' fs -> {auto p: Elem AddType fs} -> Fix' fs
add x y = In $ member $ Add x y

Functor ValType where
  map _ (Val x) = Val x

Functor AddType where
  map func (Add x y) =  Add (func x) (func y)


data Eval = EvalWitness

FAlgebra Eval ValType Int where
  algebra _ (Val x) = x

FAlgebra Eval AddType Int where
  algebra _ (Add x y) = x + y

eval : (Functor f, FAlgebra Eval f Int) => Fix f -> Int
eval = foldAlgebra (algebra EvalWitness)

sampleFix : Fix' [ValType, AddType]
sampleFix = add (add (val 101) (val 20)) (val 1216)

data Func : Type where
  FuncUnion : List (Type -> Type) -> Func

inter : Func -> Type -> Type
inter (FuncUnion xs) = Union1 xs

data TotalFix : (f : Func) -> Type where
  Inn : inter f (TotalFix f) -> TotalFix f

total
outt : TotalFix f -> inter f (TotalFix f)
outt (Inn g) = g

TotalFix' : List (Type -> Type) -> Type
TotalFix' xs = TotalFix (FuncUnion xs)

total
val' : Int -> {auto p: Elem ValType fs} -> TotalFix' fs
val' x = Inn $ member (Val x)

total
add' : TotalFix' fs -> TotalFix' fs -> {auto p: Elem AddType fs} -> TotalFix' fs
add' x y = Inn $ member (Add x y)

sampleFix' : TotalFix' [ValType, AddType]
sampleFix' = add' (add' (val' 101) (val' 20)) (val' 1216)

