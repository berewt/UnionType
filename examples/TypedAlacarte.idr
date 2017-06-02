module Main

import public Data.Union.Internal.Union2
import public Data.Union.TypedFix
import public Data.Union.HFunctor



data ValType : (e : Type -> Type) -> (w : Type) -> Type where
  Val : w -> ValType e w

HFunctor ValType where
  hmap _ (Val x) = Val x

val : a -> {auto p : Elem ValType ts} -> Fix ts a
val x = lift (Val x)


data AddType : (e : Type -> Type) -> (w : Type) -> Type where
  Add : Num w => e w -> e w -> AddType e w

HFunctor AddType where
  hmap func (Add x y) = Add (func x) (func y)

add : Num a => Fix ts a -> Fix ts a -> {auto p : Elem AddType ts} -> Fix ts a
add x y = lift $ Add x y


data IteType : (e : Type -> Type) -> (w : Type) -> Type where
  Ite : e Bool -> e a -> e a -> IteType e a

ite : Fix ts Bool -> Fix ts a -> Fix ts a -> {auto p : Elem IteType ts} -> Fix ts a
ite c t f = lift $ Ite c t f

HFunctor IteType where
  hmap func (Ite c t f) = Ite (func c) (func t) (func f)


data EqType : (e : Type -> Type) -> (w : Type) -> Type where
  Eq : e a -> e a -> EqType e Bool

eq : Fix ts a -> Fix ts a -> {auto p : Elem EqType ts} -> Fix ts Bool
eq x y = lift $ Eq x y

extract : Fix [ValType] a -> a
extract (In (MemberHere (Val x))) = x
extract (In (MemberThere x)) = absurd x


example : Fix [ValType, AddType] Nat
example = add (add (val 10) (val 20)) (val 12)

example2 : Num a => Bool -> Fix [ValType, IteType, AddType] a
example2 b = ite (val b) (add (add (val 10) (val 20)) (val 12)) (val 24)

Algebra : (f : (Type -> Type) -> Type -> Type) -> (e : Type -> Type) -> Type
Algebra f e = {w : _} -> f e w -> e w


data Eval = MkEval

eval : (HFunctor (Union fs)
       , HAlgebra Eval (Union fs) (Fix [ValType])
       ) => {w : _ } -> Fix fs w -> w
eval {fs} {w} = extract . cata (algebra MkEval)


HAlgebra Eval ValType (Fix [ValType]) where
  algebra _ (Val x) = val x

HAlgebra Eval AddType (Fix [ValType]) where
  algebra _ (Add x y) = val $ extract x + extract y

HAlgebra Eval IteType (Fix [ValType]) where
  algebra _ (Ite c t f) = val $ if extract c then extract t else extract f


test21 : Bool -> Nat
test21 = eval . example2

test22 : Bool -> Nat
test22 = eval . example2
