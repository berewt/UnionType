module Data.UnionType

import Data.Vect

%default total

data Union : Vect n Type -> Type where
  Member : t -> Elem t ts -> Union ts

member : u -> {auto e: Elem u (t::ts)} -> Union (t::ts)
member x {e} = Member x e

unionToMaybe : Union ts -> {auto e: Elem t ts} -> Maybe t
unionToMaybe (Member x Here)          {e=Here}      = Just x
unionToMaybe (Member x (There later)) {e=(There l)} = unionToMaybe (Member x later) {e=l}
unionToMaybe (Member x Here)          {e=(There _)} = Nothing
unionToMaybe (Member x (There _))     {e=Here}      = Nothing

UnionCata : Type -> Vect n Type -> Type
UnionCata a [] = a
UnionCata a (x :: xs) = Lazy (x -> a) -> UnionCata a xs

foldUnion : Union ts -> UnionCata a ts
foldUnion (Member x Here) = \f => foldUnion' (f x)
  where
    foldUnion' : {xs : Vect k Type} -> (x : a) -> UnionCata a xs
    foldUnion' {xs=[]} x = x
    foldUnion' {xs=_::xs'} x = const $ foldUnion' {xs=xs'} x
foldUnion (Member x (There later)) = const $ foldUnion (Member x later)

ixElem : (Elem t ts) -> Nat
ixElem Here = Z
ixElem (There later) = S $ ixElem later

ixUnion : Union ts -> Nat
ixUnion (Member _ e) = ixElem e

lteIxElemVectLength : (ts : Vect n x) -> (e : Elem t ts) -> LT (ixElem e) n
lteIxElemVectLength [] Here impossible
lteIxElemVectLength [] (There _) impossible
lteIxElemVectLength (x :: xs) Here = LTESucc LTEZero
lteIxElemVectLength (x :: xs) (There later) = LTESucc (lteIxElemVectLength xs later)

lteIxUnionVectLength : (ts : Vect n Type) -> (e : Union ts) -> LT (ixUnion e) n
lteIxUnionVectLength [] (Member _ Here) impossible
lteIxUnionVectLength [] (Member _ (There _)) impossible
lteIxUnionVectLength (t :: xs) (Member y Here) = LTESucc LTEZero
lteIxUnionVectLength (x :: xs) (Member y (There later)) = LTESucc $ lteIxUnionVectLength xs (Member y later)
