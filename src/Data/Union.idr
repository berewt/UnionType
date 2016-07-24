module Data.UnionType

import Data.Vect

%default total

data Union : Vect n Type -> Type where
  MemberHere : (x:t) -> Union (t::ts)
  MemberThere : Union ts -> Union (t::ts)

member : u -> {auto e: Elem u ts} -> Union ts
member x {e=Here} = MemberHere x
member x {e=There later} = MemberThere (member x {e=later})

unionToMaybe : Union ts -> {auto e: Elem t ts} -> Maybe t
unionToMaybe (MemberHere x)       {e=Here}    = Just x
unionToMaybe (MemberHere x)       {e=There _} = Nothing
unionToMaybe (MemberThere x)      {e=Here}    = Nothing
unionToMaybe (MemberThere later) {e=(There l)} = unionToMaybe later {e=l}

UnionCata : Type -> Vect n Type -> Type
UnionCata a [] = a
UnionCata a (x :: xs) = Lazy (x -> a) -> UnionCata a xs

foldUnion : Union ts -> UnionCata a ts
foldUnion (MemberHere x) = \f => foldUnion' (f x)
  where
    foldUnion' : {xs : Vect k Type} -> (x : a) -> UnionCata a xs
    foldUnion' {xs=[]} x = x
    foldUnion' {xs=_::xs'} x = const $ foldUnion' {xs=xs'} x
foldUnion (MemberThere later) = const $ foldUnion later

ixUnion : Union ts -> Nat
ixUnion (MemberHere _) = Z
ixUnion (MemberThere later) = S (ixUnion later)

lteIxUnionVectLength : (ts : Vect n Type) -> (e : Union ts) -> LT (ixUnion e) n
lteIxUnionVectLength [] (MemberHere _) impossible
lteIxUnionVectLength [] (MemberThere _) impossible
lteIxUnionVectLength (t :: xs) (MemberHere _) = LTESucc LTEZero
lteIxUnionVectLength (x :: xs) (MemberThere later) = LTESucc $ lteIxUnionVectLength xs later
