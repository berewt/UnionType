module Data.UnionType

import Data.Vect

%default total

public export
data Union : Vect n Type -> Type where
  MemberHere : (x:t) -> Union (t::ts)
  MemberThere : Union ts -> Union (t::ts)

Uninhabited (Union []) where
    uninhabited (MemberHere _) impossible
    uninhabited (MemberThere _) impossible

export
member : u -> {auto e: Elem u ts} -> Union ts
member x {e=Here} = MemberHere x
member x {e=There later} = MemberThere (member x {e=later})


export
unionToMaybe : Union ts -> {auto e: Elem t ts} -> Maybe t
unionToMaybe (MemberHere x)       {e=Here}    = Just x
unionToMaybe (MemberHere x)       {e=There _} = Nothing
unionToMaybe (MemberThere x)      {e=Here}    = Nothing
unionToMaybe (MemberThere later) {e=(There l)} = unionToMaybe later {e=l}

export
as : t -> Union ts -> {auto e: Elem t ts} -> Maybe t
as _ x {e=e} = unionToMaybe x {e=e}

export
headOrReduce : (u : Union (t::ts)) -> Either (Union ts) t
headOrReduce (MemberThere x) = Left x
headOrReduce (MemberHere x) = Right x


public export
UnionCata : Type -> Vect n Type -> Type
UnionCata a [] = a
UnionCata a (x :: xs) = Lazy (x -> a) -> UnionCata a xs

export
foldUnion : Union ts -> UnionCata a ts
foldUnion (MemberHere x) = \f => foldUnion' (f x)
  where
    foldUnion' : {xs : Vect k Type} -> (x : a) -> UnionCata a xs
    foldUnion' {xs=[]} x = x
    foldUnion' {xs=_::xs'} x = const $ foldUnion' {xs=xs'} x
foldUnion (MemberThere later) = const $ foldUnion later

export
unionToValue : Union [l] -> l
unionToValue (MemberHere x) = x
unionToValue (MemberThere x) = absurd x

export
unionToEither : Union [l, r] -> Either l r
unionToEither (MemberHere x) = Left x
unionToEither (MemberThere (MemberHere x)) = Right x
unionToEither (MemberThere (MemberThere x)) = absurd x

export
updateUnion : (t -> t) -> Union ts -> {auto e: Elem t ts} -> Union ts
updateUnion f (MemberHere y) {e = Here}          = MemberHere (f y)
updateUnion f (MemberHere y) {e = (There later)} = MemberHere y
updateUnion f (MemberThere y) {e = Here} = MemberThere y
updateUnion f (MemberThere y) {e = (There later)} = MemberThere (updateUnion f y {e=later})

ixUnion : Union ts -> Nat
ixUnion (MemberHere _) = Z
ixUnion (MemberThere later) = S (ixUnion later)

lteIxUnionVectLength : (ts : Vect n Type) -> (e : Union ts) -> LT (ixUnion e) n
lteIxUnionVectLength [] (MemberHere _) impossible
lteIxUnionVectLength [] (MemberThere _) impossible
lteIxUnionVectLength (t :: xs) (MemberHere _) = LTESucc LTEZero
lteIxUnionVectLength (x :: xs) (MemberThere later) = LTESucc $ lteIxUnionVectLength xs later
