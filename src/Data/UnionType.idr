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

public export
data Sub : Vect n Type -> Vect k Type -> Type where
  SubZ : Sub [] ys
  SubK : Sub xs ys ->  Elem t ys -> Sub (t::xs) ys

subPreserveElem :  Sub xs ys -> Elem t xs -> Elem t ys
subPreserveElem SubZ Here impossible
subPreserveElem SubZ (There _) impossible
subPreserveElem (SubK x Here) Here = Here
subPreserveElem (SubK x Here) (There later) = subPreserveElem x later
subPreserveElem (SubK x (There later)) Here = There later
subPreserveElem (SubK x (There y)) (There later) = subPreserveElem x later

public export
Retract : (t: Type) -> (ts : Vect (S n) Type) -> {auto e: Elem t ts} -> Vect n Type
Retract _ (y :: xs) {e = Here} = xs
Retract x (y :: []) {e = (There later)} = absurd later
Retract x (y :: z :: xs) {e = (There later)} = y :: Retract x (z::xs) {e=later}


export
retract : {ts: Vect (S n) Type} -> Union ts -> {auto e: Elem t ts} -> Either (Union (Retract t ts)) t
retract (MemberHere x) {e = Here} = Right x
retract (MemberHere x) {e = (There Here)} = Left (MemberHere x)
retract (MemberHere x) {e = (There (There later))} = Left (MemberHere x)
retract (MemberThere x) {e = Here} = Left x
retract (MemberThere (MemberHere x)) {e = (There Here)} = Right x
retract (MemberThere (MemberThere x)) {e = (There Here)} = Left (MemberThere x)
retract (MemberThere x) {e = (There (There later))} = either (Left . MemberThere) Right $ retract x {e = There later}

export
member : u -> {auto e: Elem u ts} -> Union ts
member x {e=Here} = MemberHere x
member x {e=There later} = MemberThere (member x {e=later})

export
generalize : Union ts -> {auto s: Sub ts ts'} -> Union ts'
generalize (MemberHere x) {s=s} = member x {e=subPreserveElem s Here}
generalize (MemberThere x) {s = (SubK y z)} = generalize x {s=y}

export
get : Union ts -> {auto e: Elem t ts} -> Maybe t
get (MemberHere x)       {e=Here}    = Just x
get (MemberHere x)       {e=There _} = Nothing
get (MemberThere x)      {e=Here}    = Nothing
get (MemberThere later) {e=(There l)} = get later {e=l}

public export
data UnionMapping : Type -> Type -> Type where
  Nil : UnionMapping a (Union [])
  (::) : (t -> a) -> UnionMapping a (Union ts) -> UnionMapping a (Union (t::ts))

export
foldUnion : UnionMapping a (Union ts) -> Union ts -> a
foldUnion [] (MemberHere _) impossible
foldUnion [] (MemberThere _) impossible
foldUnion (f :: _) (MemberHere y) = f y
foldUnion (f :: xs) (MemberThere y) = foldUnion xs y

Cast (Union [l]) l where
  cast (MemberHere x) = x
  cast (MemberThere x) = absurd x

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
