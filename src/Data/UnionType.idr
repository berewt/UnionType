||| UnionType is an alternative to sum type, which gives an easier access to the sum content
||| and that can be extended dynamically, whithout compromising type safety.
module Data.UnionType

import Data.List

%default total
%access export

||| Provide a value of the union and point to its type
public export
data Union : List Type -> Type where
  ||| Point to the first element of an Union
  ||| @ x The stored value
  ||| @ t The exact type of the union
  ||| @ ts The rest of the union
  MemberHere : (x:t) -> Union (t::ts)
  ||| Shift the provided value by one type
  ||| @ x The next step of the pointer
  ||| @ t The skipped type of the union
  ||| @ ts The rest of the union
  MemberThere : (x: Union ts) -> Union (t::ts)

Uninhabited (Union []) where
    uninhabited (MemberHere _) impossible
    uninhabited (MemberThere _) impossible

||| A partial order relation between unions
||| (totally fucked up if one of the List contains several times the same Type)
||| Sub xs ys is inhabited if each type of xs is in ys.
public export
data Sub : List Type -> List Type -> Type where
  SubZ : Sub [] ys
  SubK : Sub xs ys ->  Elem t ys -> Sub (t::xs) ys

||| Remove a type of an Union (if there are several element in the union, remove its first occurence)
||| @ ty The type to remove from the Union
||| @ ts The Union
public export
Retract : (ty: Type) -> (ts : List Type) -> {auto ne : NonEmpty ts} -> {auto e: Elem ty ts} -> List Type
Retract _ (y :: xs) {e = Here} = xs
Retract x (y :: []) {e = (There later)} = absurd later
Retract x (y :: z :: xs) {e = (There later)} = y :: Retract x (z::xs) {e=later}

||| A type that is provided when we want to fold an Union.
||| @ target The type produced by the fold
||| @ union The Union that can be fold by this element.
public export
data UnionFold : (target: Type) -> (union: Type) -> Type where
  Nil : UnionFold a (Union [])
  (::) : (t -> a) -> UnionFold a (Union ts) -> UnionFold a (Union (t::ts))

||| Create an Union instance from one of the Union value.
member : u -> {auto e: Elem u ts} -> Union ts
member x {e=Here} = MemberHere x
member x {e=There later} = MemberThere (member x {e=later})


||| Try to extract a given type from the union.
get : Union ts -> {auto e: Elem t ts} -> Maybe t
get (MemberHere x)       {e=Here}    = Just x
get (MemberHere x)       {e=There _} = Nothing
get (MemberThere x)      {e=Here}    = Nothing
get (MemberThere later) {e=(There l)} = get later {e=l}

||| Fold a whole union to compute a given type
||| @ fs gathers the function that should be apply in each case of the union
foldUnion : (fs: UnionFold a (Union ts)) -> Union ts -> a
foldUnion [] (MemberHere _) impossible
foldUnion [] (MemberThere _) impossible
foldUnion (f :: _) (MemberHere y) = f y
foldUnion (f :: xs) (MemberThere y) = foldUnion xs y

Cast (Union [l]) l where
  cast (MemberHere x) = x
  cast (MemberThere x) = absurd x

Cast (Union [l, r]) (Either l r) where
  cast (MemberHere x) = Left x
  cast (MemberThere (MemberHere x)) = Right x
  cast (MemberThere (MemberThere x)) = absurd x

||| Remove a type from the union
retract : {ts: List Type} -> Union ts -> {auto ne : NonEmpty ts} -> {auto e: Elem t ts} -> Either (Union (Retract t ts)) t
retract (MemberHere x) {e = Here} = Right x
retract (MemberHere x) {e = (There Here)} = Left (MemberHere x)
retract (MemberHere x) {e = (There (There later))} = Left (MemberHere x)
retract (MemberThere x) {e = Here} = Left x
retract (MemberThere (MemberHere x)) {e = (There Here)} = Right x
retract (MemberThere (MemberThere x)) {e = (There Here)} = Left (MemberThere x)
retract (MemberThere x) {e = (There (There later))} = either (Left . MemberThere) Right $ retract x {e = There later}

private
subPreserveElem : Sub xs ys -> Elem t xs -> Elem t ys
subPreserveElem SubZ Here impossible
subPreserveElem SubZ (There _) impossible
subPreserveElem (SubK x Here) Here = Here
subPreserveElem (SubK x Here) (There later) = subPreserveElem x later
subPreserveElem (SubK x (There later)) Here = There later
subPreserveElem (SubK x (There y)) (There later) = subPreserveElem x later

||| Replace an Union with a larger Union.
||| The order of the elemnt in the targeted union doesn't need
||| to be the same than the one in the source union.
generalize : Union ts -> {auto s: Sub ts ts'} -> Union ts'
generalize (MemberHere x) {s=s} = member x {e=subPreserveElem s Here}
generalize (MemberThere x) {s = (SubK y z)} = generalize x {s=y}


Eq (Union []) where
  (==) x _ = absurd x
  (/=) x _ = absurd x

(Eq t, Eq (Union ts)) => Eq (Union (t::ts)) where
  (==) (MemberHere x) (MemberHere y) {t=t} = x == y
  (==) (MemberHere x) (MemberThere y) = False
  (==) (MemberThere x) (MemberHere y) = False
  (==) (MemberThere x) (MemberThere y) = x == y
  (/=) (MemberHere x) (MemberHere y) = x /= y
  (/=) (MemberHere x) (MemberThere y) = True
  (/=) (MemberThere x) (MemberHere y) = True
  (/=) (MemberThere x) (MemberThere y) = x /= y
