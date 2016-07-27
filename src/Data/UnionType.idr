||| UnionType is an alternative to sum type, which gives an easier access to the sum content
||| and that can be extended dynamically, whithout compromising type safety.
module Data.UnionType

import public Data.List

%default total
%access export

||| Provide a value of the union and point to its type
public export
data Union : List Type -> Type where
  ||| Point to the first element of an Union
  ||| @ x The stored value
  ||| @ ty The exact type of the union
  ||| @ xs The rest of the union
  MemberHere : (x: ty) -> Union (ty::xs)
  ||| Shift the provided value by one type
  ||| @ x The next step of the pointer
  ||| @ ty The skipped type of the union
  ||| @ xs The rest of the union
  MemberThere : (x: Union xs) -> Union (ty::xs)

Uninhabited (Union []) where
    uninhabited (MemberHere _) impossible
    uninhabited (MemberThere _) impossible

||| A partial order relation between unions
||| Type occurences are not taken into account
||| (ie.: Sub (Union [Nat, Nat]) (Union [Nat]) is inhabited)
||| Sub xs ys is inhabited if each type of xs is in ys.
public export
data Sub : List Type -> List Type -> Type where
  SubZ : Sub [] ys
  SubK : Sub xs ys ->  Elem ty ys -> Sub (ty::xs) ys

||| Remove a type of an Union.
||| If there are several element in the union, remove only its first occurence.
||| @ ty The type to remove from the Union
||| @ ts The Union
public export
Retract : (ty: Type) -> (ts : List Type) -> {auto ne : NonEmpty ts} -> {auto p: Elem ty ts} -> List Type
Retract _ (y :: ts) {p = Here} = ts
Retract ty (y :: []) {p = (There later)} = absurd later
Retract ty (y :: z :: ts) {p = (There later)} = y :: Retract ty (z::ts) {p = later}

||| A type that is provided when we want to fold an Union.
||| @ target The type produced by the fold
||| @ union The Union that can be fold by this element.
public export
data UnionFold : (target: Type) -> (union: Type) -> Type where
  Nil : UnionFold a (Union [])
  (::) : (ty -> a) -> UnionFold a (Union ts) -> UnionFold a (Union (ty::ts))

||| Create an Union instance from one of the Union value.
member : u -> {auto p: Elem u ts} -> Union ts
member x {p = Here} = MemberHere x
member x {p = There later} = MemberThere (member x {p = later})


||| Try to extract a given type from the union.
get : Union ts -> {auto p: Elem ty ts} -> Maybe ty
get (MemberHere x)      {p = Here}      = Just x
get (MemberHere x)      {p = There _}   = Nothing
get (MemberThere x)     {p = Here}      = Nothing
get (MemberThere later) {p = (There l)} = get later {p = l}

||| Fold a whole union to compute a given type
||| @ fs gathers the function that should be apply in each case of the union
foldUnion : (fs: UnionFold a (Union xs)) -> Union xs -> a
foldUnion [] (MemberHere _) impossible
foldUnion [] (MemberThere _) impossible
foldUnion (f :: _) (MemberHere y) = f y
foldUnion (f :: xs) (MemberThere y) = foldUnion xs y

Cast (Union [ty]) ty where
  cast (MemberHere x) = x
  cast (MemberThere x) = absurd x

Cast l (Union [l]) where
  cast x = (MemberHere x)

Cast (Union [l, r]) (Either l r) where
  cast (MemberHere x) = Left x
  cast (MemberThere (MemberHere x)) = Right x
  cast (MemberThere (MemberThere x)) = absurd x

Cast (Either l r) (Union [l, r]) where
  cast (Left x) = (MemberHere x)
  cast (Right x) = (MemberThere (MemberHere x))

||| Remove a type from the union
retract : {xs: List Type} -> Union xs -> {auto ne : NonEmpty xs} -> {auto p: Elem ty xs} -> Either (Union (Retract ty xs)) ty
retract (MemberHere x) {p = Here} = Right x
retract (MemberHere x) {p = (There Here)} = Left (MemberHere x)
retract (MemberHere x) {p = (There (There later))} = Left (MemberHere x)
retract (MemberThere x) {p = Here} = Left x
retract (MemberThere (MemberHere x)) {p = (There Here)} = Right x
retract (MemberThere (MemberThere x)) {p = (There Here)} = Left (MemberThere x)
retract (MemberThere x) {p = (There (There later))} = either (Left . MemberThere) Right $ retract x {p = There later}

private
subPreserveElem : Sub xs ys -> Elem ty xs -> Elem ty ys
subPreserveElem SubZ Here impossible
subPreserveElem SubZ (There _) impossible
subPreserveElem (SubK x Here) Here = Here
subPreserveElem (SubK x Here) (There later) = subPreserveElem x later
subPreserveElem (SubK x (There later)) Here = There later
subPreserveElem (SubK x (There y)) (There later) = subPreserveElem x later

||| Replace an Union with a larger Union.
||| The order of the elemnt in the targeted union doesn't need
||| to be the same than the one in the source union.
generalize : Union xs -> {auto s: Sub xs ys} -> Union ys
generalize (MemberHere x) {s = s} = member x {p=subPreserveElem s Here}
generalize (MemberThere x) {s = (SubK y z)} = generalize x {s=y}


Eq (Union []) where
  (==) x _ = absurd x
  (/=) x _ = absurd x

(Eq ty, Eq (Union xs)) => Eq (Union (ty::xs)) where
  (==) (MemberHere x) (MemberHere y) = x == y
  (==) (MemberHere x) (MemberThere y) = False
  (==) (MemberThere x) (MemberHere y) = False
  (==) (MemberThere x) (MemberThere y) = x == y
  (/=) (MemberHere x) (MemberHere y) = x /= y
  (/=) (MemberHere x) (MemberThere y) = True
  (/=) (MemberThere x) (MemberHere y) = True
  (/=) (MemberThere x) (MemberThere y) = x /= y
