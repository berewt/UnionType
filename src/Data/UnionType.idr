||| UnionType is an alternative to sum type, which gives an easier access to the sum content
||| and that can be extended dynamically, whithout compromising type safety.
module Data.UnionType

import Control.Isomorphism
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
data Sub : List a -> List a -> Type where
  SubZ : Sub [] ys
  SubK : Sub xs ys ->  Elem ty ys -> Sub (ty::xs) ys

public export
Update : (oldTy: Type) -> (newTy: Type) -> (xs : List Type) -> {auto p: Elem oldTy xs} -> List Type
Update _ _ [] {p = p} = absurd p
Update _ newTy (x :: xs) {p = Here} = newTy :: xs
Update _ _ (x :: []) {p = There later} = absurd later
Update oldTy newTy (x :: y :: xs) {p = There later} = x :: Update oldTy newTy (y :: xs)

||| A type that is provided when we want to fold an Union.
||| @ target The type produced by the fold
||| @ union The Union that can be fold by this element.
public export
data UnionFold : (target: Type) -> (union: Type) -> Type where
  Nil : UnionFold a (Union [])
  (::) : (ty -> a) -> UnionFold a (Union ts) -> UnionFold a (Union (ty::ts))

||| Create an Union instance from one of the Union value.
||| In presence of type ambiguity
member : u -> {auto p: Elem u ts} -> Union ts
member x {p = Here} = MemberHere x
member x {p = There later} = MemberThere (member x {p = later})


||| Try to extract a given type from the union.
||| Note that if the union contains several time the same type, and
||| you do not provide explicitly the Elem proof,
||| it may fails to retrieve the value, even if it is present.
||| For example:
||| >>> :let x = the (Union [Nat, Nat]) (MemberThere (MemberHere 42))
||| >>> the (Maybe Nat) $ get x
||| Nothing : Maybe Nat
||| >>> the (Maybe Nat) $ get x {p = There Here}
||| Just 42 : Maybe Nat
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

||| Update a type of the union
update : (a -> b) -> Union ts -> {auto p: Elem a ts} -> Union (Update a b ts)
update f (MemberHere x) {p = Here} = MemberHere (f x)
update _ (MemberHere x) {p = There Here} = MemberHere x
update _ (MemberHere x) {p = There (There _)} = MemberHere x
update _ (MemberThere x) {p = Here} = MemberThere x
update f (MemberThere x) {p = There Here} = MemberThere $ update f x
update f (MemberThere x) {p = There (There later)} = MemberThere $ update f x {p = There later}

Cast (Union [ty]) ty where
  cast (MemberHere x) = x
  cast (MemberThere x) = absurd x

Cast ty (Union [ty]) where
  cast x = (MemberHere x)

oneTypeUnion : Iso (Union [ty]) ty
oneTypeUnion = MkIso cast cast from to
  where
    from _ = Refl
    to (MemberHere _) = Refl
    to (MemberThere x) = absurd x

Cast (Union [l, r]) (Either l r) where
  cast (MemberHere x) = Left x
  cast (MemberThere (MemberHere x)) = Right x
  cast (MemberThere (MemberThere x)) = absurd x

Cast (Either l r) (Union [l, r]) where
  cast (Left x) = (MemberHere x)
  cast (Right x) = (MemberThere (MemberHere x))

eitherUnion : Iso (Union [l, r]) (Either l r)
eitherUnion = MkIso cast cast from to
  where
    from (Left _) = Refl
    from (Right _) = Refl
    to (MemberHere _) = Refl
    to (MemberThere (MemberHere _)) = Refl
    to (MemberThere (MemberThere x)) = absurd x


||| Remove a type from the union
retract : Union xs -> {auto p: Elem ty xs} -> Either (Union (dropElem xs p)) ty
retract (MemberHere x) {p = Here} = Right x
retract (MemberHere x) {p = (There _)} = Left (MemberHere x)
retract (MemberThere x) {p = Here} = Left x
retract (MemberThere x) {p = (There later)} = either (Left . MemberThere) Right $ retract x {p = later}

||| Replace an Union with a larger Union.
||| The order of the elements in the targeted union doesn't need
||| to be the same than the one in the source union.
||| If some types appears several time in the source or the target union
||| the mapping between source and target types is ensures by the implicit
||| Sub parameter.
||| @ u The union to generalize
||| @ s A prrof that each type of u is in the result,
|||     used to map the value of the union.
generalize : (u: Union xs) -> {auto s: Sub xs ys} -> Union ys
generalize (MemberHere x) {s = (SubK y z)} = member x {p = z}
generalize (MemberThere x) {s = (SubK y z)} = generalize x {s=y}

generalise : (u: Union xs) -> {auto s: Sub xs ys} -> Union ys
generalise = generalize

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
