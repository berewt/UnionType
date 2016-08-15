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
  MemberHere : (x : ty) -> Union (ty :: xs)
  ||| Shift the provided value by one type
  ||| @ x The next step of the pointer
  ||| @ ty The skipped type of the union
  ||| @ xs The rest of the union
  MemberThere : (x : Union xs) -> Union (ty :: xs)

Uninhabited (Union []) where
    uninhabited (MemberHere _) impossible
    uninhabited (MemberThere _) impossible


||| Create an Union instance from one of the Union value.
||| In presence of type ambiguity
member : u -> {auto p: Elem u ts} -> Union ts
member x {p = Here} = MemberHere x
member x {p = There p} = MemberThere (member x {p})


||| A type that is provided when we want to fold an Union.
||| @ target The type produced by the fold
||| @ union The Union that can be fold by this element.
public export
data UnionFold : (target : Type) -> (union : Type) -> Type where
  Nil : UnionFold a (Union [])
  (::) : (ty -> a) -> UnionFold a (Union ts) -> UnionFold a (Union (ty::ts))

||| Try to extract a given type from the union.
||| Note that if the union contains several time the same type, and
||| you do not provide explicitly the Elem proof,
||| it may fails to retrieve the value, even if it is present.
|||
||| For example:
||| >>> :let x = the (Union [Nat, Nat]) (MemberThere (MemberHere 42))
||| >>> the (Maybe Nat) $ get x
||| Nothing : Maybe Nat
||| >>> the (Maybe Nat) $ get x {p = There Here}
||| Just 42 : Maybe Nat
get : Union ts -> {auto p : Elem ty ts} -> Maybe ty
get (MemberHere x)      {p = Here}      = Just x
get (MemberHere _)      {p = There _}   = Nothing
get (MemberThere _)     {p = Here}      = Nothing
get (MemberThere later) {p = (There p)} = get later {p}

getHereMemberIsJust : (x : a) -> get (member x) = Just x
getHereMemberIsJust _ = Refl

getMemberWithElemIsJust : (x : a) ->
                    (p : Elem a xs) ->
                    the (Maybe a) (get (member x {p}) {p}) = Just x
getMemberWithElemIsJust _ Here = Refl
getMemberWithElemIsJust x (There later) = getMemberWithElemIsJust x later

||| Fold a whole union to compute a given type
||| @ fs gathers the function that should be apply in each case of the union
foldUnion : (fs: UnionFold a (Union xs)) -> Union xs -> a
foldUnion [] x = absurd x
foldUnion (f :: _) (MemberHere y) = f y
foldUnion (_ :: xs) (MemberThere y) = foldUnion xs y


public export
Update : (newTy : Type) -> (xs : List Type) -> (p : Elem oldTy xs) -> List Type
Update _ [] p = absurd p
Update newTy (_ :: xs) Here = newTy :: xs
Update _ (_ :: []) (There later) = absurd later
Update newTy (x :: y :: xs) (There later) = x :: Update newTy (y :: xs) later

||| Update a type of the union
||| @ f The update function
||| @ u The union ot update
||| @ p The location to update
update : (f: a -> b) -> (u : Union ts) -> {auto p: Elem a ts} -> Union (Update b ts p)
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
retract : Union xs -> {auto p : Elem ty xs} -> Either (Union (dropElem xs p)) ty
retract (MemberHere x) {p = Here} = Right x
retract (MemberHere x) {p = (There _)} = Left (MemberHere x)
retract (MemberThere x) {p = Here} = Left x
retract (MemberThere x) {p = (There later)} = either (Left . MemberThere) Right $ retract x {p = later}

retractHereMemberIsRight : (x : a) -> retract (member x) = Right x
retractHereMemberIsRight _ = Refl

retractMemberWithElemIsRight : (x : a) ->
                               (p : Elem a xs) ->
                               the (Either _ a) (retract (member x {p}) {p}) = Right x
retractMemberWithElemIsRight _ Here = Refl
retractMemberWithElemIsRight x (There p) =
  cong (retractMemberWithElemIsRight x p) {f = (either (Left . MemberThere) Right)}

private
getRetractRelationshipLemma : (x : Either (Union xs) a) ->
                              either (const Nothing) Just x = either (const Nothing) Just (either (Left . MemberThere) Right x)
getRetractRelationshipLemma (Left l) = Refl
getRetractRelationshipLemma (Right r) = Refl

getRetractRelationship : (x : Union xs) ->
                         (p : Elem a xs) ->
                         get x {p} = either (const Nothing) Just (retract x {p})
getRetractRelationship (MemberHere _) Here = Refl
getRetractRelationship (MemberThere _) Here = Refl
getRetractRelationship (MemberHere _) (There _) = Refl
getRetractRelationship (MemberThere x) (There later) =
  rewrite getRetractRelationship x later in getRetractRelationshipLemma (retract x {p = later})


||| A partial order relation between unions
||| Type occurences are not taken into account
||| (ie.: Sub (Union [Nat, Nat]) (Union [Nat]) is inhabited)
||| Sub xs ys is inhabited if each type of xs is in ys.
public export
data Sub : List a -> List a -> Type where
  SubZ : Sub [] ys
  SubK : Sub xs ys ->  Elem ty ys -> Sub (ty::xs) ys

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
generalize (MemberHere x) {s = (SubK _ p)} = member x {p}
generalize (MemberThere x) {s = (SubK s _)} = generalize x {s}

||| English version of generalize
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
