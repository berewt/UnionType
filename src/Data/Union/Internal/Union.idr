||| Union is an alternative to sum type, which gives an easier access to the sum content
||| and that can be extended dynamically, whithout compromising type safety.
module Data.Union.Internal.Union

import Control.Isomorphism
import public Data.List

import public Data.Sub

%default total
%access export

namespace union

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

  public export
  Uninhabited (Union []) where
      uninhabited (MemberHere _) impossible
      uninhabited (MemberThere _) impossible


  ||| Create an Union instance from one of the Union value.
  ||| In presence of type ambiguity
  member : (x : u) -> {auto p: Elem u ts} -> Union ts
  member x {p = Here} = MemberHere x
  member x {p = There _} = MemberThere $ member x

  ||| A type that is provided when we want to fold an Union.
  ||| @ target The type produced by the fold
  ||| @ ts The Union that can be fold by this element.
  public export
  data UnionFold : (target : Type) -> (ts: List Type) -> Type where
    Nil : UnionFold a []
    (::) : (ty -> a) -> UnionFold a ts -> UnionFold a (ty::ts)

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
  get (MemberHere x)      {p = Here}    = Just x
  get (MemberHere _)      {p = There _} = Nothing
  get (MemberThere _)     {p = Here}    = Nothing
  get (MemberThere later) {p = There _} = get later

  ||| Proof: Get after member get the value back
  getHereMemberIsJust : (x : a) -> get (member x) = Just x
  getHereMemberIsJust _ = Refl

  ||| Proof: We can get back a member of an union if we know where to look
  getMemberWithElemIsJust : (x : a) ->
                      (p : Elem a xs) ->
                      the (Maybe a) (get (member x)) = Just x
  getMemberWithElemIsJust _ Here = Refl
  getMemberWithElemIsJust x (There later) = getMemberWithElemIsJust x later

  ||| Fold a whole union to compute a given type
  ||| @ fs gathers the function that should be apply in each case of the union
  public export
  foldUnion : (fs: UnionFold a xs) -> Union xs -> a
  foldUnion [] x = absurd x
  foldUnion (f :: _) (MemberHere y) = f y
  foldUnion (_ :: xs) (MemberThere y) = foldUnion xs y

  ||| Replace a type by another in a list of type
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
  update f (MemberThere x) {p = There (There _)} = MemberThere $ update f x

  Cast (Union [ty]) ty where
    cast (MemberHere x) = x
    cast (MemberThere x) = absurd x

  Cast ty (Union [ty]) where
    cast x = (MemberHere x)

  ||| A union of one type is isomorphic to this type
  oneTypeUnion : Iso (Union [ty]) ty
  oneTypeUnion = MkIso cast cast from to
    where
      from _ = Refl
      to (MemberHere _) = Refl
      to (MemberThere x) = absurd x

  Cast (Union (l::r)) (Either l (Union r)) where
    cast (MemberHere x) = Left x
    cast (MemberThere x) = Right x

  Cast (Either l (Union r)) (Union (l::r)) where
    cast (Left x) = (MemberHere x)
    cast (Right x) = (MemberThere x)


  ||| A union of (n + 1) types is isomorphic to Either the first or an union of the tail
  eitherUnionN : Iso (Union (l::r)) (Either l (Union r))
  eitherUnionN = MkIso cast cast from to
    where
      from (Left _) = Refl
      from (Right _) = Refl
      to (MemberHere _) = Refl
      to (MemberThere _) = Refl

  Cast (Union [l,r]) (Either l r) where
    cast (MemberHere x) = Left x
    cast (MemberThere (MemberHere x)) = Right x

  Cast (Either l r) (Union [l,r]) where
    cast (Left x) = (MemberHere x)
    cast (Right x) = MemberThere (MemberHere x)

  ||| A union of 2 types is isomorphic to Either
  eitherUnion2 : Iso (Union [l,r]) (Either l r)
  eitherUnion2 = MkIso cast cast from to
    where
      from (Left _) = Refl
      from (Right _) = Refl
      to (MemberHere _) = Refl
      to (MemberThere (MemberHere _)) = Refl



  ||| Remove a type from the union, returns either the contained value or the retracted union.
  retract : Union xs -> {auto p : Elem ty xs} -> Either (Union (dropElem xs p)) ty
  retract (MemberHere x) {p = Here} = Right x
  retract (MemberHere x) {p = (There _)} = Left (MemberHere x)
  retract (MemberThere x) {p = Here} = Left x
  retract (MemberThere x) {p = (There _)} = either (Left . MemberThere) Right $ retract x


  ||| Proof: Retract the current value type returns this value
  retractHereMemberIsRight : (x : a) -> retract (member x) = Right x
  retractHereMemberIsRight _ = Refl

  ||| Proof: Retract the current value type returns this value
  retractMemberWithElemIsRight : (x : a) ->
                                 (p : Elem a xs) ->
                                 the (Either _ a) (retract (member x)) = Right x
  retractMemberWithElemIsRight _ Here = Refl
  retractMemberWithElemIsRight x (There p) =
    cong (retractMemberWithElemIsRight x p) {f = (either (Left . MemberThere) Right)}

  private
  getRetractRelationshipLemma : (x : Either (Union xs) a) ->
                                either (const Nothing) Just x = either (const Nothing) Just (either (Left . MemberThere) Right x)
  getRetractRelationshipLemma (Left l) = Refl
  getRetractRelationshipLemma (Right r) = Refl

  ||| Proof : we can map get and retract
  getRetractRelationship : (x : Union xs) ->
                           (p : Elem a xs) ->
                           get x = either (const Nothing) Just (retract x)
  getRetractRelationship (MemberHere _) Here = Refl
  getRetractRelationship (MemberThere _) Here = Refl
  getRetractRelationship (MemberHere _) (There _) = Refl
  getRetractRelationship (MemberThere x) (There later) =
    rewrite getRetractRelationship x later in getRetractRelationshipLemma (retract x)


  ||| Replace an Union with a larger Union.
  ||| The order of the elements in the targeted union doesn't need
  ||| to be the same than the one in the source union.
  ||| If some types appears several time in the source or the target union
  ||| the mapping between source and target types is ensures by the implicit
  ||| Sub parameter.
  ||| @ u The union to generalize
  ||| @ sub A proof that each type of u is in the result,
  |||     used to map the value of the union.
  generalize : (u: Union xs) -> {auto sub: Sub xs ys} -> Union ys
  generalize (MemberHere x) {sub = (e :: es)} = decideLoc x e
    where
      decideLoc : (x : a) -> Elem a ys -> Union ys
      decideLoc x Here = MemberHere x
      decideLoc x (There later) = MemberThere (decideLoc x later)
  generalize (MemberThere x) {sub = (e :: es)} = generalize x

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


  DecEq (Union []) where
      decEq (MemberHere _) _ impossible
      decEq (MemberThere _) _ impossible

  private
  promoteDecEqToMemberHere : (contra : (x = y) -> Void) -> (MemberHere x = MemberHere y) -> Void
  promoteDecEqToMemberHere contra Refl = contra Refl

  private
  hereIsNotThere : (MemberHere x = MemberThere y) -> Void
  hereIsNotThere Refl impossible

  private
  recDecEqUnion : (contra : (xs = ys) -> Void) -> MemberThere xs = MemberThere ys -> Void
  recDecEqUnion contra Refl = contra Refl

  export
  (DecEq ty, DecEq (Union xs)) => DecEq (Union (ty::xs)) where
       decEq (MemberHere x) (MemberThere y) = No hereIsNotThere
       decEq (MemberThere x) (MemberHere y) = No $ negEqSym hereIsNotThere
       decEq (MemberHere x) (MemberHere y)
             = case (decEq x y) of
                    Yes Refl => Yes Refl
                    No contra => No $ promoteDecEqToMemberHere contra
       decEq (MemberThere xs) (MemberThere ys)
             = case (decEq xs ys) of
                    Yes Refl => Yes Refl
                    No contra => No $ recDecEqUnion contra

