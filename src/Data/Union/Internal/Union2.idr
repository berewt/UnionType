||| Union is an alternative to sum type, which gives an easier access to the sum content
||| and that can be extended dynamically, whithout compromising type safety.
module Data.Union.Internal.Union2

import Control.Isomorphism
import public Data.Union.HFunctor
import public Data.List

import public Data.Union.Internal.Sub

%default total
%access export

namespace union2

  ||| Provide a value of the union and point to its type
  public export
  data Union : List ((Type -> Type) -> Type -> Type) -> (Type -> Type) -> Type -> Type where
    ||| Point to the first element of an Union
    ||| @ x  The stored value
    ||| @ f  The exact parametric type of the union
    ||| @ a  The type parameter
    ||| @ w  The type witness
    ||| @ fs The rest of the union
    MemberHere : (x : f a w) -> Union (f :: fs) a w
    ||| Shift the provided value by one type
    ||| @ x  The next step of the pointer
    ||| @ f The skipped parametric type of the union
    ||| @ fs The rest of the union
    ||| @ a  The type parameter
    ||| @ w  The type witness
    MemberThere : (x : Union fs a w) -> Union (f :: fs) a w

  Uninhabited (Union [] a w) where
      uninhabited (MemberHere _) impossible
      uninhabited (MemberThere _) impossible

  ||| Create an Union instance from one of the Union value.
  ||| In presence of type ambiguity
  member : (x : f a w) -> {auto p: Elem f ts} -> Union ts a w
  member x {p = Here} = MemberHere x
  member x {p = There _} = MemberThere $ member x

  ||| A type that is provided when we want to fold an Union.
  ||| @ source The parametric type handled by the fold
  ||| @ target The type produced by the fold
  ||| @ ts The Union that can be fold by this element.
  public export
  data UnionFold : (source : Type -> Type) -> (witness : Type) -> (target : Type) -> (ts: (List ((Type -> Type) -> Type -> Type))) -> Type where
    Nil : UnionFold a w b []
    (::) : (f a w -> b) -> UnionFold a w b ts -> UnionFold a w b (f::ts)

  ||| Try to extract a given type from the union.
  ||| Note that if the union contains several time the same type, and
  ||| you do not provide explicitly the Elem proof,
  ||| it may fails to retrieve the value, even if it is present.
  |||
  ||| For example:
  ||| >>> :let x = the (Union [Maybe, Maybe] Nat) $ MemberThere $ MemberHere $ Just 42
  ||| >>> the (Maybe (Maybe Nat)) $ get x
  ||| Nothing : Maybe Nat
  ||| >>> the (Maybe (Maybe Nat)) $ get x {p = There Here}
  ||| Just 42 : Maybe Nat
  get : Union ts a w -> {auto p : Elem f ts} -> Maybe (f a w)
  get (MemberHere x)      {p = Here}    = Just x
  get (MemberHere _)      {p = There _} = Nothing
  get (MemberThere _)     {p = Here}    = Nothing
  get (MemberThere later) {p = There _} = get later

  ||| Fold a whole union to compute a given type
  ||| @ fs gathers the function that should be apply in each case of the union
  foldUnion : (fs: UnionFold a w b xs) -> Union xs a w -> b
  foldUnion [] x = absurd x
  foldUnion (f :: _) (MemberHere y) = f y
  foldUnion (_ :: xs) (MemberThere y) = foldUnion xs y

  Cast (Union [f] a w) (f a w) where
    cast (MemberHere x) = x
    cast (MemberThere x) = absurd x

  Cast (f a w) (Union [f] a w) where
    cast x = (MemberHere x)

  ||| A union of one type is isomorphic to this type
  oneTypeUnion : Iso (Union [f] a w) (f a w)
  oneTypeUnion = MkIso cast cast from to
    where
      from _ = Refl
      to (MemberHere _) = Refl
      to (MemberThere x) = absurd x

  Cast (Union [l, r] a w) (Either (l a w) (r a w)) where
    cast (MemberHere x) = Left x
    cast (MemberThere (MemberHere x)) = Right x
    cast (MemberThere (MemberThere x)) = absurd x

  Cast (Either (l a w) (r a w)) (Union [l, r] a w) where
    cast (Left x) = (MemberHere x)
    cast (Right x) = (MemberThere (MemberHere x))

  ||| A union of two types is isomorphic to Either
  eitherUnion : Iso (Union [l, r] a w) (Either (l a w) (r a w))
  eitherUnion = MkIso cast cast from to
    where
      from (Left _) = Refl
      from (Right _) = Refl
      to (MemberHere _) = Refl
      to (MemberThere (MemberHere _)) = Refl
      to (MemberThere (MemberThere x)) = absurd x


  ||| Remove a type from the union, returns either the contained value or the retracted union.
  retract : Union xs a w -> {auto p : Elem f xs} -> Either (Union (dropElem xs p) a w) (f a w)
  retract (MemberHere x) {p = Here} = Right x
  retract (MemberHere x) {p = (There _)} = Left (MemberHere x)
  retract (MemberThere x) {p = Here} = Left x
  retract (MemberThere x) {p = (There _)} = either (Left . MemberThere) Right $ retract x


  ||| Replace an Union with a larger Union.
  ||| The order of the elements in the targeted union doesn't need
  ||| to be the same than the one in the source union.
  ||| If some types appears several time in the source or the target union
  ||| the mapping between source and target types is ensures by the implicit
  ||| Sub parameter.
  ||| @ u The union to generalize
  ||| @ s A prrof that each type of u is in the result,
  |||     used to map the value of the union.
  generalize : (u: Union xs a w) -> {auto s: Sub xs ys} -> Union ys a w
  generalize (MemberHere x) {s = (SubK _ p)} = member x
  generalize (MemberThere x) {s = (SubK s _)} = generalize x

  ||| English version of generalize
  generalise : (u: Union xs a w) -> {auto s: Sub xs ys} -> Union ys a w
  generalise = generalize

  Eq (Union [] a w) where
    (==) x _ = absurd x
    (/=) x _ = absurd x

  (Eq (f a w), Eq (Union fs a w)) => Eq (Union (f::fs) a w) where
    (==) (MemberHere x) (MemberHere y) = x == y
    (==) (MemberHere x) (MemberThere y) = False
    (==) (MemberThere x) (MemberHere y) = False
    (==) (MemberThere x) (MemberThere y) = x == y
    (/=) (MemberHere x) (MemberHere y) = x /= y
    (/=) (MemberHere x) (MemberThere y) = True
    (/=) (MemberThere x) (MemberHere y) = True
    (/=) (MemberThere x) (MemberThere y) = x /= y

  DecEq (Union [] a w) where
      decEq (MemberHere _) _ impossible
      decEq (MemberThere _) _ impossible

  private
  promoteDecEqToMemberHere : (contra : (x = y) -> Void)
                          -> (MemberHere x = MemberHere y)
                          -> Void
  promoteDecEqToMemberHere contra Refl = contra Refl

  private
  hereIsNotThere : (MemberHere x = MemberThere y) -> Void
  hereIsNotThere Refl impossible

  private
  recDecEqUnion : (contra : (xs = ys) -> Void)
               -> MemberThere xs = MemberThere ys
               -> Void
  recDecEqUnion contra Refl = contra Refl

  export
  (DecEq (f a w) , DecEq (Union fs a w)) => DecEq (Union (f::fs) a w) where
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

  HFunctor (Union []) where
    hmap func x = absurd x

  export
  (HFunctor f, HFunctor (Union xs)) => HFunctor (Union (f::xs)) where
    hmap func (MemberHere x) = MemberHere $ hmap func x
    hmap func (MemberThere x) = MemberThere $ hmap func x
