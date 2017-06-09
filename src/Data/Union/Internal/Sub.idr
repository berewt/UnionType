module Data.Union.Internal.Sub

import public Data.List

%default total

||| A partial order relation between lists.
|||
||| Sub xs ys is inhabited if each type of xs is in ys.
public export
data Sub : List a -> List a -> Type where
  SubZ : Sub [] ys
  SubK : Sub xs ys -> Elem ty ys -> Sub (ty::xs) ys

%hint
public export
subElem : Sub xs ys -> {auto prf : Elem x xs} -> Elem x ys
subElem (SubK x y) Here = y
subElem (SubK x y) (There later) = subElem x later
