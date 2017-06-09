module Data.Union.Internal.Sub

import public Data.List

%default total

||| A partial order relation between lists.
|||
||| Sub xs ys is inhabited if each type of xs is in ys.
public export
data Sub : List a -> List a -> Type where
  SubZ : Sub [] ys
  SubK : Sub xs ys -> Elem x ys -> Sub (x::xs) ys

export
expandSub : Sub xs ys -> Sub xs (y :: ys)
expandSub SubZ = SubZ
expandSub (SubK sub e) {xs = (x :: xs)} = SubK (expandSub sub) (There e)

export
reflSub : Sub xs xs
reflSub {xs = []} = SubZ
reflSub {xs = (x :: xs)} = SubK (expandSub reflSub) Here

%hint
export
subHasElem : Sub xs ys -> Elem x xs -> Elem x ys
subHasElem SubZ y = absurd y
subHasElem (SubK z w) Here = w
subHasElem (SubK z w) (There later) = subHasElem z later
