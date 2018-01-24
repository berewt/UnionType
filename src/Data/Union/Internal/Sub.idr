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


data Pos : List a -> List a -> Type where
  Nil  : Pos [] ys
  (::)   : Elem x ys -> Pos xs ys -> Pos (x::xs) ys

data Emb : List a -> List a -> Type where
  Found : Pos xs ys -> Emb xs ys
  NotFound : Emb xs ys
  Ambiguous : Emb xs ys

Emb' : a -> List a -> Type
Emb' x xs = Emb [x] xs

%hint
chooseEmb : Emb' x [y]-> Emb' x ys -> Emb' x (y::ys)
chooseEmb (Found _) (Found _) = Ambiguous
chooseEmb Ambiguous _ = Ambiguous
chooseEmb _ Ambiguous = Ambiguous
chooseEmb (Found [Here]) NotFound = Found [Here]
chooseEmb NotFound (Found [pos]) = Found [There pos]
chooseEmb NotFound NotFound = NotFound

%hint
sumEmb : Emb' x ys -> Emb xs ys -> Emb (x::xs) ys
sumEmb (Found [pos]) (Found poss) = Found (pos::poss)
sumEmb Ambiguous _ = Ambiguous
sumEmb _ Ambiguous = Ambiguous
sumEmb _ NotFound = NotFound
sumEmb NotFound _ = NotFound

subsume : {e : Emb xs ys} -> Emb xs ys
subsume {e} = e

{-
namespace union

  interface Subsume (a : List Type) (b : List Type) (prf: Locator a b) where
    typeMap : Locator a b
    typeMap {prf} = prf

  Subsume [a] [a] Here where

  (Subsume [a] bs loc1, Subsume as bs loc2) => Subsume (a::as) bs (Sum loc1 loc2) where
    -}
