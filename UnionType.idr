module Data.UnionType

import Data.Vect

%default total

data Union : Vect n Type -> Type where
  Member : t -> Elem t ts -> Union ts

member : t -> {auto e: Elem t ts} -> Union ts
member x {e} = Member x e

unionToMaybe : Union ts -> {auto e: Elem t ts} -> Maybe t
unionToMaybe (Member x Here)          {e=Here}      = Just x
unionToMaybe (Member x (There later)) {e=(There l)} = unionToMaybe (Member x later) {e=l}
unionToMaybe (Member x Here)          {e=(There _)} = Nothing
unionToMaybe (Member x (There _))     {e=Here}      = Nothing

UnionCata : Type -> Vect n Type -> Type
UnionCata a [] = a
UnionCata a (x :: xs) = (x -> a) -> UnionCata a xs

cata : Union ts -> UnionCata a ts
cata (Member x Here) = \f => cata' (f x)
  where
    cata' : {xs : Vect k Type} -> (x : a) -> UnionCata a xs
    cata' {xs=[]} x = x
    cata' {xs=_::xs'} x = const $ cata' {xs=xs'} x
cata (Member x (There later)) = const $ cata (Member x later)
