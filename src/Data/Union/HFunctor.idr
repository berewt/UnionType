module Data.Union.HFunctor

public export
interface HFunctor (f : (Type -> Type) -> Type -> Type) where
  hmap : (func : {y : _} -> a y -> b y) -> f a w -> f b w

