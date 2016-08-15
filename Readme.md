# UnionType

UnionType was developped with the goal of providing a less verbose alternative
to Sum types. It has similarities with the Haskell
[`open-union`](https://hackage.haskell.org/package/open-union) package.

While sum types will lead to stuff like:

```idris
record Whiskey where
  constructor MkWhiskey
  age: Nat

record Beer where
  constructor MkBeer
  type: String

data StandardAlcohol
  = AlcoholWhiskey Whiskey
  | AlcoholBeer Beer
```

`unionType` propose the following alternative:

```idris
record Whiskey where
  constructor MkWhiskey
  age: Nat

record Beer where
  constructor MkBeer
  type: String

Alcohol : Type
Alcohol = Union [Whiskey, Beer]
```

And comes with some helpers like the `get` function that try to extract value
of a given type:

```idris
alcoholAsBeer : Alcohol -> Maybe Beer
alcoholAsBeer x = get x
```

## Known Limitation

`unionType` is clumpsy when the same type is at appears several times in the
union. A solution is to use newtypes to differentiate them.
