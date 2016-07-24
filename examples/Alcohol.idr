module Main

import Data.UnionType
import Data.Vect

record Whiskey where
  constructor MkWhiskey
  age: Nat

record Beer where
  constructor MkBeer
  type: String

-- This is Hwat we want to avoid
data StandardAlcohol
  = AlcoholWhiskey Whiskey
  | AlcoholBeer Beer

drinkWhiskey : Whiskey -> String
drinkWhiskey _ = "Try a Yoichi"

drinkBeer : Beer -> String
drinkBeer _ = "Try a Rochefort 10"

standardAlcoholAsBeer: StandardAlcohol -> Maybe Beer
standardAlcoholAsBeer (AlcoholWhiskey _) = Nothing
standardAlcoholAsBeer (AlcoholBeer x) = Just x

-------------
-- With Union
-------------

Alcohol : Type
Alcohol = Union [Whiskey, Beer]

alcoholAsBeer : Alcohol -> Maybe Beer
alcoholAsBeer x = as Beer x

