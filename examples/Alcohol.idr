module Main

import Data.Union
import Data.Vect

record Whiskey where
  constructor MkWhiskey
  age: Nat

record Beer where
  constructor MkBeer
  type: String

--------------------------------
-- This is what we want to avoid
--------------------------------

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

foldStandardAlcohol : (Whiskey -> a) -> (Beer -> a) -> StandardAlcohol -> a
foldStandardAlcohol f _ (AlcoholWhiskey x) = f x
foldStandardAlcohol _ g (AlcoholBeer x) = g x

-------------
-- With Union
-------------

Alcohol : Type
Alcohol = Union [Whiskey, Beer]

alcoholAsBeer : Alcohol -> Maybe Beer
alcoholAsBeer x = get x


foldAlchohol : (Whiskey -> a) -> (Beer -> a) -> Alcohol -> a
foldAlchohol w b = foldUnion [w, b]

-- Going Further

data Sake = MkSake String

MoreAlcohol : Type
MoreAlcohol = Union [Whiskey, Beer, Sake]

moreAlcohol : Alcohol -> MoreAlcohol
moreAlcohol x = generalize x -- eta reduction does not work

eitherAlcohol : Alcohol -> Either Whiskey Beer
eitherAlcohol = cast

backToAlcohol : MoreAlcohol -> Either Alcohol Sake
backToAlcohol x = retract x -- eta reduction does not work
