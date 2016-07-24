module Main

import Data.UnionType

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

drinkWhiskey : Whiskey -> IO ()
drinkWhiskey _ = putStrLn "Try a Yoichi"

drinkBeer : Beer -> IO ()
module Main

import Data.Union

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

drinkWhiskey : Whiskey -> IO ()
drinkWhiskey _ = putStrLn "Try a Yoichi"

drinkBeer : Beer -> IO ()
drinkBeer _ = putStrLn "Try a Rochefort 10"

drinkStandardAlcohol : StandardAlcohol -> IO ()
drinkStandardAlcohol (AlcoholWhiskey x) = drinkWhiskey x
drinkStandardAlcohol (AlcoholBeer x) = drinkBeer x

-------------
-- With Union
-------------

Alcohol = Union [Whiskey, Beer]

drinkAlcohol : Alcohol -> IO ()
drinkAlcohol x = foldUnion x drinkAlcohol drinkBeer
drinkBeer _ = putStrLn "Try a Rochefort 10"

drinkStandardAlcohol : StandardAlcohol -> IO ()
drinkStandardAlcohol (AlcoholWhiskey x) = drinkWhiskey x
drinkStandardAlcohol (AlcoholBeer x) = drinkBeer x

-------------
-- With Union
-------------

Alcohol = Union [Whiskey, Beer]

drinkAlcohol : Alcohol -> IO ()
drinkAlcohol x = foldUnion x drinkAlcohol drinkBeer
