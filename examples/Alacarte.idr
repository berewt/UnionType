module Main

import Data.Union
import Data.Union.Fix

-- Let's starts with a small language to add some values.


-- We need to be able to declare values
data ValType a b = Val a

-- and to be able to promote them into Fix
val : Num a => a -> {auto p : Elem (ValType a) xs } -> Fix xs
val x = In $ member (Val x)

-- nad of course, to be able to build a la carte stuff, we need a functor
Functor (ValType a) where
  map _ (Val x) = Val x

-- Then, we do the same with the definition of addition

data AddType a = Add a a

add : Fix xs -> Fix xs -> {auto p : Elem AddType xs} -> Fix xs
add x y = In $ member (Add x y)

Functor AddType where
  map func (Add x y) =  Add (func x) (func y)

-- and we can already define some expressions as this one
addExample : Num a => Fix [ValType a, AddType]
addExample = add (val 10) (add (val 12) (val 20))



-- We have now some pieces to define an evaluation algebra


-- We give it a name
data Eval = MkEval

-- and we define a small helper to ease the computation of this specific algebra
eval : ( Functor (wrapUnion fs)
       , Num a
       , FAlgebra Eval (wrapUnion fs) a
       )
    => Fix fs -> a
eval = foldAlgebra (algebra MkEval)

-- then for each type we want to be able to include to our algebra, we define
-- a typeclass instance

-- for values
Num a => FAlgebra Eval (ValType a) a where
  algebra _ (Val x) = x

-- and for addition
Num a => FAlgebra Eval AddType a where
  algebra _ (Add x y) = x + y

-- at this point, you should be able to load the file and to execute:
-- Idris> :l examples/Alacarte.idr
-- *examples/Alacarte> eval addExample
-- 42 : Integer



-- Now, let's add a mulitiplication to our language.
-- Again, we need a type declaration, a way to put it ino Fix and a functor:

data MultType a = Mult a a

mult : Fix xs -> Fix xs -> {auto p : Elem MultType xs} -> Fix xs
mult x y = In $ member (Mult x y)

Functor MultType where
  map func (Mult x y) =  Mult (func x) (func y)

-- And of course, a typeclass to extend our algebra
Num a => FAlgebra Eval MultType a where
  algebra _ (Mult x y) = x * y

-- And now we can use MultType
-- Idris> :l examples/Alacarte.idr
-- *examples/Alacarte> eval multExample
-- 42 : Integer
multExample : Num a => Fix [ValType a, MultType]
multExample = mult (val 3) (mult (val 2) (val 7))

-- and mix it with addition too
-- *examples/Alacarte> eval addMultExample
-- 42 : Integer
addMultExample : Num a => Fix [ValType a, AddType, MultType]
addMultExample = mult (add (val 3) (val 4)) (val 6)


-- We can also define other algebras, here an algebra to print a formula

data Display = MkDisplay

display : ( Functor (wrapUnion fs)
          , FAlgebra Display (wrapUnion fs) String
          )
       => Fix fs -> String
display = foldAlgebra (algebra MkDisplay)


Show a => FAlgebra Display (ValType a) String where
  algebra _ (Val x) = show x

FAlgebra Display AddType String where
  algebra _ (Add x y) = unwords ["(", x, ")", "+", "(", y, ")"]

FAlgebra Display MultType String where
  algebra _ (Mult x y) = unwords ["(", x, ")", "x", "(", y, ")"]

