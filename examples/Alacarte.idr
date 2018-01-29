module Main

import Data.Union
import Data.Union.Fix
import Data.Union.Term

-- Let's starts with a small language to add some values.


-- We need to be able to declare values
data ValType a b = Val a

-- and to be able to promote them into Fix
val : a -> {auto p : Elem (ValType a) xs } -> Fix xs
val x = lift $ Val x

-- nad of course, to be able to build a la carte stuff, we need a functor
Functor (ValType a) where
  map _ (Val x) = Val x

-- Then, we do the same with the definition of addition

data AddType a = Add a a

add : Fix xs -> Fix xs -> {auto p : Elem AddType xs} -> Fix xs
add x y = lift $ Add x y

Functor AddType where
  map func (Add x y) =  Add (func x) (func y)

-- and we can already define some expressions, as this one
addExample : Num a => Fix [ValType a, AddType]
addExample = add (val 10) (add (val 12) (val 20))






-- We have now some pieces to define an evaluation algebra


-- We give it a name
data Eval = MkEval

-- and we define a small helper to ease the computation of this specific algebra
eval : ( Functor (Union fs)
       , Num a
       , FAlgebra Eval (Union fs) a
       )
    => Fix fs -> a
eval = cata (algebra MkEval)

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
mult x y = lift $ Mult x y

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

display : ( Functor (Union fs)
          , FAlgebra Display (Union fs) String
          )
       => Fix fs -> String
display = foldFix (algebra MkDisplay)


Show a => FAlgebra Display (ValType a) String where
  algebra _ (Val x) = show x

FAlgebra Display AddType String where
  algebra _ (Add x y) = unwords ["(", x, ")", "+", "(", y, ")"]

FAlgebra Display MultType String where
  algebra _ (Mult x y) = unwords ["(", x, ")", "x", "(", y, ")"]



-- An example with Term (from DataTypes à la carte)

data Incr t = MkIncr Int t

incr : Int -> {auto p : Elem Incr xs} -> Term xs ()
incr x = lift $ MkIncr x (Pure ())

Functor Incr where
  map func (MkIncr x y) = MkIncr x $ func y

data Recall t = MkRecall (Int -> t)

recall : {auto p : Elem Recall xs} -> Term xs Int
recall = lift $ MkRecall Pure

Functor Recall where
  map func (MkRecall f) = MkRecall $ func . f


data Mem = MkMem Int

interface Functor f => Run (f : Type -> Type) where
  runAlgebra : f (Mem -> (a, Mem)) -> Mem -> (a, Mem)

Run Incr where
    runAlgebra (MkIncr k r) (MkMem i) = r $ MkMem (i + k)

Run Recall where
    runAlgebra (MkRecall r) (MkMem i) = r i $ MkMem i

Run (Union []) where
    runAlgebra (MemberHere _) _ impossible
    runAlgebra (MemberThere _) _ impossible

(Run f, Run (Union fs)) => Run (Union (f::fs)) where
     runAlgebra (MemberHere r) = runAlgebra r
     runAlgebra (MemberThere r) = runAlgebra r

run : Run (Union fs) => Term fs a -> Mem -> (a, Mem)
run = foldTerm MkPair runAlgebra


-- An example of a term, can be tested
--
-- Idris> :l examples/Alacarte.idr
-- Type checking ./examples/Alacarte.idr
-- *examples/Alacarte> run tick (MkMem 4)
-- (4, MkMem 5) : (Int, Mem)
tick : Term [Recall, Incr] Int
tick = do y <- recall
          incr 1
          pure y
