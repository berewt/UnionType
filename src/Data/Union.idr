||| Union is an alternative to sum type, which gives an easier access to the sum content
||| and that can be extended dynamically, whithout compromising type safety.
module Data.Union

import Control.Isomorphism
import public Data.List

import public Data.Union.HFunctor
import public Data.Union.Internal.Sub
import public Data.Union.Internal.Union
import public Data.Union.Internal.Union1
import public Data.Union.Internal.Union2

%default total
%access export
