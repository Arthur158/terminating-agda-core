module Agda.Core.Prelude where

map2 :: (b -> c) -> (a, b) -> (a, c)
map2 f (av, bv) = (av, f bv)

data Fuel = None
          | More Fuel

data Equivalence a b = Equiv{σ :: a -> b, τ :: b -> a}

