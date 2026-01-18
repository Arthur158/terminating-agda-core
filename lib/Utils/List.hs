module Utils.List where

data All a b = ANil
             | ACons b (All a b)
                 deriving Show

