{-# LANGUAGE LambdaCase #-}
module Agda.Core.Name where

import Numeric.Natural (Natural)
import Scope.Core (RScope)
import Scope.In (Index(Suc, Zero))

rScopeToRScopeNameInR :: RScope -> RScope
rScopeToRScopeNameInR [] = []
rScopeToRScopeNameInR (() : s)
  = () :
      map
        (\case
             () -> ())
        (rScopeToRScopeNameInR s)

indexToNat :: Index -> Natural
indexToNat Zero = 0
indexToNat (Suc n) = 1 + indexToNat n

instance Eq Index where
    (==) = \ n m -> indexToNat n == indexToNat m

