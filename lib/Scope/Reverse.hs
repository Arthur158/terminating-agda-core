module Scope.Reverse where

import Scope.Core (Scope)

revScopeAcc :: Scope -> Scope -> Scope
revScopeAcc [] acc = acc
revScopeAcc (x : s) acc = revScopeAcc s (x : acc)

infix 7 `revScope`
revScope :: Scope -> Scope
revScope s = revScopeAcc s []

