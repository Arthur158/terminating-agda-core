module Scope.Core where

type Scope = [()]

singleton :: Scope
singleton = [()]

infixl 5 `bind`
bind :: Scope -> Scope
bind α = α <> singleton

type RScope = [()]

rsingleton :: RScope
rsingleton = [()]

infixr 5 `rbind`
rbind :: RScope -> RScope
rbind α = rsingleton <> α

extScope :: Scope -> RScope -> Scope
extScope s [] = s
extScope α (() : rs) = extScope (bind α) rs

singExtScope :: Scope -> RScope -> Scope
singExtScope αRun [] = αRun
singExtScope α (() : rβ) = singExtScope (bind α) rβ

caseScope :: Scope -> c -> (Scope -> c) -> c
caseScope [] emptyCase bindCase = emptyCase
caseScope (() : β) emptyCase bindCase = bindCase β

caseRScope :: RScope -> c -> (RScope -> c) -> c
caseRScope [] emptyCase bindCase = emptyCase
caseRScope (() : β) emptyCase bindCase = bindCase β

singBind :: Scope -> Scope
singBind s = () : s

singUnbind :: Scope -> Scope
singUnbind s = tail s

