module Agda.Core.GlobalScope where

import Scope.Core (RScope, Scope)
import Scope.In (Index)

data Globals = Globals{defScope :: Scope, dataScope :: Scope,
                       dataParScope :: Index -> RScope, dataIxScope :: Index -> RScope,
                       dataConstructors :: Index -> RScope,
                       fieldScope :: Index -> Index -> RScope}

