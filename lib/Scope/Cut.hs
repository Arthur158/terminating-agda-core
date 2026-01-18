module Scope.Cut where

import Scope.Core (Scope)
import Scope.In (Index(Suc, Zero))
import Scope.Split (ListSplit(ConsL, EmptyL))

cut :: Scope -> Index -> (Scope, Scope)
cut (_ : α') Zero = (α', [])
cut (() : α) (Suc n) = (fst (cut α n), () : snd (cut α n))

cutSplit :: Index -> ListSplit
cutSplit Zero = EmptyL
cutSplit (Suc n) = ConsL (cutSplit n)

