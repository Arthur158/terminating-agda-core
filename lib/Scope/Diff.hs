module Scope.Diff where

import Scope.Split (ListSplit, splitAssoc)

diffSubTrans :: ListSplit -> ListSplit -> ListSplit
diffSubTrans p q = snd (splitAssoc p q)

