module Scope.In where

import Scope.Core (Scope, singleton)
import Scope.Split (ListSplit(ConsL, ConsR, EmptyL, EmptyR), splitRefl)
import Scope.Sub (subBindDrop, subRight)
import GHC.Stack (HasCallStack)

data Index = Zero
           | Suc Index
               deriving Show

inToSub :: Index -> ListSplit
inToSub Zero = subRight (splitRefl singleton)
inToSub (Suc n) = subBindDrop (inToSub n)

subToIn :: ListSplit -> Index
subToIn EmptyR = Zero
subToIn (ConsL _) = Zero
subToIn (ConsR p) = Suc (subToIn p)

coerce :: ListSplit -> Index -> Index
coerce EmptyR p = p
coerce (ConsL _) Zero = Zero
coerce (ConsL j) (Suc n) = Suc (coerce j n)
coerce (ConsR j) n = Suc (coerce j n)

inHere :: Index
inHere = Zero

inThere :: Index -> Index
inThere n = Suc n

bindSubToIn :: ListSplit -> Index
bindSubToIn s = coerce s inHere

inRHere :: Index
inRHere = Zero

inRThere :: Index -> Index
inRThere n = Suc n

inEmptyCase :: HasCallStack => a
inEmptyCase = error "impossible"

inSingCase :: Index -> a -> a
inSingCase Zero f = f

inSplitCase ::
            ListSplit -> Index -> (Index -> a) -> (Index -> a) -> a
inSplitCase EmptyL Zero f g = g inHere
inSplitCase EmptyL (Suc n) f g = g (inThere n)
inSplitCase EmptyR Zero f g = f inHere
inSplitCase EmptyR (Suc n) f g = f (inThere n)
inSplitCase (ConsL j) Zero f g = f inHere
inSplitCase (ConsL j) (Suc n) f g = inSplitCase j n (f . inThere) g
inSplitCase (ConsR j) Zero f g = g inHere
inSplitCase (ConsR j) (Suc n) f g = inSplitCase j n f (g . inThere)

inJoinCase :: Scope -> Index -> (Index -> a) -> (Index -> a) -> a
inJoinCase r = inSplitCase (splitRefl r)

inBindCase :: Index -> (Index -> a) -> a -> a
inBindCase p g f = inJoinCase singleton p g (\ q -> inSingCase q f)

decIn :: Index -> Index -> Bool
decIn Zero Zero = True
decIn Zero (Suc m) = False
decIn (Suc n) Zero = False
decIn (Suc n) (Suc m) = decIn n m

decInR :: Index -> Index -> Bool
decInR Zero Zero = True
decInR Zero (Suc m) = False
decInR (Suc n) Zero = False
decInR (Suc n) (Suc m) = decInR n m

