module Scope.Sub where

import Scope.Core (RScope, Scope, singleton)
import Scope.Split (ListSplit(ConsL, ConsR, EmptyL, EmptyR), singSplitLeft, splitAssoc, splitBindRight, splitComm, splitJoin, splitJoinLeft, splitJoinRight, splitJoinRightr, splitRefl)

subTrans :: ListSplit -> ListSplit -> ListSplit
subTrans p q = fst (splitAssoc p q)

subRight :: ListSplit -> ListSplit
subRight p = splitComm p

subWeaken :: ListSplit -> ListSplit
subWeaken p = splitBindRight p

subEmpty :: ListSplit
subEmpty = EmptyL

subRefl :: ListSplit
subRefl = EmptyR

singSub :: ListSplit -> Scope -> Scope
singSub p = singSplitLeft p

subJoin :: Scope -> ListSplit -> ListSplit -> ListSplit
subJoin r p q = splitJoin r p q

subJoinKeep :: Scope -> ListSplit -> ListSplit
subJoinKeep r p = splitJoinLeft r p

subJoinDrop :: Scope -> ListSplit -> ListSplit
subJoinDrop r p = splitJoinRight r p

subJoinHere :: Scope -> ListSplit -> ListSplit
subJoinHere r p = splitJoinRightr r p

subBindKeep :: ListSplit -> ListSplit
subBindKeep = subJoinKeep singleton

subBindDrop :: ListSplit -> ListSplit
subBindDrop = subWeaken

joinSubLeft :: Scope -> ListSplit -> ListSplit
joinSubLeft r p = fst (splitAssoc (splitRefl r) p)

joinSubRight :: Scope -> ListSplit -> ListSplit
joinSubRight r p = fst (splitAssoc (splitComm (splitRefl r)) p)

subExtScopeKeep :: RScope -> ListSplit -> ListSplit
subExtScopeKeep [] s = s
subExtScopeKeep (() : rγ) s = subExtScopeKeep rγ (ConsL s)

subExtScope :: RScope -> ListSplit -> ListSplit
subExtScope [] s = s
subExtScope (() : rγ) s = subExtScope rγ (ConsR s)

