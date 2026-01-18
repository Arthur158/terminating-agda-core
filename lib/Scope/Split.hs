module Scope.Split where

import Scope.Core (Scope, singBind, singleton)

data ListSplit = EmptyL
               | EmptyR
               | ConsL ListSplit
               | ConsR ListSplit
                   deriving Show

splitRefl :: Scope -> ListSplit
splitRefl [] = EmptyR
splitRefl (() : β) = ConsR (splitRefl β)

splitComm :: ListSplit -> ListSplit
splitComm EmptyL = EmptyR
splitComm EmptyR = EmptyL
splitComm (ConsL p) = ConsR (splitComm p)
splitComm (ConsR p) = ConsL (splitComm p)

splitAssoc :: ListSplit -> ListSplit -> (ListSplit, ListSplit)
splitAssoc EmptyL q = (EmptyL, q)
splitAssoc EmptyR q = (q, EmptyL)
splitAssoc p EmptyR = (p, EmptyR)
splitAssoc (ConsL p) (ConsL q)
  = (ConsL (fst (splitAssoc p q)), snd (splitAssoc p q))
splitAssoc (ConsR p) (ConsL q)
  = (ConsR (fst (splitAssoc p q)), ConsL (snd (splitAssoc p q)))
splitAssoc p (ConsR q)
  = (ConsR (fst (splitAssoc p q)), ConsR (snd (splitAssoc p q)))

splitQuad ::
          ListSplit ->
            ListSplit -> ((ListSplit, ListSplit), (ListSplit, ListSplit))
splitQuad EmptyL q = ((EmptyL, q), (EmptyL, EmptyL))
splitQuad EmptyR q = ((q, EmptyR), (EmptyR, EmptyR))
splitQuad p EmptyL = ((EmptyL, EmptyL), (EmptyL, p))
splitQuad p EmptyR = ((EmptyR, EmptyR), (p, EmptyR))
splitQuad (ConsL p) (ConsL q)
  = ((ConsL (fst (fst (splitQuad p q))), snd (fst (splitQuad p q))),
     (ConsL (fst (snd (splitQuad p q))), snd (snd (splitQuad p q))))
splitQuad (ConsL p) (ConsR q)
  = ((ConsR (fst (fst (splitQuad p q))), snd (fst (splitQuad p q))),
     (fst (snd (splitQuad p q)), ConsL (snd (snd (splitQuad p q)))))
splitQuad (ConsR p) (ConsL q)
  = ((fst (fst (splitQuad p q)), ConsL (snd (fst (splitQuad p q)))),
     (ConsR (fst (snd (splitQuad p q))), snd (snd (splitQuad p q))))
splitQuad (ConsR p) (ConsR q)
  = ((fst (fst (splitQuad p q)), ConsR (snd (fst (splitQuad p q)))),
     (fst (snd (splitQuad p q)), ConsR (snd (snd (splitQuad p q)))))

singSplit :: ListSplit -> Scope -> (Scope, Scope)
singSplit EmptyL r = ([], r)
singSplit EmptyR r = (r, [])
singSplit (ConsL p) r
  = (singBind (fst (singSplit p (tail r))),
     snd (singSplit p (tail r)))
singSplit (ConsR p) r
  = (fst (singSplit p (tail r)),
     singBind (snd (singSplit p (tail r))))

singSplitLeft :: ListSplit -> Scope -> Scope
singSplitLeft p r = fst (singSplit p r)

singSplitRight :: ListSplit -> Scope -> Scope
singSplitRight p r = snd (singSplit p r)

splitJoinLeft :: Scope -> ListSplit -> ListSplit
splitJoinLeft [] p = p
splitJoinLeft (() : α) p = ConsL (splitJoinLeft α p)

splitJoinRight :: Scope -> ListSplit -> ListSplit
splitJoinRight [] p = p
splitJoinRight (() : α) p = ConsR (splitJoinRight α p)

splitJoin :: Scope -> ListSplit -> ListSplit -> ListSplit
splitJoin r p EmptyL = splitJoinRight r p
splitJoin r p EmptyR = splitJoinLeft r p
splitJoin r p (ConsL q) = ConsL (splitJoin (tail r) p q)
splitJoin r p (ConsR q) = ConsR (splitJoin (tail r) p q)

splitJoinLeftr :: Scope -> ListSplit -> ListSplit
splitJoinLeftr r p = splitJoin r EmptyR p

splitJoinRightr :: Scope -> ListSplit -> ListSplit
splitJoinRightr r p = splitJoin r EmptyL p

splitBindLeft :: ListSplit -> ListSplit
splitBindLeft = splitJoinLeft singleton

splitBindRight :: ListSplit -> ListSplit
splitBindRight = splitJoinRight singleton

decSplit :: ListSplit -> ListSplit -> Bool
decSplit EmptyL EmptyL = True
decSplit EmptyR EmptyR = True
decSplit (ConsL p) (ConsL q) = decSplit p q
decSplit (ConsR p) (ConsR q) = decSplit p q
decSplit EmptyL EmptyR = False
decSplit EmptyL (ConsR q) = False
decSplit EmptyR EmptyL = False
decSplit EmptyR (ConsL q) = False
decSplit (ConsL p) EmptyR = False
decSplit (ConsL p) (ConsR q) = False
decSplit (ConsR p) EmptyL = False
decSplit (ConsR p) (ConsL q) = False

