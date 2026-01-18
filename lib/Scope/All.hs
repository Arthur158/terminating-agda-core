{-# LANGUAGE LambdaCase #-}
module Scope.All where

import Control.Arrow (second)
import Scope.Core (RScope, Scope)
import Scope.In (Index(Suc, Zero), decIn, inHere, inRHere, inRThere, inThere)
import qualified Utils.List (All(ACons, ANil))

type All p = Utils.List.All () p

allEmpty :: All p
allEmpty = Utils.List.ANil

allSingl :: p -> All p
allSingl p = Utils.List.ACons p Utils.List.ANil

getAllSingl :: All p -> p
getAllSingl (Utils.List.ACons p Utils.List.ANil) = p

allJoin :: All p -> All p -> All p
allJoin pas Utils.List.ANil = pas
allJoin pas (Utils.List.ACons px pbs)
  = Utils.List.ACons px (allJoin pas pbs)

type AllR p = Utils.List.All () p

allEmptyR :: AllR p
allEmptyR = Utils.List.ANil

allSinglR :: p -> AllR p
allSinglR p = Utils.List.ACons p Utils.List.ANil

getAllSinglR :: AllR p -> p
getAllSinglR (Utils.List.ACons p Utils.List.ANil) = p

allJoinR :: AllR p -> AllR p -> AllR p
allJoinR pas Utils.List.ANil = pas
allJoinR pas (Utils.List.ACons px pbs)
  = Utils.List.ACons px (allJoinR pas pbs)

lookupAll :: All p -> Index -> p
lookupAll (Utils.List.ACons pz pzs) Zero = pz
lookupAll (Utils.List.ACons _ pzs) (Suc n) = lookupAll pzs n

findAll :: All p -> (p -> Index -> Maybe q) -> Maybe q
findAll Utils.List.ANil qc = Nothing
findAll (Utils.List.ACons px al) qc
  = case qc px inHere of
        Just qt -> Just qt
        Nothing -> findAll al (\ pel i -> qc pel (inThere i))

lookupAllR :: AllR p -> Index -> p
lookupAllR (Utils.List.ACons pz pzs) Zero = pz
lookupAllR (Utils.List.ACons _ pzs) (Suc n) = lookupAllR pzs n

findAllR :: AllR p -> (p -> Index -> Maybe q) -> Maybe q
findAllR Utils.List.ANil qc = Nothing
findAllR (Utils.List.ACons px al) qc
  = case qc px inRHere of
        Just qt -> Just qt
        Nothing -> findAllR al (\ pel i -> qc pel (inRThere i))

mapAll :: (p -> q) -> All p -> All q
mapAll f Utils.List.ANil = Utils.List.ANil
mapAll f (Utils.List.ACons p ps)
  = Utils.List.ACons (f p) (mapAll f ps)

tabulateAll :: Scope -> (Index -> p) -> All p
tabulateAll [] f = Utils.List.ANil
tabulateAll (x : α) f
  = Utils.List.ACons (f inHere) (tabulateAll α (f . inThere))

allIn :: All p -> All (p, Index)
allIn Utils.List.ANil = Utils.List.ANil
allIn (Utils.List.ACons x al)
  = Utils.List.ACons (x, inHere) (mapAll (second inThere) (allIn al))

singAll :: All p -> Scope
singAll Utils.List.ANil = []
singAll (Utils.List.ACons _ xs) = () : singAll xs

allInScope :: All Index -> All Index -> Maybe ()
allInScope Utils.List.ANil Utils.List.ANil = Just ()
allInScope Utils.List.ANil (Utils.List.ACons _ _) = Nothing
allInScope (Utils.List.ACons _ _) Utils.List.ANil = Nothing
allInScope (Utils.List.ACons p als) (Utils.List.ACons q bls)
  = do rt <- allInScope als bls
       if decIn p q then Just () else Nothing

mapAllR :: (p -> q) -> AllR p -> AllR q
mapAllR f Utils.List.ANil = Utils.List.ANil
mapAllR f (Utils.List.ACons p ps)
  = Utils.List.ACons (f p) (mapAllR f ps)

tabulateAllR :: RScope -> (Index -> p) -> AllR p
tabulateAllR [] f = Utils.List.ANil
tabulateAllR (x : α) f
  = Utils.List.ACons (f inRHere) (tabulateAllR α (f . inRThere))

allInR :: AllR p -> AllR (p, Index)
allInR Utils.List.ANil = Utils.List.ANil
allInR (Utils.List.ACons x al)
  = Utils.List.ACons (x, inRHere)
      (mapAllR (second inRThere) (allInR al))

singAllR :: AllR p -> RScope
singAllR Utils.List.ANil = []
singAllR (Utils.List.ACons _ xs) = () : singAllR xs

allInRScope :: AllR Index -> AllR Index -> Maybe ()
allInRScope Utils.List.ANil Utils.List.ANil = Just ()
allInRScope Utils.List.ANil (Utils.List.ACons _ _) = Nothing
allInRScope (Utils.List.ACons _ _) Utils.List.ANil = Nothing
allInRScope (Utils.List.ACons p als) (Utils.List.ACons q bls)
  = do rt <- allInRScope als bls
       if decIn p q then Just () else Nothing

allLookup :: All p -> All (Index, p)
allLookup Utils.List.ANil = Utils.List.ANil
allLookup (Utils.List.ACons ph ls)
  = Utils.List.ACons (inHere, ph)
      (mapAll
         (\case
              (i, pri) -> (inThere i, pri))
         (allLookup ls))

