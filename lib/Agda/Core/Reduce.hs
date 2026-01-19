module Agda.Core.Reduce where

import Agda.Core.Prelude (Fuel(More, None))
import Agda.Core.Syntax.Signature (Signature, getBody)
import Agda.Core.Syntax.Substitute (Subst(SCons), Substitute(subst), idSubst)
import Agda.Core.Syntax.Term (Branch(BBranch), Branches(BsCons, BsNil), Term(TAnn, TApp, TCase, TCon, TData, TDef, TLam, TLet, TPi, TProj, TSort, TVar), TermS(TSCons, TSNil), Type, singTermS, unApps)
import Agda.Core.Syntax.Weakening (Weaken(weaken))
import Scope.Core (RScope, Scope)
import Scope.In (Index, decIn, decInR, inBindCase)
import Scope.Split (ListSplit)
import Scope.Sub (subBindDrop, subBindKeep, subEmpty, subExtScope, subExtScopeKeep, subRefl)
import Utils.Either (mapRight)
import Debug.Trace

data Environment = EnvNil
                 | EnvCons Environment Term

envToSub :: Environment -> ListSplit
envToSub EnvNil = subRefl
envToSub (EnvCons e _) = subBindDrop (envToSub e)

envToLets :: Environment -> Term -> Term
envToLets EnvNil v = v
envToLets (EnvCons env u) v = envToLets env (TLet u v)

envToSubst :: Scope -> Environment -> Subst
envToSubst r EnvNil = idSubst r
envToSubst r (EnvCons env v)
  = SCons (envToSubst r env) (subst (envToSubst r env) v)

data Frame = FApp Term
           | FProj Index
           | FCase Index RScope Branches Type

unFrame :: Frame -> Term -> Term
unFrame (FApp v) u = TApp u v
unFrame (FProj f) u = TProj u f
unFrame (FCase d r bs m) u = TCase d r u bs m

weakenFrame :: ListSplit -> Frame -> Frame
weakenFrame s (FApp u) = FApp (weaken s u)
weakenFrame s (FProj f) = FProj f
weakenFrame s (FCase d r bs m)
  = FCase d r (weaken s bs)
      (weaken (subBindKeep (subExtScopeKeep r s)) m)

type Stack = [Frame]

unStack :: Stack -> Term -> Term
unStack [] u = u
unStack (f : fs) u = unStack fs (unFrame f u)

weakenStack :: ListSplit -> Stack -> Stack
weakenStack s [] = []
weakenStack s (f : fs) = weakenFrame s f : weakenStack s fs

data State = MkState{env :: Environment, focus :: Term,
                     stack :: Stack}

makeState :: Term -> State
makeState v = MkState EnvNil v []

unState :: Scope -> State -> Term
unState r (MkState e v s) = subst (envToSubst r e) (unStack s v)

lookupBranch :: Branches -> Index -> Maybe (RScope, Term)
lookupBranch BsNil c = Nothing
lookupBranch (BsCons (BBranch c' aty u) bs) c
  = case decInR c' c of
        True -> Just (aty, u)
        False -> lookupBranch bs c

extendEnvironment :: TermS -> Environment -> Environment
extendEnvironment vs e = aux (singTermS vs) vs e
  where
    aux :: [()] -> TermS -> Environment -> Environment
    aux r TSNil e = e
    aux (() : rγ₀) (TSCons v vs) e
      = aux rγ₀ (weaken (subBindDrop subRefl) vs) (EnvCons e v)

lookupEnvironment :: Environment -> Index -> Either Index Term
lookupEnvironment EnvNil p = Left p
lookupEnvironment (EnvCons e v) p
  = inBindCase p
      (\ p ->
         mapRight (weaken (subBindDrop subRefl)) (lookupEnvironment e p))
      (Right (weaken (subBindDrop subRefl) v))

step :: Signature -> State -> Maybe State
step rsig (MkState e (TVar p) s)
  = case lookupEnvironment e p of
        Left _ -> Nothing
        Right v -> Just (MkState e v s)
step rsig (MkState e (TApp v w) s)
  = Just (MkState e v (FApp w : s))
step rsig (MkState e (TProj v f) s)
  = Just (MkState e v (FProj f : s))
step rsig (MkState e (TCase d r v bs m) s)
  = Just (MkState e v (FCase d r bs m : s))
step rsig (MkState e (TLam v) (FApp w : s))
  = Just
      (MkState (EnvCons e w) v (weakenStack (subBindDrop subRefl) s))
step rsig (MkState e (TLet v w) s)
  = Just
      (MkState (EnvCons e v) w (weakenStack (subBindDrop subRefl) s))
step sig (MkState e (TDef d) s)
  = case getBody sig d of
        v -> Just (MkState e (weaken subEmpty v) s)
step rsig (MkState e (TCon d' c vs) (FCase d r bs _ : s))
  = case decIn d' d of
        True -> case lookupBranch bs c of
                    Just (r, v) -> Just
                                     (MkState (extendEnvironment vs e) v
                                        (weakenStack (subExtScope r subRefl) s))
                    Nothing -> Nothing
        False -> Nothing
step rsig (MkState e (TData d ps is) s) = Nothing
step rsig (MkState e (TCon d c vs) (FProj f : s)) = Nothing
step rsig (MkState e (TCon d c x) s) = Nothing
step rsig (MkState e (TLam v) s) = Nothing
step rsig (MkState e (TPi a b) s) = Nothing
step rsig (MkState e (TSort n) s) = Nothing
step rsig (MkState e (TAnn u t) s) = Just (MkState e u s)

reduce :: Scope -> Signature -> Term -> Fuel -> Maybe Term
reduce r rsig v x = go (MkState EnvNil v []) x
  where
    go :: State -> Fuel -> Maybe Term
    go s None = Nothing
    go s (More fl)
      = case step rsig s of
            Just s' -> go s' fl
            Nothing -> Just (unState r s)

reduceClosed :: Signature -> Term -> Fuel -> Maybe Term
reduceClosed = reduce mempty

reduceAppView :: Term -> Term -> (Term, [Term])
reduceAppView s v = unApps v

