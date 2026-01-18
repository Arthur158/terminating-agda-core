module Agda.Core.Syntax.Substitute where

import Agda.Core.Syntax.Context (Telescope(EmptyTel, ExtendTel))
import Agda.Core.Syntax.Term (Branch(BBranch), Branches(BsCons, BsNil), Sort(STyp), Term(TAnn, TApp, TCase, TCon, TData, TDef, TLam, TLet, TPi, TProj, TSort, TVar), TermS(TSCons, TSNil), Type(El))
import Agda.Core.Syntax.Weakening (Weaken(weaken))
import Scope.Core (RScope, Scope)
import Scope.In (Index, coerce, inBindCase, inEmptyCase, inHere)
import Scope.Split (ListSplit)
import Scope.Sub (joinSubLeft, subBindDrop, subRefl)

data Subst = SNil
           | SCons Subst Term
               deriving Show

weakenSubst :: ListSplit -> Subst -> Subst
weakenSubst p SNil = SNil
weakenSubst p (SCons s t) = SCons (weakenSubst p s) (weaken p t)

instance Weaken Subst where
    weaken = weakenSubst

lookupSubst :: Subst -> Index -> Term
lookupSubst SNil q = inEmptyCase
lookupSubst (SCons f u) q = inBindCase q (lookupSubst f) u

subToSubst :: Scope -> ListSplit -> Subst
subToSubst [] p = SNil
subToSubst (() : α) p
  = SCons (subToSubst α (joinSubLeft [()] p))
      (TVar (coerce p inHere))

idSubst :: Scope -> Subst
idSubst r = subToSubst r subRefl

extSubst :: Subst -> TermS -> Subst
extSubst s TSNil = s
extSubst s (TSCons u t) = extSubst (SCons s u) t

liftBindSubst :: Subst -> Subst
liftBindSubst e
  = SCons (weaken (subBindDrop subRefl) e) (TVar inHere)

substExtScope :: RScope -> Subst -> Subst
substExtScope [] s = s
substExtScope (x : rγ) s
  = substExtScope rγ (weaken (subBindDrop subRefl) s)

substExtScopeKeep :: RScope -> Subst -> Subst
substExtScopeKeep [] p = p
substExtScopeKeep (x : rγ) p
  = substExtScopeKeep rγ (liftBindSubst p)

substTerm :: Subst -> Term -> Term
substTerm f (TVar k) = lookupSubst f k
substTerm f (TDef d) = TDef d
substTerm f (TData d ps is)
  = TData d (substTermS f ps) (substTermS f is)
substTerm f (TCon d c vs) = TCon d c (substTermS f vs)
substTerm f (TLam v) = TLam (substTerm (liftBindSubst f) v)
substTerm f (TApp u v) = TApp (substTerm f u) (substTerm f v)
substTerm f (TProj u p) = TProj (substTerm f u) p
substTerm f (TCase d r u bs m)
  = TCase d r (substTerm f u) (substBranches f bs)
      (substType (liftBindSubst (substExtScopeKeep r f)) m)
substTerm f (TPi a b)
  = TPi (substType f a) (substType (liftBindSubst f) b)
substTerm f (TSort s) = TSort (substSort f s)
substTerm f (TLet u v)
  = TLet (substTerm f u) (substTerm (liftBindSubst f) v)
substTerm f (TAnn u t) = TAnn (substTerm f u) (substType f t)

substSort :: Subst -> Sort -> Sort
substSort f (STyp x) = STyp x

substType :: Subst -> Type -> Type
substType f (El st t) = El (substSort f st) (substTerm f t)

substBranch :: Subst -> Branch -> Branch
substBranch f (BBranch rc r u)
  = BBranch rc r (substTerm (substExtScopeKeep r f) u)

substBranches :: Subst -> Branches -> Branches
substBranches f BsNil = BsNil
substBranches f (BsCons b bs)
  = BsCons (substBranch f b) (substBranches f bs)

substTermS :: Subst -> TermS -> TermS
substTermS f TSNil = TSNil
substTermS f (TSCons x e) = TSCons (substTerm f x) (substTermS f e)

class Substitute t where
    subst :: Subst -> t -> t

instance Substitute Term where
    subst = substTerm

instance Substitute TermS where
    subst = substTermS

instance Substitute Type where
    subst = substType

instance Substitute Sort where
    subst = substSort

instance Substitute Branch where
    subst = substBranch

instance Substitute Branches where
    subst = substBranches

substTelescope :: Subst -> Telescope -> Telescope
substTelescope f EmptyTel = EmptyTel
substTelescope f (ExtendTel a tel)
  = ExtendTel (substType f a) (substTelescope (liftBindSubst f) tel)

instance Substitute Telescope where
    subst = substTelescope

substTop :: Substitute t => Scope -> Term -> t -> t
substTop r u = subst (SCons (idSubst r) u)

composeSubst :: Subst -> Subst -> Subst
composeSubst SNil _ = SNil
composeSubst (SCons s1 u) s2
  = SCons (composeSubst s1 s2) (subst s2 u)

