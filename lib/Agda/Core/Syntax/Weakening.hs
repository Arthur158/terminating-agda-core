module Agda.Core.Syntax.Weakening where

import Agda.Core.Syntax.Context (Context(CtxEmpty, CtxExtend), Telescope(EmptyTel, ExtendTel))
import Agda.Core.Syntax.Term (Branch(BBranch), Branches(BsCons, BsNil), Sort(STyp), Term(TAnn, TApp, TCase, TCon, TData, TDef, TLam, TLet, TPi, TProj, TSort, TVar), TermS(TSCons, TSNil), Type(El))
import Scope.Core (RScope, Scope, singleton)
import Scope.In (Index, coerce, inBindCase, inEmptyCase)
import Scope.Split (ListSplit)
import Scope.Sub (subBindKeep, subExtScope, subExtScopeKeep, subJoinDrop, subRefl)

weakenNameIn :: ListSplit -> Index -> Index
weakenNameIn p b = coerce p b

weakenTerm :: ListSplit -> Term -> Term
weakenTerm p (TVar x) = TVar (weakenNameIn p x)
weakenTerm p (TDef d) = TDef d
weakenTerm p (TData d ps is)
  = TData d (weakenTermS p ps) (weakenTermS p is)
weakenTerm p (TCon d c vs) = TCon d c (weakenTermS p vs)
weakenTerm p (TLam v) = TLam (weakenTerm (subBindKeep p) v)
weakenTerm p (TApp u e) = TApp (weakenTerm p u) (weakenTerm p e)
weakenTerm p (TProj u x) = TProj (weakenTerm p u) x
weakenTerm p (TCase d r u bs m)
  = TCase d r (weakenTerm p u) (weakenBranches p bs)
      (weakenType (subBindKeep (subExtScopeKeep r p)) m)
weakenTerm p (TPi a b)
  = TPi (weakenType p a) (weakenType (subBindKeep p) b)
weakenTerm p (TSort α) = TSort (weakenSort p α)
weakenTerm p (TLet v t)
  = TLet (weakenTerm p v) (weakenTerm (subBindKeep p) t)
weakenTerm p (TAnn u t) = TAnn (weakenTerm p u) (weakenType p t)

weakenTermS :: ListSplit -> TermS -> TermS
weakenTermS p TSNil = TSNil
weakenTermS p (TSCons u e)
  = TSCons (weakenTerm p u) (weakenTermS p e)

weakenSort :: ListSplit -> Sort -> Sort
weakenSort p (STyp x) = STyp x

weakenType :: ListSplit -> Type -> Type
weakenType p (El st t) = El (weakenSort p st) (weakenTerm p t)

weakenBranch :: ListSplit -> Branch -> Branch
weakenBranch p (BBranch rc r x)
  = BBranch rc r (weakenTerm (subExtScopeKeep r p) x)

weakenBranches :: ListSplit -> Branches -> Branches
weakenBranches p BsNil = BsNil
weakenBranches p (BsCons b bs)
  = BsCons (weakenBranch p b) (weakenBranches p bs)

class Weaken t where
    weaken :: ListSplit -> t -> t

instance Weaken Term where
    weaken = weakenTerm

instance Weaken TermS where
    weaken = weakenTermS

instance Weaken Sort where
    weaken = weakenSort

instance Weaken Type where
    weaken = weakenType

instance Weaken Branch where
    weaken = weakenBranch

instance Weaken Branches where
    weaken = weakenBranches

weakenTel :: ListSplit -> Telescope -> Telescope
weakenTel p EmptyTel = EmptyTel
weakenTel p (ExtendTel ty t)
  = ExtendTel (weaken p ty) (weakenTel (subBindKeep p) t)

instance Weaken Telescope where
    weaken = weakenTel

raise :: RScope -> Term -> Term
raise r = weakenTerm (subExtScope r subRefl)

raiseType :: Scope -> Type -> Type
raiseType r = weakenType (subJoinDrop r subRefl)

lookupVar :: Context -> Index -> Type
lookupVar CtxEmpty x = inEmptyCase
lookupVar (CtxExtend g s) x
  = raiseType singleton (inBindCase x (\ q -> lookupVar g q) s)

