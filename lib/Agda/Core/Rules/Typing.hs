module Agda.Core.Rules.Typing where

import Agda.Core.Rules.Conversion (Conv)
import Agda.Core.Syntax.Signature (Constructor, Datatype(dataSort), instConIx)
import Agda.Core.Syntax.Substitute (Subst(SNil), Substitute(subst), extSubst)
import Agda.Core.Syntax.Term (Branches, Term, TermS, Type, dataType)
import Scope.In (Index)

constructorType ::
                Index -> Datatype -> Index -> Constructor -> TermS -> TermS -> Type
constructorType d dt c con pars us
  = dataType d (subst (extSubst SNil pars) (dataSort dt)) pars
      (instConIx con pars us)

data TyTerm = TyTVar Index
            | TyDef Index
            | TyData Index TyTermS TyTermS
            | TyCon Index Index TyTermS
            | TyLam TyTerm
            | TyApp Type TyTerm TyTerm
            | TyCase Index Branches Type TyTerm TyBranches TyTerm
            | TyPi TyTerm TyTerm
            | TyType
            | TyLet TyTerm TyTerm
            | TyAnn TyTerm
            | TyConv TyTerm Conv

data TyTermS = TyNil
             | TyCons TyTerm TyTermS

data TyBranches = TyBsNil
                | TyBsCons TyBranch TyBranches

data TyBranch = TyBBranch Index Term TyTerm

tyDef' :: Index -> TyTerm
tyDef' f = TyDef f

tyData' :: Index -> TyTermS -> TyTermS -> TyTerm
tyData' d typars tyixs = TyData d typars tyixs

tyCon' :: Index -> Index -> TyTermS -> TyTerm
tyCon' d c tySubst = TyCon d c tySubst

tyCase' ::
        Index ->
          Branches -> Type -> TyTerm -> TyBranches -> TyTerm -> TyTerm
tyCase' d cases return wfReturn tyCases tyu
  = TyCase d cases return wfReturn tyCases tyu

tyBBranch' :: Index -> Term -> TyTerm -> TyBranch
tyBBranch' c0 rsh crhs = TyBBranch c0 rsh crhs

