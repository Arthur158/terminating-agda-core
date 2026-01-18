module Agda.Core.Rules.Conversion where

import Agda.Core.Syntax.Substitute (Substitute(subst), idSubst, liftBindSubst)
import Agda.Core.Syntax.Term (Branch, Branches, Sort, Term, Type)
import Scope.Core (RScope, Scope)
import Scope.In (Index)

data Conv = CRefl
          | CLam Conv
          | CPi Conv Conv
          | CApp Conv Conv
          | CCase Term Term Index RScope RScope Branches Branches Type Type
                  Conv Conv ConvBranches
          | CData ConvTermS ConvTermS
          | CCon Index ConvTermS
          | CRedL Conv
          | CRedR Conv

data ConvTermS = CSNil
               | CSCons Conv ConvTermS

data ConvBranch = CBBranch Index Index RScope RScope Term Term Conv

data ConvBranches = CBranchesNil Branches Branches
                  | CBranchesCons Branch Branch Branches Branches ConvBranch
                                  ConvBranches

renameTop :: Scope -> Term -> Term
renameTop = subst . liftBindSubst . idSubst

renameTopSort :: Scope -> Sort -> Sort
renameTopSort = subst . liftBindSubst . idSubst

renameTopType :: Scope -> Type -> Type
renameTopType = subst . liftBindSubst . idSubst

