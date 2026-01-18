module Agda.Core.Syntax.Term where

import Numeric.Natural (Natural)
import Scope.Core (RScope, rbind)
import Scope.In (Index, coerce, inHere)
import Scope.Sub (subExtScope, subRefl)

data Term = TVar Index
          | TDef Index
          | TData Index TermS TermS
          | TCon Index Index TermS
          | TLam Term
          | TApp Term Term
          | TProj Term Index
          | TCase Index RScope Term Branches Type
          | TPi Type Type
          | TSort Sort
          | TLet Term Term
          | TAnn Term Type
              deriving Show

data TermS = TSNil
           | TSCons Term TermS
               deriving Show

data Type = El{typeSort :: Sort, unType :: Term}
              deriving Show

data Sort = STyp Natural
              deriving Show

data Branch = BBranch Index RScope Term
                deriving Show

data Branches = BsNil
              | BsCons Branch Branches
                  deriving Show

piSort :: Sort -> Sort -> Sort
piSort (STyp a) (STyp b) = STyp (max a b)

funSort :: Sort -> Sort -> Sort
funSort (STyp a) (STyp b) = STyp (max a b)

sucSort :: Sort -> Sort
sucSort (STyp a) = STyp (1 + a)

sortType :: Sort -> Type
sortType s = El (sucSort s) (TSort s)

dataType :: Index -> Sort -> TermS -> TermS -> Type
dataType d ds pars ixs = El ds (TData d pars ixs)

caseBsNil :: Branches -> e -> e
caseBsNil BsNil f = f

caseBsCons :: Branches -> (Branch -> Branches -> e) -> e
caseBsCons (BsCons bh bt) f = f bh bt

caseTermSNil :: TermS -> e -> e
caseTermSNil TSNil f = f

caseTermSCons :: TermS -> (Term -> TermS -> e) -> e
caseTermSCons (TSCons t ts0) f = f t ts0

singBranches :: Branches -> RScope
singBranches BsNil = mempty
singBranches (BsCons bh bt) = rbind (singBranches bt)

singTermS :: TermS -> RScope
singTermS TSNil = mempty
singTermS (TSCons u t) = rbind (singTermS t)

applys :: Term -> [Term] -> Term
applys v [] = v
applys v (u : us) = applys (TApp v u) us

unApps :: Term -> (Term, [Term])
unApps (TApp u es2)
  = case unApps u of
        (u', es1) -> (u', es1 ++ [es2])
unApps u = (u, [])

termSrepeat :: RScope -> TermS
termSrepeat [] = TSNil
termSrepeat (() : rβ)
  = TSCons (TVar (coerce (subExtScope rβ subRefl) inHere))
      (termSrepeat rβ)

