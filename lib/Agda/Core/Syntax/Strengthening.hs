module Agda.Core.Syntax.Strengthening where

import Agda.Core.Syntax.Term (Branch(BBranch), Branches(BsCons, BsNil), Sort(STyp), Term(TAnn, TApp, TCase, TCon, TData, TDef, TLam, TLet, TPi, TProj, TSort, TVar), TermS(TSCons, TSNil), Type(El))
import Scope.In (inSplitCase)
import Scope.Split (ListSplit)
import Scope.Sub (subBindKeep, subExtScopeKeep)

strengthenTerm :: ListSplit -> Term -> Maybe Term
strengthenTerm p (TVar q)
  = inSplitCase p q (\ q -> Just (TVar q)) (\ _ -> Nothing)
strengthenTerm p (TDef d) = Just (TDef d)
strengthenTerm p (TData d ps is)
  = TData d <$> strengthenTermS p ps <*> strengthenTermS p is
strengthenTerm p (TCon d c vs) = TCon d c <$> strengthenTermS p vs
strengthenTerm p (TLam v)
  = TLam <$> strengthenTerm (subBindKeep p) v
strengthenTerm p (TApp v e)
  = TApp <$> strengthenTerm p v <*> strengthenTerm p e
strengthenTerm p (TProj u f)
  = (\ v -> TProj v f) <$> strengthenTerm p u
strengthenTerm p (TCase d r u bs m)
  = TCase d r <$> strengthenTerm p u <*> strengthenBranches p bs <*>
      strengthenType (subBindKeep (subExtScopeKeep r p)) m
strengthenTerm p (TPi a b)
  = TPi <$> strengthenType p a <*> strengthenType (subBindKeep p) b
strengthenTerm p (TSort s) = TSort <$> strengthenSort p s
strengthenTerm p (TLet u v)
  = TLet <$> strengthenTerm p u <*> strengthenTerm (subBindKeep p) v
strengthenTerm p (TAnn u t)
  = TAnn <$> strengthenTerm p u <*> strengthenType p t

strengthenTermS :: ListSplit -> TermS -> Maybe TermS
strengthenTermS p TSNil = Just TSNil
strengthenTermS p (TSCons v vs)
  = TSCons <$> strengthenTerm p v <*> strengthenTermS p vs

strengthenType :: ListSplit -> Type -> Maybe Type
strengthenType p (El st t)
  = El <$> strengthenSort p st <*> strengthenTerm p t

strengthenSort :: ListSplit -> Sort -> Maybe Sort
strengthenSort p (STyp n) = Just (STyp n)

strengthenBranch :: ListSplit -> Branch -> Maybe Branch
strengthenBranch p (BBranch rc r v)
  = BBranch rc r <$> strengthenTerm (subExtScopeKeep r p) v

strengthenBranches :: ListSplit -> Branches -> Maybe Branches
strengthenBranches p BsNil = Just BsNil
strengthenBranches p (BsCons b bs)
  = BsCons <$> strengthenBranch p b <*> strengthenBranches p bs

class Strengthen t where
    strengthen :: ListSplit -> t -> Maybe t

instance Strengthen Term where
    strengthen = strengthenTerm

instance Strengthen TermS where
    strengthen = strengthenTermS

instance Strengthen Type where
    strengthen = strengthenType

instance Strengthen Sort where
    strengthen = strengthenSort

instance Strengthen Branch where
    strengthen = strengthenBranch

instance Strengthen Branches where
    strengthen = strengthenBranches

