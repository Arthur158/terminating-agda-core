{-# LANGUAGE LambdaCase #-}
module Agda.Core.Checkers.Converter where

import Agda.Core.Prelude (Fuel(More, None))
import Agda.Core.Reduce (reduce)
import Agda.Core.Rules.Conversion (Conv(CApp, CCase, CCon, CData, CLam, CPi, CRedL, CRedR, CRefl), ConvBranch(CBBranch), ConvBranches(CBranchesCons, CBranchesNil), ConvTermS(CSCons, CSNil), renameTop)
import Agda.Core.Syntax.Term (Branch(BBranch), Branches(BsCons, BsNil), Sort(STyp), Term(TApp, TCase, TCon, TData, TDef, TLam, TPi, TProj, TSort, TVar), TermS(TSCons, TSNil), Type(unType), caseBsCons, caseTermSCons)
import Agda.Core.TCM.Instances ()
import Agda.Core.TCM.TCM (TCM, tcError, tcmFuel, tcmSignature)
import Scope.Core (RScope, Scope, singBind, singExtScope)
import Scope.In (Index, decIn, decInR)

import Agda.Core.TCM.Instances

reduceTo :: Scope -> Term -> TCM Term
reduceTo r v
  = do fl <- tcmFuel
       rsig <- tcmSignature
       case reduce r rsig v fl of
           Nothing -> tcError "not enough fuel to reduce a term"
           Just u -> return $ u

reduceToPi :: Scope -> Term -> String -> TCM (Type, Type)
reduceToPi r v err
  = reduceTo r v >>=
      \case
          TPi a b -> return (a, b)
          _ -> tcError err

reduceToData ::
             Scope -> Term -> String -> TCM (Index, (TermS, TermS))
reduceToData r v err
  = reduceTo r v >>=
      \case
          TData d pars ixs -> return (d, (pars, ixs))
          _ -> tcError err

reduceToSort :: Scope -> Term -> String -> TCM Sort
reduceToSort r v err
  = reduceTo r v >>=
      \case
          TSort s -> return s
          _ -> tcError err

convNamesIn :: Index -> Index -> TCM ()
convNamesIn x y
  = if decIn x y then return () else tcError "names not equal"

convVars :: Index -> Index -> TCM Conv
convVars x y
  = do () <- convNamesIn x y
       return CRefl

convDefs :: Index -> Index -> TCM Conv
convDefs p q
  = if decIn p q then return CRefl else
      tcError "definitions not convertible"

convSorts :: Sort -> Sort -> TCM Conv
convSorts (STyp u) (STyp u')
  = if u == u' then return $ CRefl else
      tcError "can't convert two different sorts"

convertCheck :: Fuel -> Scope -> Term -> Term -> TCM Conv
convertCheck None r t z
  = tcError "not enough fuel to check conversion"
convertCheck (More x) r t q
  = do t <- reduceTo r t
       q <- reduceTo r q
       CRedL . CRedR <$> convertWhnf x r t q

convertTermSs :: Fuel -> Scope -> TermS -> TermS -> TCM ConvTermS
convertTermSs fl r TSNil _ = return CSNil
convertTermSs fl r (TSCons u s0) t
  = caseTermSCons t
      (\ v t0 ->
         do hc <- convertCheck fl r u v
            tc <- convertTermSs fl r s0 t0
            return (CSCons hc tc))

convertBranches ::
                Fuel -> Scope -> Branches -> Branches -> TCM ConvBranches
convertBranches fl r BsNil bp = return (CBranchesNil BsNil bp)
convertBranches fl r (BsCons bsh bst) bp
  = caseBsCons bp
      (\ bph bpt ->
         CBranchesCons bsh bph bst bpt <$> convertBranch fl r bsh bph <*>
           convertBranches fl r bst bpt)

convDatas ::
          Fuel ->
            Scope ->
              Index -> Index -> TermS -> TermS -> TermS -> TermS -> TCM Conv
convDatas fl r d e ps qs is ks
  = if decIn d e then
      do cps <- convertTermSs fl r ps qs
         cis <- convertTermSs fl r is ks
         return $ CData cps cis
      else tcError "datatypes not convertible"

convCons ::
         Fuel ->
           Scope ->
             Index -> Index -> Index -> Index -> TermS -> TermS -> TCM Conv
convCons fl r d d' f g lp lq
  = if decIn d d' then
      if decInR f g then
        do csp <- convertTermSs fl r lp lq
           return $ CCon f csp
        else tcError "constructors not convertible"
      else tcError "constructors are from not convertible datatypes"

convLams :: Fuel -> Scope -> Term -> Term -> TCM Conv
convLams fl r u v
  = CLam <$>
      convertCheck fl (singBind r) (renameTop r u) (renameTop r v)

convApps ::
         Fuel -> Scope -> Term -> Term -> Term -> Term -> TCM Conv
convApps fl r u u' w w'
  = do cu <- convertCheck fl r u u'
       cw <- convertCheck fl r w w'
       return (CApp cu cw)

convertCase ::
            Fuel ->
              Scope ->
                Index ->
                  Index ->
                    RScope ->
                      RScope ->
                        Term -> Term -> Branches -> Branches -> Type -> Type -> TCM Conv
convertCase fl rα d d' ri ri' u u' ws ws' rt rt'
  = do () <- convNamesIn d d'
       cu <- convertCheck fl rα u u'
       cm <- convertCheck fl (singBind (singExtScope rα ri))
               (renameTop (singExtScope rα ri) (unType rt))
               (renameTop (singExtScope rα ri') (unType rt'))
       cbs <- convertBranches fl rα ws ws'
       return (CCase u u' d ri ri' ws ws' rt rt' cu cm cbs)

convPis ::
        Fuel -> Scope -> Type -> Type -> Type -> Type -> TCM Conv
convPis fl r u u' v v'
  = CPi <$> convertCheck fl r (unType u) (unType u') <*>
      convertCheck fl (singBind r) (unType v) (renameTop r (unType v'))

convertBranch ::
              Fuel -> Scope -> Branch -> Branch -> TCM ConvBranch
convertBranch fl r (BBranch rc rz1 rhs1) (BBranch rc' rz2 rhs2)
  = CBBranch rc rc' rz1 rz2 rhs1 rhs2 <$>
      convertCheck fl (singExtScope r rz2) rhs1 rhs2

convertWhnf :: Fuel -> Scope -> Term -> Term -> TCM Conv
convertWhnf fl r (TVar x) (TVar y) = convVars x y
convertWhnf fl r (TDef x) (TDef y) = convDefs x y
convertWhnf fl r (TData d ps is) (TData e qs ks)
  = convDatas fl r d e ps qs is ks
convertWhnf fl r (TCon d c lc) (TCon d' c' ld)
  = convCons fl r d d' c c' lc ld
convertWhnf fl r (TLam u) (TLam v) = convLams fl r u v
convertWhnf fl r (TApp u e) (TApp v f) = convApps fl r u v e f
convertWhnf fl r (TProj u f) (TProj v g)
  = tcError "not implemented: conversion of projections"
convertWhnf fl r (TCase d ri u bs rt) (TCase d' ri' u' bs' rt')
  = convertCase fl r d d' ri ri' u u' bs bs' rt rt'
convertWhnf fl r (TPi tu tv) (TPi tw tz) = convPis fl r tu tw tv tz
convertWhnf fl r (TSort s) (TSort t) = convSorts s t
convertWhnf fl r _ _
  = tcError "two terms are not the same and aren't convertible"

convert :: Scope -> Term -> Term -> TCM Conv
convert r t q
  = do fl <- tcmFuel
       convertCheck fl r t q

