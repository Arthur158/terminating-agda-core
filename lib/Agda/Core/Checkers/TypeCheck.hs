{-# LANGUAGE TupleSections #-}
module Agda.Core.Checkers.TypeCheck where

import Agda.Core.Checkers.Converter (convNamesIn, convert, reduceToData, reduceToPi, reduceToSort)
import Agda.Core.Rules.Conversion (Conv(CPi, CRedL, CRedR, CRefl), renameTop, renameTopSort)
import Agda.Core.Rules.Typing (TyBranch, TyBranches(TyBsCons, TyBsNil), TyTerm(TyAnn, TyApp, TyConv, TyLam, TyLet, TyPi, TyTVar, TyType), TyTermS(TyCons, TyNil), constructorType, tyBBranch', tyCase', tyCon', tyData', tyDef')
import Agda.Core.Syntax.Context (Context(CtxExtend), Telescope(EmptyTel, ExtendTel), addContextTel, singScope)
import Agda.Core.Syntax.Signature (Constructor(conIndTel), Datatype(dataIxTel, dataParTel, dataSort), SigDefinition, Signature(sigCons, sigData), getDefinition, getType, instConIx)
import Agda.Core.Syntax.Substitute (Subst(SCons, SNil), Substitute(subst), extSubst, idSubst, substTelescope, substTop, substType, weakenSubst)
import Agda.Core.Syntax.Term (Branch(BBranch), Branches, Sort(STyp), Term(TAnn, TApp, TCase, TCon, TData, TDef, TLam, TLet, TPi, TProj, TSort, TVar), TermS, Type(El, typeSort, unType), caseBsCons, caseBsNil, caseTermSCons, caseTermSNil, dataType, piSort, singBranches, sortType, sucSort, termSrepeat)
import Agda.Core.Syntax.Weakening (Weaken(weaken), lookupVar)
import Agda.Core.TCM.Instances ()
import Agda.Core.TCM.TCM (TCM, tcError, tcmSignature)
import Scope.Core (RScope, caseRScope)
import Scope.In (Index, decIn)
import Scope.Sub (subBindDrop, subExtScope, subRefl)
import Debug.Trace

checkCoerce ::
            Context -> Term -> (Type, TyTerm) -> Type -> TCM TyTerm
checkCoerce ctx t (gty, dgty) cty
  = TyConv dgty <$> convert (singScope ctx) (unType gty) (unType cty)

tcmGetType :: Index -> TCM Type
tcmGetType x
  = do rsig <- tcmSignature
       return (getType rsig x)

tcmGetDefinition :: Index -> TCM SigDefinition
tcmGetDefinition x
  = do rsig <- tcmSignature
       return (getDefinition rsig x)

tcmGetDatatype :: Index -> TCM Datatype
tcmGetDatatype d
  = do rsig <- tcmSignature
       return (sigData rsig d)

tcmGetConstructor :: Index -> Index -> TCM Constructor
tcmGetConstructor d c
  = do rsig <- tcmSignature
       return (sigCons rsig d c)

inferVar :: Context -> Index -> TCM (Type, TyTerm)
inferVar ctx x = return $ (lookupVar ctx x, TyTVar x)

inferSort :: Context -> Term -> TCM (Sort, TyTerm)
inferSort ctx t
  = do (st, dt) <- inferType ctx t
       s <- reduceToSort (singScope ctx) (unType st)
              "couldn't reduce a term to a sort"
       return $ (s, TyConv dt (CRedL CRefl))

inferType :: Context -> Term -> TCM (Type, TyTerm)
inferType ctx (TVar x) = inferVar ctx x
inferType ctx (TDef d) = inferDef ctx d
inferType ctx (TData d ps is) = inferData ctx d ps is
inferType ctx (TCon d c x)
  = tcError "non inferrable: can't infer the type of a constructor"
inferType ctx (TLam te)
  = tcError "non inferrable: can't infer the type of a lambda"
inferType ctx (TApp u e) = inferApp ctx u e
inferType ctx (TCase d r u bs rt) = inferCase ctx d r u bs rt
inferType ctx (TProj u f) = tcError "not implemented: projections"
inferType ctx (TPi a b) = inferPi ctx a b
inferType ctx (TSort s) = inferTySort ctx s
inferType ctx (TLet te te₁)
  = tcError "non inferrable: can't infer the type of a let"
inferType ctx (TAnn u t) = (t,) <$> (TyAnn <$> checkType ctx u t)

checkType :: Context -> Term -> Type -> TCM TyTerm
checkType ctx (TVar x) ty
  = do tvar <- inferVar ctx x
       checkCoerce ctx (TVar x) tvar ty
checkType ctx (TDef d) ty
  = do tdef <- inferDef ctx d
       checkCoerce ctx (TDef d) tdef ty
checkType ctx (TData d ps is) ty
  = do tdef <- inferData ctx d ps is
       checkCoerce ctx (TData d ps is) tdef ty
checkType ctx (TCon d c x) ty = checkCon ctx d c x ty
checkType ctx (TLam te) ty = checkLambda ctx te ty
checkType ctx (TApp u e) ty
  = do tapp <- inferApp ctx u e
       checkCoerce ctx (TApp u e) tapp ty
checkType ctx (TCase d r u bs rt) ty
  = do tapp <- inferCase ctx d r u bs rt
       checkCoerce ctx (TCase d r u bs rt) tapp ty
checkType ctx (TProj u f) ty
  = tcError "not implemented: projections"
checkType ctx (TPi tu tv) ty
  = do tpi <- inferPi ctx tu tv
       checkCoerce ctx (TPi tu tv) tpi ty
checkType ctx (TSort s) ty
  = do tts <- inferTySort ctx s
       checkCoerce ctx (TSort s) tts ty
checkType ctx (TLet u v) ty = checkLet ctx u v ty
checkType ctx (TAnn u t) ty
  = do ct <- TyAnn <$> checkType ctx u t
       checkCoerce ctx (TAnn u t) (t, ct) ty

checkBranches ::
              Index ->
                Context ->
                  RScope -> Branches -> Datatype -> TermS -> Type -> TCM TyBranches
checkBranches d ctx cons bs dt ps rt
  = caseRScope cons (caseBsNil bs (return TyBsNil))
      (\ ct ->
         caseBsCons bs
           (\ bh bt ->
              TyBsCons <$> checkBranch d ctx bh dt ps rt <*>
                checkBranches d ctx (singBranches bt) bt dt ps rt))

inferApp :: Context -> Term -> Term -> TCM (Type, TyTerm)
inferApp ctx u v
  = do (tu, gtu) <- inferType ctx u
       (at, rt) <- reduceToPi (singScope ctx) (unType tu)
                     "couldn't reduce term to a pi type"
       gtv <- checkType ctx v at
       return
         (substTop (singScope ctx) v rt,
          TyApp at (TyConv gtu (CRedL CRefl)) gtv)

inferCase ::
          Context ->
            Index -> RScope -> Term -> Branches -> Type -> TCM (Type, TyTerm)
inferCase ctx d rixs u bs rt
  = do (El s tu, gtu) <- inferType ctx u
       (d', (params, ixs)) <- reduceToData (singScope ctx) tu
                                "can't typecheck a constrctor with a type that isn't a def application"
       () <- convNamesIn d d'
       df <- tcmGetDatatype d
       grt <- checkType
                (CtxExtend
                   (addContextTel ctx
                      (substTelescope (extSubst SNil params) (dataIxTel df)))
                   (weaken (subExtScope rixs subRefl)
                      (dataType d (subst (extSubst SNil params) (dataSort df)) params
                         ixs)))
                (unType rt)
                (sortType (typeSort rt))
       cb <- checkBranches d ctx (singBranches bs) bs df params rt
       return
         (substType (SCons (extSubst (idSubst (singScope ctx)) ixs) u) rt,
          tyCase' d bs rt grt cb (TyConv gtu (CRedL CRefl)))

inferPi :: Context -> Type -> Type -> TCM (Type, TyTerm)
inferPi ctx (El su u) (El sv v)
  = do tu <- checkType ctx u (sortType su)
       tv <- checkType (CtxExtend ctx (El su u)) v (sortType sv)
       return $ (sortType (piSort su sv), TyPi tu tv)

inferTySort :: Context -> Sort -> TCM (Type, TyTerm)
inferTySort ctx (STyp x)
  = return $ (sortType (sucSort (STyp x)), TyType)

inferDef :: Context -> Index -> TCM (Type, TyTerm)
inferDef ctx f
  = do ty <- tcmGetType f
       return $ (ty, tyDef' f)

checkTermS :: Context -> Telescope -> TermS -> TCM TyTermS
checkTermS ctx EmptyTel t = caseTermSNil t (return TyNil)
checkTermS ctx (ExtendTel ty rest) ts
  = caseTermSCons ts
      (\ u s ->
         do tyx <- checkType ctx u ty
            tyrest <- checkTermS ctx
                        (substTelescope (SCons (idSubst (singScope ctx)) u) rest)
                        s
            return (TyCons tyx tyrest))

inferData ::
          Context -> Index -> TermS -> TermS -> TCM (Type, TyTerm)
inferData ctx d pars ixs
  = do dt <- tcmGetDatatype d
       typars <- checkTermS ctx (subst SNil (dataParTel dt)) pars
       tyixs <- checkTermS ctx (subst (extSubst SNil pars) (dataIxTel dt))
                  ixs
       return
         (sortType (subst (extSubst SNil pars) (dataSort dt)),
          tyData' d typars tyixs)

checkBranch ::
            Index ->
              Context -> Branch -> Datatype -> TermS -> Type -> TCM TyBranch
checkBranch d ctx (BBranch c r rhs) dt ps rt
  = do con <- tcmGetConstructor d c
       crhs <- checkType
                 (addContextTel ctx
                    (substTelescope (extSubst SNil ps) (conIndTel con)))
                 rhs
                 (subst
                    (SCons
                       (extSubst
                          (weakenSubst (subExtScope r subRefl) (idSubst (singScope ctx)))
                          (instConIx con (weaken (subExtScope r subRefl) ps)
                             (termSrepeat r)))
                       (TCon d c (termSrepeat r)))
                    rt)
       return (tyBBranch' c rhs crhs)

checkCon ::
         Context -> Index -> Index -> TermS -> Type -> TCM TyTerm
checkCon ctx d c cargs (El s ty)
  = do (d', (params, ixs)) <- reduceToData (singScope ctx) ty
                                "can't typecheck a constructor with a type that isn't a def application"
       if decIn d d' then
         do dt <- tcmGetDatatype d'
            con <- tcmGetConstructor d' c
            tySubst <- checkTermS ctx
                         (subst (extSubst SNil params) (conIndTel con))
                         cargs
            checkCoerce ctx (TCon d' c cargs)
              (constructorType d' dt c con params cargs, tyCon' d' c tySubst)
              (El s ty)
         else tcError "datatypes not convertible"

checkLambda :: Context -> Term -> Type -> TCM TyTerm
checkLambda ctx u (El s ty)
  = do (tu, El tvs tvt) <- reduceToPi (singScope ctx) ty
                             "couldn't reduce a term to a pi type"
       d <- checkType (CtxExtend ctx tu) u
              (El (renameTopSort (singScope ctx) tvs)
                 (renameTop (singScope ctx) tvt))
       return $ TyConv (TyLam d) (CRedR (CPi CRefl CRefl))

checkLet :: Context -> Term -> Term -> Type -> TCM TyTerm
checkLet ctx u v ty
  = do (tu, dtu) <- inferType ctx u
       dtv <- checkType (CtxExtend ctx tu) v
                (weaken (subBindDrop subRefl) ty)
       return $ TyLet dtu dtv

