module Agda.Core.Checkers.Terminate where

import Agda.Core.Name ()
import Agda.Core.Syntax.Term (Branch(BBranch), Branches(BsCons, BsNil), Term(TApp, TCase, TDef, TLam, TLet, TVar), unApps)
import Agda.Core.Syntax.Weakening (weakenNameIn)
import Scope.Core (RScope, Scope, singleton)
import Scope.In (Index, inBindCase, inEmptyCase)
import Scope.Sub (subExtScope, subJoinDrop, subRefl, subWeaken)

data SubTermContext = StCtxEmpty
                    | StCtxExtend SubTermContext (Maybe Index)

raiseNameIn :: Scope -> Maybe Index -> Maybe Index
raiseNameIn r (Just n)
  = Just (weakenNameIn (subJoinDrop r subRefl) n)
raiseNameIn r Nothing = Nothing

lookupSt :: SubTermContext -> Index -> Maybe Index
lookupSt StCtxEmpty x = inEmptyCase
lookupSt (StCtxExtend c nameparent) name
  = raiseNameIn singleton
      (inBindCase name (\ q -> lookupSt c q) nameparent)

checkSubtermVar :: SubTermContext -> Index -> Index -> Bool
checkSubtermVar ctx name iancestor
  = case lookupSt ctx name of
        Just iparent -> case iancestor == iparent of
                            True -> True
                            False -> False
        Nothing -> False

checkSubterm :: SubTermContext -> Index -> Term -> Bool
checkSubterm con name (TVar name2) = checkSubtermVar con name name2
checkSubterm con name term = False

compareArgsToParams ::
                    SubTermContext -> [Index] -> [Term] -> [Bool]
compareArgsToParams con (param : params) (arg : args)
  = checkSubterm con param arg : compareArgsToParams con params args
compareArgsToParams _ _ _ = []

updateEnv :: SubTermContext -> RScope -> Index -> SubTermContext
updateEnv env [] _ = env
updateEnv env (() : s) name
  = updateEnv (StCtxExtend env (Just name)) s
      (weakenNameIn (subWeaken subRefl) name)

handleBranches ::
               SubTermContext -> Index -> [Index] -> Index -> Branches -> [Bool]
handleBranches con funName params name BsNil
  = map (\ _ -> True) params
handleBranches con funName params name
  (BsCons (BBranch c fields clause) branches)
  = zipWith (&&)
      (getDecreasingArgs (updateEnv con fields name) funName
         (map (weakenNameIn (subExtScope fields subRefl)) params)
         clause)
      (handleBranches con funName params name branches)

getDecreasingArgs ::
                  SubTermContext -> Index -> [Index] -> Term -> [Bool]
getDecreasingArgs con funName params (TApp u v)
  = case unApps (TApp u v) of
        (fun, args) -> zipWith (&&)
                         (foldr (zipWith (&&)) (map (\ _ -> True) params)
                            (map (getDecreasingArgs con funName params) args))
                         (case fun of
                              TDef d -> case d == funName of
                                            True -> compareArgsToParams con params args
                                            False -> map (\ _ -> True) params
                              x -> getDecreasingArgs con funName params x)
getDecreasingArgs con funName params (TLam body)
  = getDecreasingArgs (StCtxExtend con Nothing) funName
      (map (weakenNameIn (subWeaken subRefl)) params)
      body
getDecreasingArgs con funName params (TLet body1 body2)
  = zipWith (&&) (getDecreasingArgs con funName params body1)
      (getDecreasingArgs (StCtxExtend con Nothing) funName
         (map (weakenNameIn (subWeaken subRefl)) params)
         body2)
getDecreasingArgs con funName params
  (TCase _ _ (TVar nameVar) branches _)
  = handleBranches con funName params nameVar branches
getDecreasingArgs _ _ params _ = map (\ _ -> True) params

checkTermination :: Index -> [Index] -> Term -> Bool
checkTermination fun params term
  = any id (getDecreasingArgs StCtxEmpty fun params term)

