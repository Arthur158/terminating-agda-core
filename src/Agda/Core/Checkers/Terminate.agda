open import Agda.Core.Prelude
open import Agda.Core.Name
open import Agda.Core.Syntax
open import Agda.Core.Reduce
open import Agda.Core.Rules.Conversion
open import Agda.Core.Rules.Typing
open import Agda.Core.TCM.Instances
open import Agda.Core.Checkers.Converter


module Agda.Core.Checkers.Terminate
    {{@0 globals : Globals}}
    {{@0 sig     : Signature}}
  where

private open module @0 G = Globals globals

private variable
  @0 x : Name
  @0 α : Scope Name
  @0 rβ : RScope Name


data SubTermContext : @0 Scope Name → Set where
  StCtxEmpty  : SubTermContext mempty
  StCtxExtend : SubTermContext α → (@0 x : Name) → Maybe (NameIn α) → SubTermContext (α ▸ x) -- here x, is a subterm of y.
{-# COMPILE AGDA2HS SubTermContext #-}

mkStCtxFromScope : (α : Scope Name) → SubTermContext α
mkStCtxFromScope  = StCtxEmpty

private -- it should use a RScope instead of β and then could be public
  raiseNameIn : {@0 α β : Scope Name} → Singleton β → Maybe (NameIn α) →  Maybe (NameIn (α <> β))
  raiseNameIn r (Just n) = Just (weakenNameIn (subJoinDrop r subRefl) n)
  raiseNameIn r Nothing = Nothing
  {-# COMPILE AGDA2HS raiseNameIn #-}


lookupSt : (Γ : SubTermContext α) (x : NameIn α) → Maybe (NameIn α)
lookupSt StCtxEmpty x = nameInEmptyCase x
lookupSt (StCtxExtend c namesubterm nameparent) name =
    raiseNameIn (sing _) (nameInBindCase name
      (λ q → lookupSt c (⟨ _ ⟩ q))
      (λ _ → nameparent))
{-# COMPILE AGDA2HS lookupSt #-}

checkSubtermVar : SubTermContext α → NameIn α → NameIn α → Bool
checkSubtermVar ctx name (⟨ _ ⟩ ( iancestor ⟨ _ ⟩)) = case (lookupSt ctx name) of λ where
  (Just (⟨ _ ⟩ ( iparent ⟨ _ ⟩))) → case (iancestor == iparent) of λ where
    True → True
    False → False -- this needs eventually to check recursively
  Nothing → False
{-# COMPILE AGDA2HS checkSubtermVar #-}

checkSubterm : SubTermContext α → NameIn α → Term α → Bool
checkSubterm con name (TVar name2) = checkSubtermVar con name name2
checkSubterm con name term = False
{-# COMPILE AGDA2HS checkSubterm #-}


-- At some point make the lists vecs for more security
compareArgsToParams : SubTermContext α → List (NameIn α) → List (Term α) → List Bool
compareArgsToParams con (param ∷ params) (arg ∷ args) = checkSubterm con param arg ∷ compareArgsToParams con params args
compareArgsToParams _ _ _ = []
{-# COMPILE AGDA2HS compareArgsToParams #-}

opaque
  unfolding RScope extScope
  updateEnv : SubTermContext α → (cs : RScope Name) → NameIn α → SubTermContext (extScope α cs)
  updateEnv env [] _ = env
  updateEnv env (Erased x ∷ s) name = updateEnv (StCtxExtend env x (Just name)) s (weakenNameIn (subWeaken subRefl) name)
  {-# COMPILE AGDA2HS updateEnv #-}

{-# NON_TERMINATING #-} -- need to find a way to not need those
handleBranches : ∀ {@0 d : NameData} {@0 cs : RScope (NameCon d)} → SubTermContext α → NameIn defScope → List (NameIn α) → NameIn α → (bs : Branches α d cs) → List Bool

getDecreasingArgs : SubTermContext α → NameIn defScope → List (NameIn α) → Term α → List Bool

handleBranches con funName params name BsNil = map (λ _ → True) params
handleBranches {α} con funName params name (BsCons (BBranch (c ⟨ w ⟩ ) (fields ⟨ p ⟩ ) clause) branches) = 
  zipWith (λ x y → x && y)
  (getDecreasingArgs (updateEnv con fields name) funName
    (map (weakenNameIn (subExtScope (sing fields) subRefl)) params)
    ( subst0 (λ f → Term (α ◂▸ f)) p clause ))
  (handleBranches con funName params name branches)

{-# COMPILE AGDA2HS handleBranches #-}


getDecreasingArgs con funName params (TApp u v) =  case unApps (TApp u v) of λ where
  (fun , args) → zipWith (λ x y → x && y) (foldr (zipWith (λ x y → x && y)) (map (λ _ → True) params) (map (getDecreasingArgs con funName params) args)) (case fun of λ where
    (TDef d) → case (d == funName) of λ where
     True → compareArgsToParams con params args
     False → map (λ _ → True) params
    x → getDecreasingArgs con funName params x)
getDecreasingArgs con funName params (TLam name body) = 
  getDecreasingArgs (StCtxExtend con name Nothing) funName (map (weakenNameIn (subWeaken subRefl)) params) body
getDecreasingArgs con funName params (TLet name body1 body2) = 
  zipWith (λ x y → x && y) (getDecreasingArgs con funName params body1) 
    (getDecreasingArgs (StCtxExtend con name Nothing) funName (map (weakenNameIn (subWeaken subRefl)) params) body2)
getDecreasingArgs con funName params (TCase _ _ (TVar nameVar) branches _) = -- we only accept pattern matching on variable for now.
  handleBranches con funName params nameVar branches
getDecreasingArgs _ _ params _ = map (λ _ → True) params
{-# COMPILE AGDA2HS getDecreasingArgs #-}

checkTermination : SubTermContext α → NameIn defScope → List (NameIn α) → Term α → Bool
checkTermination con fun params term = any id (getDecreasingArgs con fun params term)
{-# COMPILE AGDA2HS checkTermination #-}
