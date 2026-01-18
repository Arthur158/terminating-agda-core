open import Zero
module One where

id : (A : Set) → A → A
id A x = x

ap : (A B : Set) → (A → B) → A → B
ap A B f x = f (id A x)

dap : (A : Set) (B : A → Set) → (∀ x → B x) → ∀ x → B x
dap A B f x = f (id0 A x)
