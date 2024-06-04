{-# OPTIONS --allow-unsolved-metas #-}
module Rome.Types.Semantics where

open import Preludes.Level
open import Preludes.Data

open import Rome.GVars.Kinds

open import Rome.Kinds
open import Rome.Types.Syntax

open import IndexCalculus using (Row)
import IndexCalculus as Ix

--------------------------------------------------------------------------------
-- The meaning of kinding environments and predicates (mutually recursive).

⟦_⟧t : Type Δ κ → ⟦ Δ ⟧ke → Potatoes → ⟦ κ ⟧k

⟦_⟧p : {κ : Kind ℓκ} → Pred Δ κ → ⟦ Δ ⟧ke → Potatoes → Set (lsuc ℓκ)
⟦ ρ₁ ≲ ρ₂ ⟧p H n      = ⟦ ρ₁ ⟧t H n Ix.≲ ⟦ ρ₂ ⟧t H n
⟦ ρ₁ · ρ₂ ~ ρ₃ ⟧p H n = Ix._·_~_ (⟦ ρ₁ ⟧t H n) (⟦ ρ₂ ⟧t H n) (⟦ ρ₃ ⟧t H n)

--------------------------------------------------------------------------------
-- The meaning of type vars.

⟦_⟧tv : TVar Δ κ → ⟦ Δ ⟧ke → ⟦ κ ⟧k
⟦ Z ⟧tv (_ , t) = t
⟦ S v ⟧tv (H , _) = ⟦ v ⟧tv H

--------------------------------------------------------------------------------
-- The meaning of types.

buildΣ : ∀ {ι} → (κ : Kind ι) → ⟦ R[ κ ] ⟧k → ⟦ κ ⟧k
buildΣ (★ _) ⟦ρ⟧ = Ix.Σ ⟦ρ⟧
buildΣ (κ₁ `→ κ₂) (n , f) = λ X → buildΣ κ₂ (n , λ i → f i X)
buildΣ (L _) ⟦ρ⟧ = tt
buildΣ R[ κ ] (n , f) = n , λ i → buildΣ κ (f i)

buildΠ : ∀ {ι} → (κ : Kind ι) → ⟦ R[ κ ] ⟧k → ⟦ κ ⟧k
buildΠ (★ _) ⟦ρ⟧ = Ix.Π ⟦ρ⟧
buildΠ (κ₁ `→ κ₂) (n , f) = λ X → buildΠ κ₂ (n , λ i → f i X)
buildΠ (L _) ⟦ρ⟧ = tt
buildΠ R[ κ ] (n , f) = n , λ i → buildΠ κ (f i)

--------------------------------------------------------------------------------
--

⟦ lab l ⟧t       H n = tt
⟦ tvar v ⟧t      H n = ⟦ v ⟧tv H
⟦ (t₁ `→ t₂) ⟧t H n = ⟦ t₁ ⟧t H n → ⟦ t₂ ⟧t H n
⟦ `∀ κ v ⟧t      H n = (s : ⟦ κ ⟧k) → ⟦ v ⟧t  (H , s) n
⟦ t₁ ·[ t₂ ] ⟧t  H n = (⟦ t₁ ⟧t H n) (⟦ t₂ ⟧t H n)
⟦ `λ κ v ⟧t     H n =  λ (s : ⟦ κ ⟧k) → ⟦ v ⟧t (H , s) n
⟦ _ ▹ v ⟧t       H n = ⟦ v ⟧t H n
⟦ _ R▹ τ ⟧t H n = Ix.sing (⟦ τ ⟧t H n)
⟦ ⌊ τ ⌋ ⟧t H n      = ⊤
⟦ Π {κ = κ} ρ ⟧t H n = buildΠ κ (⟦ ρ ⟧t H n)
⟦ Σ {κ = κ} ρ ⟧t H n = buildΣ κ (⟦ ρ ⟧t H n)
⟦ ρ ·⌈ τ ⌉ ⟧t H n = Ix.lift₁ (⟦ ρ ⟧t H n) (⟦ τ ⟧t H n)
⟦ ⌈ τ ⌉· ρ ⟧t H n = Ix.lift₂ (⟦ τ ⟧t H n) (⟦ ρ ⟧t H n)
⟦ π ⇒ τ ⟧t H n = ⟦ π ⟧p H n → ⟦ τ ⟧t H n
⟦ ε ⟧t H n = Ix.emptyRow
⟦ μ F ⟧t H n = Ix.mu (⟦ F ⟧t H n) n


--------------------------------------------------------------------------------
-- Testing.

-- t : ∀ (ℓ : Level) → _
-- t ℓ = ⟦ Σ ((lab "u") R▹ `λ (★ ℓ) (tvar Z)) ⟧t 
-- ε

