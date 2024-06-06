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


⟦_⟧t : Type Δ κ → ⟦ Δ ⟧ke → ⟦ κ ⟧k

⟦_⟧p : {κ : Kind ℓκ} → Pred Δ κ → ⟦ Δ ⟧ke → Set (lsuc ℓκ)
⟦ ρ₁ ≲ ρ₂ ⟧p H = ⟦ ρ₁ ⟧t H Ix.≲ ⟦ ρ₂ ⟧t H
⟦ ρ₁ · ρ₂ ~ ρ₃ ⟧p H = Ix._·_~_ (⟦ ρ₁ ⟧t H) (⟦ ρ₂ ⟧t H) (⟦ ρ₃ ⟧t H)

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

⟦ lab l ⟧t       H = tt
⟦ tvar v ⟧t      H = ⟦ v ⟧tv H
⟦ (t₁ `→ t₂) ⟧t H = ⟦ t₁ ⟧t H → ⟦ t₂ ⟧t H
⟦ `∀ κ v ⟧t      H = (s : ⟦ κ ⟧k) → ⟦ v ⟧t  (H , s)
⟦ t₁ ·[ t₂ ] ⟧t  H = (⟦ t₁ ⟧t H) (⟦ t₂ ⟧t H)
⟦ `λ κ v ⟧t     H =  λ (s : ⟦ κ ⟧k) → ⟦ v ⟧t (H , s)
⟦ _ ▹ v ⟧t       H = ⟦ v ⟧t H
⟦ _ R▹ τ ⟧t H = Ix.sing (⟦ τ ⟧t H)
⟦ ⌊ τ ⌋ ⟧t H       = ⊤
⟦ Π {κ = κ} ρ ⟧t H = buildΠ κ (⟦ ρ ⟧t H)
⟦ Σ {κ = κ} ρ ⟧t H = buildΣ κ (⟦ ρ ⟧t H)
⟦ ρ ·⌈ τ ⌉ ⟧t H = Ix.lift₁ (⟦ ρ ⟧t H) (⟦ τ ⟧t H)
⟦ ⌈ τ ⌉· ρ ⟧t H = Ix.lift₂ (⟦ τ ⟧t H) (⟦ ρ ⟧t H)
⟦ π ⇒ τ ⟧t H = ⟦ π ⟧p H → ⟦ τ ⟧t H
⟦ ε ⟧t H = Ix.emptyRow
⟦ μ {ℓ = ℓ} F ⟧t H = Σ[ n ∈ ℕ ] (Ix.mu (⟦ F ⟧t H) n)


--------------------------------------------------------------------------------
-- Testing.

-- t : ∀ (ℓ : Level) → _
-- t ℓ = ⟦ Σ ((lab "u") R▹ `λ (★ ℓ) (tvar Z)) ⟧t 
-- ε

