module Rome.Both.Types.Denotation where

open import Rome.Both.Prelude
open import Rome.Both.Kinds.Syntax
open import Rome.Both.Kinds.GVars
open import Rome.Both.Kinds.Denotation

open import Rome.Both.Types.Syntax

--------------------------------------------------------------------------------
-- Denotation

⟦_⟧tv : TVar Δ κ → ⟦ Δ ⟧ke → ⟦ κ ⟧k
⟦ Z ⟧tv (_ , t) = t
⟦ S v ⟧tv (H , _) = ⟦ v ⟧tv H

⟦_⟧t : Type Δ κ → ⟦ Δ ⟧ke → ⟦ κ ⟧k 
⟦ ` α ⟧t η = ⟦ α ⟧tv η
⟦ `λ {κ₁ = κ₁} τ ⟧t η = λ (x : ⟦ κ₁ ⟧k ) → ⟦ τ ⟧t (η , x)
⟦ τ₁ · τ₂ ⟧t η =  (⟦ τ₁ ⟧t η) (⟦ τ₂ ⟧t η)  
⟦ τ₁ `→ τ₂ ⟧t η = ⟦ τ₁ ⟧t η  → ⟦ τ₂ ⟧t η
⟦ `∀ {κ = κ} τ ⟧t η = (α : ⟦ κ ⟧k) → ⟦ τ ⟧t (η , α)
-- ⟦ μ τ ⟧t η = {!   !}
⟦ π ⇒ τ ⟧t η = {!   !}
⟦ ⦅ xs ⦆ ordered ⟧t η = {!   !}
⟦ lab l ⟧t η = # l
⟦ ⌊ τ ⌋ ⟧t η =  ⊤'   
⟦ ξ ▹ τ ⟧t η with ⟦ ξ ⟧t η 
... | # ℓ = sing (ℓ , ⟦ τ ⟧t η)
⟦ φ <$> ρ ⟧t η = {!   !}
⟦ Π ⟧t η = {!   !}
⟦ Σ ⟧t η = {!   !}
⟦ τ₂ ─ τ₁ ⟧t η = {!   !} 


-- wts that 
--  - ⟦ τ ⟧t ≡ ⟦ ⇓ τ ⟧NF (would need functional extensionality)
--  - if Δ ⊢ τ ≡t υ : κ then ⟦ τ ⟧t ≡ ⟦ υ ⟧t 
-- I'm not sure if I want to let define ⟦_⟧t as the first line. Then 
-- the second line follows from completeness. Is this a cop out?
-- A counter---I only define term reduction on normal types. So 
-- my goal is:
--   soundness : ∀ {τ : NormalType ∅ ★} {M N : NormalTerm ∅ τ} → 
--               M —→ N → ⟦ M ⟧ ≡ ⟦ N ⟧
-- Where ⟦_⟧, the meaning of terms, is typed by
--              ⟦_⟧ : NormalTerm Γ τ → ⟦ Γ ⟧ →  ⟦ τ ⟧. 
-- so in this case we do not need a meaning of `Type`, just of `NormalType`.
-- Pros of independnent definitions of ⟦_⟧ : Type and ⟦_⟧ : NormalType:
--   - Shows that ⟦_⟧ on `Type`s obeys definitional equality
--   - cooler?
-- Pros of defining as ⟦ τ ⟧t ≡ ⟦ ⇓ τ ⟧NF:
--   - metatheory for free
--   - No need to relate two differing implementations
--   - Don't actually need the meaning of non-normal types
--   - I said I would deliver the soundness claim above, 
--     who is going to quibble? Just get the Ph.D.
