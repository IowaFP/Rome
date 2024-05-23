module ROmega.Equivalence.Semantics where

open import Prelude
open import Preludes.Level

open import Shared.Postulates.FunExt

open import ROmega.Kinds
open import ROmega.Types
open import ROmega.Types.Substitution
open import ROmega.Types.Substitution.Properties -- extensionality
open import ROmega.Equivalence.Syntax
open import ROmega.GVars.Kinds

--------------------------------------------------------------------------------
-- Predicate & type equivalence.

⟦_⟧eq-π : ∀ {π₁ π₂ : Pred Δ κ} →
         π₁ ≡p π₂ → (H : ⟦ Δ ⟧ke) → ⟦ π₁ ⟧p H ≡ ⟦ π₂ ⟧p H
        
⟦_⟧eq : ∀ {τ υ : Type Δ κ} →
       τ ≡t υ → (H : ⟦ Δ ⟧ke) → ⟦ τ ⟧t H ≡ ⟦ υ ⟧t H

--------------------------------------------------------------------------------
-- Predicate equivalence.

⟦ peq-≲ eq₁ eq₂      ⟧eq-π H  rewrite ⟦ eq₁ ⟧eq H | ⟦ eq₂ ⟧eq H = refl
⟦ peq-·  eq₁ eq₂ eq₃ ⟧eq-π H rewrite ⟦ eq₁ ⟧eq H | ⟦ eq₂ ⟧eq H | ⟦ eq₃ ⟧eq H = refl

--------------------------------------------------------------------------------
-- type equivalence.

⟦ teq-refl ⟧eq H = refl
⟦ teq-sym eq ⟧eq H = sym (⟦ eq ⟧eq H)
⟦ teq-trans eq₁ eq₂ ⟧eq H = trans (⟦ eq₁ ⟧eq H) (⟦ eq₂ ⟧eq H)
⟦ teq-⇒ x t ⟧eq H rewrite ⟦ x ⟧eq-π H | ⟦ t ⟧eq H = refl
⟦ teq-∀ {τ = τ} {υ} eq ⟧eq H =
  ∀-extensionality
    extensionality
    (λ z → ⟦ τ ⟧t (H , z))
    (λ z → ⟦ υ ⟧t (H , z)) (λ X →  ⟦ eq ⟧eq (H , X)) 
⟦ teq-β {τ = τ} {υ} ⟧eq H = Substitution τ υ H
⟦ teq-· t t₁ ⟧eq H rewrite ⟦ t ⟧eq H | ⟦ t₁ ⟧eq H  =  refl
⟦ teq-sing t t₁ ⟧eq H rewrite ⟦ t₁ ⟧eq H = refl
⟦ teq-lift₁ ⟧eq H = cong (λ f → 1 , f) (extensionality {ℓ = lzero} (λ { fzero → refl ; (fsuc ()) }))
⟦ teq-lift₂ ⟧eq H = cong (λ f → 1 , f) (extensionality {ℓ = lzero} (λ { fzero → refl ; (fsuc ()) }))
⟦ teq-⌊⌋ t ⟧eq H = refl
⟦ teq-Π t ⟧eq H rewrite ⟦ t ⟧eq H = refl
⟦ teq-Σ t ⟧eq H rewrite ⟦ t ⟧eq H = refl
