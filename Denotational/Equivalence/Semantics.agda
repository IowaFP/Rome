open import Prelude
open import Preludes.Level

module Rome.Denotational.Equivalence.Semantics (g : Potatoes) where

open import Shared.Postulates.FunExt

open import Rome.Denotational.Kinds
open import Rome.Denotational.Types.Syntax
open import Rome.Denotational.Types.Substitution
open import Rome.Denotational.Types.Semantics g
open import Rome.Denotational.Types.Substitution.Properties g -- extensionality
open import Rome.Denotational.Equivalence.Syntax
open import Rome.Denotational.GVars.Kinds

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
-- Multirow equivalence.

⟦_⟧eq-ρ : ∀ {ρ₁ ρ₂ : Row Δ κ} →
          ρ₁ ≡r ρ₂ → (H : ⟦ Δ ⟧ke) → ⟦ ⦃- ρ₁ -⦄ ⟧t H ≡ ⟦ ⦃- ρ₂ -⦄ ⟧t H
⟦ req-sing _ _ ⟧eq-ρ H = refl
⟦ req-▹ eq-l eq-τ eq-ρ ⟧eq-ρ H rewrite eq-l | ⟦ eq-τ ⟧eq H | ⟦ eq-ρ ⟧eq-ρ H = refl

--------------------------------------------------------------------------------
-- type equivalence.

⟦ teq-refl ⟧eq H = refl
⟦ teq-sym eq ⟧eq H = sym (⟦ eq ⟧eq H)
⟦ teq-trans eq₁ eq₂ ⟧eq H = trans (⟦ eq₁ ⟧eq H) (⟦ eq₂ ⟧eq H)
⟦ teq-⇒ x t ⟧eq H rewrite ⟦ x ⟧eq-π H | ⟦ t ⟧eq H = refl
⟦ teq-→ x t ⟧eq H rewrite ⟦ x ⟧eq H | ⟦ t ⟧eq H = refl
⟦ teq-∀ {τ = τ} {υ} eq ⟧eq H =
  ∀-extensionality
    extensionality
    (λ z → Maybe (⟦ τ ⟧t (H , z)))
    (λ z → Maybe (⟦ υ ⟧t (H , z))) 
    (λ X →  cong Maybe (⟦ eq ⟧eq (H , X)))
⟦ teq-β {τ = τ} {υ} ⟧eq H = Substitution τ υ H
⟦ teq-· t t₁ ⟧eq H rewrite ⟦ t ⟧eq H | ⟦ t₁ ⟧eq H  =  refl
⟦ teq-sing t t₁ ⟧eq H rewrite ⟦ t₁ ⟧eq H = refl
⟦ teq-lift₁ ⟧eq H = cong (λ f → 1 , f) (extensionality {ℓ = lzero} (λ { fzero → refl ; (fsuc ()) }))
⟦ teq-lift₂ ⟧eq H = cong (λ f → 1 , f) (extensionality {ℓ = lzero} (λ { fzero → refl ; (fsuc ()) }))
⟦ teq-lift-Σ ⟧eq H = refl
⟦ teq-lift-Π ⟧eq H = refl
⟦ teq-⌊⌋ t ⟧eq H = refl
⟦ teq-Π t ⟧eq H rewrite ⟦ t ⟧eq H = refl
⟦ teq-Σ t ⟧eq H rewrite ⟦ t ⟧eq H = refl
⟦ teq-id-↑ ⟧eq H = refl 
⟦ teq-labTy-row ⟧eq H = refl
⟦ teq-row eq-ρ ⟧eq H = ⟦ eq-ρ ⟧eq-ρ H
