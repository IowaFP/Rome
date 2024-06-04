module Rome.Equivalence.Semantics where

open import Prelude
open import Preludes.Level

open import Shared.Postulates.FunExt

open import Rome.Kinds
open import Rome.Types
open import Rome.Types.Substitution
open import Rome.Types.Substitution.Properties -- extensionality
open import Rome.Equivalence.Syntax
open import Rome.GVars.Kinds

--------------------------------------------------------------------------------
-- Predicate & type equivalence.

⟦_⟧eq-π : ∀ {π₁ π₂ : Pred Δ κ} →
         π₁ ≡p π₂ → (H : ⟦ Δ ⟧ke) → (n : Potatoes) → ⟦ π₁ ⟧p H n ≡ ⟦ π₂ ⟧p H n
        
⟦_⟧eq : ∀ {τ υ : Type Δ κ} →
       τ ≡t υ → (H : ⟦ Δ ⟧ke) → (n : Potatoes) → ⟦ τ ⟧t H n ≡ ⟦ υ ⟧t H n

--------------------------------------------------------------------------------
-- Predicate equivalence.

⟦ peq-≲ eq₁ eq₂      ⟧eq-π H n rewrite ⟦ eq₁ ⟧eq H n | ⟦ eq₂ ⟧eq H n = refl
⟦ peq-·  eq₁ eq₂ eq₃ ⟧eq-π H n rewrite ⟦ eq₁ ⟧eq H n | ⟦ eq₂ ⟧eq H n | ⟦ eq₃ ⟧eq H n = refl

--------------------------------------------------------------------------------
-- type equivalence.

⟦ teq-refl ⟧eq H n = refl
⟦ teq-sym eq ⟧eq H n = sym (⟦ eq ⟧eq H n)
⟦ teq-trans eq₁ eq₂ ⟧eq H n = trans (⟦ eq₁ ⟧eq H n) (⟦ eq₂ ⟧eq H n)
⟦ teq-⇒ x t ⟧eq H n rewrite ⟦ x ⟧eq-π H n | ⟦ t ⟧eq H n = refl
⟦ teq-∀ {τ = τ} {υ} eq ⟧eq H n =
  ∀-extensionality
    extensionality
    (λ z → ⟦ τ ⟧t (H , z) n)
    (λ z → ⟦ υ ⟧t (H , z) n) (λ X →  ⟦ eq ⟧eq (H , X) n) 
⟦ teq-β {τ = τ} {υ} ⟧eq H n = Substitution τ υ H n
⟦ teq-· t t₁ ⟧eq H n rewrite ⟦ t ⟧eq H n | ⟦ t₁ ⟧eq H n  =  refl
⟦ teq-sing t t₁ ⟧eq H n rewrite ⟦ t₁ ⟧eq H n = refl
⟦ teq-lift₁ ⟧eq H n = cong (λ f → 1 , f) (extensionality {ℓ = lzero} (λ { fzero → refl ; (fsuc ()) }))
⟦ teq-lift₂ ⟧eq H n = cong (λ f → 1 , f) (extensionality {ℓ = lzero} (λ { fzero → refl ; (fsuc ()) }))
⟦ teq-lift₃ ⟧eq H n = refl
⟦ teq-⌊⌋ t ⟧eq H n = refl
⟦ teq-Π t ⟧eq H n rewrite ⟦ t ⟧eq H n = refl
⟦ teq-Σ t ⟧eq H n rewrite ⟦ t ⟧eq H n = refl
