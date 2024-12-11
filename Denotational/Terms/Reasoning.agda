module Rome.Denotational.Terms.Reasoning where

open import Rome.Preludes.Level

open import Function using (id)

open import Rome.Denotational.Kinds.Syntax
open import Rome.Denotational.Entailment.Syntax
open import Rome.Denotational.Types.Syntax
open import Rome.Denotational.Equivalence.Syntax
open import Rome.Denotational.Terms.Syntax

--------------------------------------------------------------------------------
-- Entailment derivations in the style of PLFA equational reasoning.

infixr 2 _≡⟨_⟩_

private
  variable
    ℓ ℓΔ ℓΦ ℓκ ℓΓ : Level

_≡⟨_⟩_ : ∀ 
         {Δ : KEnv ℓΔ} {Γ : Env Δ ℓΓ} {Φ : PEnv Δ ℓΦ}
         {τ₂ : Type Δ (★ ℓ)} {τ₃ : Type Δ (★ ℓ)}
         (τ₁ : Type Δ (★ ℓ)) →
         (Term Δ Φ Γ τ₁ → Term Δ Φ Γ τ₂) →
         (Term Δ Φ Γ τ₂ → Term Δ Φ Γ τ₃) →
         Term Δ Φ Γ τ₁ → Term Δ Φ Γ τ₃
_≡⟨_⟩_ _ 1→2 2→3 M = 2→3 (1→2 M)

∎ : ∀ {Δ : KEnv ℓΔ} {Γ : Env Δ ℓΓ} {Φ : PEnv Δ ℓΦ}
      {τ₁ : Type Δ (★ ℓ)} {τ₂ : Type Δ (★ ℓ)} {τ₃ : Type Δ (★ ℓ)} →
      Term Δ Φ Γ τ₁ → Term Δ Φ Γ τ₁
∎ = id

--------------------------------------------------------------------------------

