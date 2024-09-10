module Rωμ.Terms.Reasoning where

open import Preludes.Level

open import Function using (id)

open import Rωμ.Kinds.Syntax
open import Rωμ.Entailment.Syntax
open import Rωμ.Types.Syntax
open import Rωμ.Equivalence.Syntax
open import Rωμ.Terms.Syntax

--------------------------------------------------------------------------------
-- Entailment derivations in the style of PLFA equational reasoning.

infixr 2 _≡⟨_⟩_

private
  variable
    ℓ ℓΔ ℓΦ ℓκ ℓΓ : Level

_≡⟨_⟩_ : ∀ 
         {Δ : KEnv} {Γ : Env Δ} {Φ : PEnv Δ}
         {τ₂ : Type Δ ★} {τ₃ : Type Δ ★}
         (τ₁ : Type Δ ★) →
         (Term Δ Φ Γ τ₁ → Term Δ Φ Γ τ₂) →
         (Term Δ Φ Γ τ₂ → Term Δ Φ Γ τ₃) →
         Term Δ Φ Γ τ₁ → Term Δ Φ Γ τ₃
_≡⟨_⟩_ _ 1→2 2→3 M = 2→3 (1→2 M)

∎ : ∀ {Δ : KEnv} {Γ : Env Δ} {Φ : PEnv Δ}
      {τ₁ : Type Δ ★} {τ₂ : Type Δ ★} {τ₃ : Type Δ ★} →
      Term Δ Φ Γ τ₁ → Term Δ Φ Γ τ₁
∎ = id

--------------------------------------------------------------------------------

