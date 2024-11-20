module SFFP.Terms.Semantics.Reduction where

open import SFFP.Prelude

open import SFFP.Kinds.Syntax

import SFFP.Types as Types
import SFFP.Types.Normal as NTypes
open import SFFP.Types.Normal.Syntax
open import SFFP.Types.Normal.Properties

open import SFFP.Terms.Normal

open import SFFP.Kinds.GVars
open import SFFP.Terms.Normal.GVars


--------------------------------------------------------------------------------
-- Values

data Value {Δ} {Γ : Context Δ} : ∀ {τ : NormalType Δ ★} → NormalTerm Γ τ → Set where
  V-λ : ∀ {τ₁ τ₂} 
          (M : NormalTerm (Γ , τ₂) τ₁) → Value (`λ M)
  V-Λ : ∀ {τ} 
          (M : NormalTerm (Γ ,, κ) τ) → Value (Λ M)
  V-roll : ∀ {τ} {M : NormalTerm Γ (τ NTypes.β[ μ τ ])} → 
             Value M → Value (roll τ M)


--------------------------------------------------------------------------------
-- Small step semantics.

infixr 0 _—→_
data _—→_ : ∀ {τ} → NormalTerm Γ τ → NormalTerm Γ τ → Set where
  
  ξ-·1 : ∀ {τ₁ τ₂} {M₁ M₂ : NormalTerm Γ (τ₁ `→ τ₂)} {N : NormalTerm Γ τ₁} →
           M₁ —→ M₂ →
           -----------------
           M₁ · N —→ M₂ · N

  ξ-·2 : ∀ {τ₁ τ₂} {V : NormalTerm Γ (τ₁ `→ τ₂)} {N₁ N₂ : NormalTerm Γ τ₁} →
           Value V → N₁ —→ N₂ →
           -----------------------
           V · N₁ —→ V · N₂

  ξ-Λ : ∀ {τ} {M₁ M₂ : NormalTerm (Γ ,, κ) τ} →
         M₁ —→ M₂ →
         -----------------------
         (Λ M₁) —→ (Λ M₂)

  ξ-·[] : ∀ {τ} {τ'} {M₁ M₂ : NormalTerm Γ (`∀ κ τ)} →
            M₁ —→ M₂ →
            ------------------------
            M₁ ·[ τ' ] —→ M₂ ·[ τ' ]

  ξ-unroll : ∀ {τ} {M₁ M₂ : NormalTerm Γ (μ τ)} →
               M₁ —→ M₂ →
               -----------------------
               unroll τ M₁ —→ unroll τ M₂

  ξ-roll : ∀ {τ} {M₁ M₂ : NormalTerm Γ (τ NTypes.β[ (μ τ) ])} →
             M₁ —→ M₂ →
             -----------------------
             roll τ M₁ —→ roll τ M₂

  -- N.b. Call by value.
  β-λ : ∀ {τ₁ τ₂} {M : NormalTerm (Γ , τ₁) τ₂} {N : NormalTerm Γ τ₁} →
          Value N →
          -----------------------
          (`λ M) · N —→ M β[ N ]

  β-Λ : ∀ {τ₁ : NormalType Δ κ} {τ₂} {M : NormalTerm (Γ ,, κ) τ₂}  →

          --------------------------
          Λ M ·[ τ₁ ] —→ M β·[ τ₁ ]

  β-roll : ∀ {τ} {M : NormalTerm Γ (τ NTypes.β[ (μ τ) ])} →

             -------------------------
             unroll τ (roll τ M) —→ M

