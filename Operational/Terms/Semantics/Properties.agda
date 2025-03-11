module Rome.Operational.Terms.Semantics.Properties where

open import Rome.Operational.Prelude

open import Rome.Operational.Kinds.Syntax

import Rome.Operational.Types as Types

open import Rome.Operational.Types.Normal.Syntax
open import Rome.Operational.Types.Normal.Properties.Renaming

open import Rome.Operational.Terms.Syntax
open import Rome.Operational.Terms.Substitution
open import Rome.Operational.Terms.Semantics.Reduction

open import Rome.Operational.Kinds.GVars
open import Rome.Operational.Terms.GVars


--------------------------------------------------------------------------------
-- Lemmas.

-- Does the context Γ have any **type variables**?
NoVar : Context Δ → Set
NoVar ε = ⊤
NoVar (Γ ,, _) = NoVar Γ
NoVar (Γ , _) = ⊥

-- Contexts s.t. NoVar Γ is true indeed have no type variables.
noVar : NoVar Γ → ∀ {τ}(x : Var Γ τ) → ⊥
noVar p (T x) = noVar p x

--------------------------------------------------------------------------------
-- Proof of progress.

data Progress {τ} (M : Term Γ τ) : Set where
  Done : 
         Value M → 
         ----------
         Progress M

  Steps : 
          (M' : Term Γ τ) → (M —→ M') → 
          --------------------------------------
          Progress M

progress : NoVar Γ → ∀ {τ} (M : Term Γ τ) → Progress M
progress p (` x) with noVar p x 
... | ()

progress p (`λ M) = Done (V-λ M)
progress p (Λ M) = Done (V-Λ M)

progress p (M · N) with progress p M 
progress p (.(`λ M) · N) | Done (V-λ M) with progress p N 
progress p (.(`λ M) · N) | Done (V-λ M) | Done V' = Steps (M β[ N ]) (β-λ V')
progress p (M · N)       | Done V       | Steps N' steps = Steps (M · N') (ξ-·2 V steps)
progress p (M · N)       | Steps M' steps = Steps (M' · N) (ξ-·1 steps)
progress p (M ·[ τ ]) with progress p M
progress p (.(Λ V) ·[ τ ]) | Done (V-Λ V) = Steps _ β-Λ
progress p (M ·[ τ ])      | Steps M' steps = Steps _ (ξ-·[] steps)
progress p (roll τ M) with progress p M 
... | Done V         = Done (V-roll τ V) 
... | Steps M' steps = Steps (roll τ M') (ξ-roll steps) 
progress p (unroll τ M) with progress p M
progress p (unroll τ .(roll τ _)) | Done (V-roll F M) = Steps _ β-roll
progress p (unroll τ M)           | Steps M' steps = Steps _ (ξ-unroll steps)
progress p (# l) = Done V-#
progress p (ℓ Π▹ M) = {!   !}
progress p (_Π/_ {l} M ℓ) with progress p M | progress p ℓ
... | Done (V-Π ℓ₁ N VN)  | Done Vℓ = Steps N (β-Π/ N ℓ₁ ℓ VN)
... | Done (V-Π ℓ₁ N VN) | Steps ℓ' ℓ—→ℓ' = Steps ((ℓ₁ Π▹ N) Π/ ℓ') (ξ-Π/₂ M ℓ ℓ' (V-Π ℓ₁ N VN) ℓ—→ℓ')
... | Steps M' M—→M' | Done Vℓ = Steps (M' Π/ ℓ) (ξ-Π/₁ M M' ℓ M—→M')
... | Steps M' M—→M' | Steps ℓ' ℓ—→ℓ' = Steps (M' Π/ ℓ) (ξ-Π/₁ M M' ℓ M—→M')

progress p (ℓ Σ▹ M) = {!   !}
progress p (ℓ Σ/ M) = {!   !}

progress-ε : ∀ {τ} (M : Term ε τ) →
             Progress M
progress-ε = progress tt


-------------------------------------------------------------------------------
-- Tinkering 

_ : Progress (`λ ((# "l" Π▹ # "r") Π/ ` Z) · (# "l"))
_ = Steps (((# "l" Π▹ # "r") Π/ (# "l"))) (β-λ V-#)

_ : Progress ((# "l" Π▹ # "r") Π/ (# "l"))
_ = Steps (# "r") (β-Π/ (# "r") (# "l") (# "l") V-#)
