module Rome.Operational.Terms.Semantics.Progress where

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
progress p (.(`λ M) · N) | Done (V-λ M)   = Steps (M β[ N ]) β-λ
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
progress p (ℓ Π▹ M) with progress p M 
... | Done VM = Done (V-Π ℓ M VM)
... | Steps M' M—→M' = Steps (ℓ Π▹ M') (ξ-Π▹ M M' ℓ M—→M')
progress p (_Π/_ {l} M ℓ) with progress p M
... | Done (V-Π ℓ₁ N VN)  = Steps N (β-Π/ N ℓ₁ ℓ VN)
... | Steps M' M—→M' = Steps (M' Π/ ℓ) (ξ-Π/₁ M M' ℓ M—→M')
progress p (ℓ Σ▹ M) with progress p M 
... | Done VM = Done (V-Σ ℓ M VM)
... | Steps M' M—→M' = Steps (ℓ Σ▹ M') (ξ-Σ▹ M M' ℓ M—→M')
progress p (_Σ/_ {l} M ℓ) with progress p M
... | Done (V-Σ ℓ₁ N VN)  = Steps N (β-Σ/ N ℓ₁ ℓ VN)
... | Steps M' M—→M' = Steps (M' Σ/ ℓ) (ξ-Σ/₁ M M' ℓ M—→M')

progress-ε : ∀ {τ} (M : Term ε τ) →
             Progress M
progress-ε = progress tt

-------------------------------------------------------------------------------
-- Tinkering

{-# TERMINATING #-}
eval : ∀ {τ} → Term ε τ → Term ε τ 
eval M with progress tt M 
... | Done x = M
... | Steps M' x = eval M'

_ : eval ((# "l" Π▹ # "r") Π/ (# "l")) ≡ (# "r")
_ = refl