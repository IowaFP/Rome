module Operational.Rome.Terms.Semantics.Properties where

open import Operational.Rome.Prelude

open import Operational.Rome.Kinds.Syntax

import Operational.Rome.Types as Types
import Operational.Rome.Types.Normal as NTypes
open import Operational.Rome.Types.Normal.Syntax
open import Operational.Rome.Types.Normal.Properties

open import Operational.Rome.Terms.Normal

open import Operational.Rome.Terms.Semantics.Reduction

open import Operational.Rome.Kinds.GVars
open import Operational.Rome.Terms.Normal.GVars


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

data Progress {τ} (M : NormalTerm Γ τ) : Set where
  Done : 
         Value M → 
         ----------
         Progress M

  Steps : 
          (M' : NormalTerm Γ τ) → (M —→ M') → 
          --------------------------------------
          Progress M

progress : NoVar Γ → ∀ {τ} (M : NormalTerm Γ τ) → Progress M
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
... | Done V         = Done (V-roll V)
... | Steps M' steps = Steps (roll τ M') (ξ-roll steps)
progress p (unroll τ M) with progress p M
progress p (unroll τ .(roll τ _)) | Done (V-roll M) = Steps _ β-roll
progress p (unroll τ M)           | Steps M' steps = Steps _ (ξ-unroll steps)

progress-ε : ∀ {τ} (M : NormalTerm ε τ) →
             Progress M
progress-ε = progress tt
