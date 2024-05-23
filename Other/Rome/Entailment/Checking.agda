{-# OPTIONS --allow-unsolved-metas #-}
module Rome.Entailment.Checking where

open import Prelude

import Rome.Pre.Types as Pre

open import Rome.Kinds
open import Rome.Types
open import Rome.Types.Substitution
open import Rome.Entailment.Syntax

open import Shared.Monads.Fuck

--------------------------------------------------------------------------------
-- Entailment.

[_∣_]⊩?_ : ∀ {κ} (Δ : KEnv) (Φ : PEnv Δ) →
          (π : Pred Δ κ) → Fuck? (Ent Δ Φ π)
[ Δ ∣ Φ ]⊩? π = {!!}
