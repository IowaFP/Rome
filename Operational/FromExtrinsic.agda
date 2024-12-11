module Rome.Operational.FromExtrinsic where

import Rome.Extrinsic as Pre

open import Rome.Operational.Prelude

open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars
open import Rome.Operational.Types.Syntax

open import Rome.Shared.Monads.Maybe
open RawMonad {f = lzero} monad

open import Relation.Nullary
  using (Dec ; yes ; no ; ¬_)
  public

open import Data.Vec using (Vec ; _[_]=_ ; lookup)

--------------------------------------------------------------------------------
-- De-Bruijn'izing. This is a fool's errand.
--
-- (I want my damned variable names.)

depth : Pre.Type String → ℕ
depth τ = ?

Index : ℕ → Set
Index n = Vec String n

_In?_ = _∈?_ (_≟_)
index : (τ : Pre.Type String) → Index (depth τ) → Pre.Type ℕ
index I Pre.Unit = Pre.Unit
index zero (Pre.` x₁) = Pre.` zero
index (suc I) (Pre.` x₁) = Pre.` I
index zero (Pre.`λ τ) = {!!}
index (suc I) (Pre.`λ τ) = {!!}
index I (τ Pre.· τ₁) = {!!}
index I (τ Pre.`→ τ₁) = {!!}
index I (Pre.`∀ κ τ) = {!!}
index I (Pre.μ τ) = {!!}
index I (Pre.lab x₁) = {!!}
index I (τ Pre.▹ τ₁) = {!!}
index I (τ Pre.R▹ τ₁) = {!!}
index I Pre.⌊ τ ⌋ = {!!}
index I (Pre.Π τ) = {!!}
index I (Pre.Σ τ) = {!!}
index I (Pre.↑ τ) = {!!}
index I (τ Pre.↑) = {!!}


--------------------------------------------------------------------------------
-- Translating types. Todo later (Or never).

_ᵗ : Pre.Type String  → ∃[ κ ] (Type Δ κ)
_ᵗ = {! ∘ (index !}
