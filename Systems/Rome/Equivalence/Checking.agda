{-# OPTIONS --allow-unsolved-metas #-}
module Rome.Equivalence.Checking where

open import Prelude

import Rome.Pre.Types as Pre

open import Rome.Kinds
open import Rome.Types
open import Rome.Types.Substitution
open import Rome.Equivalence.Syntax

open import Shared.Monads.Fuck

_≡?_ : ∀ {Δ : KEnv} {κ : Kind} →
          (τ υ : Type Δ κ) → Fuck? (τ ≡t υ)
U ≡? U = yiss teq-refl
tvar x ≡? υ = {!!}
(τ `→ τ₁) ≡? υ = {!!}
`∀ κ τ ≡? υ = {!!}
`λ κ₁ τ ≡? υ = {!!}
(τ ·[ τ₁ ]) ≡? υ = {!!}
μ τ ≡? υ = {!!}
ν τ ≡? υ = {!!}
(π' ⇒ τ) ≡? υ = {!!}
lab l ≡? υ = {!!}
(τ ▹ τ₁) ≡? υ = {!!}
(τ R▹ τ₁) ≡? υ = {!!}
⌊ τ ⌋ ≡? υ = {!!}
∅ ≡? υ = {!!}
Π τ ≡? υ = {!!}
Σ τ ≡? υ = {!!}
(τ ·⌈ τ₁ ⌉) ≡? υ = {!!}
τ ≡? υ = fuck

-- _≡t?_ : ∀ {Δ : KEnv} {κ : Kind} →
--           (τ υ : Type Δ κ) → Dec (τ ≡t υ)
-- U ≡t? U = yes teq-refl
-- U ≡t? tvar (Z {ε}) = no {!!}
-- U ≡t? tvar (Z {Δ , x}) = {!!}
-- U ≡t? tvar (S x) = {!!}
-- U ≡t? (υ `→ υ₁) = {!!}
-- U ≡t? `∀ κ υ = {!!}
-- U ≡t? (υ ·[ υ₁ ]) = {!!}
-- U ≡t? (π ⇒ υ) = {!!}
-- U ≡t? (υ ▹ υ₁) = {!!}
-- U ≡t? ⌊ υ ⌋ = {!!}
-- U ≡t? Π υ = {!!}
-- U ≡t? Σ υ = {!!}
-- U ≡t? ∅ = {!!}
-- U ≡t? μ τ = {!!}
-- U ≡t? ν τ = {!!}


