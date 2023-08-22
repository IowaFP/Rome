module Rome.Equivalence.Decidability where

--------------------------------------------------------------------------------
-- Agda stuffs.
open import Agda.Primitive

--------------------------------------------------------------------------------
-- Relation stuffs. (prune unused.)

open import Relation.Nullary using (Dec ; yes ; no ; ¬_)
import Relation.Nullary.Decidable using (⌊_⌋; True; toWitness; fromWitness)
import Relation.Nullary.Negation using (¬?)
import Relation.Nullary.Product using (_×-dec_)
import Relation.Nullary.Sum using (_⊎-dec_)
import Relation.Binary using (Decidable)

--------------------------------------------------------------------------------
-- Rω stuffs. (TODO prune unused.)

open import Rome.Kinds
open import Rome.Entailment
open import Rome.Entailment.Reasoning
open import Rome.Equivalence
open import Rome.Types
open import Rome.Types.Substitution
open import Rome.Types.Substitution.Properties
open import Rome.Terms

--------------------------------------------------------------------------------
--

open import Relation.Binary.PropositionalEquality


_≡t?_ : ∀ {Δ : KEnv} {κ : Kind} →
          (τ υ : Type Δ κ) → Dec (τ ≡t υ)
U ≡t? U = yes teq-refl
U ≡t? tvar (Z {ε}) = no {!!}
U ≡t? tvar (Z {Δ , x}) = {!!}
U ≡t? tvar (S x) = {!!}
U ≡t? (υ `→ υ₁) = {!!}
U ≡t? `∀ κ υ = {!!}
U ≡t? (υ ·[ υ₁ ]) = {!!}
U ≡t? (π ⇒ υ) = {!!}
U ≡t? (υ ▹ υ₁) = {!!}
U ≡t? ⌊ υ ⌋ = {!!}
U ≡t? Π υ = {!!}
U ≡t? Σ υ = {!!}
U ≡t? ∅ = {!!}
U ≡t? μ τ = {!!}
U ≡t? ν τ = {!!}

tvar x ≡t? υ = {!!}
(τ `→ τ₁) ≡t? υ = {!!}
`∀ κ τ ≡t? υ = {!!}
`λ κ₁ τ ≡t? υ = {!!}
(τ ·[ τ₁ ]) ≡t? υ = {!!}
(π ⇒ τ) ≡t? υ = {!!}
lab x ≡t? υ = {!!}
(τ ▹ τ₁) ≡t? υ = {!!}
(τ R▹ τ₁) ≡t? υ = {!!}
⌊ τ ⌋ ≡t? υ = {!!}
∅ ≡t? υ = {!!}
Π τ ≡t? υ = {!!}
Σ τ ≡t? υ = {!!}
(τ ·⌈ τ₁ ⌉) ≡t? υ = {!!}
(⌈ τ ⌉· τ₁) ≡t? υ = {!!}
μ τ ≡t? υ = {!!}
ν τ ≡t? υ = {!!}
