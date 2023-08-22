module Rome.Types.Checking where

open import Relation.Nullary using (Dec ; yes ; no ; ¬_)
import Relation.Nullary.Decidable using (⌊_⌋; True; toWitness; fromWitness)
import Relation.Nullary.Product using (_×-dec_)
import Relation.Nullary.Sum using (_⊎-dec_)
import Relation.Binary using (Decidable)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)

open import Data.Product using (∃ ; ∃-syntax; Σ-syntax; _×_)

open import Rome.Kinds.Syntax
open import Rome.Kinds.Equality
open import Rome.Types.Syntax
import Rome.Types.Pre as Pre

open import Data.Nat using (ℕ ; zero ; suc)

open import Data.Maybe
open import Data.Maybe.Categorical

open Pre.Type

--------------------------------------------------------------------------------
-- TVar checking.
⊢v? : (Δ : KEnv) → (n : ℕ) → (κ : Kind) → Maybe (TVar Δ κ n)
⊢v? ε zero κ = nothing
⊢v? ε (suc n) κ = nothing
⊢v? (Δ , have) zero want with want ≡? have
... | yes refl = just Z
... | no  p    = nothing 
⊢v? (Δ , _) (suc n) κ = do
  v ← ⊢v? Δ n κ
  just (S n v)


--------------------------------------------------------------------------------
-- Predicate & type formation.

⊢ₖp? : ∀ (Δ : KEnv) → (π : Pre.Pred) → (κ : Kind) → Maybe (Pred Δ π κ)
⊢ₖ? : ∀ (Δ : KEnv) → (τ : Pre.Type) → (κ : Kind) → Maybe (Type Δ τ κ)

⊢ₖp? Δ (τ₁ Pre.≲ τ₂) κ = do 
  t₁ ← ⊢ₖ? Δ τ₁ R[ κ ]
  t₂ ← ⊢ₖ? Δ τ₂ R[ κ ]
  just (t₁ ≲ t₂)
⊢ₖp? Δ (τ₁ Pre.· τ₂ ~ τ₃) κ = do
  t₁ ← ⊢ₖ? Δ τ₁ R[ κ ]
  t₂ ← ⊢ₖ? Δ τ₂ R[ κ ]
  t₃ ← ⊢ₖ? Δ τ₃ R[ κ ]
  just (t₁ · t₂ ~ t₃)


-- This *should* return Dec (Type Δ τ κ), but for the moment I am only
-- interested in a procedure that builds typing derivations for me; false
-- negatives are fine, for now.
-- Variables.
⊢ₖ? ε (tvar x) κ = nothing
⊢ₖ? (Δ , κ') (tvar zero) κ with κ' ≡? κ
... | yes refl = just (tvar zero Z)
... | no  p = nothing
⊢ₖ? (Δ , κ') (tvar (suc n)) κ = do
  v' ← ⊢v? Δ n κ
  just (tvar (suc n) (S n v'))
-- Bindings.
⊢ₖ? Δ (`∀ κ' τ) ★ = do
  t ← ⊢ₖ? (Δ , κ') τ ★
  just (`∀ κ' t)
⊢ₖ? Δ (`λ κ' τ) (κ₁ `→ κ₂) with κ' ≡? κ₁
... | yes refl = do
  t ← ⊢ₖ? (Δ , κ') τ κ₂
  just (`λ κ₁ t)
... | no _ = nothing
⊢ₖ? Δ (μ τ) ★ = do
  t ← ⊢ₖ? Δ τ (★ `→ ★)
  just (μ t)
⊢ₖ? Δ (ν τ) ★ = do
  t ← ⊢ₖ? Δ τ (★ `→ ★)
  just (ν t)
-- Predicates.
⊢ₖ? Δ (π ⦂ κ ⇒ τ) ★ = do
  p ← ⊢ₖp? Δ π κ
  t ← ⊢ₖ? Δ τ ★
  just (p ⇒ t)
-- Applications
⊢ₖ? Δ (τ ⦂ (κ₁ `→ κ₂) ·[ υ ]) κ with κ₂ ≡? κ
... | yes refl = do
  t ← ⊢ₖ? Δ τ (κ₁ `→ κ₂)
  u ← ⊢ₖ? Δ υ κ₁
  just (t ·[ u ])
... | no q = nothing
⊢ₖ? Δ (τ ⦂ (κ₁ `→ κ₂) ·⌈ υ ⌉) R[ κ ] with κ₂ ≡? κ
... | yes refl = do
  t ← ⊢ₖ? Δ τ R[ (κ₁ `→ κ₂) ]
  u ← ⊢ₖ? Δ υ κ₁
  just (t ·⌈ u ⌉)
... | no _ = nothing
⊢ₖ? Δ (⌈ τ ⦂ (κ₁ `→ κ₂) ⌉· υ) R[ κ ] with κ₂ ≡? κ
... | yes refl = do
  t ← ⊢ₖ? Δ τ (κ₁ `→ κ₂)
  u ← ⊢ₖ? Δ υ R[ κ₁ ]
  just ( ⌈ t ⌉· u)
... | no _ = nothing
-- Trivial cases.
⊢ₖ? Δ (lab l) L = just (lab l)
⊢ₖ? Δ U ★ = just U
⊢ₖ? Δ (τ₁ `→ τ₂) ★ = do
  t₁ ← ⊢ₖ? Δ τ₁ ★
  t₂ ← ⊢ₖ? Δ τ₂ ★
  just (t₁ `→ t₂)
⊢ₖ? Δ (τ₁ ▹ τ₂) κ = do
  l ← ⊢ₖ? Δ τ₁ L
  t ← ⊢ₖ? Δ τ₂ κ
  just (l ▹ t)
⊢ₖ? Δ (τ₁ R▹ τ₂) R[ κ ] = do
  l ← ⊢ₖ? Δ τ₁ L
  t ← ⊢ₖ? Δ τ₂ κ
  just (l R▹ t)
⊢ₖ? Δ ⌊ τ ⌋ ★ = do
  l ← ⊢ₖ? Δ τ L 
  just (⌊ l ⌋) 
⊢ₖ? Δ ∅ ★ = just ∅
⊢ₖ? Δ (Π τ) ★ = do
  ρ ← ⊢ₖ? Δ τ R[ ★ ] 
  just (Π ρ)
⊢ₖ? Δ (Σ τ) ★ = do
  ρ ← ⊢ₖ? Δ τ R[ ★ ] 
  just (Σ ρ)
⊢ₖ? Δ _ _ = nothing

