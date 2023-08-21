module R2Mu.Types.Decidability where

open import Relation.Nullary using (Dec ; yes ; no ; ¬_)
import Relation.Nullary.Decidable using (⌊_⌋; True; toWitness; fromWitness)
import Relation.Nullary.Negation using (¬?)
import Relation.Nullary.Product using (_×-dec_)
import Relation.Nullary.Sum using (_⊎-dec_)
import Relation.Binary using (Decidable)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)

open import Data.Product using (∃ ; ∃-syntax; Σ-syntax; _×_)

open import R2Mu.Kinds.Syntax
open import R2Mu.Types.Syntax
import R2Mu.Types.Pre as Pre

open import Data.Maybe
open import Data.Maybe.Categorical

open Pre.Type

-- This *should* return Dec (Type Δ τ κ), but for the moment I am only
-- interested in a procedure that builds typing derivations for me; false
-- negatives are fine, for now.
⊢ₖ? : ∀ {Δ : KEnv} → (τ : Pre.Type) → (κ : Kind) → Maybe (Type Δ τ κ)
⊢ₖ? {Δ} U ★ = just U
⊢ₖ? {Δ} U _ = nothing
⊢ₖ? {Δ} (tvar x) κ = {!!}
⊢ₖ? {Δ} (τ₁ `→ τ₂) ★ = do
  t₁ ← ⊢ₖ? {Δ} τ₁ ★
  t₂ ← ⊢ₖ? {Δ} τ₂ ★
  just (t₁ `→ t₂)
⊢ₖ? {Δ} (τ₁ `→ τ₂) _ = nothing
⊢ₖ? {Δ} (`∀ κ' τ) κ = {!!}
⊢ₖ? {Δ} (`λ κ' τ) κ = {!!}
⊢ₖ? {Δ} (τ ·[ υ ]) κ₂ = {!!}
⊢ₖ? {Δ} (μ τ) κ = {!!}
⊢ₖ? {Δ} (ν τ) κ = {!!}
⊢ₖ? {Δ} (x ⇒ τ) κ = {!!}
⊢ₖ? {Δ} (lab x) L = just (lab x) 
⊢ₖ? {Δ} (lab x) _ = nothing
⊢ₖ? {Δ} (τ₁ ▹ τ₂) κ = do
  l ← ⊢ₖ? {Δ} τ₁ L
  t ← ⊢ₖ? {Δ} τ₂ κ
  just (l ▹ t)
⊢ₖ? {Δ} (τ₁ R▹ τ₂) R[ κ ] = do
  l ← ⊢ₖ? {Δ} τ₁ L
  t ← ⊢ₖ? {Δ} τ₂ κ
  just (l R▹ t)
⊢ₖ? {Δ} (τ₁ R▹ τ₂) _      = nothing
⊢ₖ? {Δ} ⌊ τ ⌋ ★ = do
  l ← ⊢ₖ? {Δ} τ L 
  just (⌊ l ⌋) 
⊢ₖ? {Δ} ⌊ τ ⌋ _ = nothing
⊢ₖ? {Δ} ∅ ★ = just ∅
⊢ₖ? {Δ} ∅ _ = nothing
⊢ₖ? {Δ} (Π τ) ★ = do
  ρ ← ⊢ₖ? {Δ} τ R[ ★ ] 
  just (Π ρ)
⊢ₖ? {Δ} (Π τ) _ = nothing
⊢ₖ? {Δ} (Σ τ) ★ = do
  ρ ← ⊢ₖ? {Δ} τ R[ ★ ] 
  just (Σ ρ)
⊢ₖ? {Δ} (Σ τ) _ = nothing
⊢ₖ? {Δ} (τ ·⌈ τ₁ ⌉) κ = {!!}
⊢ₖ? {Δ} (⌈ τ ⌉· τ₁) κ = {!!}
