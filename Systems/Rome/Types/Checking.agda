module Rome.Types.Checking where

open import Relation.Nullary using (Dec ; yes ; no ; ¬_)
open import Relation.Nullary.Decidable using (isYes; True; toWitness; fromWitness; From-yes)
import Relation.Nullary.Product using (_×-dec_)
import Relation.Nullary.Sum using (_⊎-dec_)
import Relation.Binary using (Decidable)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)

open import Data.Product using (∃ ; ∃-syntax; Σ-syntax; _×_; _,_)

open import Rome.Kinds.Syntax
open import Rome.Kinds.Equality
open import Rome.Types.Syntax
import Rome.Pre.Types as Pre

open import Shared.Lib.Monads.Fuck

open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Bool
open Pre.Type


-- --------------------------------------------------------------------------------
-- Some helper business.

to-∃ : ∀ {Δ} {τ} {κ} → Type Δ τ κ → ∃[ κ' ] (Type Δ τ κ')
to-∃ {_} {_} {κ} τ = ( κ , τ)

--------------------------------------------------------------------------------
-- TVar checking (is n ∈ ℕ in KEnv Δ?) 
_⊢v?_ : (Δ : KEnv) → (n : ℕ) → Fuck? (∃[ κ ] (TVar Δ n κ))
_⊢v?_ ε  zero = rip pfft
_⊢v?_ ε (suc n) = rip pfft
_⊢v?_ (Δ , κ) zero = yiss (κ , Z)
_⊢v?_ (Δ , _) (suc n) = do
  (κ , v) ← Δ ⊢v? n
  yiss (κ , (S v))

--------------------------------------------------------------------------------
-- Checking well-formedness of predicates & kinds, and kind synthesis (mutually
-- recursive).

-- -- Predicate formation.
_⊢p_⦂?_ : ∀ (Δ : KEnv) → (π : Pre.Pred) → (κ : Kind) → Fuck? (Pred Δ π κ)
-- Kind checking.
_⊢ₖ_⦂?_ : ∀ (Δ : KEnv) → (τ : Pre.Type) → (κ : Kind) → Fuck? (Type Δ τ κ)
-- Kind synthesis.
_⊢ₖ?_ : ∀ (Δ : KEnv) → (τ : Pre.Type) →  Fuck? (∃[ κ ] (Type Δ τ κ))

Δ ⊢ₖ? U = yiss (★ , U)
Δ ⊢ₖ? tvar x = do
  (κ , v) ← Δ ⊢v? x
  yiss (κ , tvar x v)
Δ ⊢ₖ? (τ₁ `→ τ₂) =  to-∃ <$> (Δ ⊢ₖ (τ₁ `→ τ₂) ⦂? ★)
Δ ⊢ₖ? `∀ κ τ = to-∃ <$> (Δ ⊢ₖ (`∀ κ τ) ⦂? ★)  
Δ ⊢ₖ? `λ κ τ = do
  (κ' , τ') ← (Δ , κ) ⊢ₖ? τ
  yiss (κ `→ κ' , `λ κ τ')
Δ ⊢ₖ? (τ₁ ·[ τ₂ ]) with Δ ⊢ₖ? τ₁
... | yiss (κ₁ `→ κ₂ , τ₁') = do
  τ₂' ← Δ ⊢ₖ τ₂ ⦂? κ₁
  yiss (κ₂ , τ₁' ·[ τ₂' ])
... | _                = rip pfft

Δ ⊢ₖ? μ τ = to-∃ <$> (Δ ⊢ₖ (μ τ) ⦂? ★)
Δ ⊢ₖ? ν τ = to-∃ <$> (Δ ⊢ₖ (ν τ) ⦂? ★)
Δ ⊢ₖ? (π ⦂ κ ⇒ τ) = to-∃ <$> (Δ ⊢ₖ (π ⦂ κ ⇒ τ) ⦂? ★)
Δ ⊢ₖ? lab x = yiss (L , lab x)
Δ ⊢ₖ? (τ₁ ▹ τ₂) = do
  t₁ ← Δ ⊢ₖ τ₁ ⦂? L
  (κ , t₂) ← Δ ⊢ₖ? τ₂
  yiss (κ , t₁ ▹ t₂)
Δ ⊢ₖ? (τ₁ R▹ τ₂) = do
  t₁ ← Δ ⊢ₖ τ₁ ⦂? L
  (κ , t₂) ← Δ ⊢ₖ? τ₂
  yiss (R[ κ ] , t₁ R▹ t₂)
Δ ⊢ₖ? ⌊ τ ⌋ = do
  l ← Δ ⊢ₖ τ ⦂? L
  yiss (★ , ⌊ l ⌋)
Δ ⊢ₖ? ∅ = yiss (★ , ∅)
Δ ⊢ₖ? Π τ = to-∃ <$> (Δ ⊢ₖ (Π τ) ⦂? ★)
Δ ⊢ₖ? Σ τ = to-∃ <$> (Δ ⊢ₖ (Σ τ) ⦂? ★)
Δ ⊢ₖ? (τ₁ ·⌈ τ₂ ⌉) with Δ ⊢ₖ? τ₁
... | yiss (R[ κ₁ `→ κ₂ ] , τ₁') = do
  τ₂' ← Δ ⊢ₖ τ₂ ⦂? κ₁
  yiss (R[ κ₂ ] , τ₁' ·⌈ τ₂' ⌉)
... | _ = rip pfft
Δ ⊢ₖ? (⌈ τ₁ ⌉· τ₂) with Δ ⊢ₖ? τ₁
... | yiss (κ₁ `→ κ₂ , τ₁') = do
  τ₂' ← Δ ⊢ₖ τ₂ ⦂? R[ κ₁ ]
  yiss (R[ κ₂ ] , ⌈ τ₁' ⌉· τ₂')
... | _ = rip pfft
-- Pred formation.
_⊢p_⦂?_ Δ (τ₁ Pre.≲ τ₂) κ = do 
  t₁ ← Δ ⊢ₖ τ₁ ⦂? R[ κ ]
  t₂ ← Δ ⊢ₖ τ₂ ⦂? R[ κ ]
  yiss (t₁ ≲ t₂)
_⊢p_⦂?_ Δ (τ₁ Pre.· τ₂ ~ τ₃) κ = do
  t₁ ← Δ ⊢ₖ τ₁ ⦂? R[ κ ]
  t₂ ← Δ ⊢ₖ τ₂ ⦂? R[ κ ]
  t₃ ← Δ ⊢ₖ τ₃ ⦂? R[ κ ]
  yiss (t₁ · t₂ ~ t₃)


-- Kind checking.
_⊢ₖ_⦂?_ Δ (tvar x) κ = do
  (κ' , v) ← Δ ⊢v? x
  elim {κ'} {v} (κ ≡? κ')
  where
    elim : ∀ {κ'} {v} → Dec (κ ≡ κ') → Fuck? (Type Δ (tvar x) κ)
    elim {_} {v} (yes refl) = yiss (tvar x v)
    elim (no _)     = rip pfft
_⊢ₖ_⦂?_  Δ (`∀ κ' τ) ★ = do
  t ← _⊢ₖ_⦂?_  (Δ , κ') τ ★
  yiss (`∀ κ' t)
_⊢ₖ_⦂?_  Δ (`λ κ' τ) (κ₁ `→ κ₂) with κ' ≡? κ₁
... | yes refl = do
  t ← _⊢ₖ_⦂?_  (Δ , κ') τ κ₂
  yiss (`λ κ₁ t)
... | no _ = rip pfft
_⊢ₖ_⦂?_  Δ (μ τ) ★ = do
  t ← _⊢ₖ_⦂?_  Δ τ (★ `→ ★)
  yiss (μ t)
_⊢ₖ_⦂?_  Δ (ν τ) ★ = do
  t ← _⊢ₖ_⦂?_  Δ τ (★ `→ ★)
  yiss (ν t)
-- Predicates.
_⊢ₖ_⦂?_  Δ (π ⦂ κ ⇒ τ) ★ = do
  p ← _⊢p_⦂?_ Δ π κ
  t ← _⊢ₖ_⦂?_  Δ τ ★
  yiss (p ⇒ t)
-- Applications
_⊢ₖ_⦂?_  Δ (τ ·[ υ ]) κ with Δ ⊢ₖ? τ
... | yiss (κ₁ `→ κ₂ , t) with κ₂ ≡? κ
...   | yes refl = do
      u ← Δ ⊢ₖ υ ⦂? κ₁
      yiss (t ·[ u ])
...   | _ = rip pfft
_⊢ₖ_⦂?_  Δ (τ ·[ υ ]) κ | _  = rip pfft
_⊢ₖ_⦂?_  Δ (τ ·⌈ υ ⌉) R[ κ ] with Δ ⊢ₖ? τ
... | yiss (R[ κ₁ `→ κ₂ ] , t) with κ₂ ≡? κ
...   | yes refl = do
      u ← Δ ⊢ₖ υ ⦂? κ₁
      yiss (t ·⌈ u ⌉)
...   | _ = rip pfft
_⊢ₖ_⦂?_  Δ (τ ·⌈ υ ⌉) R[ κ ] | _ = rip pfft
_⊢ₖ_⦂?_  Δ (⌈ τ ⌉· υ) R[ κ ] with Δ ⊢ₖ? τ
... | yiss (κ₁ `→ κ₂ , t) with κ₂ ≡? κ
...   | yes refl = do
      u ← Δ ⊢ₖ υ ⦂? R[ κ₁ ]
      yiss (⌈ t ⌉· u)
...   | _ = rip pfft
_⊢ₖ_⦂?_  Δ (⌈ t ⌉· u) R[ κ ] | _ = rip pfft
-- Trivial cases.
_⊢ₖ_⦂?_  Δ (lab l) L = yiss (lab l)
_⊢ₖ_⦂?_  Δ U ★ = yiss U
_⊢ₖ_⦂?_  Δ (τ₁ `→ τ₂) ★ = do
  t₁ ← _⊢ₖ_⦂?_  Δ τ₁ ★
  t₂ ← _⊢ₖ_⦂?_  Δ τ₂ ★
  yiss (t₁ `→ t₂)
_⊢ₖ_⦂?_  Δ (τ₁ ▹ τ₂) κ = do
  l ← _⊢ₖ_⦂?_  Δ τ₁ L
  t ← _⊢ₖ_⦂?_  Δ τ₂ κ
  yiss (l ▹ t)
_⊢ₖ_⦂?_  Δ (τ₁ R▹ τ₂) R[ κ ] = do
  l ← _⊢ₖ_⦂?_  Δ τ₁ L
  t ← _⊢ₖ_⦂?_  Δ τ₂ κ
  yiss (l R▹ t)
_⊢ₖ_⦂?_  Δ ⌊ τ ⌋ ★ = do
  l ← _⊢ₖ_⦂?_  Δ τ L 
  yiss (⌊ l ⌋) 
_⊢ₖ_⦂?_  Δ ∅ ★ = yiss ∅
_⊢ₖ_⦂?_  Δ (Π τ) ★ = do
  ρ ← _⊢ₖ_⦂?_  Δ τ R[ ★ ] 
  yiss (Π ρ)
_⊢ₖ_⦂?_  Δ (Σ τ) ★ = do
  ρ ← _⊢ₖ_⦂?_  Δ τ R[ ★ ] 
  yiss (Σ ρ)
_⊢ₖ_⦂?_  Δ _ _ = rip pfft

