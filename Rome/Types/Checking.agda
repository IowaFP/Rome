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
import Rome.Types.Pre as Pre

open import Data.Nat using (ℕ ; zero ; suc)

open import Data.Maybe
open import Data.Maybe.Categorical
open import Data.Bool

open Pre.Type

--------------------------------------------------------------------------------
-- TVar checking.
_⊢v?_ : (Δ : KEnv) → (n : ℕ) → Maybe (∃[ κ ] (TVar Δ n κ))
_⊢v?_ ε  zero = nothing
_⊢v?_ ε (suc n) = nothing
_⊢v?_ (Δ , κ) zero = just (κ , Z)
_⊢v?_ (Δ , _) (suc n) = do
  (κ , v) ← Δ ⊢v? n
  just (κ , (S v))


--------------------------------------------------------------------------------
-- Kind checking.

-- infix ? _⊢ₖ_⦂?_
-- infix ? _⊢ₖ?_

-- Predicate formation.
_⊢p_⦂?_ : ∀ (Δ : KEnv) → (π : Pre.Pred) → (κ : Kind) → Maybe (Pred Δ π κ)

-- Kind formation.
_⊢ₖ_⦂?_ : ∀ (Δ : KEnv) → (τ : Pre.Type) → (κ : Kind) → Maybe (Type Δ τ κ)

-- a helper to make the output of kind checking amenable to the output of
-- kind synthesis.
bundle : ∀ {Δ} {τ} {κ} → Maybe (Type Δ τ κ) → Maybe (∃[ κ' ] (Type Δ τ κ'))
bundle {_} {_} {κ} mt = do
  τ ← mt 
  just (κ , τ)

-- Kind synthesis.
_⊢ₖ?_ : ∀ (Δ : KEnv) → (τ : Pre.Type) →  Maybe (∃[ κ ] (Type Δ τ κ))
Δ ⊢ₖ? U = just (★ , U)
Δ ⊢ₖ? tvar x = do
  (κ , v) ← Δ ⊢v? x
  just (κ , tvar x v)
Δ ⊢ₖ? (τ₁ `→ τ₂) = bundle (Δ ⊢ₖ (τ₁ `→ τ₂) ⦂? ★)
Δ ⊢ₖ? `∀ κ τ = bundle (Δ ⊢ₖ (`∀ κ τ) ⦂? ★)  
Δ ⊢ₖ? `λ κ τ = do
  (κ' , τ') ← (Δ , κ) ⊢ₖ? τ
  just (κ `→ κ' , `λ κ τ')
Δ ⊢ₖ? (τ₁ ·[ τ₂ ]) with Δ ⊢ₖ? τ₁
... | just (κ₁ `→ κ₂ , τ₁') = do
  τ₂' ← Δ ⊢ₖ τ₂ ⦂? κ₁
  just (κ₂ , τ₁' ·[ τ₂' ])
... | _                = nothing

Δ ⊢ₖ? μ τ = bundle (Δ ⊢ₖ (μ τ) ⦂? ★)
Δ ⊢ₖ? ν τ = bundle (Δ ⊢ₖ (ν τ) ⦂? ★)
Δ ⊢ₖ? (π ⦂ κ ⇒ τ) = bundle (Δ ⊢ₖ (π ⦂ κ ⇒ τ) ⦂? ★)
Δ ⊢ₖ? lab x = just (L , lab x)
Δ ⊢ₖ? (τ₁ ▹ τ₂) = do
  t₁ ← Δ ⊢ₖ τ₁ ⦂? L
  (κ , t₂) ← Δ ⊢ₖ? τ₂
  just (κ , t₁ ▹ t₂)
Δ ⊢ₖ? (τ₁ R▹ τ₂) = do
  t₁ ← Δ ⊢ₖ τ₁ ⦂? L
  (κ , t₂) ← Δ ⊢ₖ? τ₂
  just (R[ κ ] , t₁ R▹ t₂)
Δ ⊢ₖ? ⌊ τ ⌋ = do
  l ← Δ ⊢ₖ τ ⦂? L
  just (★ , ⌊ l ⌋)
Δ ⊢ₖ? ∅ = just (★ , ∅)
Δ ⊢ₖ? Π τ = bundle (Δ ⊢ₖ (Π τ) ⦂? ★)
Δ ⊢ₖ? Σ τ = bundle (Δ ⊢ₖ (Σ τ) ⦂? ★)
Δ ⊢ₖ? (τ₁ ·⌈ τ₂ ⌉) with Δ ⊢ₖ? τ₁
... | just (R[ κ₁ `→ κ₂ ] , τ₁') = do
  τ₂' ← Δ ⊢ₖ τ₂ ⦂? κ₁
  just (R[ κ₂ ] , τ₁' ·⌈ τ₂' ⌉)
... | _ = nothing
Δ ⊢ₖ? (⌈ τ₁ ⌉· τ₂) with Δ ⊢ₖ? τ₁
... | just (κ₁ `→ κ₂ , τ₁') = do
  τ₂' ← Δ ⊢ₖ τ₂ ⦂? R[ κ₁ ]
  just (R[ κ₂ ] , ⌈ τ₁' ⌉· τ₂')
... | _ = nothing
-- Pred formation.
_⊢p_⦂?_ Δ (τ₁ Pre.≲ τ₂) κ = do 
  t₁ ← Δ ⊢ₖ τ₁ ⦂? R[ κ ]
  t₂ ← Δ ⊢ₖ τ₂ ⦂? R[ κ ]
  just (t₁ ≲ t₂)
_⊢p_⦂?_ Δ (τ₁ Pre.· τ₂ ~ τ₃) κ = do
  t₁ ← Δ ⊢ₖ τ₁ ⦂? R[ κ ]
  t₂ ← Δ ⊢ₖ τ₂ ⦂? R[ κ ]
  t₃ ← Δ ⊢ₖ τ₃ ⦂? R[ κ ]
  just (t₁ · t₂ ~ t₃)


-- Kind formation.
_⊢ₖ_⦂?_ Δ (tvar x) κ = do
  (κ' , v) ← Δ ⊢v? x
  elim {κ'} {v} (κ ≡? κ')
  where
    elim : ∀ {κ'} {v} → Dec (κ ≡ κ') → Maybe (Type Δ (tvar x) κ)
    elim {_} {v} (yes refl) = just (tvar x v)
    elim (no _)     = nothing
_⊢ₖ_⦂?_  Δ (`∀ κ' τ) ★ = do
  t ← _⊢ₖ_⦂?_  (Δ , κ') τ ★
  just (`∀ κ' t)
_⊢ₖ_⦂?_  Δ (`λ κ' τ) (κ₁ `→ κ₂) with κ' ≡? κ₁
... | yes refl = do
  t ← _⊢ₖ_⦂?_  (Δ , κ') τ κ₂
  just (`λ κ₁ t)
... | no _ = nothing
_⊢ₖ_⦂?_  Δ (μ τ) ★ = do
  t ← _⊢ₖ_⦂?_  Δ τ (★ `→ ★)
  just (μ t)
_⊢ₖ_⦂?_  Δ (ν τ) ★ = do
  t ← _⊢ₖ_⦂?_  Δ τ (★ `→ ★)
  just (ν t)
-- Predicates.
_⊢ₖ_⦂?_  Δ (π ⦂ κ ⇒ τ) ★ = do
  p ← _⊢p_⦂?_ Δ π κ
  t ← _⊢ₖ_⦂?_  Δ τ ★
  just (p ⇒ t)
-- Applications
_⊢ₖ_⦂?_  Δ (τ ·[ υ ]) κ with Δ ⊢ₖ? τ
... | just (κ₁ `→ κ₂ , t) with κ₂ ≡? κ
...   | yes refl = do
      u ← Δ ⊢ₖ υ ⦂? κ₁
      just (t ·[ u ])
...   | _ = nothing
_⊢ₖ_⦂?_  Δ (τ ·[ υ ]) κ | _  = nothing
_⊢ₖ_⦂?_  Δ (τ ·⌈ υ ⌉) R[ κ ] with Δ ⊢ₖ? τ
... | just (R[ κ₁ `→ κ₂ ] , t) with κ₂ ≡? κ
...   | yes refl = do
      u ← Δ ⊢ₖ υ ⦂? κ₁
      just (t ·⌈ u ⌉)
...   | _ = nothing
_⊢ₖ_⦂?_  Δ (τ ·⌈ υ ⌉) R[ κ ] | _ = nothing
_⊢ₖ_⦂?_  Δ (⌈ τ ⌉· υ) R[ κ ] with Δ ⊢ₖ? τ
... | just (κ₁ `→ κ₂ , t) with κ₂ ≡? κ
...   | yes refl = do
      u ← Δ ⊢ₖ υ ⦂? R[ κ₁ ]
      just (⌈ t ⌉· u)
...   | _ = nothing
_⊢ₖ_⦂?_  Δ (⌈ t ⌉· u) R[ κ ] | _ = nothing
-- Trivial cases.
_⊢ₖ_⦂?_  Δ (lab l) L = just (lab l)
_⊢ₖ_⦂?_  Δ U ★ = just U
_⊢ₖ_⦂?_  Δ (τ₁ `→ τ₂) ★ = do
  t₁ ← _⊢ₖ_⦂?_  Δ τ₁ ★
  t₂ ← _⊢ₖ_⦂?_  Δ τ₂ ★
  just (t₁ `→ t₂)
_⊢ₖ_⦂?_  Δ (τ₁ ▹ τ₂) κ = do
  l ← _⊢ₖ_⦂?_  Δ τ₁ L
  t ← _⊢ₖ_⦂?_  Δ τ₂ κ
  just (l ▹ t)
_⊢ₖ_⦂?_  Δ (τ₁ R▹ τ₂) R[ κ ] = do
  l ← _⊢ₖ_⦂?_  Δ τ₁ L
  t ← _⊢ₖ_⦂?_  Δ τ₂ κ
  just (l R▹ t)
_⊢ₖ_⦂?_  Δ ⌊ τ ⌋ ★ = do
  l ← _⊢ₖ_⦂?_  Δ τ L 
  just (⌊ l ⌋) 
_⊢ₖ_⦂?_  Δ ∅ ★ = just ∅
_⊢ₖ_⦂?_  Δ (Π τ) ★ = do
  ρ ← _⊢ₖ_⦂?_  Δ τ R[ ★ ] 
  just (Π ρ)
_⊢ₖ_⦂?_  Δ (Σ τ) ★ = do
  ρ ← _⊢ₖ_⦂?_  Δ τ R[ ★ ] 
  just (Σ ρ)
_⊢ₖ_⦂?_  Δ _ _ = nothing

