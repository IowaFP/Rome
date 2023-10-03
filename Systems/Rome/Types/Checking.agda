module Rome.Types.Checking where

open import Preludes.Relation
open import Preludes.Data

open import Rome.Kinds.Syntax
open import Rome.Kinds.Equality
open import Rome.Types.Syntax
import Rome.Pre.Types as Pre

open import Shared.Monads.Fuck
open Pre.Type


-- --------------------------------------------------------------------------------
-- Some helper business.

to-∃ : ∀ {Δ} {κ} → Type Δ κ → ∃[ κ' ] (Type Δ κ')
to-∃ {_} {κ} τ = ( κ , τ)

--------------------------------------------------------------------------------
-- TVar checking (is n ∈ ℕ in KEnv Δ?) 
_∈[_] : (n : ℕ) → (Δ : KEnv) → Fuck? (∃[ κ ] (TVar Δ κ))
zero ∈[ ε ] = fuck
(suc n) ∈[ ε ] = fuck
zero ∈[ (Δ , κ) ] = yiss (κ , Z)
(suc n) ∈[ (Δ , _) ] = do
  (κ , v) ← n ∈[ Δ ]
  yiss (κ , (S v))

--------------------------------------------------------------------------------
-- Checking well-formedness of predicates & kinds, and kind synthesis (mutually
-- recursive).

-- -- Predicate formation.
_⊢p_⦂?_ : ∀ (Δ : KEnv) → (π : Pre.Pred) → (κ : Kind) → Fuck? (Pred Δ κ)
-- Kind checking.
_⊢_⦂?_ : ∀ (Δ : KEnv) → (τ : Pre.Type) → (κ : Kind) → Fuck? (Type Δ κ)
-- Kind synthesis.
_⊢?_ : ∀ (Δ : KEnv) → (τ : Pre.Type) →  Fuck? (∃[ κ ] (Type Δ κ))

Δ ⊢? U = yiss (★ , U)
Δ ⊢? tvar x = do
  (κ , v) ← x ∈[ Δ ]
  yiss (κ , tvar v)
Δ ⊢? (τ₁ `→ τ₂) =  to-∃ <$> (Δ ⊢ (τ₁ `→ τ₂) ⦂? ★)
Δ ⊢? `∀ κ τ = to-∃ <$> (Δ ⊢ (`∀ κ τ) ⦂? ★)  
Δ ⊢? `λ κ τ = do
  (κ' , τ') ← (Δ , κ) ⊢? τ
  yiss (κ `→ κ' , `λ κ τ')
Δ ⊢? (τ₁ ·[ τ₂ ]) with Δ ⊢? τ₁
... | yiss (κ₁ `→ κ₂ , τ₁') = do
  τ₂' ← Δ ⊢ τ₂ ⦂? κ₁
  yiss (κ₂ , τ₁' ·[ τ₂' ])
... | _                = fuck

Δ ⊢? μ τ = to-∃ <$> (Δ ⊢ (μ τ) ⦂? ★)
Δ ⊢? ν τ = to-∃ <$> (Δ ⊢ (ν τ) ⦂? ★)
Δ ⊢? (π ⦂ κ ⇒ τ) = to-∃ <$> (Δ ⊢ (π ⦂ κ ⇒ τ) ⦂? ★)
Δ ⊢? lab x = yiss (L , lab x)
Δ ⊢? (τ₁ ▹ τ₂) = do
  t₁ ← Δ ⊢ τ₁ ⦂? L
  (κ , t₂) ← Δ ⊢? τ₂
  yiss (κ , t₁ ▹ t₂)
Δ ⊢? (τ₁ R▹ τ₂) = do
  t₁ ← Δ ⊢ τ₁ ⦂? L
  (κ , t₂) ← Δ ⊢? τ₂
  yiss (R[ κ ] , t₁ R▹ t₂)
Δ ⊢? ⌊ τ ⌋ = do
  l ← Δ ⊢ τ ⦂? L
  yiss (★ , ⌊ l ⌋)
Δ ⊢? ∅ = yiss (★ , ∅)
Δ ⊢? Π τ = to-∃ <$> (Δ ⊢ (Π τ) ⦂? ★)
Δ ⊢? Σ τ = to-∃ <$> (Δ ⊢ (Σ τ) ⦂? ★)
Δ ⊢? (τ₁ ·⌈ τ₂ ⌉) with Δ ⊢? τ₁
... | yiss (R[ κ₁ `→ κ₂ ] , τ₁') = do
  τ₂' ← Δ ⊢ τ₂ ⦂? κ₁
  yiss (R[ κ₂ ] , τ₁' ·⌈ τ₂' ⌉)
... | _ = fuck
Δ ⊢? (⌈ τ₁ ⌉· τ₂) with Δ ⊢? τ₁
... | yiss (κ₁ `→ κ₂ , τ₁') = do
  τ₂' ← Δ ⊢ τ₂ ⦂? R[ κ₁ ]
  yiss (R[ κ₂ ] , ⌈ τ₁' ⌉· τ₂')
... | _ = fuck
-- Pred formation.
_⊢p_⦂?_ Δ (τ₁ Pre.≲ τ₂) κ = do 
  t₁ ← Δ ⊢ τ₁ ⦂? R[ κ ]
  t₂ ← Δ ⊢ τ₂ ⦂? R[ κ ]
  yiss (t₁ ≲ t₂)
_⊢p_⦂?_ Δ (τ₁ Pre.· τ₂ ~ τ₃) κ = do
  t₁ ← Δ ⊢ τ₁ ⦂? R[ κ ]
  t₂ ← Δ ⊢ τ₂ ⦂? R[ κ ]
  t₃ ← Δ ⊢ τ₃ ⦂? R[ κ ]
  yiss (t₁ · t₂ ~ t₃)


-- Kind checking.
_⊢_⦂?_ Δ (tvar x) κ = do
  (κ' , v) ← x ∈[ Δ ]
  elim {κ'} {v} (κ ≡? κ')
  where
    elim : ∀ {κ'} {v} → Dec (κ ≡ κ') → Fuck? (Type Δ κ)
    elim {_} {v} (yes refl) = yiss (tvar v)
    elim (no _)     = fuck
_⊢_⦂?_  Δ (`∀ κ' τ) ★ = do
  t ← _⊢_⦂?_  (Δ , κ') τ ★
  yiss (`∀ κ' t)
_⊢_⦂?_  Δ (`λ κ' τ) (κ₁ `→ κ₂) with κ' ≡? κ₁
... | yes refl = do
  t ← _⊢_⦂?_  (Δ , κ') τ κ₂
  yiss (`λ κ₁ t)
... | no _ = fuck
_⊢_⦂?_  Δ (μ τ) ★ = do
  t ← _⊢_⦂?_  Δ τ (★ `→ ★)
  yiss (μ t)
_⊢_⦂?_  Δ (ν τ) ★ = do
  t ← _⊢_⦂?_  Δ τ (★ `→ ★)
  yiss (ν t)
-- Predicates.
_⊢_⦂?_  Δ (π ⦂ κ ⇒ τ) ★ = do
  p ← _⊢p_⦂?_ Δ π κ
  t ← _⊢_⦂?_  Δ τ ★
  yiss (p ⇒ t)
-- Applications
_⊢_⦂?_  Δ (τ ·[ υ ]) κ with Δ ⊢? τ
... | yiss (κ₁ `→ κ₂ , t) with κ₂ ≡? κ
...   | yes refl = do
      u ← Δ ⊢ υ ⦂? κ₁
      yiss (t ·[ u ])
...   | _ = fuck
_⊢_⦂?_  Δ (τ ·[ υ ]) κ | _  = fuck
_⊢_⦂?_  Δ (τ ·⌈ υ ⌉) R[ κ ] with Δ ⊢? τ
... | yiss (R[ κ₁ `→ κ₂ ] , t) with κ₂ ≡? κ
...   | yes refl = do
      u ← Δ ⊢ υ ⦂? κ₁
      yiss (t ·⌈ u ⌉)
...   | _ = fuck
_⊢_⦂?_  Δ (τ ·⌈ υ ⌉) R[ κ ] | _ = fuck
_⊢_⦂?_  Δ (⌈ τ ⌉· υ) R[ κ ] with Δ ⊢? τ
... | yiss (κ₁ `→ κ₂ , t) with κ₂ ≡? κ
...   | yes refl = do
      u ← Δ ⊢ υ ⦂? R[ κ₁ ]
      yiss (⌈ t ⌉· u)
...   | _ = fuck
_⊢_⦂?_  Δ (⌈ t ⌉· u) R[ κ ] | _ = fuck
-- Trivial cases.
_⊢_⦂?_  Δ (lab l) L = yiss (lab l)
_⊢_⦂?_  Δ U ★ = yiss U
_⊢_⦂?_  Δ (τ₁ `→ τ₂) ★ = do
  t₁ ← _⊢_⦂?_  Δ τ₁ ★
  t₂ ← _⊢_⦂?_  Δ τ₂ ★
  yiss (t₁ `→ t₂)
_⊢_⦂?_  Δ (τ₁ ▹ τ₂) κ = do
  l ← _⊢_⦂?_  Δ τ₁ L
  t ← _⊢_⦂?_  Δ τ₂ κ
  yiss (l ▹ t)
_⊢_⦂?_  Δ (τ₁ R▹ τ₂) R[ κ ] = do
  l ← _⊢_⦂?_  Δ τ₁ L
  t ← _⊢_⦂?_  Δ τ₂ κ
  yiss (l R▹ t)
_⊢_⦂?_  Δ ⌊ τ ⌋ ★ = do
  l ← _⊢_⦂?_  Δ τ L 
  yiss (⌊ l ⌋) 
_⊢_⦂?_  Δ ∅ ★ = yiss ∅
_⊢_⦂?_  Δ (Π τ) ★ = do
  ρ ← _⊢_⦂?_  Δ τ R[ ★ ] 
  yiss (Π ρ)
_⊢_⦂?_  Δ (Σ τ) ★ = do
  ρ ← _⊢_⦂?_  Δ τ R[ ★ ] 
  yiss (Σ ρ)
_⊢_⦂?_  Δ _ _ = fuck

