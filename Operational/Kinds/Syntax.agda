{-# OPTIONS --safe #-}
module Rome.Operational.Kinds.Syntax where

open import Rome.Operational.Prelude

--------------------------------------------------------------------------------
-- 2.1 Kinds

data Kind : Set where
  ★     : Kind
  L     : Kind
  _`→_ : Kind → Kind → Kind
  R[_]  : Kind → Kind

infixr 5 _`→_

--------------------------------------------------------------------------------
-- Partitioning of kinds by rows and row-valued functions.

NotLabel : Kind → Set 
NotLabel ★ = ⊤
NotLabel L = ⊥
NotLabel (κ₁ `→ κ₂) = NotLabel κ₂
NotLabel R[ κ ] = NotLabel κ

notLabel? : ∀ κ → Dec (NotLabel κ)
notLabel? ★ = yes tt
notLabel? L = no λ ()
notLabel? (κ `→ κ₁) = notLabel? κ₁
notLabel? R[ κ ] = notLabel? κ


--------------------------------------------------------------------------------
-- Partitioning of kinds by rows and row-valued functions.

Ground : Kind → Set 
Ground ★ = ⊤
Ground L = ⊤
Ground (κ `→ κ₁) = ⊥
Ground R[ κ ] = ⊥

ground? : ∀ κ → Dec (Ground κ)
ground? ★ = yes tt
ground? L = yes tt
ground? (_ `→ _) = no (λ ())
ground? R[ _ ] = no (λ ())

-- Arrow : Kind → Set 
-- Arrow ★ = ⊥
-- Arrow L = ⊥
-- Arrow (κ `→ κ₁) = ⊤
-- Arrow R[ κ ] = ⊥

-- arrow? : ∀ κ → Dec (Arrow κ)
-- arrow? ★ = no (λ ())
-- arrow? L = no (λ ())
-- arrow? (_ `→ _) = yes tt
-- arrow? R[ _ ] = no (λ ())

-- ¬Arrow→Ground : ∀ {κ} → (¬ Arrow κ) → Ground κ
-- ¬Arrow→Ground {★} a = tt
-- ¬Arrow→Ground {L} a = tt
-- ¬Arrow→Ground {κ `→ κ₁} a = ⊥-elim (a tt)
-- ¬Arrow→Ground {R[ κ ]} a = tt

--------------------------------------------------------------------------------
-- 2.2 contexts

data KEnv : Set where
  ∅ : KEnv
  _,,_ : KEnv → Kind → KEnv

--------------------------------------------------------------------------------
-- 2.3 Type variables

private
  variable
    Δ Δ₁ Δ₂ Δ₃ : KEnv
    κ κ₁ κ₂ : Kind

data KVar : KEnv → Kind → Set where
  Z : KVar (Δ ,, κ) κ
  S : KVar Δ κ₁ → KVar (Δ ,, κ₂) κ₁
