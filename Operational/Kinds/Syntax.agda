module Rome.Operational.Kinds.Syntax where

open import Rome.Operational.Prelude

--------------------------------------------------------------------------------
-- 2.1 Kinds

data Kind : Set where
  ★     : Kind
  L     : Kind
  _`→_ : Kind → Kind → Kind
  R[_]  : Kind → Kind


--------------------------------------------------------------------------------
-- Partitioning of kinds by rows and row-valued functions.

Rowed : Kind → Set
Rowed ★ = ⊥
Rowed L = ⊥
Rowed (κ₁ `→ κ₂) = Rowed κ₂
Rowed R[ κ ] = ⊤

Flat : Kind → Set
Flat ★ = ⊤
Flat L = ⊤
Flat (κ₁ `→ κ₂) = Flat κ₂
Flat R[ κ ] = ⊥

Rowed-not-Flat : ∀ κ → Rowed κ → ¬ Flat κ
Rowed-not-Flat (_ `→ κ) r = Rowed-not-Flat κ r
Rowed-not-Flat R[ κ ] r = λ ()

Flat-not-Rowed : ∀ κ → Flat κ → ¬ Rowed κ
Flat-not-Rowed ★ f = λ ()
Flat-not-Rowed L f = λ ()
Flat-not-Rowed (_ `→ κ) f = Flat-not-Rowed κ f


--------------------------------------------------------------------------------
-- 2.2 contexts

data KEnv : Set where
  ε : KEnv
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
