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

Rowed : Kind → Set
Rowed ★ = ⊥
Rowed L = ⊥
Rowed (κ₁ `→ κ₂) = Rowed κ₂
Rowed R[ κ ] = ⊤

rowed? : ∀ κ → Dec (Rowed κ)
rowed? ★ = no (λ ())
rowed? L = no (λ ())
rowed? (κ `→ κ₁) = rowed? κ₁
rowed? R[ κ ] = yes tt

Flat : Kind → Set
Flat ★ = ⊤
Flat L = ⊤
Flat (κ₁ `→ κ₂) = Flat κ₂
Flat R[ κ ] = ⊥

flat? : ∀ κ → Dec (Flat κ)
flat? ★ = yes tt
flat? L = yes tt
flat? (κ₁ `→ κ₂) = flat? κ₂
flat? R[ κ ] = no (λ ())

Rowed→¬Flat : ∀ κ → Rowed κ → ¬ Flat κ
Rowed→¬Flat (_ `→ κ) r = Rowed→¬Flat κ r
Rowed→¬Flat R[ κ ] r = λ ()

¬Flat→Rowed : ∀ κ → ¬ Flat κ → Rowed κ
¬Flat→Rowed ★ nf = nf tt
¬Flat→Rowed L nf = nf tt
¬Flat→Rowed (κ `→ κ₁) nf = ¬Flat→Rowed κ₁ nf
¬Flat→Rowed R[ κ ] nf = tt


Flat→¬Rowed : ∀ κ → Flat κ → ¬ Rowed κ
Flat→¬Rowed ★ f = λ ()
Flat→¬Rowed L f = λ ()
Flat→¬Rowed (_ `→ κ) f = Flat→¬Rowed κ f

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
