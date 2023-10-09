module Mix.Mix where

-- Modularize later.
-- open import Mix.Kinds.Syntax public
-- open import Mix.Types.Syntax public

open import Preludes.Data
open import Data.List

--------------------------------------------------------------------------------
-- Kinds.

data KEnv : Set
data Kind : Set

data Kind where
  ★     : Kind
  _`→_ : Kind → Kind → Kind
  Nat   : Kind
  `∀i   : Kind → Kind
  Ix    : Kind → Kind
  Zero : Kind
  Suc  : Kind → Kind
  ivar : ℕ   → Kind
 
IEnv : ℕ → Set
IEnv = Fin

data IVar : ∀ {n} → IEnv n → Set where
  Z : IVar {1} fzero
  S : ∀ {n} {m : IEnv n} → IVar m → IVar (fsuc m)

data WfKind : ∀ {n} → IEnv n → Kind → Set where
  ★      : ∀ {n} {N : IEnv n} → WfKind N ★
  _`→_  : ∀ {n} {N : IEnv n} {κ₁ κ₂} → WfKind N κ₁ → WfKind N κ₂ → WfKind N (κ₁ `→ κ₂)
  Nat    : ∀ {n} {N : IEnv n} → WfKind N Nat
  Zero   : ∀ {n} {N : IEnv n} → WfKind N Zero
  Suc    : ∀ {n} {N : IEnv n} {m} → WfKind N m → WfKind N (Suc m)
  ivar   : ∀ {n} {N : IEnv n} → IVar N → WfKind N (ivar n)
  `∀i    : ∀ {n} {N : IEnv n} {κ} → WfKind (fsuc N) κ → WfKind N (`∀i κ)

private 
  variable
    κ κ' κ₁ κ₂ : Kind
    n : ℕ
    N : IEnv n
    Κ : WfKind N κ
    Κ' : WfKind N κ'

data KEnv where
  ε : KEnv
  _,_ : KEnv → WfKind N κ → KEnv

--------------------------------------------------------------------------------
-- Types.

private
  variable
    Δ Δ₁ Δ₂ : KEnv

data Var : KEnv → WfKind N κ → Set where
    Z : ∀ {Κ : WfKind N κ} → Var (Δ , Κ) Κ
    S : Var Δ Κ → Var (Δ , Κ') Κ

data Type : KEnv → WfKind N κ → Set where
-- ----------------------------------------
-- Indices.
  Ix    :  (n : Type Δ Nat) → Type Δ ★
  Zero  : Type Δ Nat
  Suc  : Type Δ Nat
-- -- ----------------------------------------
-- -- Run o' the mill Fω.
--   ⊤     : Type Δ ★
--   tvar  : Var Δ κ → Type Δ κ
--   _`→_  : Type Δ ★ → Type Δ ★ → Type Δ ★
--   `λ    : ∀ {Δ} (κ₁ : Kind) →
--           Type (Δ , κ₁) κ₂ → Type Δ (κ₁ `→ κ₂)
--   _·[_] : Type Δ (κ₁ `→ κ₂) → Type Δ κ₁ →
--           Type Δ κ₂
--   `∀    : ∀ {Δ} (κ : Kind) →
--           Type (Δ , κ) ★ → Type Δ ★
--   `∃    : ∀ {Δ} (κ : Kind) →
--           Type (Δ , κ) ★ → Type Δ ★
-- -------------------------------------------
-- -- Equality.
--   _∼_   : Type Δ ★ → Type Δ ★ → Type Δ ★
-- -- ----------------------------------------
-- -- recursive fragment.
--   μ     : Type Δ (★ `→ ★) → Type Δ ★
--   ν     : Type Δ (★ `→ ★) → Type Δ ★


-- postulate
--   weaken : Type Δ κ → Type (Δ , κ') κ

-- -- --------------------------------------------------------------------------------
-- -- -- Translating Rome to Mix (Semantics).

-- -- module Rμ where
-- --  open import Rome.Kinds.Syntax public
-- --  open import Rome.Types.Syntax public

-- -- -- Constructors (and only constructors) may overlap in name.  Opening the Rμ
-- -- -- constructors below lets us use Rμ constructors on the LHS and Mix
-- -- -- constructors on the RHS.
-- -- open Rμ.Kind
-- -- open Rμ.KEnv
-- -- open Rμ.Type
-- -- open Rμ.TVar

-- -- ⟦_⟧κ : Rμ.Kind → Kind
-- -- ⟦ ★ ⟧κ = ★
-- -- ⟦ L ⟧κ = ★
-- -- ⟦ R[ κ ] ⟧κ = Nat `→ ⟦ κ ⟧κ
-- -- ⟦ κ₁ `→ κ₂ ⟧κ = ⟦ κ₁ ⟧κ `→ ⟦ κ₂ ⟧κ


-- -- ⟦_⟧Δ : Rμ.KEnv → KEnv
-- -- ⟦ ε ⟧Δ = ε
-- -- ⟦ Δ , κ ⟧Δ = ⟦ Δ ⟧Δ , ⟦ κ ⟧κ

-- -- ⟦_⟧v : ∀ {Δ} {κ} → Rμ.TVar Δ κ → Var ⟦ Δ ⟧Δ ⟦ κ ⟧κ
-- -- ⟦ Z ⟧v   = Z
-- -- ⟦ S n ⟧v = S ⟦ n ⟧v 

-- -- ⟦_⟧τ : ∀ {Δ} {κ} → Rμ.Type Δ κ → Type ⟦ Δ ⟧Δ ⟦ κ ⟧κ
-- -- -- Row business.
-- -- ⟦ Rμ.Π ρ ⟧τ = `∀ Nat (Ix (tvar Z) `→ (weaken ⟦ ρ ⟧τ ·[ tvar Z ]))
-- -- ⟦ Rμ.Σ ρ ⟧τ = `∃ Nat (weaken ⟦ ρ ⟧τ ·[ tvar Z ])
-- -- ⟦ ε ⟧τ = `λ Nat ((Ix Zero) `→ ⊤)
-- -- ⟦ l R▹ τ ⟧τ = `λ Nat (weaken ⟦ τ ⟧τ )
-- -- ⟦ τ ·⌈ υ ⌉ ⟧τ = `λ Nat (weaken ⟦ τ ⟧τ ·[ tvar Z ] ·[ weaken ⟦ υ ⟧τ ])
-- -- ⟦ ⌈ τ ⌉· υ ⟧τ = `λ Nat ((weaken ⟦ τ ⟧τ) ·[ ((weaken ⟦ υ ⟧τ) ·[ (tvar Z) ]) ])
-- -- ⟦ lab l ⟧τ = ⊤
-- -- ⟦ l Rμ.▹ τ ⟧τ = ⟦ τ ⟧τ
-- -- ⟦ Rμ.⌊_⌋ τ ⟧τ = ⊤
-- -- -- Fω
-- -- ⟦ U ⟧τ = ⊤
-- -- ⟦ tvar n ⟧τ = tvar ⟦ n ⟧v 
-- -- ⟦ τ₁ `→ τ₂ ⟧τ = ⟦ τ₁ ⟧τ `→ ⟦ τ₂ ⟧τ
-- -- ⟦ `∀ {Δ} κ τ ⟧τ = `∀ ⟦ κ ⟧κ (⟦_⟧τ {Δ , κ} τ)
-- -- ⟦ `λ {Δ} κ τ ⟧τ = `λ ⟦ κ ⟧κ (⟦_⟧τ {Δ , κ} τ)
-- -- ⟦ τ₁ ·[ τ₂ ] ⟧τ = ⟦ τ₁ ⟧τ ·[ ⟦ τ₂ ⟧τ ]
-- -- ⟦ μ τ ⟧τ = μ ⟦ τ ⟧τ
-- -- -- μ business
-- -- ⟦ ν τ ⟧τ = ν ⟦ τ ⟧τ
-- -- -- Qualified types
-- -- ⟦ π ⇒ τ ⟧τ = {!!} -- <-- trickier.

