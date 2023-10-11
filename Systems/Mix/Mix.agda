module Mix.Mix where

-- Modularize later.
-- open import Mix.Kinds.Syntax public
-- open import Mix.Types.Syntax public

open import Preludes.Data
open import Data.List
open import Data.Nat using (_⊔_)

--------------------------------------------------------------------------------

-- Tagged nats.
--
-- The natural numbers are going to wear a lot of different masks. They serve as:
--  - `var`s, or De bruijn indices of index variables in Kinds, and
--  - `nat`, an object-language nat literal,
-- so that 
--  `Ix (nat 1)` 
-- means "an index of size 1" while
--  `ix (var 1)`
-- means an index of size i, where i is the debruijn index at position 1.   

-- N.B. Something is deeply afuck here...
data INat : ∀ {n} → Fin n → Set where
  nat : ∀ {n : ℕ} {i : Fin n} → (m : ℕ) → INat i
  var : {n : ℕ} (i : Fin n) → INat i

↑ : ∀ {n}{i : Fin n} → INat {1} fzero → INat {n} i
↑ {n} {i} (nat m) = nat m
↑ {n} {i} (var .fzero) = var i

IEnv : ℕ → Set
IEnv = Fin

data Kind : ∀ {n} → IEnv n → Set where
  ★      : ∀ {n} {Ξ : IEnv n} → Kind Ξ
  _`→_  : ∀ {n} {Ξ : IEnv n} → Kind Ξ → Kind Ξ → Kind Ξ
  Ix     : ∀ {n} {Ξ : IEnv n} → (i : INat Ξ) → Kind Ξ
  `∀ⁱ    : ∀ {n}  {Ξ : IEnv n} → Kind (fsuc Ξ) → Kind Ξ
  `∃ⁱ    : ∀ {n}  {Ξ : IEnv n} → Kind (fsuc Ξ) → Kind Ξ

private 
  variable
    n : ℕ
    Ξ : IEnv n
    κ κ' κ₁ κ₂ : Kind Ξ

data KEnv : ∀ {n} → IEnv n → Set where
  ε : ∀ {n} {Ξ} → KEnv {n} Ξ
  _,_ : KEnv Ξ → Kind Ξ → KEnv Ξ

-- --------------------------------------------------------------------------------
-- -- Types.

private
  variable
    Δ Δ₁ Δ₂ : KEnv Ξ

data Var : KEnv Ξ → Kind Ξ → Set where
    Z : Var (Δ , κ) κ
    S : Var Δ κ → Var (Δ , κ') κ

postulate
  subst-κ : Kind Ξ → Kind  (fsuc Ξ)
  rename-Ξ : KEnv Ξ → KEnv (fsuc Ξ)

data Type : ∀ {n} (Ξ : IEnv n) → KEnv Ξ → Kind Ξ → Set where
-- ----------------------------------------
-- Indices.
  Ix    : ∀  {m} {Ξ : IEnv m}{Δ : KEnv Ξ} (i : INat Ξ) → Type Ξ Δ (Ix i)
-- ----------------------------------------
-- Run o' the mill Fω.
  ⊤     : Type Ξ Δ ★
  tvar  : Var Δ κ → Type Ξ Δ κ
  _`→_  : Type Ξ Δ ★ → Type Ξ Δ ★ → Type Ξ Δ ★
  `λ    : Type Ξ (Δ , κ₁) κ₂ → Type Ξ Δ (κ₁ `→ κ₂)
  _·[_] : Type Ξ Δ (κ₁ `→ κ₂) → Type Ξ Δ κ₁ →
          Type Ξ Δ κ₂
  `∀    : ∀ {Δ} (κ : Kind Ξ) →
          Type Ξ (Δ , κ) ★ → Type Ξ Δ ★
  `∀ⁱ    : ∀ {n} {Ξ : IEnv n} {Δ : KEnv Ξ} (κ : Kind Ξ) →
          Type (fsuc Ξ) (rename-Ξ Δ) (`∀ⁱ ★) → Type Ξ Δ (`∀ⁱ ★)
  `∃    : ∀ {Δ} (κ : Kind Ξ) →
          Type Ξ (Δ , κ) ★ → Type Ξ Δ (`∃ⁱ ★)
-- -------------------------------------------
-- -- Equality.
  _∼_   : Type Ξ Δ ★ → Type Ξ Δ ★ → Type Ξ Δ ★
-- -- ----------------------------------------
-- -- recursive fragment.
  μ     : Type Ξ Δ (★ `→ ★) → Type Ξ Δ ★
  ν     : Type Ξ Δ (★ `→ ★) → Type Ξ Δ ★


postulate
  weakenΔ : Type Ξ Δ κ → Type Ξ (Δ , κ') κ
  weakenΞ : Type Ξ Δ κ → Type Ξ (Δ , κ') κ
  renameΞ  : Type Ξ Δ κ → Type (fsuc Ξ) (rename-Ξ Δ) (subst-κ κ)

-- --------------------------------------------------------------------------------
-- -- Translating Rome to Mix (Semantics).

module Rμ where
 open import Rome.Kinds.Syntax public
 open import Rome.Types.Syntax public

-- Constructors (and only constructors) may overlap in name.  Opening the Rμ
-- constructors below lets us use Rμ constructors on the LHS and Mix
-- constructors on the RHS.
open Rμ.Kind
open Rμ.KEnv
open Rμ.Type
open Rμ.TVar

-- Σⁱ-syntax : (Fin n → Set) → Set
-- Σⁱ-syntax P = Σ[ n ∈ ℕ ] (Σ[ Ξ ∈ IEnv n ] (Kind Ξ))  -- (λ (n : ℕ) → ∃  -- (Σ[ j ∈ Fin n ] (P j)) -- (∃ (λ (j : Fin n) → P j))

-- syntax Σⁱ-syntax (λ Ξ → B) = Σⁱ[ Ξ ] B

-- check : ∀ {n} {Ξ : IEnv n} → Rμ.Kind →

⟦_⟧κ : Rμ.Kind →  Kind fzero
-- Are there implicit existentials?
⟦ ★ ⟧κ = ★
⟦ L ⟧κ = ★
⟦ R[ κ ] ⟧κ = `∃ⁱ (Ix (↑ (var fzero))) `→ ⟦ κ ⟧κ 
⟦ κ₁ `→ κ₂ ⟧κ = ⟦ κ₁ ⟧κ `→ ⟦ κ₂ ⟧κ

-- level : Kind → ℕ
-- level ★ = 0
-- level (Ix x) = 0
-- level (κ₁ `→ κ₂) = level κ₁ ⊔ level κ₂
-- level (`∀ⁱ κ) = suc (level κ)
-- level (`∃ⁱ κ) = suc (level κ)

-- ⟦_⟧Δ : Rμ.KEnv → KEnv
-- ⟦ ε ⟧Δ = ε
-- ⟦ Δ , κ ⟧Δ = ⟦ Δ ⟧Δ , {!!}

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

