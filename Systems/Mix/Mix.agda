module Mix.Mix where

-- Modularize later.
-- open import Mix.Kinds.Syntax public
-- open import Mix.Types.Syntax public

open import Preludes.Data

--------------------------------------------------------------------------------
-- Kinds.

data Kind : Set where
  ★     : Kind
  _`→_ : Kind → Kind → Kind
  Nat   : Kind


data KEnv : Set where
  ε : KEnv
  _,_ : KEnv → Kind → KEnv

--------------------------------------------------------------------------------
-- Types.

private
  variable
    κ κ' κ₁ κ₂ : Kind
    Δ Δ₁ Δ₂ : KEnv

data TVar : KEnv → Kind → Set where
    Z : ∀ {Δ} {κ} → TVar (Δ , κ) κ
    S : ∀ {Δ} {κ κ'} → TVar Δ κ → TVar (Δ , κ') κ

data Type : KEnv → Kind → Set where
-- ----------------------------------------
-- Indices.
  Ix    :  (n : Type Δ Nat) → Type Δ ★
  Zero  : Type Δ Nat
  Suc  : Type Δ Nat
-- ----------------------------------------
-- Run o' the mill Fω.
  ⊤     : Type Δ ★
  tvar  : TVar Δ κ → Type Δ κ
  _`→_  : Type Δ ★ → Type Δ ★ → Type Δ ★
  `λ    : ∀ {Δ} (κ₁ : Kind) →
          Type (Δ , κ₁) κ₂ → Type Δ (κ₁ `→ κ₂)
  _·[_] : Type Δ (κ₁ `→ κ₂) → Type Δ κ₁ →
          Type Δ κ₂
  `∀    : ∀ {Δ} (κ : Kind) →
          Type (Δ , κ) ★ → Type Δ ★
  `∃    : ∀ {Δ} (κ : Kind) →
          Type (Δ , κ) ★ → Type Δ ★
-------------------------------------------
-- Equality.
  _∼_   : Type Δ ★ → Type Δ ★ → Type Δ ★
-- ----------------------------------------
-- recursive fragment.
  μ     : Type Δ (★ `→ ★) → Type Δ ★
  ν     : Type Δ (★ `→ ★) → Type Δ ★


postulate
  weaken : Type Δ κ → Type (Δ , κ') κ

--------------------------------------------------------------------------------
-- Translating Rome to Mix (Semantics).

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

⟦_⟧κ : Rμ.Kind → Kind
⟦ ★ ⟧κ = ★
⟦ L ⟧κ = ★
⟦ R[ κ ] ⟧κ = Nat `→ ⟦ κ ⟧κ
⟦ κ₁ `→ κ₂ ⟧κ = ⟦ κ₁ ⟧κ `→ ⟦ κ₂ ⟧κ


⟦_⟧Δ : Rμ.KEnv → KEnv
⟦ ε ⟧Δ = ε
⟦ Δ , κ ⟧Δ = ⟦ Δ ⟧Δ , ⟦ κ ⟧κ

⟦_⟧v : ∀ {Δ} {κ} → Rμ.TVar Δ κ → TVar ⟦ Δ ⟧Δ ⟦ κ ⟧κ
⟦ Z ⟧v   = Z
⟦ S n ⟧v = S ⟦ n ⟧v 

⟦_⟧τ : ∀ {Δ} {κ} → Rμ.Type Δ κ → Type ⟦ Δ ⟧Δ ⟦ κ ⟧κ
-- Row business.
⟦ Rμ.Π ρ ⟧τ = `∀ Nat (Ix (tvar Z) `→ (weaken ⟦ ρ ⟧τ ·[ tvar Z ]))
⟦ Rμ.Σ ρ ⟧τ = `∃ Nat (weaken ⟦ ρ ⟧τ ·[ tvar Z ])
⟦ ε ⟧τ = `λ Nat ((Ix Zero) `→ ⊤)
⟦ l R▹ τ ⟧τ = `λ Nat (weaken ⟦ τ ⟧τ )
⟦ τ ·⌈ υ ⌉ ⟧τ = `λ Nat (weaken ⟦ τ ⟧τ ·[ tvar Z ] ·[ weaken ⟦ υ ⟧τ ])
⟦ ⌈ τ ⌉· υ ⟧τ = `λ Nat ((weaken ⟦ τ ⟧τ) ·[ ((weaken ⟦ υ ⟧τ) ·[ (tvar Z) ]) ])
⟦ lab l ⟧τ = ⊤
⟦ l Rμ.▹ τ ⟧τ = ⟦ τ ⟧τ
⟦ Rμ.⌊_⌋ τ ⟧τ = ⊤
-- Fω
⟦ U ⟧τ = ⊤
⟦ tvar n ⟧τ = tvar ⟦ n ⟧v 
⟦ τ₁ `→ τ₂ ⟧τ = ⟦ τ₁ ⟧τ `→ ⟦ τ₂ ⟧τ
⟦ `∀ {Δ} κ τ ⟧τ = `∀ ⟦ κ ⟧κ (⟦_⟧τ {Δ , κ} τ)
⟦ `λ {Δ} κ τ ⟧τ = `λ ⟦ κ ⟧κ (⟦_⟧τ {Δ , κ} τ)
⟦ τ₁ ·[ τ₂ ] ⟧τ = ⟦ τ₁ ⟧τ ·[ ⟦ τ₂ ⟧τ ]
⟦ μ τ ⟧τ = μ ⟦ τ ⟧τ
-- μ business
⟦ ν τ ⟧τ = ν ⟦ τ ⟧τ
-- Qualified types
⟦ π ⇒ τ ⟧τ = {!!} -- <-- trickier.

