module Mix.Terms where

open import Preludes.Data
open import Data.List
open import Preludes.Relation

import Mix.Pre.Terms as Pre
open Pre using (Sort ; sort?)

--------------------------------------------------------------------------------
-- Declare contexts and judgements.
-- (mutually recursive.)

data Context : Set
data Type : Context → Pre.Term → Set
data Term : (Γ : Context) → {τ : Pre.Term} → Type Γ τ  → Set

open Pre.Term

-- Context house assumptions 
data Context where
  ε : Context
  _,_ : ∀ {Δ}{σ} → (Γ : Context) → Type Δ σ → Context

private
  variable
    Γ Δ Δ' : Context

--------------------------------------------------------------------------------
-- Lookup 
infix 4 _∋_

-- N.b.: don't need type-level vars, but do need
-- "cascading" environments.
data _∋_ : ∀ {σ} → (Γ : Context) → Type Δ σ → Set where

  -- Z {★} {T = Nat : Type ε ★} → (ε , Nat : Type ε ★) ∋ (Nat : Type ε ★)
  Z : ∀ {σ} {T : Type Γ σ} →

      -----------
      (Γ , T) ∋ T

  -- S : ∀ {σ σ'} {A : Type Δ σ} {T : Type (Δ , T) σ'}
  --     → Δ ∋ A
  --     ------------------
  --   → (Γ , T) ∋ A

-- --------------------------------------------------------------------------------
-- -- Typing judgements.

data Type where
  ★ : Type Γ 𝓤
  --
  ⊤★ : Type Γ ★
  tt : Type Γ ⊤
  --
  Nat : Type Γ ★
  --
  Ix  : Term Γ Nat → Type Γ ★
  --
  Π : ∀ {σ} →
        (τ : Type Γ σ)   →   Type (Γ , τ) ★ →
        -------------------------------------------
        Type Γ σ
  Σ : ∀ {σ} →
        (τ : Type Γ σ)   →   Type (Γ , τ) ★ → 
        -------------------------------------------        
        Type Γ ★
  -- 
  up : Term Γ ★ → Type Γ ★

postulate
  WellSorted : ∀ {σ} → Type Δ σ → Sort σ
  WellSortedEnv : ∀ {σ}{Γ : Context} {T : Type Γ σ} →
                  Γ ∋ T → Sort σ

  -- (beta-)substitution of terms over types
  _β[_]ₜ : ∀ {τ υ}{T₁ : Type Γ τ} → Type (Γ , T₁) υ → Term Γ T₁ → Type Γ υ

data Term where
  var : ∀ {σ}
        {T : Type Γ σ}  →  Γ ∋ T →
        ---------------------------
        Term Γ {σ} T
  --
  Zero : Term Γ Nat
  Suc : Term Γ Nat → Term Γ Nat
  --
  FZero : ∀ {n} → Term Γ (Ix n)
  FSuc  : ∀ {n} → Term Γ (Ix n) → Term Γ (Ix (Suc n))
  --
  `λ : ∀ {σ} → 
         (T : Type Γ σ)   → {N : Type (Γ , T) ★} →  (M : Term (Γ , T) ★)  → 
         ---------------------------------------------------------------------
         Term Γ (Π T N)
  _·_ : ∀ {τ υ : Pre.Term}{T₁ : Type Γ τ}{T₂ : Type (Γ , T₁) ★} → 
        Term Γ (Π T₁ T₂) → (N : Term Γ T₁) → 
        Term Γ (T₂ β[ N ]ₜ)
  -- -- Use custon syntax to switch this to ⟪_⦂_,_⟫
  -- Sum : ∀ {τ υ}{T₂ : Type (Γ , T₁) υ} → 
  --           (T₁ : Type Γ τ) → (Term Γ T₁) → (v : Term (Γ , T₁) T₂) → 
  --           ----------------------------------------------------------------
  --           Term Γ (Σ T₁ v)
  -- fst : ∀ {τ M σ} → Γ ⊢ M ⦂ Σ τ σ → Γ ⊢ (fst M) ⦂ τ
  -- snd : ∀ {τ M σ} → (s : Γ ⊢ M ⦂ Σ τ σ) → Γ ⊢ (snd M) ⦂ σ

-- --------------------------------------------------------------------------------
-- -- Sanity checking

term-Nat : Term ε Nat
term-Nat = Zero

term-Nat₁ : Term ε Nat
term-Nat₁ = Suc Zero

wut : (ε , Nat) ∋ Nat
wut = Z

term-var₁ : Term (_,_ {Δ = ε} ε Nat ) (Nat {ε , Nat})
term-var₁ = var {ε , Nat {ε}} {★} {Nat {ε , Nat}} {!!}
