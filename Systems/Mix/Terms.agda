module Mix.Terms where

open import Preludes.Data
open import Data.List
open import Preludes.Relation

import Mix.Pre.Terms as Pre
open Pre using (Sort ; sort?)

--------------------------------------------------------------------------------
-- Declare contexts and judgements.
-- (mutually recursive.)

private
  variable
    M N T : Pre.Term

data Context : Set
data Type : {M : Pre.Term} → Context → Sort M → Set
data Term : (Γ : Context) {σ : Sort T} → Type Γ σ  → Set

open Pre.Term
open Pre.Sort

-- Context house assumptions 
data Context where
  ε : Context
  _,_ : (Γ : Context) {σ : Sort T} → Type Γ σ → Context

private
  variable
    Γ Δ Δ' : Context

-- --------------------------------------------------------------------------------
-- -- Lookup 
-- infix 4 _∋_

-- -- N.b.: don't need type-level vars, but do need
-- -- "cascading" environments.
-- data _∈_ : ∀ {σ} → Type Δ σ → Context → Set where

--   -- Z {★} {T = Nat : Type ε ★} → (ε , Nat : Type ε ★) ∋ (Nat : Type ε ★)
--   Z : ∀ {σ} {T : Type Γ σ} →

--       -----------
--       T ∈ (Γ , T)

--   -- S : ∀ {σ σ'} {A : Type Δ σ} {T : Type (Δ , T) σ'}
--   --     → Δ ∋ A
--   --     ------------------
--   --   → (Γ , T) ∋ A

-- -- --------------------------------------------------------------------------------
-- -- -- Typing judgements.

data Type where
  ★ : (Γ : Context) → Type Γ □
--   --
--   var : ∀ {σ}
--         {T : Type Γ σ}  →  T ∈ Γ →
--         ---------------------------
--         Type Γ σ
--   --
  ⊤ : (σ : Sort M) → Type Γ σ
--   --
  Nat : {Γ : Context} → Type Γ ★
--   --
  Ix  : Term Γ Nat → Type Γ ★
--   --
  `∀ : ∀ {σ₁ : Sort M} {σ₂ : Sort N} →
        (τ : Type Γ σ₁)   →   Type (Γ , τ) σ₂ → 
        -------------------------------------------        
        Type Γ σ₂
  `∃ : ∀ {σ₁ : Sort M} {σ₂ : Sort N} →
        (τ : Type Γ σ₁)   →   Type (Γ , τ) σ₂ → 
        -------------------------------------------        
        Type Γ σ₂

  _Or_ : ∀ {σ : Sort M} →
        Type Γ σ   →   Type Γ σ → 
        ---------------------------
        Type Γ σ

  _~_  : ∀ {σ : Sort M} →
        Type Γ σ → Type Γ σ → 
        -----------------------
        Type Γ σ

-- --------------------------------------------------------------------------------
-- -- Sanity-checking

-- nat : Type ε 𝓤
-- nat = Π (★ {!!}) (var {{!!}}{{!!}} {★ {!!}} {!Z!})

-- --------------------------------------------------------------------------------
-- -- Terms.

-- -- postulate
-- --   weakenType : ∀ {σ} {T : Type Γ σ} → Type Γ σ → Type (Γ , T) σ
-- --   WellSorted : ∀ {σ} → Type ε σ → Sort σ
-- --   WellSortedEnv : ∀ {σ}{Γ : Context} {T : Type Γ σ} →
-- --                   Γ ∋ T → Sort σ

-- --   -- (beta-)substitution of terms over types
-- --   _β[_]ₜ : ∀ {τ υ}{T₁ : Type Γ τ} → Type (Γ , T₁) υ → Term Γ T₁ → Type Γ υ

data Term where
-- --   var : ∀ {σ}
-- --         {T : Type Γ σ}  →  Γ ∋ T →
-- --         ---------------------------
-- --         Term Γ {σ} T
-- --   --
-- --   tt : Term Γ ⊤★
-- --   --
-- --   Zero : Term Γ (Nat Γ)
-- --   Suc : Term Γ (Nat Γ) → Term Γ (Nat Γ)
-- --   --
-- --   FZero : ∀ {n} → Term Γ (Ix n)
-- --   FSuc  : ∀ {n} → Term Γ (Ix n) → Term Γ (Ix (Suc n))
-- --   --
-- --   `λ : ∀ {σ} → 
-- --          (T : Type Γ σ)   → {N : Type (Γ , T) ★} →  (M : Term (Γ , T) ★)  → 
-- --          ---------------------------------------------------------------------
-- --          Term Γ (Π T N)
-- --   _·_ : ∀ {τ υ : Pre.Term}{T₁ : Type Γ τ}{T₂ : Type (Γ , T₁) ★} → 
-- --         Term Γ (Π T₁ T₂) → (N : Term Γ T₁) → 
-- --         Term Γ (T₂ β[ N ]ₜ)
-- --   -- -- Use custon syntax to switch this to ⟪_⦂_,_⟫
-- --   -- Sum : ∀ {τ υ}{T₂ : Type (Γ , T₁) υ} → 
-- --   --           (T₁ : Type Γ τ) → (Term Γ T₁) → (v : Term (Γ , T₁) T₂) → 
-- --   --           ----------------------------------------------------------------
-- --   --           Term Γ (Σ T₁ v)
-- --   -- fst : ∀ {τ M σ} → Γ ⊢ M ⦂ Σ τ σ → Γ ⊢ (fst M) ⦂ τ
-- --   -- snd : ∀ {τ M σ} → (s : Γ ⊢ M ⦂ Σ τ σ) → Γ ⊢ (snd M) ⦂ σ

-- -- -- postulate
-- -- --   weakenTerm : ∀ {σ σ'} {T₁ : Type Γ σ} {T₂ : Type Γ σ'} → Term Γ T₂ → Term (Γ , T₁) (weakenType T₂)
-- -- -- --------------------------------------------------------------------------------
-- -- -- -- Sanity checking

-- -- term-Nat : Term ε (Nat ε)
-- -- term-Nat = Zero

-- -- term-Nat₁ : Term ε (Nat ε)
-- -- term-Nat₁ = Suc Zero

-- -- -- wut : (ε , Nat ε) ∋ Nat ε
-- -- -- wut = Z

-- -- wut : Term (ε , Nat ε) (Nat (ε , Nat ε))
-- -- wut = {!!}

-- -- term-var₁ : Term (ε , Nat ε) (Nat (ε , Nat ε))
-- -- term-var₁ = var {!Z!}
