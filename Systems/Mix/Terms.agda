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
    -- Todo: establish a better meta-naming convention to distinguish
    -- pre-terms denoting terms, pre-terms denoting types,
    -- intrinsic types, and intrinsic terms.
    M N T : Pre.Term

data Context : Set
data Type : Context → Sort M → Set
data Term : (Γ : Context) {σ : Sort M} → Type Γ σ  → Set

open Pre.Term
open Pre.Sort

-- Context house assumptions 
data Context where
  ε : Context
  _,_ : (Γ : Context) {σ : Sort T} → Type Γ σ → Context

private
  variable
    Γ Γ' : Context

weaken : ∀ {σ₁ : Sort M} {σ₂ : Sort N} {A : Type Γ σ₁} → 
         Type Γ σ₂ → Type (Γ , A) σ₂
_β[_]t : ∀ {σ₁ : Sort M} {σ₂ : Sort N} {A : Type Γ σ₁} → 
         Type (Γ , A) σ₂ → Term Γ A → Type Γ σ₂


--------------------------------------------------------------------------------
-- Lookup 
infix 4 _∋_

-- N.b.: don't need type-level vars, but do need
-- "cascading" environments.
data _∋_ : ∀ {σ : Sort M} → (Δ : Context) → Type Δ σ → Set where

  Z : ∀ {σ : Sort M} {A : Type Γ σ} →

      -----------
      (Γ , A) ∋ (weaken A)

  S : ∀ {σ : Sort M} {σ' : Sort N} {A : Type Γ σ} {B : Type Γ σ'}
      → Γ ∋ A
      ------------------
    → (Γ , B) ∋ (weaken A)

-- -- --------------------------------------------------------------------------------
-- -- -- Typing judgements.

data Type where
  ★ : Type Γ □
--   --
  var : ∀ {σ : Sort M}
        {A : Type Γ σ}  →  Γ ∋ A →
        ---------------------------
        Type Γ σ
--   --
  ⊤ : (σ : Sort M) → Type Γ σ
--   --
  Nat : {Γ : Context} → Type Γ ★
--   --
  Ix  : Term Γ Nat → Type Γ ★
--   --
  `∀ : ∀ {σ₁ : Sort M} {σ₂ : Sort N} →
        (A : Type Γ σ₁)   →   Type (Γ , A) σ₂ → 
        -------------------------------------------        
        Type Γ σ₂
  `∃ : ∀ {σ₁ : Sort M} {σ₂ : Sort N} →
        (A : Type Γ σ₁)   →   Type (Γ , A) σ₂ → 
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

_`→_ : ∀ {σ : Sort M} {σ' : Sort N} → Type Γ σ → Type Γ σ' → Type Γ σ'
A `→ B = `∀ A (weaken B)

_`×_ : ∀ {σ : Sort M} {σ' : Sort N} → Type Γ σ → Type Γ σ' → Type Γ σ'
A `× B = `∃ A (weaken B)

-- --------------------------------------------------------------------------------
-- -- Sanity-checking

idF : Type ε □
idF = `∀ ★ (var Z)

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
  -- Variables.
  var : ∀ {σ : Sort M}
        {A : Type Γ σ}  →  Γ ∋ A →
        ---------------------------
        Term Γ A
  -- The unit.
  tt : ∀ {σ : Sort M} → Term Γ (⊤ σ)
  -- ℕ. (todo: natelim)
  Zero : Term Γ Nat
  Suc : Term Γ Nat → Term Γ Nat
  -- Ix. (todo IxElim)
  FZero : ∀ {n} → Term Γ (Ix n)
  FSuc  : ∀ {n} → Term Γ (Ix n) → Term Γ (Ix (Suc n))
  ƛ⦅⦆   : ∀ { σ : Sort M} → 
          (A : Type Γ σ) → 
          Term Γ ((Ix Zero) `→ A)
  -- `∀.
  `λ : ∀ {σ : Sort N} {σ' : Sort T} → 
         (A : Type Γ σ)   →   {B : Type (Γ , A) σ'}   →   (M : Term (Γ , A) B) →
         ------------------------------------------------------------------------
         Term Γ (`∀ A B)

  _·_ : ∀ {σ : Sort M}{σ' : Sort N} 
        {A : Type Γ σ}{B : Type (Γ , A) σ'} → 
        Term Γ (`∀ A B)   →   (N : Term Γ A) → 
        ---------------------------------------
        Term Γ (B β[ N ]t)
  -- ∃.
  ⟪_,_⟫ : ∀ {σ : Sort M}{σ' : Sort N}
            {A : Type Γ σ} → (m : Term Γ A) → {B : Type (Γ , A) σ'} → Term Γ (B β[ m ]t) →
            -------------------------------------------------------------------------------
            Term Γ (`∃ A B)
  Case_of⟪_⟫ : ∀ {σ₁ : Sort M}   {σ₂ : Sort N}   {σ₃ : Sort T}
                 {A : Type Γ σ₁} {B : Type (Γ , A) σ₂} {C : Type Γ σ₃} →
               Term Γ (`∃ A B) → Term Γ (`∀ A (B `→ (weaken C))) → 
               -----------------------------------------------------
               Term Γ C

  -- Sums. todo elim.
  left : ∀ {σ : Sort M} {A : Type Γ σ} {B : Type Γ σ} → 
         Term Γ A → 
         ---------------
         Term Γ (A Or B)
  right : ∀ {σ : Sort M} {A : Type Γ σ} {B : Type Γ σ} → 
         Term Γ B → 
         --------------
         Term Γ (A Or B)
  -- Identity. Todo elim.
  Refl : ∀ {σ : Sort M} {A : Type Γ σ} → 
         Term Γ (A ~ A)

--------------------------------------------------------------------------------
--
weaken = {!!}
τ β[ M ]t = {!!}
