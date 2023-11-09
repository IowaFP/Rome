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
data Term : (Δ : Context) → {τ : Pre.Term} → Type Δ τ  → Set

open Pre.Term

data Context where
  ε : Context
  _,_ : ∀ {τ} → (Δ : Context) → Type Δ τ  → Context

--------------------------------------------------------------------------------
-- Lookup 
infix 4 _∈_

data _∈_ : Pre.Term → Context → Set where

  Z : ∀ {σ} {Δ : Context} {A : Type Δ σ}
      ------------------
    → σ ∈ (Δ , A)

  S : ∀ {σ σ'} {Δ} {B : Type Δ σ'}
    → σ ∈ Δ
      ------------------
    → σ ∈ (Δ , B)

-- data ⊢Context : Context → Set where
--   ε : ⊢Context ε
--   _,_ : ∀ {τ}{Δ}{M} → 
--           ⊢Context Δ → 
--           Term Δ τ → 
--           ----------------------------
--           ⊢Context (Δ , τ)
private
  variable
    Δ : Context 

--------------------------------------------------------------------------------
-- Typing judgements.

data Type where
  ★ : Type Δ 𝓤
  --
  ⊤ : ∀ {σ} → Sort σ →  Type Δ σ
  tt : Type Δ ⊤
  --
  var : ∀ {σ} → σ ∈ Δ → Type Δ σ
  --
  Nat : Type Δ ★
  --
  Ix  : Term Δ Nat → Type Δ ★
  --
  Π : ∀ {σ σ'} → -- {_ : True (sort? σ)}
        (τ : Type Δ σ)   →   Type (Δ , τ) σ' →
        -------------------------------------------
        Type Δ σ'
  Σ : ∀ {σ σ'} → -- {_ : True (sort? σ)} 
        (τ : Type Δ σ)   →   Type (Δ , τ) σ' → 
        
        Type Δ σ'
data Term where
  var : ∀ {σ}{τ} → σ ∈ Δ → Term Δ {σ} τ
  --
  Zero : Term Δ Nat
  Suc : Term Δ Nat → Term Δ Nat
  --
  FZero : ∀ {n} → Term Δ (Ix n)
  FSuc  : ∀ {n} → Term Δ (Ix n) → Term Δ (Ix (Suc n))
  --
  `λ : ∀ {σ σ'}{τ : Type Δ σ} {υ : Type (Δ , τ) σ'} → 
         Term Δ τ   →   Term (Δ , τ) υ  → 
         ---------------------------------------------------
         Term Δ (Π τ υ)
  _·_ : ∀ {τ υ} → 
        Term Δ (Π τ υ) → Term Δ τ  → 
        Term Δ {!Need to substitute over υ[0 ↦ new term]!}
  -- --
  -- ⟪_⦂_,_⟫ : ∀ {τ υ σ σ₁ σ₂} → 
  --           (Δ ⊢ τ ⦂ σ₁)   →   (t : Δ ⊢ σ₁ ⦂ σ₂)   →   (Δ , σ₁) ⊢ υ ⦂ σ → 
  --           ----------------------------------------------------------------
  --           Δ ⊢ ⟪ τ ⦂ σ₁ , υ ⟫ ⦂ Σ σ₁ σ
  -- fst : ∀ {τ M σ} → Δ ⊢ M ⦂ Σ τ σ → Δ ⊢ (fst M) ⦂ τ
  -- snd : ∀ {τ M σ} → (s : Δ ⊢ M ⦂ Σ τ σ) → Δ ⊢ (snd M) ⦂ σ
