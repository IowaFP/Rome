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

private
  variable
    Δ : Context 

--------------------------------------------------------------------------------
-- Typing judgements.

data Type where
  ★ : Type Δ 𝓤
  --
  -- (The Sort σ) predicate simply states that
  -- σ ∈ {★ , 𝓤}
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
        -------------------------------------------        
        Type Δ σ'

postulate
  -- (beta-)substitution of terms over types
  _β[_]ₜ : ∀ {τ υ}{T₁ : Type Δ τ} → Type (Δ , T₁) υ → Term Δ T₁ → Type Δ υ

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
  _·_ : ∀ {τ υ : Pre.Term}{T₁ : Type Δ τ}{T₂ : Type (Δ , T₁) υ} → 
        Term Δ (Π T₁ T₂) → (N : Term Δ T₁) → 
        Term Δ (T₂ β[ N ]ₜ)
  -- -- Use custon syntax to switch this to ⟪_⦂_,_⟫
  Sum : ∀ {τ υ}{T₂ : Type (Δ , T₁) υ} → 
            (T₁ : Type Δ τ) → (Term Δ T₁) → (v : Term (Δ , T₁) T₂) → 
            ----------------------------------------------------------------
            Term Δ (Σ T₁ v)
  -- fst : ∀ {τ M σ} → Δ ⊢ M ⦂ Σ τ σ → Δ ⊢ (fst M) ⦂ τ
  -- snd : ∀ {τ M σ} → (s : Δ ⊢ M ⦂ Σ τ σ) → Δ ⊢ (snd M) ⦂ σ
