module Mix.Terms where

open import Preludes.Data
open import Data.List
open import Preludes.Relation

open import Mix.Pre.Terms

--------------------------------------------------------------------------------
-- Declare contexts and judgements.
-- (mutually recursive.)
data Context : Set
data _⊢_⦂_ : Context → Term → Term → Set

data Context where
  ε : Context
  _,_ : ∀ {M}{τ} → (Δ : Context) → Δ ⊢ M ⦂ τ → Context

private
  variable
    Δ : Context 

--------------------------------------------------------------------------------
-- Typing judgements.

data _⊢_⦂_ where
  ★ : Δ ⊢ ★ ⦂ 𝓤
  --
  ⊤ : ∀ {σ} → Sort σ →  Δ ⊢ ⊤ ⦂ σ
  tt : Δ ⊢ tt ⦂ ⊤
  --
  varZ : ∀ {τ σ} {⊢τ : Δ ⊢ τ ⦂ σ}  → (Δ , ⊢τ) ⊢ varZ ⦂ τ
  varS : ∀ {τ σ υ n} {⊢υ : Δ ⊢ υ ⦂ σ} →
            Δ ⊢ n ⦂ τ
         → (Δ , ⊢υ) ⊢ varS n ⦂ τ
  --
  Nat : Δ ⊢ Nat ⦂ ★
  Zero : Δ ⊢ Zero ⦂ Nat
  Suc : ∀ {n} → Δ ⊢ n ⦂ Nat → Δ ⊢ Suc n ⦂ Nat
  --
  Ix  : ∀ {n} → Δ ⊢ n ⦂ Nat → Δ ⊢ Ix n ⦂ ★
  --
  FZero : ∀ {n} → Δ ⊢ Ix n ⦂ ★ → Δ ⊢ FZero ⦂ Ix n
  FSuc  : ∀ {n} → Δ ⊢ Ix n ⦂ ★ → Δ ⊢ FSuc n ⦂ Ix (Suc n) 
  --
  Π : ∀ {τ υ σ σ'} → -- {_ : True (sort? σ)}
        (t : Δ ⊢ τ ⦂ σ)   →   (Δ , t) ⊢ υ ⦂ σ' →
        -------------------------------------------
        Δ ⊢ (Π τ υ) ⦂ σ'
  `λ : ∀ {τ υ σ M} → 
         (t : Δ ⊢ τ ⦂ σ)   →   (Δ , t) ⊢ (rename M) ⦂ υ  → 
         ---------------------------------------------------
         Δ ⊢ `λ τ M ⦂ Π τ υ 
  _·_ : ∀ {τ υ M N} → Δ ⊢ M ⦂ Π τ υ → Δ ⊢ N ⦂ τ  → Δ ⊢ M · N ⦂ υ
  --
  Σ : ∀ {τ υ σ σ'} → -- {_ : True (sort? σ)}
        (t : Δ ⊢ τ ⦂ σ)   →   (Δ , t) ⊢ υ ⦂ σ' → 
        ------------------------------------------
        Δ ⊢ (Σ τ υ) ⦂ σ'
  ⟪_⦂_,_⟫ : ∀ {τ υ σ σ₁ σ₂} → (Δ ⊢ τ ⦂ σ₁) → (t : Δ ⊢ σ₁ ⦂ σ₂) → (Δ , t) ⊢ υ ⦂ σ → Δ ⊢ ⟪ τ ⦂ σ₁ , υ ⟫ ⦂ Σ σ₁ σ
  fst : ∀ {τ M σ} → Δ ⊢ M ⦂ Σ τ σ → Δ ⊢ (fst M) ⦂ τ
  snd : ∀ {τ M σ} → (s : Δ ⊢ M ⦂ Σ τ σ) → Δ ⊢ (snd M) ⦂ σ
