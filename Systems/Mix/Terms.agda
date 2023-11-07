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
  _,_ : Context → Term → Context

--------------------------------------------------------------------------------
-- Lookup 
infix 4 _∈_

data _∈_ : Term → Context → Set where

  Z : ∀ {Γ A}
      ------------------
    → A ∈ (Γ , A)

  S : ∀ {Γ A B}
    → A ∈ Γ
      ------------------
    → A ∈ (Γ , B)

data ⊢Context : Context → Set where
  ε : ⊢Context ε
  _,_ : ∀ {τ}{Δ}{M} → 
          ⊢Context Δ → 
          Δ ⊢ M ⦂ τ → 
          ----------------------------
          ⊢Context (Δ , τ)
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
  varZ : ∀ {τ}  → (Δ , τ) ⊢ varZ ⦂ τ
  varS : ∀ {τ υ n} →
            Δ ⊢ n ⦂ τ
         → (Δ , υ) ⊢ varS n ⦂ τ
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
        (Δ ⊢ τ ⦂ σ)   →   (Δ , τ) ⊢ υ ⦂ σ' →
        -------------------------------------------
        Δ ⊢ (Π τ υ) ⦂ σ'
  `λ : ∀ {τ υ σ M} → 
         Δ ⊢ τ ⦂ σ   →   (Δ , τ) ⊢ (rename M) ⦂ υ  → 
         ---------------------------------------------------
         Δ ⊢ `λ τ M ⦂ Π τ υ 
  _·_ : ∀ {τ υ M N} → Δ ⊢ M ⦂ Π τ υ → Δ ⊢ N ⦂ τ  → Δ ⊢ M · N ⦂ υ
  --
  Σ : ∀ {τ υ σ σ'} → -- {_ : True (sort? σ)}
        Δ ⊢ τ ⦂ σ   →   (Δ , τ) ⊢ υ ⦂ σ' → 
        ------------------------------------------
        Δ ⊢ (Σ τ υ) ⦂ σ'
  ⟪_⦂_,_⟫ : ∀ {τ υ σ σ₁ σ₂} → 
            (Δ ⊢ τ ⦂ σ₁)   →   (t : Δ ⊢ σ₁ ⦂ σ₂)   →   (Δ , σ₁) ⊢ υ ⦂ σ → 
            ----------------------------------------------------------------
            Δ ⊢ ⟪ τ ⦂ σ₁ , υ ⟫ ⦂ Σ σ₁ σ
  fst : ∀ {τ M σ} → Δ ⊢ M ⦂ Σ τ σ → Δ ⊢ (fst M) ⦂ τ
  snd : ∀ {τ M σ} → (s : Δ ⊢ M ⦂ Σ τ σ) → Δ ⊢ (snd M) ⦂ σ
