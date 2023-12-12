module Mix.Pre.Terms where

open import Preludes.Data
open import Preludes.Relation

data Term : Set where
  ★ : Term
  □ : Term
  --
  varZ : Term
  varS : Term → Term
  -- 
  Nat  : Term
  Z : Term
  S  : Term → Term
  Case_of[Z↦_S↦_] : Term → Term → Term → Term
  --
  Ix   : Term → Term
  I₀ : Term
  Iₛ : Term → Term
  Case_of[I₀↦_Iₛ↦_] : Term → Term → Term → Term
  ƛ⦅⦆ : Term
  --
  ⊤ : Term
  tt : Term
  -- 
  `∀ : Term → Term → Term
  `λ : Term → Term → Term
  _·_ : Term → Term → Term
  --
  `∃ : (τ : Term) → Term → Term
  ⟪_⦂_,_⟫ : Term → Term → Term → Term
  Case_of⟪_⟫ : Term → Term → Term
  --
  _Or_ : Term → Term → Term
  left : Term → Term
  right : Term → Term
  case_of[left↦_right↦_] : Term → Term → Term → Term
  --
  _~_ : Term → Term → Term
  Refl : Term

--------------------------------------------------------------------------------
-- Synonyms

_`×_ = `∃
_`→_ = `∀

Zero One Two Three : Term
Zero = Z
One = S Z
Two = S One
Three = S Two

x₀ x₁ x₂ x₃ x₄ x₅ : Term
x₀ = varZ
x₁ = varS x₀
x₂ = varS x₁
x₃ = varS x₂
x₄ = varS x₃
x₅ = varS x₄

--------------------------------------------------------------------------------
-- Sorts (predicate).

data Sort : Term → Set where
  ★ : Sort ★
  □ : Sort □

-- (Wish this were less verbose, but I believe we are forced to discriminate in
-- each case.)
sort? : (s : Term) → Dec (Sort s)
sort? ★ = yes ★
sort? □ = yes □
sort? varZ = no (λ ())
sort? (varS s) = no (λ ())
sort? Nat = no (λ ())
sort? Z = no (λ ())
sort? (S s) = no (λ ())
sort? Case s of[Z↦ s₁ S↦ s₂ ] = no (λ ())
sort? (Ix s) = no (λ ())
sort? I₀ = no (λ ())
sort? (Iₛ s) = no (λ ())
sort? Case s of[I₀↦ s₁ Iₛ↦ s₂ ] = no (λ ())
sort? ƛ⦅⦆ = no (λ ())
sort? ⊤ = no (λ ())
sort? tt = no (λ ())
sort? (`∀ s s₁) = no (λ ())
sort? (`λ s s₁) = no (λ ())
sort? (s · s₁) = no (λ ())
sort? (`∃ s s₁) = no (λ ())
sort? ⟪ s ⦂ s₁ , s₂ ⟫ = no (λ ())
sort? Case s of⟪ s₁ ⟫ = no (λ ())
sort? (s Or s₁) = no (λ ())
sort? (left s) = no (λ ())
sort? (right s) = no (λ ())
sort? case s of[left↦ s₁ right↦ s₂ ] = no (λ ())
sort? (s ~ s₁) = no (λ ())
sort? Refl = no (λ ())
