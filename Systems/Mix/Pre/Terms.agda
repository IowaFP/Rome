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
  Caseℕ_of[_∣_] : Term → Term → Term → Term
  --
  Ix   : Term → Term
  I₀ : Term
  Iₛ : Term → Term
  CaseIx_of[_∣_] : Term → Term → Term → Term
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
  Case∃_of[_] : Term → Term → Term
  --
  _Or_ : Term → Term → Term
  left : Term → Term
  right : Term → Term
  case_of[_]or[_] : Term → Term → Term → Term
  --
  _~_ : Term → Term → Term
  Refl : Term

Zero One Two Three : Term
Zero = Z
One = S Z
Two = S One
Three = S Two

--------------------------------------------------------------------------------
-- Types (as predicate).



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
sort? Caseℕ s of[ s₁ ∣ s₂ ] = no (λ ())
sort? (Ix s) = no (λ ())
sort? I₀ = no (λ ())
sort? (Iₛ s) = no (λ ())
sort? CaseIx s of[ s₁ ∣ s₂ ] = no (λ ())
sort? ƛ⦅⦆ = no (λ ())
sort? ⊤ = no (λ ())
sort? tt = no (λ ())
sort? (`∀ s s₁) = no (λ ())
sort? (`λ s s₁) = no (λ ())
sort? (s · s₁) = no (λ ())
sort? (`∃ s s₁) = no (λ ())
sort? ⟪ s ⦂ s₁ , s₂ ⟫ = no (λ ())
sort? Case∃ s of[ s₁ ] = no (λ ())
sort? (s Or s₁) = no (λ ())
sort? (left s) = no (λ ())
sort? (right s) = no (λ ())
sort? case s of[ s₁ ]or[ s₂ ] = no (λ ())
sort? (s ~ s₁) = no (λ ())
sort? Refl = no (λ ())

--------------------------------------------------------------------------------
-- Renaming.

-- TD: don't use s for var names here
-- rename : Term → Term
-- rename ★ = ★
-- rename 𝓤 = 𝓤
-- rename varZ = varS varZ
-- rename (varS n) = varS (rename n)
-- rename Zero = Zero
-- rename (Suc s) = Suc (rename s)
-- rename (Ix s) = Ix (rename s)
-- rename FZero = FZero
-- rename (FSuc s) = FSuc (rename s)
-- rename ⊤ = ⊤
-- rename tt = tt
-- rename (Π s s₁) = Π (rename s) (rename s₁)
-- rename (`λ s s₁) = `λ (rename s) (rename s₁)
-- rename (s · s₁) = (rename s) · (rename s₁)
-- rename (Σ s s₁) = Σ (rename s) (rename s₁)
-- rename ⟪ s ⦂ s₁ , s₂ ⟫ = ⟪ rename s ⦂ rename s₁ , rename s₂ ⟫
-- rename (fst s) = fst (rename s)
-- rename (snd s) = snd (rename s)
-- rename (s Or s₁) = rename s Or rename s₁
-- rename (left s) = left (rename s)
-- rename (right s) = right (rename s)
-- rename case s of[ s₁ ]or[ s₂ ] = case (rename s) of[ rename s₁ ]or[ rename s₂ ]
-- rename (s ~ s₁) = rename s ~ rename s₁
-- rename refl = refl
-- rename (Sub s s₁) = Sub (rename s) (rename s₁)
-- rename Nat = Nat
