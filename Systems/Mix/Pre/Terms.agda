module Mix.Pre.Terms where

open import Preludes.Data
open import Preludes.Relation

data Term : Set where
  ★ : Term
  𝓤 : Term
  --
  varZ : Term
  varS : Term → Term
  -- 
  Nat  : Term
  Zero : Term
  Suc  : Term → Term
  --
  Ix   : Term → Term
  FZero : Term
  FSuc : Term → Term
  --
  ⊤ : Term
  tt : Term
  -- 
  Π : Term → Term → Term
  `λ : Term → Term → Term
  _·_ : Term → Term → Term
  --
  Σ : (τ : Term) → Term → Term
  ⟪_⦂_,_⟫ : Term → Term → Term → Term
  fst : Term → Term
  snd : Term → Term
  --
  _Or_ : Term → Term → Term
  left : Term → Term
  right : Term → Term
  case_of[_]or[_] : Term → Term → Term → Term
  --
  _~_ : Term → Term → Term
  refl : Term
  Sub : Term → Term → Term

--------------------------------------------------------------------------------
-- Sorts (predicate).

data Sort : Term → Set where
  ★ : Sort ★
  𝓤 : Sort 𝓤

-- (Wish this were less verbose, but I believe we are forced to discriminate in
-- each case.)
sort? : (s : Term) → Dec (Sort s)
sort? ★ = yes ★
sort? 𝓤 = yes 𝓤
sort? varZ = no (λ ())
sort? (varS n) = no (λ ())
sort? Nat = no (λ ())
sort? Zero = no (λ ())
sort? (Suc s) = no (λ ())
sort? (Ix s) = no (λ ())
sort? FZero = no (λ ())
sort? (FSuc s) = no (λ ())
sort? ⊤ = no (λ ())
sort? tt = no (λ ())
sort? (Π s s₁) = no (λ ())
sort? (`λ s s₁) = no (λ ())
sort? (s · s₁) = no (λ ())
sort? (Σ s s₁) = no (λ ())
sort? ⟪ a ⦂ b , c ⟫ = no (λ ())
sort? (fst s) = no (λ ())
sort? (snd s) = no (λ ())
sort? (s Or s₁) = no (λ ())
sort? (left s) = no (λ ())
sort? (right s) = no (λ ())
sort? case s of[ s₁ ]or[ s₂ ] = no (λ ())
sort? (s ~ s₁) = no (λ ())
sort? refl = no (λ ())
sort? (Sub s s₁) = no (λ ())

--------------------------------------------------------------------------------
-- Renaming.

-- TD: don't use s for var names here
rename : Term → Term
rename ★ = ★
rename 𝓤 = 𝓤
rename varZ = varS varZ
rename (varS n) = varS (rename n)
rename Zero = Zero
rename (Suc s) = Suc (rename s)
rename (Ix s) = Ix (rename s)
rename FZero = FZero
rename (FSuc s) = FSuc (rename s)
rename ⊤ = ⊤
rename tt = tt
rename (Π s s₁) = Π (rename s) (rename s₁)
rename (`λ s s₁) = `λ (rename s) (rename s₁)
rename (s · s₁) = (rename s) · (rename s₁)
rename (Σ s s₁) = Σ (rename s) (rename s₁)
rename ⟪ s ⦂ s₁ , s₂ ⟫ = ⟪ rename s ⦂ rename s₁ , rename s₂ ⟫
rename (fst s) = fst (rename s)
rename (snd s) = snd (rename s)
rename (s Or s₁) = rename s Or rename s₁
rename (left s) = left (rename s)
rename (right s) = right (rename s)
rename case s of[ s₁ ]or[ s₂ ] = case (rename s) of[ rename s₁ ]or[ rename s₂ ]
rename (s ~ s₁) = rename s ~ rename s₁
rename refl = refl
rename (Sub s s₁) = Sub (rename s) (rename s₁)
rename Nat = Nat
