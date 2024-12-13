{-# OPTIONS --allow-unsolved-metas #-}
module Rome.Operational.Types.Semantic.Syntax where

open import Data.Product using (_×_ ; _,_)
open import Rome.Operational.Prelude
open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

open import Rome.Operational.Types.Syntax
open import Rome.Operational.Types.Renaming using (lift ; Renaming)
open import Rome.Operational.Types.Properties

open import Rome.Operational.Types.Normal.Syntax
open import Rome.Operational.Types.Normal.Renaming
  
--------------------------------------------------------------------------------
-- Congruences.
--
-- NBE reflects non-neutral functions into Agda function spaces so as to use
-- Agda's computation to eliminate applications.  A Congruence specifies any
-- syntax under which could occur a binder. For example, consider: 
--   τ = Π (ℓ ▹ (λ x. ` Z))
-- We obviously expect that this normalizes to itself (modulo data type)
--   ⇓ τ ≊ τ 
-- but we must reflect the function portion (λ x. x) into an Agda function.

data Congruence Δ : Kind → Set where
  _▹  : NormalType Δ L → Congruence Δ κ
  _R▹ : NormalType Δ L → Congruence Δ R[ κ ]
  ΠR▹    : NormalType Δ L → Congruence Δ κ
  ΣR▹    : NormalType Δ L → Congruence Δ κ

Congruences : KEnv → Kind → Set
Congruences Δ κ = List (Congruence Δ κ)



--------------------------------------------------------------------------------
-- Semantic types.

SemType : KEnv → Kind → Set
SemType-R : KEnv → Kind → Set
SemFunction : KEnv → Kind → Kind → Set

SemFunction Δ₁ κ₁ κ₂ = 
  (Congruences Δ₁ (κ₁ `→ κ₂) × 
  (∀ {Δ₂} → Renaming Δ₁ Δ₂ → SemType Δ₂ κ₁ → SemType Δ₂ κ₂))

SemType Δ ★ = NormalType Δ ★
SemType Δ L = NormalType Δ L
SemType Δ₁ (κ₁ `→ κ₂) = 
  NeutralType Δ₁ (κ₁ `→ κ₂) or SemFunction Δ₁ κ₁ κ₂
SemType Δ R[ κ ] = SemType-R Δ κ

-- unravel : ℕ → Kind → Kind
-- unravel zero κ = κ
-- unravel (suc n) κ = unravel n R[ κ ] 

-- E.g. SemType-R (ℓ R▹ ⊤)
SemType-R Δ ★ = NormalType Δ R[ ★ ]
-- E.g. SemType-R (ℓ R▹ ℓ)
SemType-R Δ L = NormalType Δ R[ L ]
-- E.g. SemType-R (ℓ R▹ (ℓ R▹ τ))
SemType-R Δ R[ κ ] with SemType-R Δ κ
... | c = {!!}
-- SemType-R (ℓ R▹ λ x : ★. x) makes sense
-- but evaluating
--   SemType-R {a : λ x. x, b : λ x. ⊤}
-- to a function does not make sense.
-- This is a separate problem, I think, than the congruence problem.
SemType-R Δ₁ (κ₁ `→ κ₂) = 
  NeutralType Δ₁ R[ κ₁ `→ κ₂ ] or (NormalType Δ₁ L × SemFunction Δ₁ κ₁ κ₂)


-- _ : {!∀ Δ → SemType-R Δ R[ R[ ★ ] ]!}
