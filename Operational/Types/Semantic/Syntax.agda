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

data Congruence (Δ : KEnv) : Set where
  Π  : NormalType Δ L → Congruence Δ
  Σ  : NormalType Δ L → Congruence Δ




--------------------------------------------------------------------------------
-- Semantic types.

SemType : KEnv → Kind → Set
-- SemType-R : KEnv → Kind → Set
SemFunction : KEnv → Kind → Kind → Set

SemFunction Δ₁ κ₁ κ₂ = List (Congruence Δ₁) × (∀ {Δ₂} → Renaming Δ₁ Δ₂ → SemType Δ₂ κ₁ → SemType Δ₂ κ₂)

SemType Δ ★ = NormalType Δ ★
SemType Δ L = NormalType Δ L
SemType Δ₁ (κ₁ `→ κ₂) = 
  NeutralType Δ₁ (κ₁ `→ κ₂) or SemFunction Δ₁ κ₁ κ₂
-- E.g. SemType-R (ℓ ▹ ⊤)
SemType Δ R[ ★ ] = NormalType Δ R[ ★ ]
-- E.g. SemType-R (ℓ ▹ ℓ)
SemType Δ R[ L ] = NormalType Δ R[ L ]
-- E.g. SemType-R (ℓ ▹ λ x : ★. x)
SemType Δ R[ κ₁ `→ κ₂ ] = 
  NeutralType Δ R[ κ₁ `→ κ₂ ] or 
  (NormalType Δ L × SemFunction Δ κ₁ κ₂)
-- E.g. SemType-R (ℓ₁ ▹ (ℓ₂ ▹ τ))
SemType Δ R[ R[ κ ] ] = 
  NeutralType Δ R[ R[ κ ] ] or
  (NormalType Δ L × SemType Δ R[ κ ])
