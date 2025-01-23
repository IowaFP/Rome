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
-- Semantic types.

SemType : KEnv → Kind → Set

KripkeFunction : KEnv → Kind → Kind → Set
KripkeFunction Δ₁ κ₁ κ₂ =  (∀ {Δ₂} → Renaming Δ₁ Δ₂ → SemType Δ₂ κ₁ → SemType Δ₂ κ₂)

SemType Δ ★ = NormalType Δ ★
SemType Δ L = NormalType Δ L
SemType Δ₁ (κ₁ `→ κ₂) = 
  NeutralType Δ₁ (κ₁ `→ κ₂) or KripkeFunction Δ₁ κ₁ κ₂
SemType Δ R[ ★ ] = NormalType Δ R[ ★ ]
SemType Δ R[ L ] = NormalType Δ R[ L ]
SemType Δ R[ κ₁ `→ κ₂ ] = 
  NeutralType Δ R[ κ₁ `→ κ₂ ] or 
  (NormalType Δ L × SemType Δ (κ₁ `→ κ₂))
SemType Δ R[ R[ κ ] ] = 
  NeutralType Δ R[ R[ κ ] ] or
  (NormalType Δ L × SemType Δ R[ κ ])  
