module Operational.Rome.Types.Semantic.Syntax where

open import Operational.Rome.Prelude
open import Operational.Rome.Kinds.Syntax
open import Operational.Rome.Kinds.GVars

open import Operational.Rome.Types.Syntax
open import Operational.Rome.Types.Renaming using (↑ ; Renaming)
open import Operational.Rome.Types.Properties

open import Operational.Rome.Types.Normal.Syntax
open import Operational.Rome.Types.Normal.Renaming

--------------------------------------------------------------------------------
-- 3.2. Type Normalization algorithm
--
-- This is the NormalTypeization by Evaluation (NBE) technique:
-- 1. Define a "semantic" class of types (values);
-- 2. define "reflection" from the syntactic to the semantic;
-- 3. define "reification" from the semantic to the syntactic; 
-- 4. evaluate each syntactic type to a semantic type; then
-- 5. Normalize by reifying the evaluation.


-- data SemValue Δ : Kind → Set where
--   Nm-★  : NormalType Δ ★ → SemValue Δ ★
--   Nm-L  : NormalType Δ L → SemValue Δ L
--   Ne    : NeutralType Δ (κ₁ `→ κ₂) → SemValue Δ (κ₁ `→ κ₂)
--   Ner   : NeutralType Δ (R[ κ₁ `→ κ₂ ]) → SemValue Δ (R[ κ₁ `→ κ₂ ])
--   Ne-→ : (∀ {Δ₂} → Renaming Δ₁ Δ₂ → SemValue Δ₂ κ₁ → SemValue Δ₂ κ₂) → SemValue Δ (κ₁ `→ κ₂)
--   ne-R→ : (∀ {Δ₂} → Renaming Δ₁ Δ₂ → SemValue Δ₂ κ₁ → SemValue Δ₂ κ₂) → SemValue Δ (κ₁ `→ κ₂)
  
-- This should be specified inductively, I think
SemType : KEnv → Kind → Set
SemType Δ ★ = NormalType Δ ★
SemType Δ L = NormalType Δ L
SemType Δ₁ (κ₁ `→ κ₂) = 
  (NeutralType Δ₁ (κ₁ `→ κ₂)) or 
  (∀ {Δ₂} → Renaming Δ₁ Δ₂ → SemType Δ₂ κ₁ → SemType Δ₂ κ₂)
-- This is wrong, I think.
SemType Δ R[ κ ] = NormalType Δ R[ κ ]

-- SemType Δ R[ L ] = NormalType Δ R[ L ]
-- -- This needs its own builder
-- SemType Δ₁ R[ κ₁ `→ κ₂ ] = (NeutralType Δ₁ R[ (κ₁ `→ κ₂) ]) or 
--   (∀ {Δ₂} → Renaming Δ₁ Δ₂ → SemType Δ₂ κ₁ → SemType Δ₂ κ₂)
-- SemType Δ R[ R[ κ ] ] = NormalType Δ R[ R[ κ ] ]

reflect : ∀ {κ} → NeutralType Δ κ → SemType Δ κ
reflect {κ = ★} τ = ne τ
reflect {κ = L} τ = ne τ
reflect {κ = R[ κ ]} τ = ne τ
reflect {κ = κ `→ κ₁} τ = left τ

reify : ∀ {κ} → SemType Δ κ → NormalType Δ κ
reify {κ = ★} τ = τ
reify {κ = L} τ = τ
reify {κ = R[ κ' ]} τ = τ
reify {κ = κ₁ `→ κ₂} (left τ) = ne τ
reify {κ = κ₁ `→ κ₂} (right F) = `λ (reify (F S (reflect (` Z))))

