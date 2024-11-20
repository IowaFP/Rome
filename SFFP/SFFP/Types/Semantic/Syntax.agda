module SFFP.Types.Semantic.Syntax where

open import SFFP.Prelude
open import SFFP.Kinds.Syntax
open import SFFP.Kinds.GVars

open import SFFP.Types.Syntax
open import SFFP.Types.Renaming using (↑ ; Renaming)
open import SFFP.Types.Properties

open import SFFP.Types.Normal.Syntax
open import SFFP.Types.Normal.Renaming

--------------------------------------------------------------------------------
-- 3.2. Type Normalization algorithm
--
-- This is the NormalTypeization by Evaluation (NBE) technique:
-- 1. Define a "semantic" class of types (values);
-- 2. define "reflection" from the syntactic to the semantic;
-- 3. define "reification" from the semantic to the syntactic; 
-- 4. evaluate each syntactic type to a semantic type; then
-- 5. Normalize by reifying the evaluation.

SemType : KEnv → Kind → Set
SemType Δ ★ = NormalType Δ ★
SemType Δ₁ (κ₁ `→ κ₂) = 
  (NeutralType Δ₁ (κ₁ `→ κ₂)) or 
  (∀ {Δ₂} → Renaming Δ₁ Δ₂ → SemType Δ₂ κ₁ → SemType Δ₂ κ₂)

reflect : ∀ {κ} → NeutralType Δ κ → SemType Δ κ
reflect {κ = ★} τ = ne τ
reflect {κ = κ `→ κ₁} τ = left τ

reify : ∀ {κ} → SemType Δ κ → NormalType Δ κ
reify {κ = ★} τ = τ
reify {κ = κ₁ `→ κ₂} (left τ) = ne τ
reify {κ = κ₁ `→ κ₂} (right F) = `λ (reify (F S (reflect (` Z))))
