module SFFP.Types.Normal.Evaluation where

open import SFFP.Prelude
open import SFFP.Kinds.Syntax
open import SFFP.Kinds.GVars

open import SFFP.Types.Syntax
open import SFFP.Types.Renaming using (↑ ; Renaming)
open import SFFP.Types.Properties

open import SFFP.Types.Normal.Syntax
open import SFFP.Types.Semantic.Syntax
open import SFFP.Types.Semantic.Renaming


--------------------------------------------------------------------------------
-- 3.2. Type Normalization algorithm
--
-- This is the NormalTypeization by Evaluation (NBE) technique:
-- 1. Define a "semantic" class of types (values);
-- 2. define "reflection" from the syntactic to the semantic;
-- 3. define "reification" from the semantic to the syntactic; 
-- 4. evaluate each syntactic type to a semantic type; then
-- 5. NormalTypeize by reifying the evaluation.

Env : KEnv → KEnv → Set
Env Δ₁ Δ₂ = ∀ {κ} → KVar Δ₁ κ → SemType Δ₂ κ

extende : (η : Env Δ₁ Δ₂) → (V : SemType Δ₂ κ) → Env (Δ₁ ,, κ) Δ₂
extende η V Z     = V
extende η V (S x) = η x

↑e : Env Δ₁ Δ₂ → Env (Δ₁ ,, κ) (Δ₂ ,, κ)
↑e η = extende (weakenSem ∘ η) (reflect (` Z))

-- "SemType application"
_·V_ : SemType Δ (κ₁ `→ κ₂) → SemType Δ κ₁ → SemType Δ κ₂
left A ·V V = reflect (A · (reify V))
right F ·V V = F id V

eval : Type Δ₁ κ → Env Δ₁ Δ₂ → SemType Δ₂ κ
eval (` x) η = η x
eval (`λ τ) η = right λ ρ v → eval τ (extende (renSem ρ ∘ η) v)
eval (τ₁ · τ₂) η = (eval τ₁ η) ·V (eval τ₂ η)
eval (τ₁ `→ τ₂) η = (eval τ₁ η) `→ (eval τ₂ η)
eval (`∀ κ τ) η = `∀ _ (eval τ (↑e η))
eval (μ τ) η = μ (eval τ (↑e η))

idEnv : Env Δ Δ
idEnv = reflect ∘ `

-- NormalType forms.
⇓ : Type Δ κ → NormalType Δ κ
⇓ τ = reify (eval τ idEnv)

--------------------------------------------------------------------------------
-- 3.3. Completeness of type normalization.
--
-- Completeness states that normalizing two β-equal types yields the same normal
-- form. In other words, `nf` is injective: normalization picks out unique
-- representations for normal forms.
--
-- (OMITTED).


