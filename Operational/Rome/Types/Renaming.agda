module Operational.Rome.Types.Renaming where

open import Operational.Rome.Prelude
open import Operational.Rome.Types.Syntax
open import Operational.Rome.Kinds.Syntax
open import Operational.Rome.Kinds.GVars

--------------------------------------------------------------------------------
-- 2.5 Type Renaming
--
-- Renamings map variables in context Δ₁ to context Δ₂.
-- Renaming and substitution are defined in "parallel".
-- weakening is just a special case of renaming;

Renaming : KEnv → KEnv → Set
Renaming Δ₁ Δ₂ = ∀ {κ} → KVar Δ₁ κ → KVar Δ₂ κ

-- (extensional) equivalence of renamings
_≈_ : ∀ {Δ₁} (ρ₁ ρ₂ : Renaming Δ₁ Δ₂) → Set
_≈_ {Δ₁ = Δ₁} ρ₁ ρ₂ = ∀ {κ} (x : KVar Δ₁ κ) → ρ₁ x ≡ ρ₂ x


-- ↑ing over binders.
↑ : Renaming Δ₁ Δ₂ → Renaming (Δ₁ ,, κ) (Δ₂ ,, κ)
↑ ρ Z = Z
↑ ρ (S x) = S (ρ x)

ren : Renaming Δ₁ Δ₂ → Type Δ₁ κ → Type Δ₂ κ
ren ρ Unit  = Unit
ren ρ (` x) = ` (ρ x)
ren ρ (`λ τ) = `λ (ren (↑ ρ) τ)
ren ρ (τ₁ · τ₂) = (ren ρ τ₁) · (ren ρ τ₂)
ren ρ (τ₁ `→ τ₂) = (ren ρ τ₁) `→ (ren ρ τ₂)
ren ρ (`∀ κ τ) = `∀ κ (ren (↑ ρ) τ)
ren ρ (μ F) = μ (ren ρ F)
ren ρ (Π τ) = Π (ren ρ τ)
ren ρ (Σ τ) = Σ (ren ρ τ)
ren ρ (lab x) = lab x
ren ρ (ℓ ▹ τ) = (ren ρ ℓ) ▹ (ren ρ τ)
ren ρ (ℓ R▹ τ) = (ren ρ ℓ) R▹ (ren ρ τ)
ren ρ ⌊ ℓ ⌋ = ⌊ (ren ρ ℓ) ⌋

weaken : Type Δ κ₂ → Type (Δ ,, κ₁) κ₂
weaken = ren S
