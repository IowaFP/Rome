module Rome.Operational.Types.Substitution where

open import Rome.Operational.Prelude
open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars
open import Rome.Operational.Types.Syntax
open import Rome.Operational.Types.Renaming

--------------------------------------------------------------------------------
-- 2.6 Substitution
--
-- A substitution maps variables to types.

Sub : KEnv → KEnv → Set
Sub Δ₁ Δ₂ = ∀ {κ} → KVar Δ₁ κ → Type Δ₂ κ

-- ↑ing a substitution over binders.
↑s :  Sub Δ₁ Δ₂ → Sub (Δ₁ ,, κ) (Δ₂ ,, κ)
↑s σ Z = ` Z
↑s σ (S x) = weaken (σ x)

-- This is simultaneous substitution: Given subst σ and type τ, we replace *all*
-- variables in τ with the types mapped to by σ.
sub : Sub Δ₁ Δ₂ → Type Δ₁ κ → Type Δ₂ κ
sub σ Unit = Unit
sub σ (` x) = σ x
sub σ (`λ τ) = `λ (sub (↑s σ) τ)
sub σ (τ₁ · τ₂) = (sub σ τ₁) · (sub σ τ₂)
sub σ (τ₁ `→ τ₂) = (sub σ τ₁) `→ (sub σ τ₂)
sub σ (`∀ κ τ) = `∀ κ (sub (↑s σ) τ)
sub σ (μ F) = μ (sub σ F)
sub σ (Π) = Π
sub σ Σ = Σ
sub σ (lab x) = lab x
sub σ (ℓ ▹ τ) = (sub σ ℓ) ▹ (sub σ τ)
sub σ ⌊ ℓ ⌋ = ⌊ (sub σ ℓ) ⌋
-- sub σ (↑ τ) = ↑ (sub σ τ)
-- sub σ (τ ↑) = (sub σ τ) ↑

-- "Substitutions could be implemented as lists of types and then the cons
-- constructor would extend a substitution by an additional term. Using our
-- functional representation for substitutions, it is convenient to define an
-- operation for this. This effectively defines a new func that,
--   - if it is applied to the Z variable, returns our additional terms,
--   - and otherwise invokes the original substitution."
--
-- AH> This is analogous to the following procedure: define a "list" as a
--     function Int -> A and then write cons : A -> (Int -> A) -> (Int -> A).
extend : Sub Δ₁ Δ₂ → (A : Type Δ₂ κ) → Sub (Δ₁ ,, κ) Δ₂
extend σ A Z = A
extend σ A (S x) = σ x

-- Single variable substitution is a special case of simultaneous substitution.
_β[_] : Type (Δ ,, κ₁) κ₂ → Type Δ κ₁ → Type Δ κ₂
B β[ A ] = sub (extend ` A) B
