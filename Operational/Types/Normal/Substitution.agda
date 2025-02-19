module Rome.Operational.Types.Normal.Substitution where

open import Rome.Operational.Prelude
open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

open import Rome.Operational.Types.Syntax
open import Rome.Operational.Types.Properties
import Rome.Operational.Types.Substitution as TypeSub

open import Rome.Operational.Types.Normal.Syntax
open import Rome.Operational.Types.Normal.Renaming
open import Rome.Operational.Types.Semantic.NBE

--------------------------------------------------------------------------------
-- 3.6 Normality preserving Type Substitution

Sub : KEnv → KEnv → Set
Sub Δ₁ Δ₂ = ∀ {κ} → KVar Δ₁ κ → NormalType Δ₂ κ

-- -- ↑ing a substitution over binders.
lifts :  Sub Δ₁ Δ₂ → Sub (Δ₁ ,, κ) (Δ₂ ,, κ)
lifts {κ = ★} σ Z = ne (` Z)
lifts {κ = L} σ Z = ne (` Z)
lifts {κ = κ₁ `→ κ₂} σ Z = `λ (ne ((` (S Z)) · {! lifts σ   !}))
lifts {κ = R[ κ ]} σ Z = ne (` Z)
lifts σ (S x) = weaken (σ x)

-- Effectively: denormalize `n`, substitute, then normalize.
sub : Sub Δ₁ Δ₂ → NormalType Δ₁ κ → NormalType Δ₂ κ
sub σ n = ⇓ (TypeSub.sub (⇑ ∘ σ) (⇑ n))

extend : Sub Δ₁ Δ₂ → (A : NormalType Δ₂ κ) → Sub (Δ₁ ,, κ) Δ₂
extend σ A Z = A
extend σ A (S x) = σ x

-- -- Single variable substitution is a special case of simultaneous substitution.
_β[_] : NormalType (Δ ,, κ₁) κ₂ → NormalType Δ κ₁ → NormalType Δ κ₂
τ₁ β[ τ₂ ] = {!   !} -- sub (extend (ne ∘ `) τ₂) τ₁
