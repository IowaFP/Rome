module SFFP.Types.Normal.Substitution where

open import SFFP.Prelude
open import SFFP.Kinds.Syntax
open import SFFP.Kinds.GVars

open import SFFP.Types.Syntax
open import SFFP.Types.Properties
import SFFP.Types.Substitution as TypeSub

open import SFFP.Types.Normal.Syntax
open import SFFP.Types.Normal.Renaming
open import SFFP.Types.Normal.Evaluation

--------------------------------------------------------------------------------
-- 3.6 Normality preserving Type Substitution

Sub : KEnv → KEnv → Set
Sub Δ₁ Δ₂ = ∀ {κ} → KVar Δ₁ κ → NormalType Δ₂ κ

-- -- ↑ing a substitution over binders.
↑s :  Sub Δ₁ Δ₂ → Sub (Δ₁ ,, κ) (Δ₂ ,, κ)
↑s σ Z = ne (` Z)
↑s σ (S x) = weaken (σ x)

-- Effectively: denormalize `n`, substitute, then normalize.
sub : Sub Δ₁ Δ₂ → NormalType Δ₁ κ → NormalType Δ₂ κ
sub σ n = ⇓ (TypeSub.sub (embed ∘ σ) (embed n))

extend : Sub Δ₁ Δ₂ → (A : NormalType Δ₂ κ) → Sub (Δ₁ ,, κ) Δ₂
extend σ A Z = A
extend σ A (S x) = σ x

-- -- Single variable substitution is a special case of simultaneous substitution.
_β[_] : NormalType (Δ ,, κ₁) κ₂ → NormalType Δ κ₁ → NormalType Δ κ₂
τ₁ β[ τ₂ ] = sub (extend (ne ∘ `) τ₂) τ₁
