{-# OPTIONS --safe #-}
module Rome.Pre.Types.Substitution where

open import Agda.Primitive
open import Preludes.Data
open import Preludes.Relation

open import Rome.Kinds
open import Rome.Pre.Types.Syntax

open import Function

--------------------------------------------------------------------------------
-- Pre-Renaming.

index = ℕ → ℕ
τ-map = Type → Type
π-map = Pred → Pred

ext : index → index
ext f zero = zero
ext f (suc n) = suc (f n)

rename : index → Type → Type
rename-π : index → Pred → Pred
rename-π f (ρ₁ ≲ ρ₂) = (rename f ρ₁) ≲ ((rename f ρ₂))
rename-π f (ρ₁ · ρ₂ ~ ρ₃) = (rename f ρ₁) · rename f ρ₂ ~ (rename f ρ₃)

rename f U = U
rename f (tvar x) = tvar (f x)
rename f (τ `→ τ') = rename f τ `→ rename f τ'
rename f (`∀ κ τ) = `∀ κ (rename (ext f) τ) 
rename f (`λ κ τ) = `λ κ (rename (ext f) τ) 
rename f (τ ·[ τ' ]) = (rename f τ) ·[ rename f τ' ]
rename f (μ τ) = μ (rename f τ)
rename f (ν τ) = ν (rename f τ)
rename f (π ⦂ κ ⇒ τ) = (rename-π f π) ⦂ κ ⇒ (rename f τ) 
rename f (lab x) = lab x
rename f (τ ▹ τ') = (rename f τ) ▹ (rename f τ')
rename f (τ R▹ τ') = (rename f τ) R▹ (rename f τ')
rename f ⌊ τ ⌋ = ⌊ (rename f τ) ⌋
rename f ε = ε
rename f (Π τ) = Π (rename f τ)
rename f (Σ τ) = Σ (rename f τ)
rename f (τ ·⌈ τ' ⌉) = (rename f τ) ·⌈ (rename f τ') ⌉
rename f (⌈ τ ⌉· τ') = ⌈ (rename f τ) ⌉· (rename f τ')

--------------------------------------------------------------------------------
-- substitution.

context = ℕ → Type
ext-c : context → context
ext-c f zero = tvar zero
ext-c f (suc n) = rename suc (f n)

subst : context → Type → Type
subst-π : context → Pred → Pred
subst-π f (ρ₁ ≲ ρ₂) = (subst f ρ₁) ≲ ((subst f ρ₂))
subst-π f (ρ₁ · ρ₂ ~ ρ₃) = (subst f ρ₁) · subst f ρ₂ ~ (subst f ρ₃)

subst f U = U
subst f (tvar x) = f x
subst f (τ `→ τ') = subst f τ `→ subst f τ'
subst f (`∀ κ τ) = `∀ κ (subst (ext-c f) τ) -- `∀ κ ((ext f) <$>τ τ) 
subst f (`λ κ τ) = `λ κ (subst (ext-c f) τ) -- `λ κ ((ext f) <$>τ τ)
subst f (τ ·[ τ' ]) = (subst f τ) ·[ subst f τ' ]
subst f (μ τ) = μ (subst f τ)
subst f (ν τ) = ν (subst f τ)
subst f (π ⦂ κ ⇒ τ) = (subst-π f π) ⦂ κ ⇒ (subst f τ) 
subst f (lab x) = lab x
subst f (τ ▹ τ') = (subst f τ) ▹ (subst f τ')
subst f (τ R▹ τ') = (subst f τ) R▹ (subst f τ')
subst f ⌊ τ ⌋ = ⌊ (subst f τ) ⌋
subst f ε = ε
subst f (Π τ) = Π (subst f τ)
subst f (Σ τ) = Σ (subst f τ)
subst f (τ ·⌈ τ' ⌉) = (subst f τ) ·⌈ (subst f τ') ⌉
subst f (⌈ τ ⌉· τ') = ⌈ (subst f τ) ⌉· (subst f τ')

--------------------------------------------------------------------------------
-- β reduction.

Z↦ : Type → context
Z↦ t zero    = t
Z↦ t (suc n) = tvar n

_β[_] : Type → Type → Type
τ β[ υ ] = subst (Z↦ υ) τ

