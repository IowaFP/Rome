{-# OPTIONS --safe #-}
module F.Types.Substitution where

open import Agda.Primitive
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import F.Kinds
open import F.Types

--------------------------------------------------------------------------------
-- Defs.

-- A Δ-map (renaming) maps type vars in environment Δ₁ to environment Δ₂.
Δ-map : ∀ {ℓ₁ ℓ₂} (Δ₁ : KEnv ℓ₁) (Δ₂ : KEnv ℓ₂) → Set
Δ-map Δ₁ Δ₂ =
  (∀ {ℓ₃} {κ : Kind ℓ₃} → TVar Δ₁ κ → TVar Δ₂ κ)

-- A mapping from types to types.
τ-map : ∀ {ℓ₁ ℓ₂} (Δ₁ : KEnv ℓ₁) (Δ₂ : KEnv ℓ₂) → Set
τ-map Δ₁ Δ₂ = (∀ {ℓ₃} {κ : Kind ℓ₃} → Type Δ₁ κ → Type Δ₂ κ)

-- A Context maps type vars to types.
Context : ∀ {ℓ₁ ℓ₂} (Δ₁ : KEnv ℓ₁) (Δ₂ : KEnv ℓ₂) → Set
Context Δ₁ Δ₂ = ∀ {ℓ₃} {κ : Kind ℓ₃} → TVar Δ₁ κ → Type Δ₂ κ

--------------------------------------------------------------------------------
-- Extension.
--
-- Given a map from variables in one Context to variables in another, extension
-- yields a map from the first Context extended to the second Context similarly
-- extended.

ext : ∀ {ℓ₁ ℓ₂ ℓ₃} {Δ₁ : KEnv ℓ₁} {Δ₂ : KEnv ℓ₂} {ι : Kind ℓ₃} →
         Δ-map Δ₁ Δ₂ →
         Δ-map (Δ₁ , ι) (Δ₂ , ι)
ext ρ Z = Z
ext ρ (S x) = S (ρ x)

--------------------------------------------------------------------------------
-- Renaming.
--
-- Renaming is a necessary prelude to substitution, enabling us to “rebase” a
-- type from one Context to another.

rename : ∀ {ℓ₁ ℓ₂} {Δ₁ : KEnv ℓ₁} {Δ₂ : KEnv ℓ₂} →
           Δ-map Δ₁ Δ₂ →
           τ-map Δ₁ Δ₂

rename ρ (tvar v) = tvar (ρ v)
rename ρ (τ `→ υ) = rename ρ τ `→ rename ρ υ
rename ρ (`∀ κ τ) = `∀ κ (rename (ext ρ) τ)
rename ρ U = U

--------------------------------------------------------------------------------
-- Weakening (of a typing derivation.)

weaken : ∀ {ℓΔ ℓκ} {Δ : KEnv ℓΔ} {κ : Kind ℓκ} →
           τ-map Δ (Δ , κ)
weaken = rename S
           
--------------------------------------------------------------------------------
-- Simultaneous Substitution.
--
-- Instead of substituting a closed term for a single variable, we provide a
-- map that takes each free variable of the original type to another
-- tye. Further, the substituted terms are over an arbitrary Context, and need
-- not be closed.


exts : ∀ {ℓ₁ ℓ₂ ℓ₃}
         {Δ₁ : KEnv ℓ₁} {Δ₂ : KEnv ℓ₂}
         {ι : Kind ℓ₃} →
         Context Δ₁ Δ₂ →
         Context (Δ₁ , ι) (Δ₂ , ι) 
exts θ Z = tvar Z
exts θ (S x) = rename S (θ x)

--------------------------------------------------------------------------------
-- Substitution.
--

subst : ∀ {ℓ₁ ℓ₂} {Δ₁ : KEnv ℓ₁} {Δ₂ : KEnv ℓ₂} →
           Context Δ₁ Δ₂ →
           τ-map Δ₁ Δ₂
subst θ U = U
subst θ (tvar x) = θ x
subst θ (τ `→ υ) = subst θ τ `→ subst θ υ
subst θ (`∀ κ τ) = `∀ κ (subst (exts θ) τ)

--------------------------------------------------------------------------------
-- Single substitution.

-- (Z↦ υ) τ maps the 0th De Bruijn index in τ to υ.
Z↦ : ∀ {ℓΔ ℓκ} {Δ : KEnv ℓΔ} {κ : Kind ℓκ} →
        Type Δ κ → Context (Δ , κ) Δ
Z↦ τ Z = τ
Z↦ τ (S x) = tvar x

-- Regular ol' substitution.
_β[_] : ∀ {ℓΔ ℓκ ℓι} {Δ : KEnv ℓΔ} {κ : Kind ℓκ}{ι : Kind ℓι}
         → Type (Δ , ι) κ → Type Δ ι → Type Δ κ
τ β[ υ ] = subst (Z↦ υ) τ

--------------------------------------------------------------------------------
-- examples, to move elsewhere

t0 : Type (ε , ★ lzero) (★ lzero)
t0 = tvar Z `→ tvar Z

_ : subst (Z↦ U) t0 ≡ U `→ U
_ = refl
