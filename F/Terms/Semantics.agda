module F.Terms.Semantics where

open import Agda.Primitive

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong₂; cong-app; subst)

open import Data.Unit.Polymorphic
open import Data.Product
  using (_×_; Σ-syntax; _,_)
  renaming (proj₁ to fst; proj₂ to snd)

open import Data.Sum
  renaming (_⊎_ to _or_; inj₁ to left; inj₂ to right)
open import Data.Fin
  renaming (zero to fzero; suc to fsuc)
  hiding (fold)

open import F.Kinds
open import F.Types
open import F.Types.Substitution
open import F.Types.Substitution.Properties -- extensionality
open import F.Terms.Syntax
open import Lib.Equality

--------------------------------------------------------------------------------
-- The meaning of environments.

⟦_⟧e : ∀ {ℓΔ} {ℓΓ} {Δ : KEnv ℓΔ} →
       Env Δ ℓΓ → ⟦ Δ ⟧ke → Set ℓΓ
⟦ ε ⟧e H = ⊤
⟦ Γ , τ ⟧e H = ⟦ Γ ⟧e H × ⟦ τ ⟧t H

--------------------------------------------------------------------------------
-- The meaning of variables.

⟦_⟧v : ∀ {ℓΔ} {Δ : KEnv ℓΔ} {ℓΓ} {Γ : Env Δ ℓΓ} {ℓτ} {τ : Type Δ (★ ℓτ)} →
       Var Γ τ → (H : ⟦ Δ ⟧ke) → ⟦ Γ ⟧e H → ⟦ τ ⟧t H
⟦ Z ⟧v H (η , x) = x
⟦ S v ⟧v H (η , x) = ⟦ v ⟧v H η

--------------------------------------------------------------------------------
-- Denotational Weakening Lemma.

weaken⟦_⟧e : ∀ {ℓΔ ℓΓ ℓκ} {Δ : KEnv ℓΔ} {κ : Kind ℓκ} →
             (Γ : Env Δ ℓΓ) → (H : ⟦ Δ ⟧ke) → (⟦Γ⟧ : ⟦ Γ ⟧e H) →
             (X : ⟦ κ ⟧k) →
               ⟦ weakΓ Γ ⟧e (H , X)
weaken⟦ ε ⟧e H ⟦Γ⟧ X = tt
weaken⟦_⟧e {Δ = Δ} {κ = κ} (_,_ {ℓκ = ℓκ} Γ τ) H (⟦Γ⟧ , ⟦τ⟧) X
  rewrite τ-preservation Δ (Δ , κ) H (H , X) S (λ _ → refl) τ = weaken⟦ Γ ⟧e H ⟦Γ⟧ X , ⟦τ⟧

--------------------------------------------------------------------------------
-- The meaning of terms.
 
⟦_⟧ : ∀ {ℓΔ} {Δ : KEnv ℓΔ} {ℓΓ ℓτ} {Γ : Env Δ ℓΓ}
        {τ : Type Δ (★ ℓτ)} →
        Term Δ Γ τ →
        (H : ⟦ Δ ⟧ke) → ⟦ Γ ⟧e H → ⟦ τ ⟧t H
⟦ var x ⟧ H η = ⟦ x ⟧v H η
⟦ `λ _ M ⟧ H η = λ x → ⟦ M ⟧ H (η , x)
⟦ M · N ⟧ H η = ⟦ M ⟧ H η (⟦ N ⟧ H η)
⟦ (`Λ κ M) ⟧ H η = λ (X : ⟦ κ ⟧k) → ⟦ M ⟧ (H , X) (weaken⟦ _ ⟧e H η X)
⟦ _·[_] {τ = τ} M υ ⟧ H η
  rewrite (sym (Substitution τ υ H)) = ⟦ M ⟧ H η (⟦ υ ⟧t H)
