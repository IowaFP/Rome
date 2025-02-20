{-# OPTIONS --allow-unsolved-metas #-}
module Rome.Operational.Types.Theorems.Soundness.Relation where

open import Rome.Operational.Prelude

open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

open import Rome.Operational.Types
open import Rome.Operational.Types.Properties
open import Rome.Operational.Types.Renaming using (Renaming ; _≈_ ; lift)

open import Rome.Operational.Types.Normal.Syntax
import Rome.Operational.Types.Normal.Renaming as N
open import Rome.Operational.Types.Normal.Properties.Renaming
open import Rome.Operational.Types.Semantic.Syntax
open import Rome.Operational.Types.Semantic.Renaming
open import Rome.Operational.Types.Semantic.NBE

open import Rome.Operational.Types.Equivalence
-- open import Rome.Operational.Types.Normal.Properties.Postulates

--------------------------------------------------------------------------------
-- Soundness of type normalization: 
-- All types are equivalent (under ≡t) to their normal forms.

infix 0 _≋_
_≋_ : ∀ {κ} → Type Δ κ → SemType Δ κ → Set
SoundKripke : Type Δ₁ (κ₁ `→ κ₂) → KripkeFunction Δ₁ κ₁ κ₂ → Set


_≋_ {κ = ★} τ V = τ ≡t ⇑ V
_≋_ {κ = L} τ V = τ ≡t ⇑ V
_≋_ {Δ₁} {κ = κ₁ `→ κ₂} τ F = SoundKripke τ F
_≋_ {κ = R[ κ ]} τ (left n) = τ ≡t (⇑NE n)
_≋_ {κ = R[ κ ]} τ (right (l , υ)) = τ ≡t ⇑ (l ▹ reify υ)

SoundKripke {Δ₁ = Δ₁} {κ₁ = κ₁} {κ₂ = κ₂} υ F =     
    ∀ {Δ₂} (ρ : Renaming Δ₁ Δ₂) {v V} → 
      v ≋ V → 
      ren ρ υ · v ≋ renKripke ρ F ·V V

--------------------------------------------------------------------------------
-- - Types equivalent to neutral types under ≡t reflect to equivalence under _≋_, and 
-- - Types related under _≋_ have reifications equivalent under _≡t_

reflect-≋ : ∀ {τ : Type Δ κ} {υ :  NeutralType Δ κ} → 
             τ ≡t ⇑NE υ → τ ≋ (reflect υ)
reify-≋ : ∀ {τ : Type Δ κ} {V :  SemType Δ κ} → 
              τ ≋ V → τ ≡t ⇑ (reify V)

cong-ren-≡t : ∀ {τ υ : Type Δ₁ κ} (ρ : Renaming Δ₁ Δ₂) → 
                τ ≡t υ → ren ρ τ ≡t ren ρ υ 
cong-ren-≡t {τ = τ} {υ} ρ e = {! e  !} 

reflect-≋ {κ = ★} e = e 
reflect-≋ {κ = L} e = e
reflect-≋ {κ = κ₁ `→ κ₂} {τ} {υ} e = λ ρ q → reflect-≋ 
    (eq-· 
        (eq-sym (eq-trans (inst (↻-ren-⇑NE ρ υ)) 
            (cong-ren-≡t ρ (eq-sym e)))) 
        (reify-≋ q))
reflect-≋ {κ = R[ κ ]} e = e           

reify-≋ {κ = ★} {τ} {V} e = e 
reify-≋ {κ = L} {τ} {V} e = e
reify-≋ {κ = κ₁ `→ κ₂} {τ} {F} e = 
    eq-trans 
        eq-η 
        (eq-λ (eq-trans 
            (reify-≋ (e S {` Z} {reflect (` Z)} (reflect-≋ eq-refl))) 
            (inst refl)))
reify-≋ {κ = R[ κ ]} {τ} {left n} e = e 
reify-≋ {κ = R[ κ ]} {τ} {right (l , υ)} e = e 

--------------------------------------------------------------------------------
-- Relating syntactic substitutions to semantic environments

SREnv : ∀ {Δ₁ Δ₂} → Substitution Δ₁ Δ₂ → Env Δ₁ Δ₂ → Set
SREnv {Δ₁} σ η = ∀ {κ} (α : KVar Δ₁ κ) → (σ α) ≋ (η α) 