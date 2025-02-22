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
import Rome.Operational.Types.Normal.Properties.Renaming as NPR
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
cong-ren-≡p : ∀ {π₁ π₂ : Pred Δ₁ R[ κ ]} (ρ : Renaming Δ₁ Δ₂) → 
                π₁ ≡p π₂ → renPred ρ π₁ ≡p renPred ρ π₂

cong-ren-≡t {τ = τ} {υ} ρ eq-refl = eq-refl
cong-ren-≡t {τ = τ} {υ} ρ (eq-sym e) = eq-sym (cong-ren-≡t ρ e)
cong-ren-≡t {τ = τ} {υ} ρ (eq-trans e e₁) = eq-trans (cong-ren-≡t ρ e) (cong-ren-≡t ρ e₁)
cong-ren-≡t {τ = τ} {υ} ρ (eq-→ e e₁) = eq-→ (cong-ren-≡t ρ e) (cong-ren-≡t ρ e₁)
cong-ren-≡t {τ = τ} {υ} ρ (eq-∀ e) = eq-∀ (cong-ren-≡t (lift ρ) e)
cong-ren-≡t {τ = τ} {υ} ρ (eq-μ e) = eq-μ (cong-ren-≡t ρ e)
cong-ren-≡t {τ = τ} {υ} ρ (eq-λ e) = eq-λ (cong-ren-≡t (lift ρ) e)
cong-ren-≡t {τ = τ} {υ} ρ (eq-· e e₁) = eq-· (cong-ren-≡t ρ e) (cong-ren-≡t ρ e₁)
cong-ren-≡t {τ = τ} {υ} ρ (eq-⌊⌋ e) = eq-⌊⌋ (cong-ren-≡t ρ e)
cong-ren-≡t {τ = τ} {υ} ρ (eq-▹ e e₁) = eq-▹ (cong-ren-≡t ρ e) (cong-ren-≡t ρ e₁)
cong-ren-≡t {τ = τ} {υ} ρ (eq-⇒ x e) = eq-⇒ (cong-ren-≡p ρ x) (cong-ren-≡t ρ e)
cong-ren-≡t {τ = τ} {.(`λ (weaken τ · ` Z))} ρ eq-η = 
    eq-trans 
        (eq-η {f = ren ρ τ}) 
        (eq-λ (eq-· 
            (inst (sym (↻-lift-weaken ρ τ) )) 
            eq-refl))
cong-ren-≡t {τ = `λ τ₁ · τ₂} {.(τ₁ β[ τ₂ ])} ρ (eq-β {τ₁ = τ₁} {τ₂}) = 
    eq-trans 
        (eq-β {τ₁ = ren (lift ρ) τ₁} {ren ρ τ₂}) 
        (eq-sym (inst (↻-ren-β ρ τ₁ τ₂)))
cong-ren-≡t {τ = τ} {υ} ρ eq-Π = eq-Π 
cong-ren-≡t {τ = τ} {υ} ρ eq-Σ = eq-Σ
cong-ren-≡t {τ = (Π · (l ▹ `λ τ))} {υ} ρ (eq-Πλ {l = l} {τ}) = 
    eq-trans 
    (eq-Πλ {l = ren ρ l} {ren (lift ρ) τ}) 
    (eq-λ (eq-· eq-refl (eq-▹ (inst (sym (↻-lift-weaken ρ l))) eq-refl)))
cong-ren-≡t {τ = τ} {υ} ρ eq-▹$ = eq-▹$
cong-ren-≡t {τ = τ} {υ} ρ eq-assoc-Π = eq-assoc-Π
cong-ren-≡t {τ = τ} {υ} ρ eq-assoc-Σ = eq-assoc-Σ
cong-ren-≡t {τ = τ} {υ} ρ eq-app-lift-Π = eq-app-lift-Π
cong-ren-≡t {τ = τ} {υ} ρ (eq-<$> t u) = eq-<$> (cong-ren-≡t ρ t) (cong-ren-≡t ρ u)

cong-ren-≡p {π₁} {π₂} ρ (eq₁ eq-≲ eq₂) = cong-ren-≡t ρ eq₁ eq-≲ cong-ren-≡t ρ eq₂
cong-ren-≡p {π₁} {π₂} ρ (eq₁ eq-· eq₂ ~ eq₃) = (cong-ren-≡t ρ eq₁) eq-· (cong-ren-≡t ρ eq₂) ~ (cong-ren-≡t ρ eq₃)

reflect-≋ {κ = ★} e = e 
reflect-≋ {κ = L} e = e
reflect-≋ {κ = κ₁ `→ κ₂} {τ} {υ} e = λ ρ q → reflect-≋ 
    (eq-· 
        (eq-sym (eq-trans (inst (NPR.↻-ren-⇑NE ρ υ)) 
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