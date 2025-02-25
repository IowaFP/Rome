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
open import Rome.Operational.Types.Theorems.Completeness.Commutativity
-- open import Rome.Operational.Types.Normal.Properties.Postulates

--------------------------------------------------------------------------------
-- Soundness of type normalization: 
-- All types are equivalent (under ≡t) to their normal forms.

infix 0 _≋_
_≋_ : ∀ {κ} → Type Δ κ → SemType Δ κ → Set
SoundKripke : Type Δ₁ (κ₁ `→ κ₂) → KripkeFunction Δ₁ κ₁ κ₂ → Set


_≋_ {κ = ★} τ V = τ ≡t ⇑ V
_≋_ {κ = L} τ V = τ ≡t ⇑ V
_≋_ {Δ₁} {κ = κ₁ `→ κ₂} f F = SoundKripke f F
_≋_ {κ = R[ κ ]} τ (left n) = τ ≡t (⇑NE n)
_≋_ {κ = R[ κ ]} τ (right (l , υ)) = (τ ≡t ⇑ (l ▹ reify υ)) × (⇑ (reify υ) ≋ υ)

SoundKripke {Δ₁ = Δ₁} {κ₁ = κ₁} {κ₂ = κ₂} f F =     
    (∀ {Δ₂} (ρ : Renaming Δ₁ Δ₂) {v V} → 
      v ≋ V → 
      ren ρ f · v ≋ renKripke ρ F ·V V)

--------------------------------------------------------------------------------
-- - Types equivalent to neutral types under ≡t reflect to equivalence under _≋_, and 
-- - Types related under _≋_ have reifications equivalent under _≡t_

reflect-≋ : ∀ {τ : Type Δ κ} {υ :  NeutralType Δ κ} → 
             τ ≡t ⇑NE υ → τ ≋ (reflect υ)
reify-≋ : ∀ {τ : Type Δ κ} {V :  SemType Δ κ} → 
              τ ≋ V → τ ≡t ⇑ (reify V)

reflect-≋ {κ = ★} e = e -- e 
reflect-≋ {κ = L} e = e -- e
reflect-≋ {κ = κ₁ `→ κ₂} {τ} {υ} e = 
    λ ρ q → reflect-≋ 
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
            (reify-≋ (e S (reflect-≋ eq-refl))) 
            eq-refl))
reify-≋ {κ = R[ κ ]} {τ} {left n} e = e 
reify-≋ {κ = R[ κ ]} {τ} {right (l , υ)} e = fst e 
        
-- -- --------------------------------------------------------------------------------
-- -- -- Equivalent types relate to the same semantic types

subst-≋ : ∀ {τ₁ τ₂ : Type Δ κ} → 
  τ₁ ≡t τ₂ → 
  {V : SemType Δ κ} → 
  τ₁ ≋ V → 
  ---------
  τ₂ ≋ V 

subst-≋ {κ = ★} {τ₁ = τ₁} {τ₂} q {V} rel = eq-trans (eq-sym q) rel
subst-≋ {κ = L} {τ₁ = τ₁} {τ₂} q {V} rel = eq-trans (eq-sym q) rel
subst-≋ {κ = κ `→ κ₁} {τ₁ = τ₁} {τ₂} q {F} rel = λ ρ {v} {V} rel-v → subst-≋ (eq-· (cong-ren-≡t ρ q) eq-refl) (rel ρ rel-v)
subst-≋ {κ = R[ κ ]} {τ₁ = τ₁} {τ₂} q {left x} rel = eq-trans (eq-sym q) rel
subst-≋ {κ = R[ κ ]} {τ₁ = τ₁} {τ₂} q {right (l , F)} (eq , rel) = eq-trans (eq-sym q) eq , rel

--------------------------------------------------------------------------------
-- Stability rule for reification

reify-stable : ∀ {v : Type Δ κ} {V : SemType Δ κ} → 
                v ≋ V →
               ⇑ (reify V) ≋ V
reify-stable {κ = κ} rel-v = subst-≋ (reify-≋ rel-v) rel-v

--------------------------------------------------------------------------------
-- renaming respects _≋_


ren-≋ : ∀ (ρ : Renaming Δ₁ Δ₂) 
           {v : Type Δ₁ κ} 
           {V : SemType Δ₁ κ} → 
           v ≋ V → 
           ren ρ v ≋ renSem ρ V
ren-≋ {κ = ★} ρ {v} {V} rel-v = eq-trans (cong-ren-≡t ρ rel-v) (eq-sym ((inst (NPR.↻-ren-⇑ ρ V))))
ren-≋ {κ = L} ρ {v} {V} rel-v = eq-trans (cong-ren-≡t ρ rel-v) (eq-sym ((inst (NPR.↻-ren-⇑ ρ V))))
ren-≋ {κ = κ `→ κ₁} ρ₁ {v₁} {V₁} rel-v₁ ρ₂ {v₂} {V₂} rel-v₂  = subst-≋ (eq-· (inst (ren-comp ρ₁ ρ₂ v₁)) eq-refl) (rel-v₁ (ρ₂ ∘ ρ₁) rel-v₂)
ren-≋ {κ = R[ κ ]} ρ {v} {left V} rel-v = eq-trans (cong-ren-≡t ρ rel-v) (eq-sym ((inst (NPR.↻-ren-⇑NE ρ V))))
ren-≋ {κ = R[ κ ]} ρ {v} {right (l , V)} (eq-v , rel-v) = 
  eq-trans 
    (cong-ren-≡t ρ eq-v) 
    (eq-▹ (inst (sym (NPR.↻-ren-⇑ ρ l))) (reify-≋ (ren-≋ ρ rel-v))) , 
    reify-stable (ren-≋ ρ rel-v)           

-- --------------------------------------------------------------------------------
-- -- Equivalent types relate to the same semantic types

-- App-≋ : ∀
--     {f : Type Δ (κ₁ `→ κ₂)}
--   → {F : SemType Δ (κ₁ `→ κ₂)}
--   → f ≋ F
--   → {τ : Type Δ κ₁}
--   → {W : SemType Δ κ₁}
--   → τ ≋ W
--     ---------------------
--   → (f · τ) ≋ (F ·V W)
-- App-≋ {F = F} sound-f rel-v = {! subst-≋ (reify-≋ (sound-f id rel-v)) (sound-f id rel-v) !}  


--------------------------------------------------------------------------------
-- Relating syntactic substitutions to semantic environments
 
SREnv : ∀ {Δ₁ Δ₂} → Substitution Δ₁ Δ₂ → Env Δ₁ Δ₂ → Set  
SREnv {Δ₁} σ η = ∀ {κ} (α : KVar Δ₁ κ) → (σ α) ≋ (η α)    

--------------------------------------------------------------------------------
-- Relating syntactic substitutions to semantic environments
 
weaken-≋ : ∀ {κ} {κ₁} {σ : Substitution Δ₁ Δ₂} {η : Env Δ₁ Δ₂} → SREnv σ η → 
           (α : KVar (Δ₁ ,, κ) κ₁) →
           lifts σ α ≋ extende (λ {κ'} v → renSem S (η v)) (reflect (` Z)) α
weaken-≋ e Z = reflect-≋ eq-refl
weaken-≋ e (S α) = ren-≋ S (e α)           
