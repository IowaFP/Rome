{-# OPTIONS --allow-unsolved-metas #-}
module Rome.Operational.Types.Theorems.Soundness.Relation where

open import Rome.Operational.Prelude

open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

open import Rome.Operational.Types.Syntax
open import Rome.Operational.Types.Renaming
open import Rome.Operational.Types.Properties.Renaming
open import Rome.Operational.Types.Properties.Equivalence

open import Rome.Operational.Types.Normal.Syntax
open import Rome.Operational.Types.Normal.Renaming 
open import Rome.Operational.Types.Normal.Properties.Renaming

open import Rome.Operational.Types.Semantic.Syntax
open import Rome.Operational.Types.Semantic.Renaming
open import Rome.Operational.Types.Semantic.NBE


open import Rome.Operational.Types.Equivalence
open import Rome.Operational.Types.Theorems.Completeness
open import Rome.Operational.Types.Theorems.Stability

--------------------------------------------------------------------------------
-- Soundness of type normalization: 
-- All types are equivalent (under ≡t) to their normal forms.

infix 0 ⟦_⟧≋_
⟦_⟧≋_ : ∀ {κ} → Type Δ κ → SemType Δ κ → Set
SoundKripke : Type Δ₁ (κ₁ `→ κ₂) → KripkeFunction Δ₁ κ₁ κ₂ → Set


⟦_⟧≋_ {κ = ★} τ V = τ ≡t ⇑ V
⟦_⟧≋_ {κ = L} τ V = τ ≡t ⇑ V
⟦_⟧≋_ {Δ₁} {κ = κ₁ `→ κ₂} f F = SoundKripke f F
⟦_⟧≋_ {κ = R[ κ ]} τ (left x) = τ ≡t ⇑NE x
⟦_⟧≋_ {Δ} {κ = R[ κ ]} τ (right (n , P)) = 
  Σ[ ρ ∈ SimpleRow Type Δ R[ κ ] ] 
  Σ[ pf ∈ length ρ ≡ n ] 
    (τ ≡t ⦅ ρ ⦆) ×
    (∀ (i : Fin n) → ⟦ (lookup ρ (subst-Fin (sym pf) i)) ⟧≋ (P i))

SoundKripke {Δ₁ = Δ₁} {κ₁ = κ₁} {κ₂ = κ₂} f F =     
    (∀ {Δ₂} (ρ : Renamingₖ Δ₁ Δ₂) {v V} → 
      ⟦ v ⟧≋ V → 
      ⟦ (renₖ ρ f · v) ⟧≋ (renKripke ρ F ·V V))

--------------------------------------------------------------------------------
-- - Types equivalent to neutral types under ≡t reflect to equivalence under _≋_, and 
-- - Types related under _≋_ have reifications equivalent under _≡t_

reflect-⟦⟧≋ : ∀ {τ : Type Δ κ} {υ :  NeutralType Δ κ} → 
             τ ≡t ⇑NE υ → ⟦ τ ⟧≋ (reflect υ)
reify-⟦⟧≋ : ∀ {τ : Type Δ κ} {V :  SemType Δ κ} → 
               ⟦ τ ⟧≋ V → τ ≡t ⇑ (reify V)
reifyRow-⟦⟧≋ : ∀ (xs : SimpleRow Type Δ R[ κ ]) → 
                 (n : ℕ) → 
                 (P : Fin n → SemType Δ κ) → 
                 ⟦ ⦅ xs ⦆ ⟧≋ right ((n , P)) → 
                 xs ≡r ⇑Row (reifyRow' n P)

-- sameRow : ∀ (xs : SimpleRow Type Δ R[ κ ]) → 
--                  (n : ℕ) → 
--                  (P : Fin n → SemType Δ κ) → 
--                  ⟦ ⦅ xs ⦆ ⟧≋ right ((n , P)) → 
--                  xs ≡ evalRow 

reflect-⟦⟧≋ {κ = ★} e = e  
reflect-⟦⟧≋ {κ = L} e = e 
reflect-⟦⟧≋ {κ = κ₁ `→ κ₂} {τ} {υ} e = 
    λ ρ q → reflect-⟦⟧≋ 
    (eq-· 
        (eq-sym (eq-trans (inst (↻-ren-⇑NE ρ υ)) 
            (renₖ-≡t ρ (eq-sym e)))) 
        (reify-⟦⟧≋ q)) 
reflect-⟦⟧≋ {κ = R[ κ ]} e = e

reify-⟦⟧≋ {κ = ★} {τ} {V} e = e 
reify-⟦⟧≋ {κ = L} {τ} {V} e = e
reify-⟦⟧≋ {κ = κ₁ `→ κ₂} {τ} {F} e = 
    eq-trans 
        eq-η 
        (eq-λ (eq-trans 
            (reify-⟦⟧≋ (e S (reflect-⟦⟧≋ eq-refl))) 
            eq-refl))

reify-⟦⟧≋ {κ = R[ κ ]} {τ} {left x} e = e
reify-⟦⟧≋ {κ = R[ κ ]} {τ} {right (n , P)} (xs , refl , eq , I) = eq-trans eq (eq-row (reifyRow-⟦⟧≋ xs n P (xs , refl , eq-refl , I)))
-- reify-⟦⟧≋ {κ = R[ κ ]} {τ} {right (0 , P)} ([] , refl , eq , I) = eq
-- reify-⟦⟧≋ {κ = R[ κ ]} {τ} {right (suc n , P)} ((x ∷ xs) , pf@refl , eq , I) = 
--   eq-trans 
--     eq 
--     (eq-row 
--       (eq-cons 
--         (reify-⟦⟧≋ (I fzero)) 
--         (reifyRow-⟦⟧≋ xs n (P ∘ fsuc) (xs , refl , eq-refl , λ { i → I (fsuc i) }))))

--------------------------------------------------------------------------------
-- Properties of row equivalence & reification lemma for rows

empty-unique-t : ∀ (xs : SimpleRow Type Δ R[ κ ]) → ⦅ [] ⦆ ≡t ⦅ xs ⦆ → xs ≡ []
empty-unique-t  xs eq with completeness eq 
empty-unique-t [] eq | _ = refl 

empty-unique-r : ∀ (xs : SimpleRow Type Δ R[ κ ]) → [] ≡r xs → xs ≡ []
empty-unique-r xs eq with completeness (eq-row eq)
empty-unique-r [] eq | _ = refl 

-- canonical-⦅⦆ : ∀ {xs : SimpleRow Type Δ R[ κ ]} {ρ : Type Δ R[ κ ]} → ⦅ xs ⦆ ≡t ρ → ∃[ ys ] ((⦅ xs ⦆ ≡t ⦅ ys ⦆) × ρ ≡ ⦅ ys ⦆) -- (xs ≡r zs) × (zs ≡r ys) 
inj-⦅⦆t : ∀ {xs ys : SimpleRow Type Δ R[ κ ]} → ⦅ xs ⦆ ≡t ⦅ ys ⦆ → xs ≡r ys
inj-⦅⦆t {xs = xs} {ys} eq-refl = eq-reflᵣ xs
inj-⦅⦆t {xs = xs} {ys} (eq-sym eq) = eq-symᵣ (inj-⦅⦆t eq)
inj-⦅⦆t {xs = xs} {ys} (eq-trans {τ₂ = τ₂} eq₁ eq₂) with ⇓ τ₂ | completeness eq₁
... | ⦅ x₁ ⦆ | d = {!   !}
inj-⦅⦆t {xs = xs} {ys} (eq-row eq) = eq


-- inj-⦅⦆t {xs = xs} {ys} eq with completeness eq
-- ... | _ = {! eq  !} 


reifyRow-⟦⟧≋ xs n P (ys , refl , eq , I) with completeness eq
reifyRow-⟦⟧≋ [] .(length []) P ([] , refl , eq , I) | _ = eq-[]
reifyRow-⟦⟧≋ (x ∷ xs) .(length (y ∷ ys)) P (y ∷ ys , refl , eq , I) | _ = {! eq  !} -- eq-cons (eq-trans {!   !} (reify-⟦⟧≋ (I fzero))) {!   !}

-- -- -- --------------------------------------------------------------------------------
-- -- -- -- Equivalent types relate to the same semantic types

-- subst-⟦⟧≋ : ∀ {τ₁ τ₂ : Type Δ κ} → 
--   τ₁ ≡t τ₂ → 
--   {V : SemType Δ κ} → 
--   ⟦ τ₁ ⟧≋ V → 
--   ---------
--   ⟦ τ₂ ⟧≋ V 

-- subst-⟦⟧≋ {κ = ★} {τ₁ = τ₁} {τ₂} q {V} rel = eq-trans (eq-sym q) rel
-- subst-⟦⟧≋ {κ = L} {τ₁ = τ₁} {τ₂} q {V} rel = eq-trans (eq-sym q) rel
-- subst-⟦⟧≋ {κ = κ `→ κ₁} {τ₁ = τ₁} {τ₂} q {F} rel = λ ρ {v} {V} rel-v → subst-⟦⟧≋ (eq-· (renₖ-≡t ρ q) eq-refl) (rel ρ rel-v)
-- subst-⟦⟧≋ {κ = R[ κ ]} {τ₁ = τ₁} {τ₂} q {just (left x)} rel = eq-trans (eq-sym q) rel
-- subst-⟦⟧≋ {κ = R[ κ ]} {τ₁ = τ₁} {τ₂} q {just (right (l , F))} (eq , rel) = eq-trans (eq-sym q) eq , rel
-- subst-⟦⟧≋ {κ = R[ κ ]} {τ₁ = τ₁} {τ₂} q {nothing} p = eq-trans (eq-sym q) p

-- --------------------------------------------------------------------------------
-- -- Stability rule for reification

-- refl-⟦⟧≋ : ∀ {v : Type Δ κ} {V : SemType Δ κ} → 
--                 ⟦ v ⟧≋ V  →
--                ⟦ ⇑ (reify V) ⟧≋ V 
-- refl-⟦⟧≋ {κ = κ} rel-v = subst-⟦⟧≋ (reify-⟦⟧≋ rel-v) rel-v

-- --------------------------------------------------------------------------------
-- -- Stability rule for reification

-- -- map-⟦⟧≋ : ∀ {f : Type Δ (κ₁ `→ κ₂)} {F : SemType Δ (κ₁ `→ κ₂)} → 
-- --           ⟦ f ⟧≋ F → 
-- --           {v : Type Δ R[ κ₁ ]} {V : SemType Δ R[ κ₁ ]} → 
-- --           ⟦ v ⟧≋ V → 
-- --           ⟦ f <$> v ⟧≋ F <$>V V
-- -- map-⟦⟧≋ {f = f} {F} rel-f {v} {just (left x)} rel-v = 
-- --   eq-<$> 
-- --     (eq-trans eq-η (eq-λ (reify-⟦⟧≋ {! reflect-⟦⟧≋ eq-β  !}))) 
-- --     rel-v
-- -- map-⟦⟧≋ {f = f} {F} rel-f {v} {just (right y)} rel-v = {!   !}
-- -- map-⟦⟧≋ {f = f} {F} rel-f {v} {nothing} rel-v = {!   !} 
          
-- --------------------------------------------------------------------------------
-- -- renaming respects _≋_


-- ren-⟦⟧≋ : ∀ (ρ : Renamingₖ Δ₁ Δ₂) 
--            {v : Type Δ₁ κ} 
--            {V : SemType Δ₁ κ} → 
--            ⟦ v ⟧≋ V → 
--            ⟦ renₖ ρ v ⟧≋ renSem ρ V
-- ren-⟦⟧≋ {κ = ★} ρ {v} {V} rel-v = eq-trans (renₖ-≡t ρ rel-v) (eq-sym ((inst (↻-ren-⇑ ρ V))))
-- ren-⟦⟧≋ {κ = L} ρ {v} {V} rel-v = eq-trans (renₖ-≡t ρ rel-v) (eq-sym ((inst (↻-ren-⇑ ρ V))))
-- ren-⟦⟧≋ {κ = κ `→ κ₁} ρ₁ {v₁} {V₁} rel-v₁ ρ₂ {v₂} {V₂} rel-v₂  = subst-⟦⟧≋ (eq-· (inst (renₖ-comp ρ₁ ρ₂ v₁)) eq-refl) (rel-v₁ (ρ₂ ∘ ρ₁) rel-v₂)
-- ren-⟦⟧≋ {κ = R[ κ ]} ρ {v} {just (left V)} rel-v = eq-trans (renₖ-≡t ρ rel-v) (eq-sym ((inst (↻-ren-⇑NE ρ V))))
-- ren-⟦⟧≋ {κ = R[ κ ]} ρ {v} {just (right (l , V))} (eq-v , rel-v) = 
--   eq-trans 
--     (renₖ-≡t ρ eq-v) 
--     (eq-▹ (inst (sym (↻-ren-⇑ ρ l))) (reify-⟦⟧≋ (ren-⟦⟧≋ ρ rel-v))) , 
--     refl-⟦⟧≋ (ren-⟦⟧≋ ρ rel-v)           
-- ren-⟦⟧≋ {κ = R[ κ ]} ρ {v} {nothing} rel-v = renₖ-≡t ρ rel-v

-- --------------------------------------------------------------------------------
-- -- Relating syntactic substitutions to semantic environments
 
-- ⟦_⟧≋e_ : ∀ {Δ₁ Δ₂} → Substitutionₖ Δ₁ Δ₂ → Env Δ₁ Δ₂ → Set  
-- ⟦_⟧≋e_ {Δ₁} σ η = ∀ {κ} (α : KVar Δ₁ κ) → ⟦ (σ α) ⟧≋ (η α)

-- --------------------------------------------------------------------------------
-- -- Extended substitutions relate to extended environments

-- extend-⟦⟧≋ : ∀ {κ} {σ : Substitutionₖ Δ₁ Δ₂} {η : Env Δ₁ Δ₂} → 
--              ⟦ σ ⟧≋e η →
--              ∀ {τ : Type Δ₂ κ} {V : SemType Δ₂ κ} → 
--              ⟦ τ ⟧≋ V → 
--              ⟦ (extendₖ σ τ) ⟧≋e (extende η V)
-- extend-⟦⟧≋ p q Z = q
-- extend-⟦⟧≋ p q (S x) = p x


-- --------------------------------------------------------------------------------
-- -- Weakened substitutions relate to weakened environments
 
-- weaken-⟦⟧≋ : ∀ {κ} {σ : Substitutionₖ Δ₁ Δ₂} {η : Env Δ₁ Δ₂} → 
--            ⟦ σ ⟧≋e η → 
--            ⟦ liftsₖ {κ = κ} σ ⟧≋e (extende (λ {κ'} v → renSem S (η v)) (reflect (` Z)))
-- weaken-⟦⟧≋ e Z = reflect-⟦⟧≋ eq-refl
-- weaken-⟦⟧≋ e (S α) = ren-⟦⟧≋ S (e α)           

-- --------------------------------------------------------------------------------
-- -- 

-- substEnv-⟦⟧≋ : ∀ {σ₁ σ₂ : Substitutionₖ Δ₁ Δ₂} {η : Env Δ₁ Δ₂} → 
--              (∀ {κ} (x : KVar Δ₁ κ) → σ₁ x ≡ σ₂ x) →
--              ⟦ σ₁ ⟧≋e η →
--              ⟦ σ₂ ⟧≋e η
-- substEnv-⟦⟧≋ eq rel x rewrite sym (eq x) = rel x
   
   