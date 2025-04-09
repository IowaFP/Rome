{-# OPTIONS --allow-unsolved-metas #-}
module Rome.Operational.Types.Theorems.Soundness.Relation where

open import Rome.Operational.Prelude

open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

open import Rome.Operational.Types.Syntax
open import Rome.Operational.Types.Substitution
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
open import Rome.Operational.Types.Properties.Equivalence
open import Rome.Operational.Types.Theorems.Completeness
open import Rome.Operational.Types.Theorems.Stability

--------------------------------------------------------------------------------
-- Soundness of type normalization: 
-- All types are equivalent (under ≡t) to their normal forms.

infix 0 ⟦_⟧≋_
⟦_⟧≋_ : ∀ {κ} → Type Δ κ → SemType Δ κ → Set
SoundKripke : Type Δ₁ (κ₁ `→ κ₂) → KripkeFunction Δ₁ κ₁ κ₂ → Set


⟦_⟧≋_ {κ = ★} τ₁ τ₂ = τ₁ ≡t ⇑ τ₂
⟦_⟧≋_ {κ = L} τ₁ τ₂ = τ₁ ≡t ⇑ τ₂
⟦_⟧≋_ {Δ₁} {κ = κ₁ `→ κ₂} f F = SoundKripke f F
⟦_⟧≋_ {κ = R[ κ ]} τ (left x) = τ ≡t ⇑NE x
⟦_⟧≋_ {Δ} {κ = R[ κ ]} τ (right (n , P)) =
  (τ ≡t ⦅ ⇑Row (reifyRow (n , P)) ⦆)
  -- Σ[ pf ∈ n ≡ length (⇑Row (reifyRow (n , P))) ]
  --   (τ ≡t ⦅ ⇑Row (reifyRow (n , P)) ⦆) × 
  --   (∀ (i : Fin n) → 
  --       ⟦ (lookup (⇑Row (reifyRow (n , P))) (cast pf i)) ⟧≋ P i)

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
reify-⟦⟧≋ {κ = R[ κ ]} {τ} {right (zero , P)} eq = eq
reify-⟦⟧≋ {κ = R[ κ ]} {τ} {right (suc n , P)} eq = eq-trans eq (eq-row (eq-cons eq-refl (eq-reflᵣ _)))

--------------------------------------------------------------------------------
-- Equivalent types relate to the same semantic types

subst-⟦⟧≋ : ∀ {τ₁ τ₂ : Type Δ κ} → 
  τ₁ ≡t τ₂ → 
  {V : SemType Δ κ} → 
  ⟦ τ₁ ⟧≋ V → 
  ---------
  ⟦ τ₂ ⟧≋ V 

subst-⟦⟧≋ {κ = ★} {τ₁ = τ₁} {τ₂} q {V} rel = eq-trans (eq-sym q) rel
subst-⟦⟧≋ {κ = L} {τ₁ = τ₁} {τ₂} q {V} rel = eq-trans (eq-sym q) rel
subst-⟦⟧≋ {κ = κ `→ κ₁} {τ₁ = τ₁} {τ₂} q {F} rel = λ ρ {v} {V} rel-v → subst-⟦⟧≋ (eq-· (renₖ-≡t ρ q) eq-refl) (rel ρ rel-v)
subst-⟦⟧≋ {κ = R[ κ ]} {τ₁ = τ₁} {τ₂} q {left x} rel = eq-trans (eq-sym q) rel
subst-⟦⟧≋ {κ = R[ κ ]} {τ₁ = τ₁} {τ₂} q {right (n , P)} eq = eq-sym (eq-trans (eq-sym eq) q)

--------------------------------------------------------------------------------
-- Stability rule for reification

refl-⟦⟧≋ : ∀ {v : Type Δ κ} {V : SemType Δ κ} → 
                ⟦ v ⟧≋ V  →
               ⟦ ⇑ (reify V) ⟧≋ V 
refl-⟦⟧≋ {κ = κ} rel-v = subst-⟦⟧≋ (reify-⟦⟧≋ rel-v) rel-v


-- wellFuckit : ∀ (ρ : Renamingₖ Δ₁ Δ₂) (V : SemType Δ₁ κ) → 
--                ⇑ (renₖNF ρ (reify V)) ≡
--                ⇑ (reify (renSem ρ V))
-- wellFuckit {κ = ★} ρ V = refl
-- wellFuckit {κ = L} ρ V = refl
-- wellFuckit {κ = κ₁ `→ κ₂} ρ F = cong `λ (trans (wellFuckit (liftₖ ρ) (F S (idEnv Z))) {!!})
-- wellFuckit {κ = R[ κ ]} ρ (left x) = refl
-- wellFuckit {κ = R[ κ ]} ρ (right (n , P)) = cong ⦅_⦆ (cong ⇑Row {!!})
-- ren-row-reify : ∀ (ρ : Renamingₖ Δ₁ Δ₂) (n : ℕ) (P : Fin n → SemType Δ₁ κ) → 
--                 renRowₖ ρ (⇑Row (reifyRow (n , P))) ≡r
--                 ⇑Row (reifyRow (n , (λ x → renSem ρ (P x))))            
-- ren-row-reify ρ zero P = eq-[]
-- ren-row-reify ρ (suc n) P = eq-cons (eq-trans (eq-sym (inst (↻-ren-⇑ ρ (reify (P fzero))))) {!↻-ren-reify!}) {!!}
    
-- --------------------------------------------------------------------------------
-- -- 1. (cr-to-sr) Equivalent semantic types are related under SR
-- -- 2. (sr-to-cr) If type v relates to SemType V then the evaluation of v is 
-- --    equivalent to V.

-- cr-to-sr : ∀ {V₁ V₂ : SemType Δ κ} → 
--             V₁ ≋ V₂ → 
--             ⟦ ⇑ (reify V₁) ⟧≋ V₂ 

-- sr-to-cr : ∀ {v : Type Δ κ} {V : SemType Δ κ} → 
--         ⟦ v ⟧≋ V → 
--         eval v idEnv ≋ V 

-- --------------------------------------------------------------------------------
-- -- Any semantic type in the soundness relation is equivalent to itself 
-- -- under the completeness relation.

-- sr-to-cr-refl : ∀ {v : Type Δ κ} {V : SemType Δ κ} → 
--         ⟦ v ⟧≋ V → 
--         V ≋ V 

-- sr-to-cr-refl rel = refl-≋ᵣ (sr-to-cr rel)

-- --------------------------------------------------------------------------------
-- -- cr-to-sr definition

-- cr-to-sr {κ = ★} refl = eq-refl
-- cr-to-sr {κ = L} refl = eq-refl
-- cr-to-sr {κ = κ₁ `→ κ₂} {V₁ = F} {V₂ = G} rel-F = λ ρ {v₂} {V₂} rel-v₂ → subst-⟦⟧≋ {! reify-≋ rel-F  !} {!   !} -- subst-⟦⟧≋ (eq-· {! eq-η  !} {!   !}) {!   !}
-- cr-to-sr {κ = R[ κ ]} rel-V = {!   !}   

-- --------------------------------------------------------------------------------
-- -- sr-to-cr definition

-- sr-to-cr {κ = ★} {v = v} {V} rel-V = trans (completeness rel-V) (stability V)
-- sr-to-cr {κ = L} {v = v} {V} rel-V = trans (completeness rel-V) (stability V)
-- sr-to-cr {κ = κ₁ `→ κ₂} {v = f} {F} rel-F = 
--   fst (↻-renSem-eval id f idEnv-≋) , 
--   (λ ρ₁ ρ₂ V₁ V₂ x → 
--     trans-≋ 
--       (trans-≋ 
--         (ren-≋ ρ₂ (sym-≋ (sr-to-cr (rel-F ρ₁  {⇑ (reify V₁)} {V₁} (cr-to-sr (refl-≋ₗ x)))))) 
--         (trans-≋ 
--           (↻-renSem-eval ρ₂ (renₖ ρ₁ f · (⇑ (reify V₁))) idEnv-≋)
--           (trans-≋ 
--             (cong-App 
--               {V₁ = eval (renₖ ρ₁ f) (renSem ρ₂ ∘ idEnv)} 
--               {eval f (idEnv ∘ ρ₂ ∘ ρ₁)} 
--               (↻-renₖ-eval ρ₁ f {η₁ = renSem ρ₂ ∘ idEnv} {idEnv ∘ ρ₂} (↻-ren-reflect ρ₂ ∘ `) ) 
--               (idext (ren-≋ ρ₂ ∘ idEnv-≋ ) (⇑ (reify V₁))) ) 
--             (sym-≋ 
--               (cong-App 
--                 {V₁ = eval (renₖ (ρ₂ ∘ ρ₁) f) idEnv} 
--                 (↻-renₖ-eval (ρ₂ ∘ ρ₁) f idEnv-≋) 
--                 {eval (⇑ (reify (renSem ρ₂ V₁))) idEnv} 
--                 {eval (⇑ (reify V₁)) (renSem ρ₂ ∘ idEnv)} 
--                 (trans-≋ 
--                   (subst 
--                     (λ y → eval (⇑ y) idEnv ≋ renSem ρ₂ (eval (⇑ (reify V₁)) idEnv)) 
--                     (↻-ren-reify ρ₂ (refl-≋ₗ x)) 
--                     (subst 
--                       (λ y → eval y idEnv ≋ renSem ρ₂ (eval (⇑ (reify V₁)) idEnv)) 
--                       (sym (↻-ren-⇑ ρ₂ (reify V₁))) 
--                       (trans-≋ 
--                         (↻-renₖ-eval ρ₂ (⇑ (reify V₁)) idEnv-≋) 
--                         (trans-≋ 
--                           (idext (sym-≋ ∘ ↻-ren-reflect ρ₂ ∘ `) (⇑ (reify V₁))) 
--                           (sym-≋ (↻-renSem-eval ρ₂ (⇑ (reify V₁)) idEnv-≋)))))) 
--                   (↻-renSem-eval ρ₂ (⇑ (reify V₁)) idEnv-≋ ))))))) 
--       (sr-to-cr (rel-F (ρ₂ ∘ ρ₁) {⇑ (reify (renSem ρ₂ V₁))} {renSem ρ₂ V₂} (cr-to-sr (ren-≋ ρ₂ x))))  ) , 
--   λ ρ {V₁} {V₂} rel-V → trans-≋ {! fundC {τ₁ = f} {f} idEnv-≋ eq-refl !} (sr-to-cr-refl (rel-F ρ (cr-to-sr rel-V))) 
-- sr-to-cr {κ = R[ κ ]} {v = v} {left x} rel-V = {!   !}
-- sr-to-cr {κ = R[ κ ]} {v = v} {right y} rel-V = {!   !}



--------------------------------------------------------------------------------
-- renaming respects _≋_

ren-⟦⟧≋ : ∀ (ρ : Renamingₖ Δ₁ Δ₂) 
           {v : Type Δ₁ κ} 
           {V : SemType Δ₁ κ} → 
           ⟦ v ⟧≋ V → 
           ⟦ renₖ ρ v ⟧≋ renSem ρ V
ren-⟦⟧≋ {κ = ★} ρ {v} {V} rel-v = eq-trans (renₖ-≡t ρ rel-v) (eq-sym ((inst (↻-ren-⇑ ρ V))))
ren-⟦⟧≋ {κ = L} ρ {v} {V} rel-v = eq-trans (renₖ-≡t ρ rel-v) (eq-sym ((inst (↻-ren-⇑ ρ V))))
ren-⟦⟧≋ {κ = κ `→ κ₁} ρ₁ {v₁} {V₁} rel-v₁ ρ₂ {v₂} {V₂} rel-v₂  = subst-⟦⟧≋ (eq-· (inst (renₖ-comp ρ₁ ρ₂ v₁)) eq-refl) (rel-v₁ (ρ₂ ∘ ρ₁) rel-v₂)
ren-⟦⟧≋ {κ = R[ κ ]} ρ {v} {left V} rel-v = eq-trans (renₖ-≡t ρ rel-v) (eq-sym ((inst (↻-ren-⇑NE ρ V))))
ren-⟦⟧≋ {κ = R[ κ ]} ρ {v} {right (n , P)} eq = eq-trans (renₖ-≡t ρ eq) (eq-row {!!}) -- (eq-trans (renₖ-≡t ρ eq) (inst (cong ⦅_⦆ (trans (sym (↻-ren-⇑Row ρ _)) (cong ⇑Row (↻-ren-reifyRow P P ρ I)))))) , (λ { i → ren-≋ ρ (I i) })
  -- sym (length-⇑-reify n _) , 
  -- eq-trans (renₖ-≡t ρ eq) (inst (cong ⦅_⦆ (trans (sym (↻-ren-⇑Row ρ _)) (cong ⇑Row {!↻-ren-reifyRow P P ρ !})))) , 
  -- λ { fzero → subst-⟦⟧≋ (reify-⟦⟧≋ (ren-⟦⟧≋ ρ {⇑ (reify (P fzero))} {P fzero} (refl-⟦⟧≋ (I fzero)))) (ren-⟦⟧≋ ρ (refl-⟦⟧≋ (I fzero)))
  --   ; (fsuc x) → subst-⟦⟧≋ {!   !} (ren-⟦⟧≋ ρ (I (fsuc x))) }
    
--------------------------------------------------------------------------------
-- Relating syntactic substitutions to semantic environments
 
⟦_⟧≋e_ : ∀ {Δ₁ Δ₂} → Substitutionₖ Δ₁ Δ₂ → Env Δ₁ Δ₂ → Set  
⟦_⟧≋e_ {Δ₁} σ η = ∀ {κ} (α : KVar Δ₁ κ) → ⟦ (σ α) ⟧≋ (η α)

--------------------------------------------------------------------------------
-- Extended substitutions relate to extended environments

extend-⟦⟧≋ : ∀ {κ} {σ : Substitutionₖ Δ₁ Δ₂} {η : Env Δ₁ Δ₂} → 
             ⟦ σ ⟧≋e η →
             ∀ {τ : Type Δ₂ κ} {V : SemType Δ₂ κ} → 
             ⟦ τ ⟧≋ V → 
             ⟦ (extendₖ σ τ) ⟧≋e (extende η V)
extend-⟦⟧≋ p q Z = q
extend-⟦⟧≋ p q (S x) = p x


--------------------------------------------------------------------------------
-- Weakened substitutions relate to weakened environments
 
weaken-⟦⟧≋ : ∀ {κ} {σ : Substitutionₖ Δ₁ Δ₂} {η : Env Δ₁ Δ₂} → 
           ⟦ σ ⟧≋e η → 
           ⟦ liftsₖ {κ = κ} σ ⟧≋e (extende (λ {κ'} v → renSem S (η v)) (reflect (` Z)))
weaken-⟦⟧≋ e Z = reflect-⟦⟧≋ eq-refl
weaken-⟦⟧≋ e (S α) = ren-⟦⟧≋ S (e α)           

--------------------------------------------------------------------------------
-- 

substEnv-⟦⟧≋ : ∀ {σ₁ σ₂ : Substitutionₖ Δ₁ Δ₂} {η : Env Δ₁ Δ₂} → 
             (∀ {κ} (x : KVar Δ₁ κ) → σ₁ x ≡ σ₂ x) →
             ⟦ σ₁ ⟧≋e η →
             ⟦ σ₂ ⟧≋e η
substEnv-⟦⟧≋ eq rel x rewrite sym (eq x) = rel x
     
      
 
