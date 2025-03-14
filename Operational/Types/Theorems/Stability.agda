{-# OPTIONS --allow-unsolved-metas #-}
module Rome.Operational.Types.Theorems.Stability where

open import Rome.Operational.Prelude

open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

open import Rome.Operational.Types
open import Rome.Operational.Types.Renaming
open import Rome.Operational.Types.Equivalence

open import Rome.Operational.Types.Normal.Syntax
open import Rome.Operational.Types.Normal.Properties.Renaming

open import Rome.Operational.Types.Semantic.Syntax
open import Rome.Operational.Types.Semantic.Renaming
open import Rome.Operational.Types.Semantic.NBE

open import Rome.Operational.Types.Theorems.Completeness
open import Rome.Operational.Types.Theorems.Soundness

--------------------------------------------------------------------------------
-- - stability : ⇑ is right-inverse to ⇓ 
--     or, ⇓ is a split-monomorphism/section.
-- - stabilityNE : eval ∘ ⇑NE  = reflect
--   or, round trips from neutral semantic terms to semantic terms are preserved.


stability   : ∀ (τ : NormalType Δ κ) → ⇓ (⇑ τ) ≡ τ
stabilityNE : ∀ (τ : NeutralType Δ κ) → eval (⇑NE τ) (idEnv {Δ}) ≡ reflect τ
stabilityPred : ∀ (π : NormalPred Δ R[ κ ]) → evalPred (⇑Pred π) idEnv ≡ π

stabilityNE {κ = κ} (` x) = refl
stabilityNE {Δ} {κ} (τ₁ · τ₂) 
  rewrite stabilityNE τ₁ | stability τ₂ = cong reflect (cong (_· τ₂) (renₖNE-id τ₁))
stabilityNE {κ = R[ κ ]} (F <$> τ) 
  rewrite stabilityNE τ | stability F = refl

stability-β : ∀ (τ : NormalType (Δ ,, κ₁) κ₂) → reify
      (eval (⇑ τ)
       (extende (λ {κ} v' → renSem S (idEnv v')) (reflect (` Z))))
      ≡ τ
stability-β {Δ = Δ} τ = 
    trans (reify-≋ (idext η (⇑ τ))) (stability τ)
    where
        η : Env-≋ (extende (λ {κ} v' → renSem S (idEnv v')) (reflect (` Z))) idEnv
        η Z = reflect-≋ refl
        η (S x) = ↻-ren-reflect S (` x)
  
stability {κ = ★} (ne x) = stabilityNE x
stability {κ = L} (ne x)       = stabilityNE x
stability {_} {κ `→ κ₁} (ne x {()})
stability {κ = R[ κ ]} (ne x) rewrite stabilityNE x = refl
stability {κ   = κ₁ `→ κ₂} (`λ τ) = cong `λ (stability-β τ)
stability (`∀ κ τ) = cong (`∀ κ) (stability-β τ)
stability (μ τ)  rewrite stability τ = refl
stability (lab x)                             = refl
stability ⌊ τ ⌋ rewrite stability τ           = refl
stability (τ₁ `→ τ₂) 
    rewrite stability τ₁ | stability τ₂ = refl
stability (π ⇒ τ) rewrite stabilityPred π | stability τ = refl    
stability (l ▹ τ) rewrite stability l | stability τ = refl 
stability ε = refl
stability (Π x)  rewrite stability x = refl
stability (ΠL x) rewrite stability x = refl
stability (Σ x)  rewrite stability x = refl
stability (ΣL x) rewrite stability x = refl

stabilityPred (ρ₁ · ρ₂ ~ ρ₃) 
    rewrite stability ρ₁ | stability ρ₂ | stability ρ₃ = refl
stabilityPred (ρ₁ ≲ ρ₂) 
    rewrite stability ρ₁ | stability ρ₂ = refl

--------------------------------------------------------------------------------
-- idempotency
 
idempotency : ∀ (τ : Type Δ κ) → (⇑ (⇓ (⇑ (⇓ τ)))) ≡ ⇑ (⇓ τ)
idempotency τ rewrite stability (⇓ τ) = refl

--------------------------------------------------------------------------------
-- surjectivity
--   
 
surjectivity : ∀ (τ : NormalType Δ κ) → ∃[ υ ] (⇓ υ ≡ τ)
surjectivity τ = ( ⇑ τ , stability τ ) 
     

--------------------------------------------------------------------------------
-- Another way of stating stability

stability' : ∀ (τ : NormalType Δ κ) → reify (⇈ τ) ≡ τ 
stability' = stability

--------------------------------------------------------------------------------
-- Injectivity of embedding

⇑-inj : ∀ (x y : NormalType Δ κ) → ⇑ x ≡ ⇑ y → x ≡ y
⇑-inj x y eq = 
  subst 
    (λ a → a ≡ y) 
    (stability x) 
  (subst (λ b → ⇓ (⇑ x) ≡ b) 
    (stability y) 
    (reify-≋ (fundC {τ₁ = ⇑ x} {τ₂ = ⇑ y} idEnv-≋ (inst eq)))) 

--------------------------------------------------------------------------------
-- Flippy floppy
-- (rename me)

maybs : ∀ (x : NormalType Δ κ) (y : Type Δ κ) → ⇑ x ≡ y → x ≡ ⇓ y 
maybs x y eq = trans (sym (stability x)) (cong ⇓ eq)
maybs2 : ∀ (x : NormalType Δ κ) (y : Type Δ κ) → x ≡ ⇓ y → ⇑ x ≡t y
maybs2 x y eq = eq-trans (inst (cong ⇑ eq)) (eq-sym (soundness y)) 

     
 
 
 