{-# OPTIONS --allow-unsolved-metas #-}
module Rome.Operational.Types.Theorems.Stability where

open import Rome.Operational.Prelude

open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

import Rome.Operational.Types as Types
import Rome.Operational.Types.Properties as TypeProps
open import Rome.Operational.Types.Renaming using (Renaming ; _≈_ ; lift)

open import Rome.Operational.Types.Normal
open import Rome.Operational.Types.Normal.Properties.Postulates
open import Rome.Operational.Types.Normal.Properties.Renaming
open import Rome.Operational.Types.Semantic.Syntax
open import Rome.Operational.Types.Semantic.Renaming
open import Rome.Operational.Types.Semantic.NBE

open import Rome.Operational.Types.Theorems.Completeness

--------------------------------------------------------------------------------
-- - stability : ⇑ is right-inverse to ⇓ 
--     or, ⇓ is a split-monomorphism/section.
-- - stabilityNE : eval ∘ ⇑NE  = reflectNE
--   or, round trips from neutral semantic terms to semantic terms are preserved.

stability   : ∀ (τ : NormalType Δ κ) → ⇓ (⇑ τ) ≡ τ
stabilityNE : ∀ (τ : NeutralType Δ κ) → eval (⇑NE τ) (idEnv {Δ}) ≡ reflectNE τ
stability<$> : ∀ (F : NormalType Δ (κ₁ `→ κ₂)) (τ : NeutralType Δ R[ κ₁ ]) → eval (⇑NE (F <$> τ)) idEnv ≡ reflectNE (F <$> τ)
stabilityRow : ∀ (r : Row Δ R[ κ ]) → ⇓ (⇑Row r) ≡ row r

stabilityNE {κ = ★} (` x) = refl
stabilityNE {κ = L} (` x) = refl
stabilityNE {κ = κ `→ κ₁} (` x) = refl
stabilityNE {κ = R[ κ ]} (` x) = refl
stabilityNE {Δ} {★} (τ₁ · τ₂) rewrite stabilityNE τ₁ | stability τ₂ = refl
stabilityNE {Δ} {L} (τ₁ · τ₂) rewrite stabilityNE τ₁ | stability τ₂ = refl
stabilityNE {Δ} {κ `→ κ₁} (τ₁ · τ₂) rewrite stabilityNE τ₁ | stability τ₂ = refl
stabilityNE {Δ} {R[ κ ]} (τ₁ · τ₂) rewrite stabilityNE τ₁ | stability τ₂ = refl     
stabilityNE {κ = ★} (Π τ) rewrite stabilityNE τ = refl
stabilityNE {κ = L} (Π τ) rewrite stabilityNE τ = refl
stabilityNE {κ = κ `→ κ₁} (Π τ) rewrite stabilityNE τ = refl
stabilityNE {κ = R[ ★ ]} (Π τ) rewrite stabilityNE τ = refl
stabilityNE {κ = R[ L ]} (Π τ) rewrite stabilityNE τ = refl
stabilityNE {κ = R[ κ `→ κ₁ ]} (Π τ) rewrite stabilityNE τ = refl
stabilityNE {κ = R[ R[ κ ] ]} (Π τ) rewrite stabilityNE τ = refl
stabilityNE {κ = ★} (Σ τ)      rewrite stabilityNE τ  = refl
stabilityNE {κ = L} (Σ τ)       rewrite stabilityNE τ = refl
stabilityNE {κ = κ `→ κ₁} (Σ τ) rewrite stabilityNE τ = refl
stabilityNE {κ = R[ ★ ]}      (Σ τ) rewrite stabilityNE τ       = refl
stabilityNE {κ = R[ L ]}       (Σ τ) rewrite stabilityNE τ       = refl
stabilityNE {κ = R[ κ `→ κ₁ ]} (Σ τ) rewrite stabilityNE τ = refl
stabilityNE {κ = R[ R[ κ ] ]}  (Σ τ) rewrite stabilityNE τ  = refl
stabilityNE {κ = R[ κ ]} (_<$>_ {κ₁} {κ₂} F τ) = stability<$> F τ

stability<$> F τ with eval (⇑ F) idEnv | stability F
stability<$> {κ₁ = ★} F τ | left x | refl rewrite stabilityNE τ = refl
stability<$> {κ₁ = L} F τ | left x | refl rewrite stabilityNE τ = refl
stability<$> {κ₁ = κ₁ `→ κ₂} F τ | left x | refl rewrite stabilityNE τ = refl
stability<$> {κ₁ = R[ κ₁ ]} F τ | left x | refl rewrite stabilityNE τ = refl
stability<$> {κ₁ = ★} .(reify (right F)) τ | right F | refl rewrite stabilityNE τ = refl
stability<$> {κ₁ = L} .(reify (right F)) τ | right F | refl rewrite stabilityNE τ = refl 
stability<$> {κ₁ = κ₁ `→ κ₂} .(reify (right F)) τ | right F | refl rewrite stabilityNE τ = refl
stability<$> {κ₁ = R[ κ₁ ]} .(reify (right F)) τ | right F | refl rewrite stabilityNE τ = refl

stability-β : ∀ (τ : NormalType (Δ ,, κ₁) κ₂) → reify
      (eval (⇑ τ)
       (extende (λ {κ} v' → renSem S (idEnv v')) (reflectNE (` Z))))
      ≡ τ
stability-β τ = trans (reify-≋ (idext η (⇑ τ))) (stability τ)
    where
        η : Env-≋ (extende (λ v → renSem S (idEnv v)) (reflectNE (` Z))) idEnv
        η Z = reflNE-≋ (` Z)
        η (S x) = (↻-renSem-reflectNE S (` x))            

stability Unit = refl
stability {κ = ★} (ne x)       = stabilityNE x
stability {κ = L} (ne x)       = stabilityNE x
stability {κ = κ `→ κ₁} (ne x) = cong reify (stabilityNE x)
stability {κ = R[ ★ ]} (ne x)  = stabilityNE x
stability {κ = R[ L ]} (ne x)  = stabilityNE x
stability {κ   = R[ κ `→ κ₁ ]} (ne x) 
    rewrite stabilityNE x = refl
stability {κ   = R[ R[ κ ] ]} (ne x) 
    rewrite stabilityNE x  = refl
stability {κ   = κ₁ `→ κ₂} (`λ τ) = cong `λ (stability-β τ)
stability (`∀ κ τ) = cong (`∀ κ) (stability-β τ)
stability (μ (ne x)) rewrite stabilityNE x    = refl
stability (μ (`λ τ)) rewrite stability (`λ τ) = cong μ refl
stability (lab x)                             = refl
stability ⌊ τ ⌋ rewrite stability τ           = refl
stability (τ₁ `→ τ₂) 
    rewrite stability τ₁ | stability τ₂ = refl
stability (row x)                             = stabilityRow x
stability (Π x) rewrite stabilityRow x        = refl
stability (ΠL x) rewrite stabilityRow x       = refl
stability (Σ x)  rewrite stabilityRow x       = refl
stability (ΣL x) rewrite stabilityRow x = refl 

stabilityRow {κ = ★} (l ▹ τ) rewrite stability l | stability τ | ren-id l = cong row refl
stabilityRow {κ = L} (l ▹ τ) rewrite stability l | stability τ | ren-id l = cong row refl
stabilityRow {κ = κ `→ κ₁} (l ▹ ne x) rewrite stability l rewrite stabilityNE x = refl
stabilityRow {κ = κ `→ κ₁} (l ▹ F@(`λ m)) rewrite stability l | stability m = cong row (cong (_▹_ l) (cong `λ (stability-β m)))
stabilityRow {κ = R[ κ ]} (l ▹ τ) rewrite stability l | stability τ = refl
 
--------------------------------------------------------------------------------
-- idempotency

idempotency : ∀ (τ : Types.Type Δ κ) → (⇑ (⇓ (⇑ (⇓ τ)))) ≡ ⇑ (⇓ τ)
idempotency τ rewrite stability (⇓ τ) = refl

--------------------------------------------------------------------------------
-- surjectivity
--   
 
surjectivity : ∀ (τ : NormalType Δ κ) → ∃[ υ ] (⇓ υ ≡ τ)
surjectivity τ = ( ⇑ τ , stability τ ) 
     
     