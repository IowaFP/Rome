{-# OPTIONS --allow-unsolved-metas #-}
module Rome.Operational.Types.Theorems.Stability where

open import Rome.Operational.Prelude

open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

open import Rome.Operational.Types.Syntax
open import Rome.Operational.Types.Renaming
open import Rome.Operational.Types.Equivalence.Relation

open import Rome.Operational.Types.Normal.Syntax
open import Rome.Operational.Types.Normal.Properties.Renaming

open import Rome.Operational.Types.Semantic.Syntax
open import Rome.Operational.Types.Semantic.Renaming
open import Rome.Operational.Types.Semantic.NBE

open import Rome.Operational.Types.Theorems.Completeness

--------------------------------------------------------------------------------
-- - stability : ⇑ is right-inverse to ⇓ 
--     or, ⇓ is a split-monomorphism/section.
-- - stabilityNE : eval ∘ ⇑NE  = reflect
--   or, round trips from neutral semantic terms to semantic terms are preserved.

stability   : ∀ (τ : NormalType Δ κ) → ⇓ (⇑ τ) ≡ τ
stabilityNE : ∀ (τ : NeutralType Δ κ) → eval (⇑NE τ) (idEnv {Δ}) ≡ reflect τ
stabilityNE' : ∀ (τ : NeutralType Δ κ) → reify (eval (⇑NE τ) (idEnv {Δ})) ≡ reify (reflect τ)
stabilityPred : ∀ (π : NormalPred Δ R[ κ ]) → evalPred (⇑Pred π) idEnv ≡ π
stabilityRow : ∀ (ρ : SimpleRow NormalType Δ R[ κ ]) → reifyRow (evalRow (⇑Row ρ) idEnv) ≡ ρ

stabilityNE {κ = κ} (` x) = refl
stabilityNE {Δ} {κ} (τ₁ · τ₂) rewrite stabilityNE τ₁ | stability τ₂ = cong reflect (cong₂ _·_ (renₖNE-id τ₁) refl) 
stabilityNE {κ = R[ κ ]} (F <$> τ) 
  rewrite stabilityNE τ | stability F = refl 
stabilityNE (ρ₂ ─₁ ρ₁)  with eval (⇑NE ρ₂) idEnv | eval (⇑ ρ₁) idEnv | stabilityNE ρ₂ | stability ρ₁ 
... | left (left ρ₂) | left (left x₁) | refl | refl = refl
... | left (left ρ₂) | left (right y₁) | refl | refl = refl
... | _ | right _ | refl | refl = refl
stabilityNE (ρ₂ ─₂ ρ₁) with eval (⇑ ρ₂) idEnv | eval (⇑NE ρ₁) idEnv | stability ρ₂ | stabilityNE ρ₁  
stabilityNE ((ρ₂ ─₂ ρ₁) {()}) | left (left x₁) | left (left ρ₁) | refl | refl
stabilityNE ((ρ₂ ─₂ ρ₁) {()}) | left (right y₁) | left (left ρ₁) | refl | refl
... | right y₁ | _ | refl | refl = refl
stabilityNE (l ▹ₙ τ) with eval (⇑NE l) idEnv | isNeutral? (eval (⇑NE l) idEnv) | stabilityNE l
... | ne x₁ | yes p | refl = {!!} -- cong left (cong₂ _▹ₙ_ refl (stability τ))
... | .(ne l) | no q | refl = ⊥-elim (q tt)

stabilityNE' (` α) = refl
stabilityNE' {κ = κ} (τ · τ₁) = {!stability τ₁!}
stabilityNE' (φ <$> τ) = {!!}
stabilityNE' (l ▹ₙ τ) with eval (⇑NE l) idEnv | isNeutral? (eval (⇑NE l) idEnv) | stabilityNE' l
... | ne x₂ | yes p | refl = cong-ne (cong (l ▹ₙ_) (stability τ))
... | ne x₁ | no p | q = ⊥-elim (p tt)
stabilityNE' (τ ─₁ ρ) = {!!}
stabilityNE' (ρ ─₂ τ) = {!!}


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
  
stability {κ = ★} (ne x) = {! !}
stability {κ = L} (ne x) rewrite stabilityNE x        = refl
stability {_} {κ `→ κ₁} (ne x {()})
stability {κ = R[ κ ]} (ne x) rewrite stabilityNE x = refl
stability {κ   = κ₁ `→ κ₂} (`λ τ) = cong `λ (stability-β τ)
stability (`∀ τ) = cong (`∀) (stability-β τ)
stability (μ τ)  rewrite stability τ = refl
stability ⌊ τ ⌋ rewrite stability τ           = refl
stability (τ₁ `→ τ₂) 
    rewrite stability τ₁ | stability τ₂ = refl
stability (π ⇒ τ) rewrite stabilityPred π | stability τ = refl    
stability (Π x)  rewrite stability x = refl
stability (Σ x)  rewrite stability x = refl
stability (⦅ ρ ⦆ oρ)  = cong-⦅⦆ (stabilityRow ρ) 
stability (lab l) = refl

stabilityRow [] = refl
stabilityRow ((l , τ) ∷ ρ) = cong₂ _∷_ (cong₂ _,_ refl (stability τ)) (stabilityRow ρ)

stabilityPred (ρ₁ · ρ₂ ~ ρ₃) 
    rewrite stability ρ₁ | stability ρ₂ | stability ρ₃ = refl
stabilityPred (ρ₁ ≲ ρ₂) 
    rewrite stability ρ₁ | stability ρ₂ = refl

--------------------------------------------------------------------------------
-- idempotency

idempotency : ∀ (τ : Type Δ κ) → (⇑ ∘ ⇓ ∘ ⇑ ∘ ⇓) τ ≡  (⇑ ∘ ⇓)  τ
idempotency τ rewrite stability (⇓ τ) = refl

--------------------------------------------------------------------------------
-- surjectivity
--   
 
surjectivity : ∀ (τ : NormalType Δ κ) → ∃[ υ ] (⇓ υ ≡ τ)
surjectivity τ = ( ⇑ τ , stability τ ) 
     

--------------------------------------------------------------------------------
-- NormalType and SemType bijectivity

bijectivity₁ :  ∀ (τ : NormalType Δ κ) → reify (↓ τ) ≡ τ 
bijectivity₁ τ = stability τ 

--------------------------------------------------------------------------------
-- Embedding is injective
 
⇑-inj : ∀ (τ₁ τ₂ : NormalType Δ κ) → ⇑ τ₁ ≡ ⇑ τ₂ → τ₁ ≡ τ₂                   
⇑-inj τ₁ τ₂ eq = trans (sym (stability τ₁)) (trans (cong ⇓ eq) (stability τ₂))
