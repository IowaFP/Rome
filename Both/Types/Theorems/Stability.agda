{-# OPTIONS --safe #-}
module Rome.Both.Types.Theorems.Stability where

open import Rome.Both.Prelude

open import Rome.Both.Kinds.Syntax
open import Rome.Both.Kinds.GVars

open import Rome.Both.Types.Syntax
open import Rome.Both.Types.Substitution
open import Rome.Both.Types.Renaming
open import Rome.Both.Types.Equivalence.Relation

open import Rome.Both.Types.Normal.Syntax
open import Rome.Both.Types.Normal.Substitution
open import Rome.Both.Types.Normal.Properties.Renaming

open import Rome.Both.Types.Semantic.Syntax
open import Rome.Both.Types.Semantic.Renaming
open import Rome.Both.Types.Semantic.NBE

open import Rome.Both.Types.Theorems.Soundness

--------------------------------------------------------------------------------
-- - stability : ⇑ is right-inverse to ⇓ 
--     or, ⇓ is a split-monomorphism/section.
-- - stabilityNE : eval ∘ ⇑NE  = reflect
--   or, round trips from neutral semantic terms to semantic terms are preserved.

stability   : ∀ (τ : NormalType Δ κ) → ⇓ (⇑ τ) ≡ τ
stabilityNE : ∀ (τ : NeutralType Δ κ) → eval (⇑NE τ) (idEnv {Δ}) ≡ reflect τ

stabilityPred : ∀ (π : NormalPred Δ R[ κ ]) → evalPred (⇑Pred π) idEnv ≡ π
stabilityRow : ∀ (ρ : SimpleRow NormalType Δ R[ κ ]) → reifyRow (evalRow (⇑Row ρ) idEnv) ≡ ρ

stabilityNE {κ = κ} (` x) = refl
stabilityNE {Δ} {κ} (τ₁ · τ₂) rewrite stabilityNE τ₁ | stability τ₂ = cong reflect (cong₂ _·_ (renₖNE-id τ₁) refl) 

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
stability {κ = L} (ne x) = stabilityNE x
stability {_} {κ `→ κ₁} (ne x {()})
stability {κ = R[ κ ]} (ne x {()})
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
stability ((ρ₂ ─ ρ₁) {nsr}) with eval (⇑ ρ₂) idEnv | eval (⇑ ρ₁) idEnv | stability ρ₂ | stability ρ₁
... | φ₁ <$> n₁ | _ | refl | refl = refl 
... | x₁ ▹ x₂ | x₃ ▹ x₄ | refl | refl = refl
... | x₁ ▹ x₂ | row ρ x₃ | refl | refl = refl
... | x₁ ▹ x₂ | d ─ d₁ | refl | refl = refl
... | x₁ ▹ x₂ | φ <$> n | refl | refl = refl
... | row ρ x₁ | x₂ ▹ x₃ | refl | refl = refl
... | row ρ x₁ | d ─ d₁ | refl | refl = cong-─ (cong-⦅⦆ refl) refl
... | row ρ x₁ | φ <$> n | refl | refl = refl
... | c ─ c₁ | x₁ ▹ x₂ | refl | refl = cong-─ refl refl
... | c ─ c₁ | row ρ x₁ | refl | refl = cong-─ refl (cong-⦅⦆ refl)
... | c ─ c₁ | d ─ d₁ | refl | refl = cong-─ refl refl
... | c ─ c₁ | φ <$> n | refl | refl = cong-─ refl refl
stability (l ▹ₙ τ) with eval (⇑NE l) idEnv | isNeutral? (eval (⇑NE l) idEnv) | stabilityNE l
... | ne x₁ | yes p | refl = cong (l ▹ₙ_) (stability τ)
... | .(ne l) | no q | refl = ⊥-elim (q tt)
stability ((φ <$> n)) rewrite stabilityNE n = cong₂ _<$>_ (stability φ) refl

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
-- Embedding is injective
 
⇑-inj : ∀ (τ₁ τ₂ : NormalType Δ κ) → ⇑ τ₁ ≡ ⇑ τ₂ → τ₁ ≡ τ₂                   
⇑-inj τ₁ τ₂ eq = trans (sym (stability τ₁)) (trans (cong ⇓ eq) (stability τ₂))
