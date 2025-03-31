{-# OPTIONS --allow-unsolved-metas #-}
module Rome.Operational.Types.Theorems.Completeness.Congruence where

open import Rome.Operational.Prelude

open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

open import Rome.Operational.Types.Syntax
open import Rome.Operational.Types.Properties.Renaming
open import Rome.Operational.Types.Renaming

open import Rome.Operational.Types.Normal.Syntax
open import Rome.Operational.Types.Normal.Renaming
open import Rome.Operational.Types.Normal.Properties.Renaming
open import Rome.Operational.Types.Semantic.Syntax
open import Rome.Operational.Types.Semantic.Renaming
open import Rome.Operational.Types.Semantic.NBE
open import Rome.Operational.Types.Theorems.Completeness.Relation

--------------------------------------------------------------------------------
-- - Uniformity is preserved under renaming (ren-Uniform)
--   (This is actually just what uniformity means.)

ren-Uniform : ∀ {F : KripkeFunction Δ₁ κ₁ κ₂} → (ρ : Renamingₖ Δ₁ Δ₂) → Uniform F → Uniform (renKripke ρ F) 
ren-Uniform ρ Unif-F ρ₁ ρ₂ V₁ V₂ q = Unif-F (ρ₁ ∘ ρ) ρ₂ V₁ V₂ q

--------------------------------------------------------------------------------
-- renaming respects ≋

ren-≋ : ∀ {V₁ V₂ : SemType Δ₁ κ} 
        (ρ : Renamingₖ Δ₁ Δ₂) → 
        V₁ ≋ V₂ → 
        (renSem ρ V₁) ≋ (renSem ρ V₂)
ren-≋ {κ = ★} {V₁ = V₁} {V₂} ρ refl = refl
ren-≋ {κ = L} {V₁ = V₁} {V₂} ρ refl = refl
ren-≋ {κ = κ₁ `→ κ₂} {V₁ = F} {G} ρ₁ (unif-F , unif-G , Ext) = 
  (λ ρ₂ ρ₃ V₁  → unif-F (ρ₂ ∘ ρ₁) ρ₃ V₁) , 
  (λ ρ₂ ρ₃ V₁  → unif-G (ρ₂ ∘ ρ₁) ρ₃ V₁) ,  
  λ ρ₃ q → Ext (ρ₃ ∘ ρ₁) q
ren-≋ {κ = R[ κ ]} {V₁ = left x} {left y} ρ refl = refl
ren-≋ {κ = R[ κ ]} {V₁ = right (n , P)} {right (m , Q)} ρ (refl , eq) = refl , λ { refl → (ren-≋ ρ) ∘ eq refl }

-- --------------------------------------------------------------------------------
-- -- Application respects ≋

cong-App : ∀ {V₁ V₂ : SemType Δ (κ₁ `→ κ₂)} → 
           _≋_ {κ = κ₁ `→ κ₂} V₁ V₂ → 
           {W₁ W₂ : SemType Δ κ₁} → 
           W₁ ≋ W₂ → 
           (V₁ ·V W₁) ≋ (V₂ ·V W₂)
cong-App {V₁ = F} {G} (unif-F , unif-G , Ext) q = Ext id q           

-- --------------------------------------------------------------------------------
-- -- Labeled rows respect ≋

-- cong-▹ : ∀ {L₁ L₂ : NormalType Δ L} → 
--            _≋_ {κ = L} L₁ L₂ → 
--            {W₁ W₂ : SemType Δ κ} → 
--            W₁ ≋ W₂ → 
--            _≋_ {κ = R[ κ ]} (L₁ ▹V W₁)  (L₂ ▹V W₂)
-- cong-▹ {κ = κ} ℓ w = ℓ , w

-- --------------------------------------------------------------------------------
-- -- Mapping respects ≋

cong-<$> : ∀ {V₁ V₂ : SemType Δ (κ₁ `→ κ₂)} → 
           _≋_ {κ = κ₁ `→ κ₂} V₁ V₂ → 
           {W₁ W₂ : SemType Δ R[ κ₁ ]} → 
           _≋_ {κ = R[ κ₁ ]} W₁ W₂ → 
           _≋_ {κ = R[ κ₂ ]} (V₁ <$>V W₁)  (V₂ <$>V W₂)
cong-<$> v {left x} {left x₁} refl = cong (_<$> x) (reify-≋ v)
cong-<$> v {right (n , P)} {right (m , Q)} (refl , eq) =  refl , λ { refl → cong-App v ∘ eq refl } 

--------------------------------------------------------------------------------
-- Given a : κ₁, The semantic image of (λ f : κ₁ `→ κ₂. f a) is uniform.
-- (This goal appears with the use of the flapping operator (??).)

Unif-apply : ∀ {V₁ V₂ : SemType Δ κ₁} → 
               V₁ ≋ V₂ → 
               Uniform {Δ} {κ₁ `→ κ₂} {κ₂} (apply V₂)
Unif-apply {V₁ = V₁} {V₂} v ρ₁ ρ₂ V₃ V₄ x = 
  trans-≋
    (fst x id ρ₂ (renSem ρ₁ V₂) (renSem ρ₁ V₂) (ren-≋ ρ₁ (refl-≋ᵣ v)))
    (third x ρ₂ (sym-≋ (renSem-comp-≋ ρ₁ ρ₂ (refl-≋ᵣ v)))) 

cong-apply : ∀ {V₁ V₂ : SemType Δ κ₁} → 
               V₁ ≋ V₂ → 
               _≋_ {κ = (κ₁ `→ κ₂) `→ κ₂} (apply V₁)  (apply V₂)
cong-apply v = 
  Unif-apply (sym-≋ v) , 
  Unif-apply v , 
  λ ρ v' → third v' id (ren-≋ ρ v)  

-- --------------------------------------------------------------------------------
-- -- Mapping respects ≋

cong-<?> : ∀ {V₁ V₂ : SemType Δ R[ κ₁ `→ κ₂ ]} → 
           _≋_ {κ = R[ κ₁ `→ κ₂ ]} V₁ V₂ → 
           {W₁ W₂ : SemType Δ κ₁} → 
           _≋_ {κ = κ₁} W₁ W₂ → 
           _≋_ {κ = R[ κ₂ ]} (V₁ <?>V W₁)  (V₂ <?>V W₂)
cong-<?> v {W₁} {W₂} w = 
  cong-<$> 
  (cong-apply w) v

