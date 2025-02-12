{-# OPTIONS --allow-unsolved-metas #-}
module Rome.Operational.Types.Theorems.Completeness.Congruence where

open import Rome.Operational.Prelude

open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

open import Rome.Operational.Types as Types
import Rome.Operational.Types.Properties as TypeProps
open import Rome.Operational.Types.Renaming using (Renaming ; _≈_ ; lift)

open import Rome.Operational.Types.Normal
open import Rome.Operational.Types.Normal.Renaming as N
open import Rome.Operational.Types.Normal.Properties.Renaming as NTypeProps
open import Rome.Operational.Types.Semantic.Syntax
open import Rome.Operational.Types.Semantic.Renaming
open import Rome.Operational.Types.Semantic.NBE
open import Rome.Operational.Types.Theorems.Completeness.Relation
-- --------------------------------------------------------------------------------
-- -- renaming respects ≋

ren-≋ : ∀ {V₁ V₂ : SemType Δ₁ κ} 
        (ρ : Renaming Δ₁ Δ₂) → 
        V₁ ≋ V₂ → 
        (renSem ρ V₁) ≋ (renSem ρ V₂)
ren-≋ {κ = ★} {V₁ = V₁} {V₂} ρ refl = refl
ren-≋ {κ = L} {V₁ = V₁} {V₂} ρ refl = refl
ren-≋ {κ = κ₁ `→ κ₂} {V₁ = left _} {left _} ρ refl = refl
ren-≋ {κ = κ₁ `→ κ₂} {V₁ = right F} {right G} ρ₁ (unif-F , unif-G , Ext) = 
  (λ ρ₂ ρ₃ V₁  → unif-F (ρ₂ ∘ ρ₁) ρ₃ V₁) , 
  (λ ρ₂ ρ₃ V₁  → unif-G (ρ₂ ∘ ρ₁) ρ₃ V₁) ,  
  λ ρ₃ q → Ext (ρ₃ ∘ ρ₁) q
ren-≋ {κ = R[ κ ]} {V₁ = left x} {left _} ρ refl = refl
ren-≋ {κ = R[ κ ]} {V₁ = right (l , τ₁)} {right (l , τ₂)} ρ (refl , q) = refl , (ren-≋ ρ q)

--------------------------------------------------------------------------------
-- Application respects ≋

cong-App : ∀ {V₁ V₂ : SemType Δ (κ₁ `→ κ₂)} → 
           _≋_ {κ = κ₁ `→ κ₂} V₁ V₂ → 
           {W₁ W₂ : SemType Δ κ₁} → 
           W₁ ≋ W₂ → 
           (V₁ ·V W₁) ≋ (V₂ ·V W₂)
cong-App {V₁ = left (Π x)} {left .(Π x)} refl q = 
  reflect-≋ (cong Π (cong (_<$> x) (cong `λ (cong ne (cong (` Z ·_) (cong (N.ren S) (reify-≋ q))))))) 
cong-App {V₁ = left f@(` α)} {left f@.(` α)} refl q = reflect-≋ (cong (f ·_) (reify-≋ q))
cong-App {V₁ = left f@(x · τ)} {left f@.(x · τ)} refl q = reflect-≋ (cong (f ·_) (reify-≋ q))
cong-App {V₁ = left (Σ x)} {left .(Σ x)} refl q = {!   !} -- reflect-≋ (cong (x ·_) (reify-≋ q))
cong-App {V₁ = left x} {right y} () q
cong-App {V₁ = right y} {left x} () q
cong-App {V₁ = right F} {right G} (unif-F , unif-G , Ext) q = Ext id q           

--------------------------------------------------------------------------------
-- Labeled rows respect ≋

cong-▹ : ∀ {L₁ L₂ : NormalType Δ L} → 
           _≋_ {κ = L} L₁ L₂ → 
           {W₁ W₂ : SemType Δ κ} → 
           W₁ ≋ W₂ → 
           _≋_ {κ = R[ κ ]} (L₁ ▹V W₁)  (L₂ ▹V W₂)
cong-▹ {κ = κ} ℓ w = ℓ , w

--------------------------------------------------------------------------------
-- Mapping respects ≋

cong-<$> : ∀ {V₁ V₂ : SemType Δ (κ₁ `→ κ₂)} → 
           _≋_ {κ = κ₁ `→ κ₂} V₁ V₂ → 
           {W₁ W₂ : SemType Δ R[ κ₁ ]} → 
           _≋_ {κ = R[ κ₁ ]} W₁ W₂ → 
           _≋_ {κ = R[ κ₂ ]} (V₁ <$>V W₁)  (V₂ <$>V W₂)
cong-<$> v {left x} {left x₁} refl = cong (_<$> x) (reify-≋ v)
cong-<$> v {right (l , τ₁)} {right (l , τ₂)} (refl , w) = refl , (cong-App v w)

