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

--------------------------------------------------------------------------------
-- Application respects ≋

cong-App : ∀ {V₁ V₂ : SemType Δ (κ₁ `→ κ₂)} → 
           _≋_ {κ = κ₁ `→ κ₂} V₁ V₂ → 
           {W₁ W₂ : SemType Δ κ₁} → 
           W₁ ≋ W₂ → 
           (V₁ ·V W₁) ≋ (V₂ ·V W₂)
cong-App {V₁ = left x} {left .x} refl q = reflectNE-≋ (cong (x ·_) (reify-≋ q))
cong-App {V₁ = left x} {right y} () q
cong-App {V₁ = right y} {left x} () q
cong-App {V₁ = right F} {right G} (unif-F , unif-G , Ext) q = Ext id q           

--------------------------------------------------------------------------------
-- Labeled rows respect ≋

cong-▹ : ∀ {L₁ L₂ : NormalType Δ L} → 
           _≋_ {κ = L} L₁ L₂ → 
           {W₁ W₂ : SemType Δ κ₁} → 
           W₁ ≋ W₂ → 
           (L₁ ▹V W₁) ≋ (L₂ ▹V W₂)
cong-▹ {κ₁ = ★} refl refl = refl
cong-▹ {κ₁ = L} refl refl = refl
cong-▹ {κ₁ = κ₁ `→ κ₂} refl {left x} {left x₁} w = refl , w
cong-▹ {κ₁ = κ₁ `→ κ₂} refl {right F} {right G} ≋W = 
  refl , ≋W
cong-▹ {κ₁ = R[ κ₁ ]} refl w = refl , w

--------------------------------------------------------------------------------
-- Mapping respects ≋

cong-<$> : ∀ {V₁ V₂ : SemType Δ (κ₁ `→ κ₂)} → 
           _≋_ {κ = κ₁ `→ κ₂} V₁ V₂ → 
           {W₁ W₂ : SemType Δ R[ κ₁ ]} → 
           W₁ ≋ W₂ → 
           _≋_ {κ = R[ κ₂ ]} (V₁ <$>V W₁)  (V₂ <$>V W₂)
cong-<$> {κ₁ = ★} {V₁ = left _} {left _} refl {ne _} refl = reflectNE-≋ refl
cong-<$> {κ₁ = ★} {V₁ = left _} {left _} refl {row (l ▹ τ)} refl = cong-▹ refl (reflectNE-≋ refl)
cong-<$> {κ₁ = ★} {V₁ = right F} {right G} (Unif-F , Unif-G , Ext) {ne x} refl = reflectNE-≋ (cong₂ _<$>_ (cong `λ (reify-≋ (Ext S refl))) refl)
cong-<$> {κ₁ = ★} {V₁ = right F} {right G} (Unif-F , Unif-G , Ext) {row (l ▹ τ)} refl = cong-▹ refl (Ext id refl)
cong-<$> {κ₁ = L} {V₁ = left _} {left _} refl {ne _} refl = reflectNE-≋ refl
cong-<$> {κ₁ = L} {V₁ = left _} {left _} refl {row (l ▹ τ)} refl = cong-▹ refl (reflectNE-≋ refl)
cong-<$> {κ₁ = L} {V₁ = right F} {right G} (Unif-F , Unif-G , Ext) {ne x} refl = reflectNE-≋ (cong₂ _<$>_ (cong `λ (reify-≋ (Ext S refl))) refl)
cong-<$> {κ₁ = L} {V₁ = right F} {right G} (Unif-F , Unif-G , Ext) {row (l ▹ τ)} refl = cong-▹ refl (Ext id refl)
cong-<$> {κ₁ = κ₁ `→ κ₂} {V₁ = left x₁} {left x₂} refl {left x} {left .x} refl = reflectNE-≋ refl
cong-<$> {κ₁ = κ₁ `→ κ₂} {V₁ = right _} {right _} (Unif-F , Unif-G , Ext) {left _} {left _} refl = 
    reflectNE-≋ (cong₂ _<$>_ (cong `λ (reify-≋ (Ext S refl))) refl)
cong-<$> {κ₁ = κ₁ `→ κ₂} {V₁ = left _} {left _} refl {right (l , left _)} {right (.l , left _)} (refl , refl) = cong-▹ refl (reflectNE-≋ refl)
cong-<$> {κ₁ = κ₁ `→ κ₂} {V₁ = right F} {right G} (_ , _ , Ext) {right (l , left _)} {right (.l , left _)} (refl , refl) = cong-▹ refl (Ext id refl)
cong-<$> {κ₁ = κ₁ `→ κ₂} {V₁ = left x} {left x₁} refl {right (l , right F)} {right (.l , right G)} (refl , Unif-F , Unif-G , Ext) = 
    cong-▹ refl (reflectNE-≋ (cong (x ·_) (cong `λ (reify-≋ (Ext S (reflectNE-≋ refl))))))
cong-<$> {κ₁ = κ₁ `→ κ₂} {V₁ = right F₁} {right G₁} (_ , _ , Ext₁) {right (l , right F₂)} {right (.l , right G₂)} (refl , q) = cong-▹ refl (Ext₁ id q)
cong-<$> {κ₁ = R[ κ₁ ]} {V₁ = left x} {left x₁} refl {left x₂} {left x₃} refl = reflectNE-≋ refl
cong-<$> {κ₁ = R[ κ₁ ]} {V₁ = left f} {left .f} refl {right (l , V₁)} {right (.l , V₂)} (refl , q) = cong-▹ refl (reflectNE-≋ (cong (f ·_) (reify-≋ q)))
cong-<$> {κ₁ = R[ κ₁ ]} {V₁ = right F} {right G} (_ , _ , Ext) {left _} {left _} refl = reflectNE-≋ (cong₂ _<$>_ (cong `λ (reify-≋ (Ext S (reflectNE-≋ refl)))) refl)
cong-<$> {κ₁ = R[ κ₁ ]} {V₁ = right F} {right G} (_ , _ , Ext) {right (l , V₁)} {right (.l , V₂)} (refl , q) = cong-▹ refl (Ext id q)

--------------------------------------------------------------------------------
-- renaming respects ≋

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
ren-≋ {κ = R[ ★ ]} {V₁ = V₁} {V₂} ρ refl = refl
ren-≋ {κ = R[ L ]} {V₁ = V₁} {V₂} ρ refl = refl
ren-≋ {κ = R[ κ₁ `→ κ₂ ]} {V₁ = left x} {left x₁} ρ refl = refl
ren-≋ {κ = R[ κ₁ `→ κ₂ ]} {V₁ = right (l , left F)} {right (.l , left G)} ρ (refl , refl) = refl , refl
ren-≋ {κ = R[ κ₁ `→ κ₂ ]} {V₁ = right (l , right F)} {right (.l , right G)} ρ₁
  (refl , q) = refl , ren-≋ {κ = κ₁ `→ κ₂} {V₁ = right F} {V₂ = right G}  ρ₁ q
ren-≋ {κ = R[ R[ κ ] ]} {V₁ = left _} {left _} ρ refl = refl
ren-≋ {κ = R[ R[ κ ] ]} {V₁ = right (l , F)} {right (.l , G)} ρ (refl , q) = refl , (ren-≋ {κ = R[ κ ]} ρ q)
