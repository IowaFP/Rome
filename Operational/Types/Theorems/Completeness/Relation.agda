{-# OPTIONS --allow-unsolved-metas #-}
module Rome.Operational.Types.Theorems.Completeness.Relation where

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

--------------------------------------------------------------------------------
-- Completeness of type normalization


-- Completeness relation on semantic types
_≋_ : SemType Δ κ → SemType Δ κ → Set
Extensionality-≋ : ∀ {Δ₁} {κ₁} {κ₂} (F G : KripkeFunction Δ₁ κ₁ κ₂) → Set
Uniform :  ∀ {Δ} {κ₁} {κ₂} → KripkeFunction Δ κ₁ κ₂ → Set

_≋_ {κ = ★} τ₁ τ₂ = τ₁ ≡ τ₂
_≋_ {κ = L} τ₁ τ₂ = τ₁ ≡ τ₂
_≋_ {κ = κ₁ `→ κ₂} (left x) (left y) = x ≡ y
_≋_ {κ = κ₁ `→ κ₂} (left x) (right y) = ⊥
_≋_ {κ = κ₁ `→ κ₂} (right y) (left x) = ⊥
_≋_ {Δ₁} {κ = κ₁ `→ κ₂} (right F) (right G) = 
  Uniform F × Uniform G × Extensionality-≋ {Δ₁} F G
 
_≋_ {κ = R[ ★ ]} τ₁ τ₂ = τ₁ ≡ τ₂
_≋_ {κ = R[ L ]} τ₁ τ₂ = τ₁ ≡ τ₂
_≋_ {κ = R[ κ `→ κ₁ ]} (left x) (left y) = x ≡ y
_≋_ {κ = R[ κ `→ κ₁ ]} (left x) (right y) = ⊥
_≋_ {κ = R[ κ `→ κ₁ ]} (right x) (left y) = ⊥
_≋_ {Δ₁} {κ = R[ κ₁ `→ κ₂ ]} (right ( l₁ ,  F )) (right ( l₂ , G )) =
  l₁ ≡ l₂ × (_≋_ {κ = κ₁ `→ κ₂} F G)
_≋_ {κ = R[ R[ κ ] ]} (left x) (left y) = x ≡ y
_≋_ {κ = R[ R[ κ ] ]} (left x) (right y) = ⊥
_≋_ {κ = R[ R[ κ ] ]} (right y) (left x) = ⊥
_≋_ {Δ₁} {κ = R[ R[ κ ] ]} (right ( l₁ , τ₁ )) (right ( l₂ , τ₂ )) = 
  l₁ ≡ l₂ × τ₁ ≋ τ₂

Extensionality-≋ {Δ₁} {κ₁} {κ₂} F G = 
  ∀ {Δ₂} (ρ : Renaming Δ₁ Δ₂) {V₁ V₂ : SemType Δ₂ κ₁} → 
  V₁ ≋ V₂ → F ρ V₁ ≋ G ρ V₂

Uniform {Δ₁} {κ₁} {κ₂} F = 
  ∀ {Δ₂ Δ₃} (ρ₁ : Renaming Δ₁ Δ₂) (ρ₂ : Renaming Δ₂ Δ₃) (V₁ V₂ : SemType Δ₂ κ₁) →
  V₁ ≋ V₂ → (renSem ρ₂ (F ρ₁ V₁)) ≋ (F (ρ₂ ∘ ρ₁) (renSem ρ₂ V₂))

--------------------------------------------------------------------------------
-- Pointwise PER for environments

Env-≋ : (η₁ η₂ : Env Δ₁ Δ₂) → Set
Env-≋ η₁ η₂ = ∀ {κ} (x : KVar _ κ) → (η₁ x) ≋ (η₂ x)

-- extension
extend-≋ : ∀ {η₁ η₂ : Env Δ₁ Δ₂} → Env-≋ η₁ η₂ → 
            {V₁ V₂ : SemType Δ₂ κ} → 
            V₁ ≋ V₂ → 
            Env-≋ (extende η₁ V₁) (extende η₂ V₂)
extend-≋ p q Z = q
extend-≋ p q (S v) = p v

--------------------------------------------------------------------------------
-- Semantic equality forms a PER
-- - Kind of reflexive (as not all SemTypes satisfy Uniformity.)
-- - symmetric
-- - transitive

refl-≋ₗ : ∀ {V₁ V₂ : SemType Δ κ} → V₁ ≋ V₂ → V₁ ≋ V₁
refl-≋ᵣ : ∀ {V₁ V₂ : SemType Δ κ} → V₁ ≋ V₂ → V₂ ≋ V₂
sym-≋ : ∀ {τ₁ τ₂ : SemType Δ κ} → τ₁ ≋ τ₂ → τ₂ ≋ τ₁
trans-≋ : ∀ {τ₁ τ₂ τ₃ : SemType Δ κ} → τ₁ ≋ τ₂ → τ₂ ≋ τ₃ → τ₁ ≋ τ₃

sym-≋ {κ = ★}  refl = refl
sym-≋ {κ = L}  refl = refl
sym-≋ {κ = κ `→ κ₁} {left x} {left x₁} refl = refl
sym-≋ {κ = κ `→ κ₁} 
  {right F} {right G} 
  (Unif-F , (Unif-G , Ext)) = 
     Unif-G ,  Unif-F , (λ {Δ₂} ρ {V₁} {V₂} z → sym-≋ (Ext ρ (sym-≋ z)))
sym-≋ {κ = R[ ★ ]}   refl = refl
sym-≋ {κ = R[ L ]}   refl = refl
sym-≋ {κ = R[ κ `→ κ₁ ]} {left x} {left x₁} refl = refl
sym-≋ {κ = R[ κ `→ κ₁ ]} {right (l₁ , F)} {right (.l₁ , G)} (refl , F≋G) = refl , (sym-≋ F≋G)
sym-≋ {κ = R[ R[ κ ] ]} {left x} {left x₁} refl = refl
sym-≋ {κ = R[ R[ κ ] ]} {right (l , τ₁)} {right (.l , τ₂)} (refl , eq) = refl , sym-≋ eq 


refl-≋ₗ q = trans-≋ q (sym-≋ q)
refl-≋ᵣ q = refl-≋ₗ (sym-≋ q)

trans-≋ {κ = ★} q₁ q₂ = trans q₁ q₂
trans-≋ {κ = L} q₁ q₂ = trans q₁ q₂
trans-≋ {κ = κ₁ `→ κ₂} {left _} {left _} refl q₂ = q₂
trans-≋ {κ = κ₁ `→ κ₂} {right F} {right G} {right H} 
  (unif-F , unif-G , Ext-F-G) (unif-G' , unif-H , Ext-G-H) = 
    unif-F , 
    unif-H , 
    λ ρ q → trans-≋ (Ext-F-G ρ q) (Ext-G-H ρ (refl-≋ₗ (sym-≋ q)))
trans-≋ {κ = R[ ★ ]} q₁ q₂ = trans q₁ q₂
trans-≋ {κ = R[ L ]} q₁ q₂ = trans q₁ q₂
trans-≋ {κ = R[ κ₁ `→ κ₂ ]} {left _} {left _} refl q₂ = q₂
trans-≋ {κ = R[ κ₁ `→ κ₂ ]} {right (l , F)} {right (.l , G)} {right (l' , H)} 
  (refl , F≋G) (refl , G≋H) = refl , trans-≋ F≋G G≋H
trans-≋ {κ = R[ R[ κ ] ]} {left x} {left x₁} {τ₃ = τ₃} refl q₂ = q₂
trans-≋ {κ = R[ R[ κ ] ]} {right (l , F)} {right (.l , G)} {τ₃ = right (.l , H)} (refl , F≋G) (refl , G≋H) = refl , trans-≋ F≋G G≋H


--------------------------------------------------------------------------------
-- Pointwise extensionality (accordingly) forms a PER

refl-Extₗ : ∀ {F G : KripkeFunction Δ₁ κ₁ κ₂} → Extensionality-≋ F G → Extensionality-≋ F F
refl-Extₗ Ext ρ q = trans-≋ (Ext ρ q) (sym-≋ (Ext ρ (refl-≋ₗ (sym-≋ q))))

sym-Ext : ∀ {F G : KripkeFunction Δ₁ κ₁ κ₂} → Extensionality-≋ F G → Extensionality-≋ G F
sym-Ext Ext ρ q = trans-≋ (refl-≋ₗ (sym-≋ (Ext ρ (sym-≋ q)))) (sym-≋ (Ext ρ (sym-≋ q)))

refl-Extᵣ : ∀ {F G : KripkeFunction Δ₁ κ₁ κ₂} → Extensionality-≋ F G → Extensionality-≋ G G
refl-Extᵣ Ext ρ q = refl-Extₗ (sym-Ext Ext) ρ q

trans-Ext : ∀ {F G H : KripkeFunction Δ₁ κ₁ κ₂} → Extensionality-≋ F G → Extensionality-≋ G H → Extensionality-≋ F H
trans-Ext Ext-FG Ext-GH ρ q = trans-≋ (Ext-FG ρ q) (trans-≋ (Ext-GH ρ (sym-≋ q)) (refl-Extᵣ Ext-GH ρ q))

--------------------------------------------------------------------------------
-- Reasoning

infixr 2 _≋⟨_⟩∎ _≋⟨_⟩_

_≋⟨_⟩∎ : ∀ (V₁ : SemType Δ κ) {V₂ : SemType Δ κ}
  → V₁ ≋ V₂
    -----
  → V₁ ≋ V₂
x ≋⟨ q ⟩∎  =  q
  
_≋⟨_⟩_ : ∀ {V₂ V₃ : SemType Δ κ} → 
          (V₁ : SemType Δ κ) → 
          (V₁ ≋ V₂) →
          (V₂ ≋ V₃) →
          V₁ ≋ V₃
V₁ ≋⟨ q ⟩ r = trans-≋ q r

--------------------------------------------------------------------------------
-- Reflecting propositional equality of neutral types into semantic equality.
-- (Well kinded neutral types are in the logical relation.)

reflectNE-≋  : ∀ {τ₁ τ₂ : NeutralType Δ κ} → τ₁ ≡ τ₂ → reflectNE τ₁ ≋ reflectNE τ₂
reflectNE-≋ {κ = ★} refl = refl
reflectNE-≋ {κ = L} refl = refl
reflectNE-≋ {κ = κ `→ κ₁} eq = eq
reflectNE-≋ {κ = R[ ★ ]} {τ₁ = τ₁} refl = refl
reflectNE-≋ {κ = R[ L ]} {τ₁ = τ₁} refl = refl
reflectNE-≋ {κ = R[ κ `→ κ₁ ]} {τ₁ = τ₁} refl = refl
reflectNE-≋ {κ = R[ R[ κ ] ]} {τ₁ = τ₁} refl = refl

--------------------------------------------------------------------------------
-- Reify semantic equality back to propositional equality

reify-≋  : ∀ {τ₁ τ₂ : SemType Δ κ} → τ₁ ≋ τ₂ → reify τ₁ ≡ reify τ₂ 
reify-≋ {κ = ★}  sem-eq = sem-eq
reify-≋ {κ = L} sem-eq = sem-eq
reify-≋ {κ = κ₁ `→ κ₂} {left τ₁} {left τ₂} refl = refl
reify-≋ {κ = κ₁ `→ κ₂} {right F} {right  G}
  ( unif-F , ( unif-G , ext ) ) = cong `λ (reify-≋  (ext S (reflectNE-≋ refl)))
reify-≋ {κ = R[ ★ ]} sem-eq = sem-eq
reify-≋ {κ = R[ L ]} sem-eq = sem-eq
reify-≋ {κ = R[ κ `→ κ₁ ]} {left x} {left x₁} refl = refl
reify-≋ {κ = R[ κ `→ κ₁ ]} {right (l₁ , left F)} {right (l₂ , left G)} (refl , refl) = refl
reify-≋ {κ = R[ κ `→ κ₁ ]} {right (l₁ , right F)} {right (l₂ , right G)} (refl , unif-F , unif-G , Ext) = 
  cong row (cong (_▹_ l₁) (cong `λ (reify-≋ (Ext S (reflectNE-≋ refl)))))
reify-≋ {κ = R[ R[ κ ] ]} {left x} {left x₁} refl = refl
reify-≋ {κ = R[ R[ κ ] ]} {right y} {right y₁} ( refl , sem-eq ) 
 rewrite reify-≋ sem-eq = refl

--------------------------------------------------------------------------------
-- Functorial actions

renSem-id-≋    : ∀ {V₁ V₂ : SemType Δ₁ κ} → V₁ ≋ V₂  → (renSem id V₁) ≋ V₂
renSem-id-≋ {κ = ★} refl = ren-id _
renSem-id-≋ {κ = L} refl = ren-id _
renSem-id-≋ {κ = κ `→ κ₁} {left f} {left .f} refl = ren-id-ne f
renSem-id-≋ {κ = κ `→ κ₁} {right F} {right G} e = e
renSem-id-≋ {κ = R[ κ ]} {V₁} e rewrite renSem-id V₁ = e

ren-comp-≋  : ∀ (ρ₁ : Renaming Δ₁ Δ₂)(ρ₂ : Renaming Δ₂ Δ₃){V₁ V₂ : SemType Δ₁ κ} → 
                 V₁ ≋ V₂ → (renSem (ρ₂ ∘ ρ₁) V₁) ≋ (renSem ρ₂ (renSem ρ₁ V₂))
ren-comp-≋ {κ = ★} ρ₁ ρ₂ refl = ren-comp _ _ _
ren-comp-≋ {κ = L} ρ₁ ρ₂ refl = ren-comp _ _ _
ren-comp-≋ {κ = κ `→ κ₁} ρ₁ ρ₂ {left _} {left _} refl = ren-comp-ne ρ₁ ρ₂ _
ren-comp-≋ {κ = κ `→ κ₁} ρ₁ ρ₂ {right F} {right G} (Unif-F , Unif-G , Ext) = 
  (λ ρ₃ → Unif-F (ρ₃ ∘ ρ₂ ∘ ρ₁)) ,
  (λ ρ₃ → Unif-G (ρ₃ ∘ ρ₂ ∘ ρ₁)) , 
  (λ ρ₃ → Ext (ρ₃ ∘ ρ₂ ∘ ρ₁))
ren-comp-≋ {κ = R[ ★ ]} ρ₁ ρ₂ {V₁} refl = ren-comp _ _ _
ren-comp-≋ {κ = R[ L ]} ρ₁ ρ₂ {V₁} refl = ren-comp _ _ _
ren-comp-≋ {κ = R[ κ `→ κ₁ ]} ρ₁ ρ₂ {left _} {left _} refl = ren-comp-ne _ _ _
ren-comp-≋ {κ = R[ κ `→ κ₁ ]} ρ₁ ρ₂ {right (l , left _)} {right (.l , left _)} (refl , refl) = (ren-comp _ _ _) , (ren-comp-ne _ _ _)
ren-comp-≋ {κ = R[ κ `→ κ₁ ]} ρ₁ ρ₂ {right (l , right y)} {right (.l , right y₁)} (refl , Unif-F , Unif-G , Ext) = 
  (ren-comp _ _ _) , 
  (λ ρ₃ → Unif-F (ρ₃ ∘ ρ₂ ∘ ρ₁)) ,
  (λ ρ₃ → Unif-G (ρ₃ ∘ ρ₂ ∘ ρ₁)) , 
  (λ ρ₃ → Ext (ρ₃ ∘ ρ₂ ∘ ρ₁))
ren-comp-≋ {κ = R[ R[ κ ] ]} ρ₁ ρ₂ {left _} {left _} refl = ren-comp-ne _ _ _
ren-comp-≋ {κ = R[ R[ κ ] ]} ρ₁ ρ₂ {right (l , F)} {right (.l , G)} (refl , q)  = (ren-comp _ _ _) , (ren-comp-≋ _ _ q)

