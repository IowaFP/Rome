{-# OPTIONS --allow-unsolved-metas #-}
module Rome.Operational.Types.Theorems.Completeness where

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
-- Semantic equality forms a PER
-- - Kind of reflexive
-- - symmetric
-- - transitive

reflNE-≋ : ∀ (τ : NeutralType Δ κ) → reflectNE τ ≋ reflectNE τ
reflNE-≋ {κ = ★} τ = refl
reflNE-≋ {κ = L} τ = refl
reflNE-≋ {κ = κ `→ κ₁} τ = refl
reflNE-≋ {κ = R[ ★ ]} τ = refl
reflNE-≋ {κ = R[ L ]} τ = refl
reflNE-≋ {κ = R[ κ `→ κ₁ ]} τ = refl
reflNE-≋ {κ = R[ R[ κ ] ]} τ = refl

--------------------------------------------------------------------------------
-- Congruence

sym-≋ : ∀ {τ₁ τ₂ : SemType Δ κ} → τ₁ ≋ τ₂ → τ₂ ≋ τ₁
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

refl-≋ : ∀ {V₁ V₂ : SemType Δ κ} → V₁ ≋ V₂ → V₁ ≋ V₁
trans-≋ : ∀ {τ₁ τ₂ τ₃ : SemType Δ κ} → τ₁ ≋ τ₂ → τ₂ ≋ τ₃ → τ₁ ≋ τ₃

refl-≋ q = trans-≋ q (sym-≋ q)

trans-≋ {κ = ★} q₁ q₂ = trans q₁ q₂
trans-≋ {κ = L} q₁ q₂ = trans q₁ q₂
trans-≋ {κ = κ₁ `→ κ₂} {left _} {left _} refl q₂ = q₂
trans-≋ {κ = κ₁ `→ κ₂} {right F} {right G} {right H} 
  (unif-F , unif-G , Ext-F-G) (unif-G' , unif-H , Ext-G-H) = 
    unif-F , 
    unif-H , 
    λ ρ q → trans-≋ (Ext-F-G ρ q) (Ext-G-H ρ (refl-≋ (sym-≋ q)))
trans-≋ {κ = R[ ★ ]} q₁ q₂ = trans q₁ q₂
trans-≋ {κ = R[ L ]} q₁ q₂ = trans q₁ q₂
trans-≋ {κ = R[ κ₁ `→ κ₂ ]} {left _} {left _} refl q₂ = q₂
trans-≋ {κ = R[ κ₁ `→ κ₂ ]} {right (l , F)} {right (.l , G)} {right (l' , H)} 
  (refl , F≋G) (refl , G≋H) = refl , trans-≋ F≋G G≋H
trans-≋ {κ = R[ R[ κ ] ]} {left x} {left x₁} {τ₃ = τ₃} refl q₂ = q₂
trans-≋ {κ = R[ R[ κ ] ]} {right (l , F)} {right (.l , G)} {τ₃ = right (.l , H)} (refl , F≋G) (refl , G≋H) = refl , trans-≋ F≋G G≋H

--------------------------------------------------------------------------------
-- Reflecting propositional equality of neutral types into semantic equality.


reflectNE-≋  : ∀ {τ₁ τ₂ : NeutralType Δ κ} → τ₁ ≡ τ₂ → reflectNE τ₁ ≋ reflectNE τ₂
reflectNE-≋ {κ = ★} refl = refl
reflectNE-≋ {κ = L} refl = refl
reflectNE-≋ {κ = κ `→ κ₁} eq = eq
reflectNE-≋ {κ = R[ κ ]} {τ₁ = τ₁} refl = reflNE-≋ τ₁

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
-- related applicands yield related applications

App-≋ : ∀ {V₁ V₂ : SemType Δ (κ₁ `→ κ₂)} → 
           _≋_ {κ = κ₁ `→ κ₂} V₁ V₂ → 
           {W₁ W₂ : SemType Δ κ₁} → 
           W₁ ≋ W₂ → 
           (V₁ ·V W₁) ≋ (V₂ ·V W₂)
App-≋ {V₁ = left x} {left .x} refl q = reflectNE-≋ (cong (x ·_) (reify-≋ q))
App-≋ {V₁ = left x} {right y} () q
App-≋ {V₁ = right y} {left x} () q
App-≋ {V₁ = right F} {right G} (unif-F , unif-G , Ext) q = Ext id q           

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

--------------------------------------------------------------------------------
-- Functor laws for renaming as a functorial action

renSem-id : ∀ {V₁ V₂ : SemType Δ κ} → V₁ ≋ V₂ → (renSem id V₁) ≋ V₂ 
renSem-id {κ = ★} refl = NTypeProps.ren-id _
renSem-id {κ = L} refl = NTypeProps.ren-id _
renSem-id {κ = κ₁ `→ κ₂} {left x} {left .x} refl = NTypeProps.ren-id-ne x
renSem-id {κ = κ₁ `→ κ₂} {right F} {right G} q = q
renSem-id {κ = R[ ★ ]} refl = NTypeProps.ren-id _
renSem-id {κ = R[ L ]} refl = NTypeProps.ren-id _
renSem-id {κ = R[ κ₁ `→ κ₂ ]} {left x} {left .x} refl = NTypeProps.ren-id-ne x
renSem-id {κ = R[ κ₁ `→ κ₂ ]} {right (l , left x)} {right (.l , left x₁)} 
  (refl , refl) = (NTypeProps.ren-id _) , NTypeProps.ren-id-ne _
renSem-id {κ = R[ κ₁ `→ κ₂ ]} {right (l , right y)} {right (.l , right y₁)} 
  (refl , q) = (NTypeProps.ren-id _) , q
renSem-id {κ = R[ R[ κ ] ]} {left x} {left x₁} refl = NTypeProps.ren-id-ne _ 
renSem-id {κ = R[ R[ κ ] ]} {right (l , F)} {right (.l , G)} 
  (refl , q) = (NTypeProps.ren-id _) , (renSem-id q) 


renSem-comp : ∀ (ρ₁ : Renaming Δ₁ Δ₂) (ρ₂ : Renaming Δ₂ Δ₃) {V₁ V₂ : SemType Δ₁ κ} → 
                V₁ ≋ V₂ → (renSem (ρ₂ ∘ ρ₁) V₁) ≋ (renSem ρ₂ (renSem ρ₁ V₂))
renSem-comp {κ = κ} ρ₁ ρ₂ {V₁} {V₂} q = {!   !}


--------------------------------------------------------------------------------
-- Renaming commutes with reflection of neutral types

--             
--            ren ρ 
-- Type Δ₁ κ -------------> Type Δ₂ κ 
--  |                        |
--  | reflectNE              | reflectNE
--  |                        |
--  V                        V 
-- SemType Δ₁ κ ----------> SemType Δ₂ κ
--               renSem ρ 

↻-renSem-reflectNE  : 
  ∀ (ρ : Renaming Δ₁ Δ₂) (τ : NeutralType Δ₁ κ) → 
    (renSem ρ (reflectNE τ)) ≋ (reflectNE (renNE ρ τ))
↻-renSem-reflectNE {κ = ★} ρ τ = refl
↻-renSem-reflectNE {κ = L} ρ τ = refl
↻-renSem-reflectNE {κ = κ `→ κ₁} ρ τ = refl
↻-renSem-reflectNE {κ = R[ ★ ]} ρ τ = refl
↻-renSem-reflectNE {κ = R[ L ]} ρ τ = refl
↻-renSem-reflectNE {κ = R[ κ `→ κ₁ ]} ρ τ = refl
↻-renSem-reflectNE {κ = R[ R[ κ ] ]} ρ τ = refl

--------------------------------------------------------------------------------
-- Lemma hell 



cong-π : ∀ {τ₁ τ₂ : SemType Δ R[ κ ]} → τ₁ ≋ τ₂ → π τ₁ ≋ π τ₂
cong-π {κ = ★} e = cong (π {κ = ★}) e
cong-π {κ = L} e = cong (π {κ = L}) e
cong-π {κ = κ₁ `→ κ₂} {left x} {left x₁} refl = refl
cong-π {κ = κ₁ `→ κ₂} {right (l , left f)} {right (l , left g)} (refl , refl) = {!   !}
cong-π {κ = κ₁ `→ κ₂} {right (l , right F)} {right (l , right G)} (refl , eq) = {!   !}
cong-π {κ = R[ κ ]} e = {!   !}

--------------------------------------------------------------------------------
-- id extension
--
-- Lemma needed for semantic renaming commutation theorem.
-- States that if we evaluate a single term in related environments, we get related results.
-- 
-- Mutually recursive with commutativity of semantic renaming and evaluation (↻-renSem-eval):

--            eval in (renSem (ρ ∘ η₂))
--  Type Δ₁ κ  ------
--  |                \            
--  | eval in η₁       \          
--  |                    \          
--  V                      V        
-- NormalType Δ₂ κ ----------> SemType Δ₂ κ
--                  renSem ρ 


idext : ∀ {η₁ η₂ : Env Δ₁ Δ₂} → Env-≋ η₁ η₂ → (τ : Type Δ₁ κ) →
          eval τ η₁ ≋ eval τ η₂
↻-renSem-eval : ∀ (ρ : Renaming Δ₂ Δ₃) (τ : Type Δ₁ κ) → {η₁ η₂ : Env Δ₁ Δ₂} → 
                  (Ρ : Env-≋ η₁ η₂) → (renSem ρ (eval τ η₁)) ≋ eval τ (renSem ρ ∘ η₂)

Unif-F-NE : ∀ (l : NormalType Δ L) (f : NeutralType Δ (κ₁ `→ κ₂)) → Uniform (λ ρ' v → π (N.ren ρ' l ▵ reflectNE (renNE ρ' f · reify v)))
Unif-F-NE {κ₁ = ★} {★} l f ρ₁ ρ₂ V₁ V₂ refl rewrite ren-comp ρ₁ ρ₂ l | ren-comp-ne ρ₁ ρ₂ f = cong Π refl
Unif-F-NE {κ₁ = ★} {L} l f ρ₁ ρ₂ V₁ V₂ refl rewrite ren-comp ρ₁ ρ₂ l | ren-comp-ne ρ₁ ρ₂ f = cong ΠL refl
Unif-F-NE {κ₁ = ★} {κ₂ `→ κ₃} l f ρ₁ ρ₂ V₁ V₂ refl = {! Unif-F-NE l f  !} , ({!   !} , {!   !}) !
Unif-F-NE {κ₁ = ★} {R[ κ₂ ]} l f ρ₁ ρ₂ V₁ V₂ refl = {!   !}
Unif-F-NE {κ₁ = L} l f ρ₁ ρ₂ V₁ V₂ q = {!   !}
Unif-F-NE {κ₁ = κ₁ `→ κ₂} l f ρ₁ ρ₂ V₁ V₂ q = {!   !}
Unif-F-NE {κ₁ = R[ κ₁ ]} l f ρ₁ ρ₂ V₁ V₂ q = {!   !} 

↻-ren-π : ∀ {Δ₁} {Δ₂} (ρ : Renaming Δ₁ Δ₂) → (V₁ V₂ : SemType Δ₁ R[ κ ]) → V₁ ≋ V₂ → renSem ρ (π V₁) ≋ π (renSem ρ V₂) 
↻-ren-π {★} ρ (ne x) _ refl = refl
↻-ren-π {★} ρ (row x) _ refl = refl
↻-ren-π {L} ρ (ne x) _ refl = refl
↻-ren-π {L} ρ (row x) _ refl = refl
↻-ren-π {κ₁ `→ κ₂} ρ (left f) (left g) refl = refl
↻-ren-π {κ₁ `→ κ₂} ρ (right (l , left f)) (right (.l , left g)) (refl , refl) = 
  (λ ρ₁ ρ₂ V₁ V₂ x → {! ↻-renSem-eval ρ₂   !}) , 
  {!   !} , 
  {!   !} 
↻-ren-π {κ₁ `→ κ₂} ρ (right (l , right F)) (right (.l , right G)) (refl , q) = {!   !}
↻-ren-π {R[ κ ]} ρ V₁ V₂ q = {!   !} 

-- ↻-ren-π {κ = ★} ρ (ne x) = refl
-- ↻-ren-π {κ = ★} ρ (row x) = refl
-- ↻-ren-π {κ = L} ρ (ne x) = refl
-- ↻-ren-π {κ = L} ρ (row x) = refl
-- ↻-ren-π {κ = κ `→ κ₁} ρ (left _) = refl
-- ↻-ren-π {κ = κ₁ `→ κ₂} ρ (right (l , left f)) = {!   !} , {!   !} 

-- ↻-ren-π {κ = κ₁ `→ κ₂} {Δ₁ = Δ₁} {Δ₂} ρ (right (l , right F)) = Unif-F l F , ({!   !} , {!   !})
--   where
--     Unif-F : ∀ {k₁ k₂} (l : NormalType Δ₁ L) (F : KripkeFunction Δ₁ k₁ k₂) → Uniform (renKripke ρ (λ ρ' v → π (N.ren ρ' l ▵ F ρ' v)))
--     Unif-F {★} l F ρ₁ ρ₂ V₁ V₂ refl = trans-≋ ((↻-ren-π ρ₂ (N.ren (λ x → ρ₁ (ρ x)) l ▵ F (λ x → ρ₁ (ρ x)) V₁))) (cong-π {! ↻-renSem-eval (ρ₁ ∘ ρ) ((⇑ l) ▹ (⇑ (reify ( right F))))   !})
--     Unif-F {L} ρ₁ ρ₂ V₁ V₂ x = {!   !}
--     Unif-F {k₁ `→ k₂} ρ₁ ρ₂ V₁ V₂ x = {!   !}
--     Unif-F {R[ k₁ ]} ρ₁ ρ₂ V₁ V₂ x = {!   !}
-- ↻-ren-π {κ = R[ ★ ]} ρ (left x) = refl
-- ↻-ren-π {κ = R[ ★ ]} ρ (right (l , F)) = cong row (cong (N.ren ρ l ▹_) (↻-ren-π {κ = ★} ρ F))
-- ↻-ren-π {κ = R[ L ]} ρ (left x) = refl
-- ↻-ren-π {κ = R[ L ]} ρ (right (l , F)) = cong row (cong (N.ren ρ l ▹_) (↻-ren-π {κ = L} ρ F))
-- ↻-ren-π {κ = R[ κ `→ κ₁ ]} ρ τ = {!   !}
-- ↻-ren-π {κ = R[ R[ κ ] ]} ρ τ = {!   !}


idext {κ = κ} e Unit = refl
idext {κ = ★} e (` x) = e x
idext {κ = L} e (` x) = e x
idext {κ = κ `→ κ₁} e (` x) = e x
idext {κ = R[ κ ]} e (` x) = e x
idext {κ = κ} e (`λ τ) = 
  (λ ρ₁ ρ₂ V₁ V₂ q → 
    trans-≋ 
      (↻-renSem-eval ρ₂ τ 
        (extend-≋ (ren-≋ ρ₁ ∘ refl-≋ ∘ e) q))
      (idext 
        (λ { Z → ren-≋ ρ₂ (refl-≋ (sym-≋ q))
           ; (S x) → sym-≋ (renSem-comp ρ₁ ρ₂ (refl-≋ (e x))) }) τ)) , 
  (λ ρ₁ ρ₂ V₁ V₂ q → 
    trans-≋ 
      (↻-renSem-eval ρ₂ τ 
        (extend-≋ (ren-≋ ρ₁ ∘ refl-≋ ∘ sym-≋ ∘ e) q))
      (idext 
        (λ { Z → ren-≋ ρ₂ (refl-≋ (sym-≋ q))
           ; (S x) → sym-≋ (renSem-comp ρ₁ ρ₂ (refl-≋ (sym-≋ (e x)))) }) τ)) , 
  λ ρ q → idext (extend-≋ (ren-≋ ρ ∘ e) q) τ
idext {κ = ★} e (τ₁ · τ₂) = App-≋ (idext e τ₁) (idext e τ₂)
idext {κ = L} e (τ₁ · τ₂) = App-≋ (idext e τ₁) (idext e τ₂)
idext {κ = κ `→ κ₁} e (τ₁ · τ₂) = App-≋ (idext e τ₁) (idext e τ₂)
idext {κ = R[ κ ]} e (τ₁ · τ₂) = App-≋ (idext e τ₁) (idext e τ₂)
idext {κ = κ} e (τ₁ `→ τ₂) = cong₂ _`→_ (idext e τ₁) (idext e τ₂)
idext {κ = κ} e (`∀ κ₁ τ) = cong (`∀ κ₁) (idext (extend-≋ (ren-≋ S ∘ e) (reflectNE-≋ refl)) τ)
idext {κ = ★} {η₁} {η₂} e (μ τ) with eval τ η₁ | eval τ η₂ | reify-≋ (idext e τ)
... | left x | left x₁ | refl = refl
... | right F | right G | r = cong μ r
idext {κ = κ} e (lab x) = refl
idext {κ = R[ ★ ]} {η₁} {η₂} e (l ▹ τ) rewrite idext e l | idext e τ = refl
idext {κ = R[ L ]} {η₁} {η₂} e (l ▹ τ) rewrite idext e l | idext e τ = refl
idext {κ = R[ κ₁ `→ κ₂ ]} {η₁} {η₂} e (l ▹ τ) with eval τ η₁ | eval τ η₂ | idext e τ | reify-≋ (idext e τ)
... | left x | left y | ide | refl = (idext e l) , refl
... | right F | right G | ide | d = (idext e l) , ide
idext {κ = R[ R[ κ₁ ] ]} {η₁} {η₂} e (l ▹ τ) = (idext e l) , (idext e τ)
idext {κ = κ} e ⌊ τ ⌋ = cong ⌊_⌋ (idext e τ)
idext {κ = R[ κ₁ ] `→ κ₁} {η₁} {η₂} e Π = 
  (λ { ρ₁ ρ₂ V₁ V₂ q → ↻-ren-π ρ₂ V₁ V₂ q }) , 
  ((λ { ρ₁ ρ₂ V₁ V₂ q → ↻-ren-π ρ₂ V₁ V₂ q })) , 
  λ ρ x → cong-π x -- cong (π {κ = κ₁}) x)
idext {κ = κ} e Σ = {!   !}
idext {κ = κ} e (τ <$> τ₁) = {!   !} 
 
↻-renSem-eval ρ τ {η₁} {η₂} P = {!   !}
   
 