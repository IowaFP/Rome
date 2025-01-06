{-# OPTIONS --allow-unsolved-metas #-}
module Rome.Operational.Types.Theorems.Completeness where

open import Rome.Operational.Prelude

open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

open import Rome.Operational.Types as Types
import Rome.Operational.Types.Properties as TypeProps
open import Rome.Operational.Types.Renaming using (Renaming ; _≈_ ; lift)

open import Rome.Operational.Types.Normal
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
_≋_ {Δ₁} {κ = κ₁ `→ κ₂} (right ( cs₁ , F )) (right ( cs₂ , G )) = 
  cs₁ ≡ cs₂ × Uniform F × Uniform G × Extensionality-≋ {Δ₁} F G
 
_≋_ {κ = R[ ★ ]} τ₁ τ₂ = τ₁ ≡ τ₂
_≋_ {κ = R[ L ]} τ₁ τ₂ = τ₁ ≡ τ₂
_≋_ {κ = R[ κ `→ κ₁ ]} (left x) (left y) = x ≡ y
_≋_ {κ = R[ κ `→ κ₁ ]} (left x) (right y) = ⊥
_≋_ {κ = R[ κ `→ κ₁ ]} (right x) (left y) = ⊥
_≋_ {Δ₁} {κ = R[ κ `→ κ₁ ]} (right ( l₁ , ( cs₁ , F ) )) (right ( l₂ , ( cs₂ , G ) )) = 
  l₁ ≡ l₂ × cs₁ ≡ cs₂ × Uniform F × Uniform G × Extensionality-≋ {Δ₁} F G
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

refl-≋ : ∀ (τ : NeutralType Δ κ) → reflectNE τ ≋ reflectNE τ
refl-≋ {κ = ★} τ = refl
refl-≋ {κ = L} τ = refl
refl-≋ {κ = κ `→ κ₁} τ = refl
refl-≋ {κ = R[ ★ ]} τ = refl
refl-≋ {κ = R[ L ]} τ = refl
refl-≋ {κ = R[ κ `→ κ₁ ]} τ = refl
refl-≋ {κ = R[ R[ κ ] ]} τ = refl

sym-≋ : ∀ (τ₁ τ₂ : SemType Δ κ) → τ₁ ≋ τ₂ → τ₂ ≋ τ₁
sym-≋ {κ = ★} t₁ t₂ refl = refl
sym-≋ {κ = L} t₁ t₂ refl = refl
sym-≋ {κ = κ `→ κ₁} (left x) (left x₁) refl = refl
sym-≋ {κ = κ `→ κ₁} 
  (right (cs , F)) (right (.cs , G)) 
  (refl , (Unif-F , (Unif-G , Ext))) = 
     refl ,  Unif-G ,  Unif-F , (λ {Δ₂} ρ {V₁} {V₂} z → sym-≋ (F ρ V₂) (G ρ V₁) (Ext ρ (sym-≋ V₁ V₂ z)))
sym-≋ {κ = R[ ★ ]} t₁ t₂ refl = refl
sym-≋ {κ = R[ L ]} t₁ t₂ refl = refl
sym-≋ {κ = R[ κ `→ κ₁ ]} (left x) (left x₁) refl = refl
sym-≋ {κ = R[ κ `→ κ₁ ]} (right (l , cs , snd₁)) (right (.l , .cs , snd₂)) (refl , refl , Unif-F , Unif-G , Ext) = refl ,
  refl ,
  Unif-G ,
  Unif-F ,
  (λ {Δ₂} ρ {V₁} {V₂} z →
     sym-≋ (snd₁ ρ V₂) (snd₂ ρ V₁) (Ext ρ (sym-≋ V₁ V₂ z)))
sym-≋ {κ = R[ R[ κ ] ]} (left x) (left x₁) refl = refl
sym-≋ {κ = R[ R[ κ ] ]} (right (l , τ₁)) (right (.l , τ₂)) (refl , eq) = refl , sym-≋ τ₁ τ₂ eq 

postulate
  -- todo
  trans-≋ : ∀ (τ₁ τ₂ τ₃ : SemType Δ κ) → τ₁ ≋ τ₂ → τ₂ ≋ τ₃ → τ₁ ≋ τ₃

--------------------------------------------------------------------------------
-- Reflecting propositional equality of neutral types into semantic equality.


reflectNE-≋  : ∀ {τ₁ τ₂ : NeutralType Δ κ} → τ₁ ≡ τ₂ → reflectNE τ₁ ≋ reflectNE τ₂
reflectNE-≋ {κ = ★} refl = refl
reflectNE-≋ {κ = L} refl = refl
reflectNE-≋ {κ = κ `→ κ₁} eq = eq
reflectNE-≋ {κ = R[ κ ]} {τ₁ = τ₁} refl = refl-≋ τ₁

--------------------------------------------------------------------------------
-- Reify semantic equality back to propositional equality

reify-≋→ : 
  ∀ (F G : SemType Δ (κ₁ `→ κ₂)) →  _≋_ {Δ = Δ} {κ = κ₁ `→ κ₂} F  G →
  reify {Δ = Δ} {κ = κ₁ `→ κ₂} F ≡ reify G
reify-≋  : ∀ {τ₁ τ₂ : SemType Δ κ} → τ₁ ≋ τ₂ → reify τ₁ ≡ reify τ₂
reify-≋→ (left τ₁) (left τ₂) refl = refl
reify-≋→ (right ( [] , F )) (right ( .[] , G ))
  ( refl , ( unif-F , ( unif-G , ext ) ) ) = cong `λ (reify-≋  (ext S (reflectNE-≋ refl)))
reify-≋→  
  (right ( Π l ∷ cs , F )) (right ( .(Π l ∷ cs) , G ))
  (( refl , ( unif-F , ( unif-G , ext ) ) )) = 
  cong (Π▹ l) (reify-≋ {τ₁ = (right ( cs , _ ))} {τ₂ = right ( cs , _ )} ( refl , ( unif-F , ( unif-G , ext ) ) ))
reify-≋→  
  (right ( Σ l ∷ cs , F )) (right ( .(Σ l ∷ cs) , G ))
  (( refl , ( unif-F , ( unif-G , ext ) ) )) = 
  cong (Σ▹ l) (reify-≋ {τ₁ = (right ( cs , _ ))} {τ₂ = right ( cs , _ )} ( refl , ( unif-F , ( unif-G , ext ) ) ))
                  

reify-≋ {κ = ★}  sem-eq = sem-eq
reify-≋ {κ = L} sem-eq = sem-eq
reify-≋ {κ = κ `→ κ₁} {τ₁} {τ₂} sem-eq = reify-≋→ τ₁ τ₂ sem-eq
reify-≋ {κ = R[ ★ ]} sem-eq = sem-eq
reify-≋ {κ = R[ L ]} sem-eq = sem-eq
reify-≋ {κ = R[ κ `→ κ₁ ]} {left x} {left x₁} refl = refl
reify-≋ {κ = R[ κ `→ κ₁ ]} {right ( l₁ , F )} {right ( l₂ , G )} ( refl , eeeqs ) 
  rewrite reify-≋→ (right F) (right G) eeeqs = refl
reify-≋ {κ = R[ R[ κ ] ]} {left x} {left x₁} refl = refl
reify-≋ {κ = R[ R[ κ ] ]} {right y} {right y₁} ( refl , sem-eq ) 
  rewrite reify-≋ sem-eq = refl

--------------------------------------------------------------------------------
-- Pointwise PER for environments

Env-≋ : (η₁ η₂ : Env Δ₁ Δ₂) → Set
Env-≋ η₁ η₂ = ∀ {κ} (x : KVar _ κ) → (η₁ x) ≋ (η₂ x)

--------------------------------------------------------------------------------
-- id extension
--
-- Lemma needed for semantic renaming commutation theorem.
-- States that if we evaluate a single term in related environments, we get related results.

postulate 
  idext : ∀ {η₁ η₂ : Env Δ₁ Δ₂} → Env-≋ η₁ η₂ → (τ : Type Δ₁ κ) →
        reflect τ η₁ ≋ reflect τ η₂


--------------------------------------------------------------------------------
-- Semantic renaming commutes with evaluation (reflection of types)

postulate
  ↻-renSem-reflectNE  : 
    ∀ (ρ : Renaming Δ₁ Δ₂) (τ : NeutralType Δ₁ κ) → 
      (renSem ρ (reflectNE τ)) ≋ (reflectNE (renNE ρ τ))
  
  ↻-renSem-reflect : 
    ∀ (ρ : Renaming Δ₂ Δ₃) (τ : Type Δ₁ κ) → {η₁ η₂ : Env Δ₁ Δ₂} → {Ρ : Env-≋ η₁ η₂} →
      (renSem ρ (reflect τ η₁)) ≋ reflect τ (renSem ρ ∘ η₂)




--------------------------------------------------------------------------------
-- Need:
-- - idext
-- - reflectCR
-- - ren⊧-reflect
-- - reifyCR
 