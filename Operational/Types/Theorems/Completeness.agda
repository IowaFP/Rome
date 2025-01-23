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

sym-≋ : ∀ (τ₁ τ₂ : SemType Δ κ) → τ₁ ≋ τ₂ → τ₂ ≋ τ₁
sym-≋ {κ = ★} t₁ t₂ refl = refl
sym-≋ {κ = L} t₁ t₂ refl = refl
sym-≋ {κ = κ `→ κ₁} (left x) (left x₁) refl = refl
sym-≋ {κ = κ `→ κ₁} 
  (right F) (right G) 
  (Unif-F , (Unif-G , Ext)) = 
     Unif-G ,  Unif-F , (λ {Δ₂} ρ {V₁} {V₂} z → sym-≋ (F ρ V₂) (G ρ V₁) (Ext ρ (sym-≋ V₁ V₂ z)))
sym-≋ {κ = R[ ★ ]} t₁ t₂ refl = refl
sym-≋ {κ = R[ L ]} t₁ t₂ refl = refl
sym-≋ {κ = R[ κ `→ κ₁ ]} (left x) (left x₁) refl = refl
sym-≋ {κ = R[ κ `→ κ₁ ]} (right (l₁ , F)) (right (.l₁ , G)) (refl , F≋G) = refl , (sym-≋ _ _ F≋G)
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
reflectNE-≋ {κ = R[ κ ]} {τ₁ = τ₁} refl = reflNE-≋ τ₁

--------------------------------------------------------------------------------
-- Reify semantic equality back to propositional equality

reify-≋→ : 
  ∀ (F G : SemType Δ (κ₁ `→ κ₂)) →  _≋_ {Δ = Δ} {κ = κ₁ `→ κ₂} F  G →
  reify {Δ = Δ} {κ = κ₁ `→ κ₂} F ≡ reify G
reify-≋  : ∀ {τ₁ τ₂ : SemType Δ κ} → τ₁ ≋ τ₂ → reify τ₁ ≡ reify τ₂
reify-≋→ (left τ₁) (left τ₂) refl = refl
reify-≋→ (right F) (right  G)
  ( unif-F , ( unif-G , ext ) ) = cong `λ (reify-≋  (ext S (reflectNE-≋ refl)))
-- reify-≋→  
--   (right ( Π l ∷ cs , F )) (right ( .(Π l ∷ cs) , G ))
--   (( refl , ( unif-F , ( unif-G , ext ) ) )) = 
--     cong ne (cong Π (cong (_▹_ l) 
--     ((reify-≋ {τ₁ = (right ( cs , _ ))} {τ₂ = right ( cs , _ )} ( refl , ( unif-F , ( unif-G , ext )))))))
-- reify-≋→  
--   (right ( Σ l ∷ cs , F )) (right ( .(Σ l ∷ cs) , G ))
--   (( refl , ( unif-F , ( unif-G , ext ) ) )) = 
--     cong ne (cong Σ (cong (_▹_ l) 
--     ((reify-≋ {τ₁ = (right ( cs , _ ))} {τ₂ = right ( cs , _ )} ( refl , ( unif-F , ( unif-G , ext )))))))
                  
reify-≋ {κ = ★}  sem-eq = sem-eq
reify-≋ {κ = L} sem-eq = sem-eq
reify-≋ {κ = κ `→ κ₁} {τ₁} {τ₂} sem-eq = reify-≋→ τ₁ τ₂ sem-eq
reify-≋ {κ = R[ ★ ]} sem-eq = sem-eq
reify-≋ {κ = R[ L ]} sem-eq = sem-eq
reify-≋ {κ = R[ κ `→ κ₁ ]} {left x} {left x₁} refl = refl
reify-≋ {κ = R[ κ `→ κ₁ ]} {right (l₁ , left F)} {right (l₂ , left G)} (refl , refl) = refl
reify-≋ {κ = R[ κ `→ κ₁ ]} {right (l₁ , right F)} {right (l₂ , right G)} (refl , unif-F , unif-G , Ext) = 
  cong row (cong (_▹_ l₁) (cong `λ (reify-≋ (Ext S (reflectNE-≋ refl)))))
--   rewrite reify-≋→ (right F) (right G) eeeqs = refl
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


idext : ∀ {η₁ η₂ : Env Δ₁ Δ₂} → Env-≋ η₁ η₂ → (τ : Type Δ₁ κ) →
          eval τ η₁ ≋ eval τ η₂
idext {κ = κ} e Unit = refl
idext {κ = ★} e (` x) = e x
idext {κ = L} e (` x) = e x
idext {κ = κ `→ κ₁} e (` x) = e x
idext {κ = R[ κ ]} e (` x) = e x
idext {κ = κ} e (`λ τ) = (λ ρ₁ ρ₂ V₁ V₂ x → {!   !}) , ({!   !} , {!   !})
idext {κ = κ} e (τ · τ₁) = {!   !}
idext {κ = κ} e (τ `→ τ₁) = {!   !}
idext {κ = κ} e (`∀ κ₁ τ) = {!   !}
idext {κ = κ} e (μ τ) = {!   !}
idext {κ = κ} e (lab x) = {!   !}
idext {κ = κ} e (τ ▹ τ₁) = {!   !}
idext {κ = κ} e ⌊ τ ⌋ = {!   !}
idext {κ = κ} e Π = {!   !}
idext {κ = κ} e Σ = {!   !}
idext {κ = κ} e (τ <$> τ₁) = {!   !} 
 

--------------------------------------------------------------------------------
-- Semantic renaming commutes with evaluation (reflection of types)

postulate
  ↻-renSem-reflectNE  : 
    ∀ (ρ : Renaming Δ₁ Δ₂) (τ : NeutralType Δ₁ κ) → 
      (renSem ρ (reflectNE τ)) ≋ (reflectNE (renNE ρ τ))
   
  ↻-renSem-eval : 
    ∀ (ρ : Renaming Δ₂ Δ₃) (τ : Type Δ₁ κ) → {η₁ η₂ : Env Δ₁ Δ₂} → {Ρ : Env-≋ η₁ η₂} →
      (renSem ρ (eval τ η₁)) ≋ eval τ (renSem ρ ∘ η₂)