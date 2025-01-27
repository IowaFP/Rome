module Rome.Operational.Types.Theorems.Soundness where

open import Rome.Operational.Prelude
open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

open import Rome.Operational.Types.Syntax
open import Rome.Operational.Types.Substitution
open import Rome.Operational.Types.Renaming

open import Rome.Operational.Types.Normal.Syntax
import Rome.Operational.Types.Normal.Renaming as NR
import Rome.Operational.Types.Normal.Renaming as NR

open import Rome.Operational.Types.Semantic.Syntax
open import Rome.Operational.Types.Semantic.NBE
open import Rome.Operational.Types.Semantic.Renaming

open import Rome.Operational.Types.Theorems.Stability
open import Rome.Shared.Postulates.FunExt

-------------------------------------------------------------------------------


infix 0 _↝_
data _↝_ : Type Δ κ → Type Δ κ → Set where 

    β : ∀ {τ₁ : Type (Δ ,, κ₁) κ₂} {τ₂ : Type Δ κ₁} → 


        ----------------------------
        ((`λ τ₁) · τ₂) ↝ (τ₁ β[ τ₂ ])

    Π² : ∀ {l} {τ : Type Δ R[ κ ]} → 

         ----------------------------
         Π · (Π · (l ▹ τ)) ↝ Π · (l ▹ (Π · τ))
    
    Πℓ² : ∀ {l₁ l₂} {τ : Type Δ R[ κ ]} → 

        -------------------------------------------
        Π · (l₁ ▹ (l₂ ▹ τ)) ↝ l₁ ▹ (Π · (l₂ ▹ τ))

    Πλ : ∀ {l} {τ : Type (Δ ,, κ₁) R[ κ₂ ]} → 

        -------------------------------------------
        Π · (l ▹ `λ τ) ↝ `λ (Π · (weaken l ▹ τ))

    ▹$ : ∀ {l} {τ : Type Δ κ₁} {F : Type Δ (κ₁ `→ κ₂)} → 

        -------------------------------------------
        (F <$> (l ▹ τ)) ↝ (l ▹ F · τ)



data _↝*_ : Type Δ κ → Type Δ κ → Set where

    inst-↝ : ∀ {τ₁ τ₂ : Type Δ κ} → 

              τ₁ ↝ τ₂ → 
              ----------
              τ₁ ↝* τ₂

    refl-↝ : ∀ {τ : Type Δ κ} → 

              -------
              τ ↝* τ  

    trans-↝ : ∀ {τ₁ τ₂ τ₃ : Type Δ κ} → 

              τ₁ ↝* τ₂ → τ₂ ↝* τ₃ → 
              ----------------------
              τ₁ ↝* τ₃

nested-π-ne : ∀ (x : NeutralType Δ R[ R[  κ ] ]) → πNE x ≡ π (left x)
nested-π-ne {κ = ★} x = refl
nested-π-ne {κ = L} x = refl
nested-π-ne {κ = κ `→ κ₁} x = refl
nested-π-ne {κ = R[ κ ]} x = refl

-- ↻-ren-eval : ∀ (ρ : Renaming Δ₂ Δ₃) (τ : Type Δ₁ κ) (η₁ : Env Δ₁ Δ₂) (η₂ : Env Δ₃ Δ₃) → 
--                 η₁ ≡ η₂ → (renSem ρ (eval τ η₁)) ≡ eval τ (renSem ρ ∘ η₂)
-- ↻-ren-eval ρ τ η₁ η₂ q = {!   !}

↻-ren-reify : ∀ (ρ : Renaming Δ₁ Δ₂) → (v : SemType Δ₁ κ) → 
              NR.ren ρ (reify v) ≡ reify (renSem ρ v)
↻-ren-reify {κ = ★} ρ v = refl
↻-ren-reify {κ = L} ρ v = refl
↻-ren-reify {κ = κ₁ `→ κ₂} ρ (left x) = refl
-- I think I found where I need uniformity.
↻-ren-reify {κ = κ₁ `→ κ₂} ρ (right F) = cong `λ (trans (↻-ren-reify (lift ρ) (F S (reflectNE (` Z)))) (cong reify {!   !}))
↻-ren-reify {κ = R[ κ ]} ρ v = {!   !}              

↻-ren-eval : ∀ (ρ : Renaming Δ₂ Δ₃) (τ : Type Δ₁ κ) (η : Env Δ₁ Δ₂) → 
                (renSem ρ (eval τ η)) ≡ eval τ (renSem ρ ∘ η)
↻-ren-eval {κ = κ} ρ Unit η = refl
↻-ren-eval {κ = ★} ρ (` α) η = refl
↻-ren-eval {κ = L} ρ (` α) η = refl
↻-ren-eval {κ = κ `→ κ₁} ρ (` α) η = refl
↻-ren-eval {κ = R[ κ ]} ρ (` α) η = refl
↻-ren-eval {κ = κ} ρ (`λ τ) η = cong right 
    (extensionality-i (extensionality 
        (λ ρ' → extensionality 
            (λ v → idext (λ { Z → refl
                            ; (S x) → renSem-comp (η x) ρ ρ' }) τ))))
↻-ren-eval {κ = ★} ρ (_·_ {κ₁} τ₁ τ₂) η 
    with eval τ₁ (λ x → renSem ρ (η x)) 
    | sym (↻-ren-eval ρ τ₁ η) 
    | eval τ₂ (λ x → renSem ρ (η x)) 
    | sym (↻-ren-eval ρ τ₂ η) 
    | eval τ₁ η 
    | inspect (λ x → eval x η) τ₁ 
    | eval τ₂ η
    | inspect (λ x → eval x η) τ₂ 
... | c | refl | d | refl | left x | [ eq₁ ] | g | [ eq₂ ] rewrite eq₁ | eq₂  = cong ne (cong₂ _·_ refl (↻-ren-reify ρ g))
... | c | refl | d | refl | right y | pfft | g | p2  = {!   !} 
↻-ren-eval {κ = L} ρ (_·_ {κ₁} τ₁ τ₂) η = {!   !}
↻-ren-eval {κ = κ `→ κ₂} ρ (_·_ {κ₁} τ₁ τ₂) η = {!   !}
↻-ren-eval {κ = R[ κ ]} ρ (_·_ {κ₁} τ₁ τ₂) η = {!   !}
↻-ren-eval {κ = κ} ρ (τ₁ `→ τ₂) η = {!   !}
↻-ren-eval {κ = κ} ρ (`∀ κ₁ τ) η = {!   !}
↻-ren-eval {κ = κ} ρ (μ τ) η = {!   !}
↻-ren-eval {κ = κ} ρ (π₁ ⇒ τ) η = {!   !}
↻-ren-eval {κ = κ} ρ (lab l) η = {!   !}
↻-ren-eval {κ = κ} ρ (τ₁ ▹ τ₂) η = {!   !}
↻-ren-eval {κ = κ} ρ ⌊ τ ⌋ η = {!   !}
↻-ren-eval {κ = κ} ρ Π η = {!   !}
↻-ren-eval {κ = κ} ρ Σ η = {!   !}
↻-ren-eval {κ = κ} ρ (τ <$> τ₁) η = {!   !}

↻-weaken : ∀ (τ : Type Δ₁ κ) {κ'} → 
            eval τ (weakenSem {κ₂ = κ'} ∘ idEnv) ≡ eval (ren S τ) (extende (renSem S ∘ idEnv) (reflectNE {Δ = Δ₁ ,, κ'} (` Z)))
↻-weaken τ {κ'} = {!  !}

-- ↻-weaken : ∀ {κ'} (Gr (τ : Type Δ κ) →
--             renSem ρ (eval τ idEnv) ≡ eval (ren ρ τ) (extende (renSem S ∘ idEnv) (reflectNE (` Z)))
-- ↻-weaken {κ'} τ  = {!   !}

soundness : ∀ {τ₁ τ₂ : Type Δ κ} → τ₁ ↝* τ₂ → ⇓ τ₁ ≡ ⇓ τ₂
soundness (inst-↝ β) = {! refl  !}
soundness {κ = ★} (inst-↝ (Π² {l = l} {τ = τ})) = refl
soundness {κ = L} (inst-↝ (Π² {l = l} {τ = τ})) = refl
soundness {κ = κ `→ κ₁} (inst-↝ (Π² {l = l} {τ = τ})) with eval τ idEnv
... | left x = refl
... | right y = refl
soundness {κ = R[ κ ]} (inst-↝ (Π² {l = l} {τ = τ})) with eval τ idEnv 
... | right y = refl
... | left x rewrite nested-π-ne x = refl 
soundness {κ = κ} (inst-↝ (Πℓ² {l₁ = l₁} {l₂} {τ})) = refl
soundness {κ = κ₁ `→ R[ κ₂ ]} (inst-↝ (Πλ {l = l})) = 
    cong `λ (cong reify (cong π (cong right (cong₂ _,_ (trans (↻-ren-eval S l idEnv) (↻-weaken l)) refl))))
soundness {κ = R[ ★ ]} (inst-↝ ▹$) = {!   !}
soundness {κ = R[ L ]} (inst-↝ ▹$) = {!   !}
soundness {κ = R[ κ₂ `→ κ₃ ]} (inst-↝ ▹$) = {!   !}
soundness {κ = R[ R[ κ₂ ] ]} (inst-↝ ▹$) = {!   !} -- cong reify {! κ  !}
soundness refl-↝ = refl
soundness (trans-↝ s₁ s₂) = trans (soundness s₁) (soundness s₂) 
  