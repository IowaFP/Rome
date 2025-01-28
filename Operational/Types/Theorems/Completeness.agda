{-# OPTIONS --allow-unsolved-metas #-}
module Rome.Operational.Types.Theorems.Completeness where

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

-- open import Rome.Operational.Types.Theorems.Stability
open import Rome.Operational.Types.Theorems.CompletenessRelation
open import Rome.Shared.Postulates.FunExt

-------------------------------------------------------------------------------
-- Small step relation on terms

infix 0 _≡t_
infix 0 _≡p_
data _≡p_ : Pred Δ R[ κ ] → Pred Δ R[ κ ] → Set
data _≡t_ : Type Δ κ → Type Δ κ → Set 

private
    variable
        l l₁ l₂ l₃ : Type Δ L
        ρ₁ ρ₂ ρ₃   : Type Δ R[ κ ]
        π₁ π₂    : Pred Δ R[ κ ]
        τ τ₁ τ₂ τ₃ υ υ₁ υ₂ υ₃ : Type Δ κ 

data _≡p_ where

  _eq-≲_ : 

        τ₁ ≡t υ₁ → τ₂ ≡t υ₂ → 
        --------------------
        τ₁ ≲ τ₂ ≡p  υ₁ ≲ υ₂

  _eq-·_~_ : 

        τ₁ ≡t υ₁ → τ₂ ≡t υ₂ → τ₃ ≡t υ₃ → 
        -----------------------------------
        τ₁ · τ₂ ~ τ₃ ≡p  υ₁ · υ₂ ~ υ₃


data _≡t_ where 

  -- -------------------------------------
  -- Eq. relation
    
    eq-refl : 

        ------
        τ ≡t τ 

    eq-sym : 
    
        τ₁ ≡t τ₂ →
        ----------
        τ₂ ≡t τ₁

    eq-trans : 
    
        τ₁ ≡t τ₂ → τ₂ ≡t τ₃ → 
        ---------------------
        τ₁ ≡t τ₃

  -- -------------------------------------
  -- Congruence rules

    eq-→ : 

        τ₁ ≡t τ₂ → υ₁ ≡t υ₂ →
        -----------------------
        τ₁ `→ υ₁ ≡t τ₂ `→ υ₂

    eq-∀ : 

        τ ≡t υ →
        ----------------
        `∀ κ τ ≡t `∀ κ υ

    eq-μ : 

        τ ≡t υ →
        ----------------
        μ τ ≡t μ υ

    eq-λ : 

        τ ≡t υ →
        ----------------
        `λ τ ≡t `λ υ

    eq-· :

        τ₁ ≡t υ₁ → τ₂ ≡t υ₂ →
        ---------------------
        τ₁ · τ₂ ≡t υ₁ · υ₂

    eq-⌊⌋ : 

        τ ≡t υ →
        -------------
        ⌊ τ ⌋ ≡t ⌊ υ ⌋

    eq-▹ :

         l₁ ≡t l₂ → τ₁ ≡t τ₂ →
        ------------------------
        (l₁ ▹ τ₁) ≡t (l₂ ▹ τ₂)

    eq-⇒ :

         π₁ ≡p π₂ → τ₁ ≡t τ₂ →
        ------------------------
        (π₁ ⇒ τ₁) ≡t (π₂ ⇒ τ₂)
         

  -- -------------------------------------
  -- Interesting rules

    eq-β : ∀ {τ₁ : Type (Δ ,, κ₁) κ₂} {τ₂ : Type Δ κ₁} → 


        ----------------------------
        ((`λ τ₁) · τ₂) ≡t (τ₁ β[ τ₂ ])

    eq-Π² : ∀ {l} {τ : Type Δ R[ κ ]} → 

         ----------------------------
         Π · (Π · (l ▹ τ)) ≡t Π · (l ▹ (Π · τ))
    
    eq-Πℓ² : ∀ {l₁ l₂} {τ : Type Δ R[ κ ]} → 

        -------------------------------------------
        Π · (l₁ ▹ (l₂ ▹ τ)) ≡t l₁ ▹ (Π · (l₂ ▹ τ))

    eq-Πλ : ∀ {l} {τ : Type (Δ ,, κ₁) R[ κ₂ ]} → 

        -------------------------------------------
        Π · (l ▹ `λ τ) ≡t `λ (Π · (weaken l ▹ τ))

    eq-▹$ : ∀ {l} {τ : Type Δ κ₁} {F : Type Δ (κ₁ `→ κ₂)} → 

        -------------------------------------------
        (F <$> (l ▹ τ)) ≡t (l ▹ F · τ)

    eq-assoc-Π : ∀ {ρ : Type Δ (R[ κ₁ `→ κ₂ ])} {τ : Type Δ κ₁} → 

        -------------------------------------------
        (Π · ρ) · τ ≡t Π · (ρ ?? τ)

nested-π-ne : ∀ (x : NeutralType Δ R[ R[  κ ] ]) → πNE x ≡ π (left x)
nested-π-ne {κ = ★} x = refl
nested-π-ne {κ = L} x = refl
nested-π-ne {κ = κ `→ κ₁} x = refl
nested-π-ne {κ = R[ κ ]} x = refl

-- -- ↻-ren-eval : ∀ (ρ : Renaming Δ₂ Δ₃) (τ : Type Δ₁ κ) (η₁ : Env Δ₁ Δ₂) (η₂ : Env Δ₃ Δ₃) → 
-- --                 η₁ ≡ η₂ → (renSem ρ (eval τ η₁)) ≡ eval τ (renSem ρ ∘ η₂)
-- -- ↻-ren-eval ρ τ η₁ η₂ q = {!   !}

-- ↻-ren-reify : ∀ (ρ : Renaming Δ₁ Δ₂) → (v : SemType Δ₁ κ) → 
--               NR.ren ρ (reify v) ≡ reify (renSem ρ v)
-- ↻-ren-reify {κ = ★} ρ v = refl
-- ↻-ren-reify {κ = L} ρ v = refl
-- ↻-ren-reify {κ = κ₁ `→ κ₂} ρ (left x) = refl
-- -- I think I found where I need uniformity.
-- ↻-ren-reify {κ = κ₁ `→ κ₂} ρ (right F) = cong `λ (trans (↻-ren-reify (lift ρ) (F S (reflectNE (` Z)))) (cong reify {!   !}))
-- ↻-ren-reify {κ = R[ κ ]} ρ v = {!   !}              

-- ↻-ren-eval : ∀ (ρ : Renaming Δ₂ Δ₃) (τ : Type Δ₁ κ) (η : Env Δ₁ Δ₂) → 
--                 (renSem ρ (eval τ η)) ≡ eval τ (renSem ρ ∘ η)
-- ↻-ren-eval {κ = κ} ρ Unit η = refl
-- ↻-ren-eval {κ = ★} ρ (` α) η = refl
-- ↻-ren-eval {κ = L} ρ (` α) η = refl
-- ↻-ren-eval {κ = κ `→ κ₁} ρ (` α) η = refl
-- ↻-ren-eval {κ = R[ κ ]} ρ (` α) η = refl
-- ↻-ren-eval {κ = κ} ρ (`λ τ) η = cong right 
--     (extensionality-i (extensionality 
--         (λ ρ' → extensionality 
--             (λ v → idext (λ { Z → refl
--                             ; (S x) → renSem-comp (η x) ρ ρ' }) τ))))
-- ↻-ren-eval {κ = ★} ρ (_·_ {κ₁} τ₁ τ₂) η 
--     with eval τ₁ (λ x → renSem ρ (η x)) 
--     | sym (↻-ren-eval ρ τ₁ η) 
--     | eval τ₂ (λ x → renSem ρ (η x)) 
--     | sym (↻-ren-eval ρ τ₂ η) 
--     | eval τ₁ η 
--     | inspect (λ x → eval x η) τ₁ 
--     | eval τ₂ η
--     | inspect (λ x → eval x η) τ₂ 
-- ... | c | refl | d | refl | left x | [ eq₁ ] | g | [ eq₂ ] rewrite eq₁ | eq₂  = cong ne (cong₂ _·_ refl (↻-ren-reify ρ g))
-- ... | c | refl | d | refl | right y | pfft | g | p2  = {!   !} 
-- ↻-ren-eval {κ = L} ρ (_·_ {κ₁} τ₁ τ₂) η = {!   !}
-- ↻-ren-eval {κ = κ `→ κ₂} ρ (_·_ {κ₁} τ₁ τ₂) η = {!   !}
-- ↻-ren-eval {κ = R[ κ ]} ρ (_·_ {κ₁} τ₁ τ₂) η = {!   !}
-- ↻-ren-eval {κ = κ} ρ (τ₁ `→ τ₂) η = {!   !}
-- ↻-ren-eval {κ = κ} ρ (`∀ κ₁ τ) η = {!   !}
-- ↻-ren-eval {κ = κ} ρ (μ τ) η = {!   !}
-- ↻-ren-eval {κ = κ} ρ (π₁ ⇒ τ) η = {!   !}
-- ↻-ren-eval {κ = κ} ρ (lab l) η = {!   !}
-- ↻-ren-eval {κ = κ} ρ (τ₁ ▹ τ₂) η = {!   !}
-- ↻-ren-eval {κ = κ} ρ ⌊ τ ⌋ η = {!   !}
-- ↻-ren-eval {κ = κ} ρ Π η = {!   !}
-- ↻-ren-eval {κ = κ} ρ Σ η = {!   !}
-- ↻-ren-eval {κ = κ} ρ (τ <$> τ₁) η = {!   !}

-- ↻-weaken : ∀ (τ : Type Δ₁ κ) {κ'} → 
--             eval τ (weakenSem {κ₂ = κ'} ∘ idEnv) ≡ eval (ren S τ) (extende (renSem S ∘ idEnv) (reflectNE {Δ = Δ₁ ,, κ'} (` Z)))
-- ↻-weaken τ {κ'} = {!  !}

-- -- ↻-weaken : ∀ {κ'} (Gr (τ : Type Δ κ) →
-- --             renSem ρ (eval τ idEnv) ≡ eval (ren ρ τ) (extende (renSem S ∘ idEnv) (reflectNE (` Z)))
-- -- ↻-weaken {κ'} τ  = {!   !}


fund : ∀ {τ₁ τ₂ : Type Δ₁ κ} {η₁ η₂ : Env Δ₁ Δ₂} → Env-≋ η₁ η₂ → τ₁ ≡t τ₂ → eval τ₁ η₁ ≋ eval τ₂ η₂
fund-pred : ∀ {π₁ π₂ : Pred Δ₁ R[ κ ]} {η₁ η₂ : Env Δ₁ Δ₂} → Env-≋ η₁ η₂ → π₁ ≡p π₂ → evalPred π₁ η₁ ≡ evalPred π₂ η₂

fund-pred e (τ₁ eq-≲ τ₂) = cong₂ _≲_ (reify-≋ (fund e τ₁)) (reify-≋ (fund e τ₂))
fund-pred e (τ₁ eq-· τ₂ ~ τ₃) rewrite
    reify-≋ (fund e τ₁) 
  | reify-≋ (fund e τ₂) 
  | reify-≋ (fund e τ₃) = refl

fund {τ₁ = τ} e eq-refl = idext e τ
fund e (eq-sym eq) = sym-≋ (fund (sym-≋ ∘ e) eq)
fund e (eq-trans eq₁ eq₂) = trans-≋ (fund (refl-≋ ∘ e) eq₁) (fund e eq₂)
fund e (eq-→ {τ₁ = τ₁} {υ₁ = υ₁} eq-τ eq-υ) = cong₂ _`→_ (fund e eq-τ) (fund e eq-υ)
fund {κ = ★} e (eq-· eq₁ eq₂) = App-≋ (fund e eq₁) (fund e eq₂)
fund {κ = L} e (eq-· eq₁ eq₂) = App-≋ (fund e eq₁) (fund e eq₂)
fund {κ = κ `→ κ₁} e (eq-· eq₁ eq₂) = App-≋ (fund e eq₁) (fund e eq₂)
fund {κ = R[ κ ]} e (eq-· eq₁ eq₂) = App-≋ (fund e eq₁) (fund e eq₂)
fund e (eq-∀ eq) = cong (`∀ _) (fund (extend-≋ (ren-≋ S ∘ e) (reflectNE-≋ refl)) eq)
fund {η₁ = η₁} {η₂} e (eq-μ {τ = τ} {υ} eq) with eval τ η₁ | eval υ η₂ | fund e eq
... | left x | left x₁ | refl = refl
... | right y | right y₁ | Unif-F , Unif-G , Ext = cong μ (cong `λ (Ext S refl))
fund e (eq-⌊⌋ eq) rewrite fund e eq = refl
fund e (eq-λ eq) = {! !}
fund e (eq-▹ eq-l eq-τ) rewrite fund e eq-l = ▹-≋ refl (fund e eq-τ)
fund e (eq-⇒ eq-π eq-τ) = cong₂ _⇒_ (fund-pred e eq-π) (fund e eq-τ)
fund e eq-β = {!!}
fund {κ = ★} e (eq-Π² {l = l} {τ = τ}) rewrite 
    fund e (eq-refl {τ = l}) 
  | fund e (eq-refl {τ = τ}) = refl
fund {κ = L} e (eq-Π² {l = l} {τ = τ}) rewrite 
    fund e (eq-refl {τ = l}) 
  | fund e (eq-refl {τ = τ}) = refl
fund {κ = κ₁ `→ κ₂} {η₁ = η₁} {η₂ = η₂} e (eq-Π² {l = l} {τ = τ}) with eval τ η₁ | eval τ η₂ | fund {τ₁ = τ} {τ₂ = τ} e eq-refl
... | left x | left .x | refl = 
  (λ ρ₁ ρ₂ V₁ V₂ q → {!!}) ,
  {!!} ,
  {!!}
... | right (l , left f) | right (.l , left .f) | refl , refl = (λ ρ₁ ρ₂ V₁ V₂ x → trans-≋ {!!} {!!}) , ({!!} , {!!})
... | right (l , right F) | right (.l , right G) | refl , eq = {!!}
fund {κ = R[ κ ]} e eq-Π² = {!!}
fund e eq-Πℓ² = {!!}
fund e eq-Πλ = {!!}
fund e eq-▹$ = {!!}
fund e eq-assoc-Π = {!!}

idEnv-≋ : ∀ {Δ} → Env-≋ (idEnv {Δ}) (idEnv {Δ})
idEnv-≋ x = reflectNE-≋ refl

completeness : ∀ {τ₁ τ₂ : Type Δ κ} → τ₁ ≡t τ₂ → ⇓ τ₁ ≡ ⇓ τ₂
completeness eq = reify-≋ (fund idEnv-≋ eq) 

-- soundness {κ = ★} (inst-≡t (Π² {l = l} {τ = τ})) = refl
-- soundness {κ = L} (inst-≡t (Π² {l = l} {τ = τ})) = refl
-- soundness {κ = κ `→ κ₁} (inst-≡t (Π² {l = l} {τ = τ})) with eval τ idEnv
-- ... | left x = refl
-- ... | right y = refl
-- soundness {κ = R[ κ ]} (inst-≡t (Π² {l = l} {τ = τ})) with eval τ idEnv 
-- ... | right y = refl
-- ... | left x rewrite nested-π-ne x = refl 
-- soundness {κ = κ} (inst-≡t (Πℓ² {l₁ = l₁} {l₂} {τ})) = refl
-- soundness {κ = κ₁ `→ R[ κ₂ ]} (inst-≡t (Πλ {l = l})) = 
--     cong `λ (cong reify (cong π (cong right (cong₂ _,_ (trans (↻-ren-eval S l idEnv) (↻-weaken l)) refl))))
-- soundness {κ = R[ ★ ]} (inst-≡t ▹$) = {!   !}
-- soundness {κ = R[ L ]} (inst-≡t ▹$) = {!   !}
-- soundness {κ = R[ κ₂ `→ κ₃ ]} (inst-≡t ▹$) = {!   !}
-- soundness {κ = R[ R[ κ₂ ] ]} (inst-≡t ▹$) = {!   !} -- cong reify {! κ  !}
-- soundness refl-≡t = refl
-- soundness (trans-≡t s₁ s₂) = trans (soundness s₁) (soundness s₂) 
  
