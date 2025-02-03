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
open import Rome.Operational.Types.Theorems.Completeness.Relation
open import Rome.Operational.Types.Theorems.Completeness.RelationProperties
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

    eq-Π : ∀ {l} {τ : Type Δ R[ κ ]} → 

         ----------------------------
         Π · (l ▹ τ) ≡t (l ▹ (Π · τ))


    eq-Πλ : ∀ {l} {τ : Type (Δ ,, κ₁) R[ κ₂ ]} → 

        -------------------------------------------
        Π · (l ▹ `λ τ) ≡t `λ (Π · (weaken l ▹ τ))

    eq-▹$ : ∀ {l} {τ : Type Δ κ₁} {F : Type Δ (κ₁ `→ κ₂)} → 

        -------------------------------------------
        (F <$> (l ▹ τ)) ≡t (l ▹ F · τ)

    eq-assoc-Π : ∀ {ρ : Type Δ (R[ κ₁ `→ κ₂ ])} {τ : Type Δ κ₁} → 

        -------------------------------------------
        (Π · ρ) · τ ≡t Π · (ρ ?? τ)

-------------------------------------------------------------------------------
-- Admissable but informative rules

eq-Π² : ∀ {l} {τ : Type Δ R[ κ ]} → 
        ----------------------------
        Π · (Π · (l ▹ τ)) ≡t Π · (l ▹ (Π · τ))
eq-Π² = eq-· eq-refl eq-Π 


eq-Πℓ² : ∀ {l₁ l₂} {τ : Type Δ R[ κ ]} → 
        -------------------------------------------
        Π · (l₁ ▹ (l₂ ▹ τ)) ≡t l₁ ▹ (Π · (l₂ ▹ τ))
eq-Πℓ² = eq-Π

-------------------------------------------------------------------------------
-- Fundamental theorem

nested-π-ne : ∀ (x : NeutralType Δ R[ R[  κ ] ]) → πNE x ≋ π (left x)
nested-π-ne {κ = ★} x = refl
nested-π-ne {κ = L} x = refl
nested-π-ne {κ = κ `→ κ₁} x = refl
nested-π-ne {κ = R[ κ ]} x = refl

fund : ∀ {τ₁ τ₂ : Type Δ₁ κ} {η₁ η₂ : Env Δ₁ Δ₂} → 
       Env-≋ η₁ η₂ → τ₁ ≡t τ₂ → eval τ₁ η₁ ≋ eval τ₂ η₂
fund-pred : ∀ {π₁ π₂ : Pred Δ₁ R[ κ ]} {η₁ η₂ : Env Δ₁ Δ₂} → 
            Env-≋ η₁ η₂ → π₁ ≡p π₂ → evalPred π₁ η₁ ≡ evalPred π₂ η₂

fund-pred e (τ₁ eq-≲ τ₂) = cong₂ _≲_ (reify-≋ (fund e τ₁)) (reify-≋ (fund e τ₂))
fund-pred e (τ₁ eq-· τ₂ ~ τ₃) rewrite
    reify-≋ (fund e τ₁) 
  | reify-≋ (fund e τ₂) 
  | reify-≋ (fund e τ₃) = refl

fund {τ₁ = τ} e eq-refl = idext e τ
fund e (eq-sym eq) = sym-≋ (fund (sym-≋ ∘ e) eq)
fund e (eq-trans eq₁ eq₂) = trans-≋ (fund (refl-≋ₗ ∘ e) eq₁) (fund e eq₂)
fund e (eq-→ {τ₁ = τ₁} {υ₁ = υ₁} eq-τ eq-υ) = cong₂ _`→_ (fund e eq-τ) (fund e eq-υ)
fund {κ = ★} e (eq-· eq₁ eq₂) = cong-App (fund e eq₁) (fund e eq₂)
fund {κ = L} e (eq-· eq₁ eq₂) = cong-App (fund e eq₁) (fund e eq₂)
fund {κ = κ `→ κ₁} e (eq-· eq₁ eq₂) = cong-App (fund e eq₁) (fund e eq₂)
fund {κ = R[ κ ]} e (eq-· eq₁ eq₂) = cong-App (fund e eq₁) (fund e eq₂)
fund e (eq-∀ eq) = cong (`∀ _) (fund (extend-≋ (ren-≋ S ∘ e) (reflectNE-≋ refl)) eq)
fund {η₁ = η₁} {η₂} e (eq-μ {τ = τ} {υ} eq) with eval τ η₁ | eval υ η₂ | fund e eq
... | left x | left x₁ | refl = refl
... | right y | right y₁ | Unif-F , Unif-G , Ext = cong μ (cong `λ (Ext S refl))
fund e (eq-⌊⌋ eq) rewrite fund e eq = refl
fund e (eq-λ eq) = {! !}
fund e eq-β = {! !}
fund e (eq-▹ eq-l eq-τ) rewrite fund e eq-l = cong-▹ refl (fund e eq-τ)
fund e (eq-⇒ eq-π eq-τ) = cong₂ _⇒_ (fund-pred e eq-π) (fund e eq-τ)
fund {κ = R[ ★ ]} e (eq-Π {l = l} {τ}) = cong row (cong₂ _▹_ (idext e l) (cong (π {κ = ★}) (idext {κ = R[ ★ ]} e τ)))
fund {κ = R[ L ]} e (eq-Π {l = l} {τ}) = cong row (cong₂ _▹_ (idext e l) (cong (π {κ = L}) (idext {κ = R[ L ]} e τ)))
fund {κ = R[ κ `→ κ₁ ]} {η₁ = η₁} {η₂ = η₂} e (eq-Π {l = ℓ} {τ}) with eval ℓ η₁ | eval ℓ η₂ | idext e ℓ | eval τ η₁ | eval τ η₂ | idext e τ 
... | l | .l | refl | left x | left x₁ | refl = refl , refl
... | l | .l | refl | right (l' , left f) | right (.l' , left .f) | refl , refl = 
    refl , Unif-NE-π▹· l' f , Unif-NE-π▹· l' f , λ ρ v → cong-π (cong-▹ refl (reflectNE-≋ (cong₂ _·_ refl (reify-≋ v))))
... | l | .l | refl | right (l' , right F) | right (.l' , right G) | refl , (Unif-F , Unif-G , Ext) = 
    refl , 
    Unif-π▹· l' F (Unif-F , (Unif-F , refl-Extₗ Ext)) , 
    Unif-π▹· l' G (Unif-G , (Unif-G , refl-Extᵣ Ext)) , 
    λ ρ v → cong-π (cong-▹ refl (Ext ρ v))
fund {κ = R[ R[ κ ] ]} {η₁ = η₁} {η₂ = η₂} e (eq-Π {l = ℓ} {τ}) with eval ℓ η₁ | eval ℓ η₂ | idext e ℓ | eval τ η₁ | eval τ η₂ | idext e τ 
... | l | .l | refl | left x | left x₁ | refl = refl , nested-π-ne x
... | l | .l | refl | right y | right y₁ | c = refl , (cong-π c)
-- it would be worthwhile to do the β and λ cases first, which should in effect be simpler.
fund e eq-Πλ = {! !}
fund e eq-▹$ = {!  !}
fund e eq-assoc-Π = {!  !}

idEnv-≋ : ∀ {Δ} → Env-≋ (idEnv {Δ}) (idEnv {Δ})
idEnv-≋ x = reflectNE-≋ refl

completeness : ∀ {τ₁ τ₂ : Type Δ κ} → τ₁ ≡t τ₂ → ⇓ τ₁ ≡ ⇓ τ₂
completeness eq = reify-≋ (fund idEnv-≋ eq) 