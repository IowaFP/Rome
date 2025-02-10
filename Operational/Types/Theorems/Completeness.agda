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
import Rome.Operational.Types.Normal.Properties.Renaming as NRP

open import Rome.Operational.Types.Semantic.Syntax
open import Rome.Operational.Types.Semantic.NBE
open import Rome.Operational.Types.Semantic.Renaming

-- open import Rome.Operational.Types.Theorems.Stability
open import Rome.Operational.Types.Theorems.Completeness.Relation
open import Rome.Operational.Types.Theorems.Completeness.Congruence
open import Rome.Operational.Types.Theorems.Completeness.Commutativity
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

    eq-λ : ∀ {τ υ : Type (Δ ,, κ₁) κ₂} → 

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
  -- Computational laws

    eq-β : ∀ {τ₁ : Type (Δ ,, κ₁) κ₂} {τ₂ : Type Δ κ₁} → 


        ----------------------------
        ((`λ τ₁) · τ₂) ≡t (τ₁ β[ τ₂ ])

    eq-Π : ∀ {l} {τ : Type Δ R[ κ ]} → 

         ----------------------------
         Π · (l ▹ τ) ≡t (l ▹ (Π · τ))

    eq-Σ : ∀ {l} {τ : Type Δ R[ κ ]} → 

         ----------------------------
         Σ · (l ▹ τ) ≡t (l ▹ (Σ · τ))


    eq-Πλ : ∀ {l} {τ : Type (Δ ,, κ₁) κ₂} → 

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


eq-Πℓ² : ∀ {l₁ l₂} {τ : Type Δ κ} → 
        -------------------------------------------
        Π · (l₁ ▹ (l₂ ▹ τ)) ≡t l₁ ▹ (Π · (l₂ ▹ τ))
eq-Πℓ² = eq-Π

-- eq-assoc-Π' : ∀ {ρ : Type Δ (R[ κ₁ `→ κ₂ ])} {τ : Type Δ κ₁} → 
--             -------------------------------------------
--             (Π · ρ) · τ ≡t Π · (ρ ?? τ)
-- eq-assoc-Π' = eq-sym {! eq-Π  !}            

-------------------------------------------------------------------------------
-- Fundamental theorem

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
fund {κ = κ} e (eq-· eq₁ eq₂) = cong-App (fund e eq₁) (fund e eq₂)
fund e (eq-∀ eq) = cong (`∀ _) (fund (extend-≋ (ren-≋ S ∘ e) (reflectNE-≋ refl)) eq)
fund {η₁ = η₁} {η₂} e (eq-μ {τ = τ} {υ} eq) with eval τ η₁ | eval υ η₂ | fund e eq
... | left x | left x₁ | refl = refl
... | right y | right y₁ | Unif-F , Unif-G , Ext = cong μ (cong `λ (Ext S refl))
fund e (eq-⌊⌋ eq) rewrite fund e eq = refl
fund e (eq-λ {τ = τ} {υ = υ} eq) = 
    (λ ρ₁ ρ₂ V₁ V₂ q → trans-≋ 
      (↻-renSem-eval ρ₂ τ (extend-≋ (λ x → ren-≋ ρ₁ (e x)) q)) 
      (idext (λ { Z → ren-≋ ρ₂ (refl-≋ᵣ q)
                ; (S x) → sym-≋ (ren-comp-≋ ρ₁ ρ₂ (e x)) }) τ))  , 
    (λ ρ₁ ρ₂ V₁ V₂ q → trans-≋ 
      (↻-renSem-eval ρ₂ υ (extend-≋ (λ x → ren-≋ ρ₁ (sym-≋ (e x))) q)) 
      (idext (λ { Z → ren-≋ ρ₂ (refl-≋ᵣ q)
                ; (S x) → sym-≋ (ren-comp-≋ ρ₁ ρ₂ (sym-≋ (e x))) }) υ)), 
    λ ρ q → fund (extend-≋ (λ x → ren-≋ ρ (e x)) q) eq
fund {η₁ = η₁} {η₂ = η₂} e (eq-β {τ₁ = τ₁} {τ₂}) = 
    trans-≋ 
        (idext 
            {η₂ = extende η₁ (eval τ₂ η₁)} 
            (λ { Z → idext {η₂ = η₁}  (refl-≋ₗ ∘ e) τ₂
           ; (S x) → renSem-id-≋ (refl-≋ₗ  (e x)) }) τ₁) 
        (sym-≋ 
            (trans-≋ 
                ((↻-subst-eval τ₁ (sym-≋ ∘ e) (extend ` τ₂))) 
                (idext (λ { Z → idext (refl-≋ₗ ∘ e) τ₂
                          ; (S x) → (refl-≋ₗ ∘ e) x }) τ₁)))
fund e (eq-▹ eq-l eq-τ) rewrite fund e eq-l = cong-▹ refl (fund e eq-τ)
fund e (eq-⇒ eq-π eq-τ) = cong₂ _⇒_ (fund-pred e eq-π) (fund e eq-τ)
fund {κ = R[ κ ]} {η₁ = η₁} {η₂ = η₂} e (eq-Π {l = l} {τ}) = (idext e l) , cong-π {τ₁ = eval τ η₁} {τ₂ = eval τ η₂} (idext e τ)
fund {κ = R[ κ ]} {η₁ = η₁} {η₂ = η₂} e (eq-Σ {l = l} {τ}) = (idext e l) , cong-σ {τ₁ = eval τ η₁} {τ₂ = eval τ η₂} (idext e τ)

-- it would be worthwhile to do the β and λ cases first, which should in effect be simpler.
fund {η₁ = η₁} {η₂ = η₂} e (eq-Πλ {l = l} {τ = τ}) = {!   !}
    -- (λ ρ₁ ρ₂ V₁ V₂ q → trans-≋ 
    --   (↻-ren-π ρ₂ (NR.ren ρ₁ (eval l η₁) ▹V
    --     eval τ (extende (λ {κ} v' → renSem ρ₁ (η₁ v')) V₁)) (NR.ren ρ₁ (eval l η₁) ▹V
    --     eval τ (extende (λ {κ} v' → renSem ρ₁ (η₁ v')) V₁)) (cong-▹ refl (refl-≋ₗ (idext (extend-≋ {η₂ = (renSem ρ₁ ∘ η₁)} (λ x → ren-≋ ρ₁ (refl-≋ₗ (e x))) q) τ) )) )
    --   (cong-π 
    --     (trans-≋ 
    --       (↻-ren-▹ ρ₂ (NR.ren ρ₁ (eval l η₁)) (eval τ (extende (λ {κ} v' → renSem ρ₁ (η₁ v')) V₁)) (eval τ (extende (λ {κ} v' → renSem ρ₁ (η₁ v')) V₁))  {!   !}) 
    --       -- I may need substitution lemma, again
    --       (cong-▹ (sym (NRP.ren-comp ρ₁ ρ₂ (eval l η₁))) {! ↻-renSem-eval ρ₂ τ {(extende (λ {κ} v' → renSem ρ₁ (η₁ v')) V₁)}  !})))) ,
    -- {!   !} , 
    -- {!   !}
fund {η₁ = η₁} {η₂} e (eq-▹$ {l = l} {τ} {F}) = 
    (idext e l) , 
    cong-App 
      {V₁ = eval F η₁} 
      {V₂ = eval F η₂} 
      (idext e F) 
      {W₁ = eval τ η₁} 
      {W₂ = eval τ η₂} 
      (idext e τ)
fund {κ = κ} {η₁ = η₁} {η₂} e (eq-assoc-Π {κ₁ = κ₁} {κ₂ = κ₂} {ρ = ρ} {τ}) with eval ρ η₁ | eval ρ η₂ | idext e ρ
... | right (l , F) | right (.l , G) | refl , q rewrite 
      NRP.ren-id l 
    | renSem-id {κ = κ₁ `→ κ₂} F 
    | renSem-id {κ = κ₁ `→ κ₂} G
    | renSem-id (eval τ η₂) = cong-π 
        {τ₁ = right (l , (F ·V eval τ η₁))}
        {τ₂ = right (l , (G ·V eval τ η₂))} 
        (refl , (cong-App q (idext e τ)))
-- Maybe we don't actually need <$> as a neutral form, and can instead eta expand?
... | left x | left .x | refl rewrite NRP.ren-id-ne x | sym (↻-ren-reify (S {κ₂ = κ}) (idext e τ)) = reflectNE-≋ {! sym (↻-ren-reify (S {κ₂ = κ}) (idext e τ))   !} 

idEnv-≋ : ∀ {Δ} → Env-≋ (idEnv {Δ}) (idEnv {Δ})
idEnv-≋ x = reflectNE-≋ refl

completeness : ∀ {τ₁ τ₂ : Type Δ κ} → τ₁ ≡t τ₂ → ⇓ τ₁ ≡ ⇓ τ₂
completeness eq = reify-≋ (fund idEnv-≋ eq)  
 
 