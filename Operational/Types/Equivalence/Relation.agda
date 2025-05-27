{-# OPTIONS --allow-unsolved-metas #-}
module Rome.Operational.Types.Equivalence.Relation where

open import Rome.Operational.Prelude
open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

open import Rome.Operational.Types.Syntax
open import Rome.Operational.Types.Substitution
open import Rome.Operational.Types.Renaming

-------------------------------------------------------------------------------
-- Small step relation on terms

infix 0 _≡t_
infix 0 _≡p_
data _≡p_ : Pred Type Δ R[ κ ] → Pred Type Δ R[ κ ] → Set
data _≡t_ : Type Δ κ → Type Δ κ → Set 

private
    variable
        ℓ ℓ₁ ℓ₂ ℓ₃ : Label
        l l₁ l₂ l₃ : Type Δ L
        ρ₁ ρ₂ ρ₃   : Type Δ R[ κ ]
        π₁ π₂    : Pred Type Δ R[ κ ]
        τ τ₁ τ₂ τ₃ υ υ₁ υ₂ υ₃ : Type Δ κ 

data _≡r_ : SimpleRow Type Δ R[ κ ] → SimpleRow Type Δ R[ κ ] → Set where 

  eq-[] : 
    
    _≡r_  {Δ = Δ} {κ = κ} [] []
    
  eq-cons : {xs ys : SimpleRow Type Δ R[ κ ]} → 

            ℓ₁ ≡ ℓ₂ → τ₁ ≡t τ₂ → xs ≡r ys → 
            -----------------------
            ((ℓ₁ , τ₁) ∷ xs) ≡r ((ℓ₂ , τ₂) ∷ ys)

data _≡p_ where

  _eq-≲_ : 

        τ₁ ≡t υ₁ → τ₂ ≡t υ₂ → 
        --------------------
        τ₁ ≲ τ₂ ≡p  υ₁ ≲ υ₂

  _eq-·_~_ : 

        τ₁ ≡t υ₁ → τ₂ ≡t υ₂ → τ₃ ≡t υ₃ → 
        -----------------------------------
        τ₁ · τ₂ ~ τ₃ ≡p  υ₁ · υ₂ ~ υ₃

Ξλ-ordered : ∀ (ρ : SimpleRow Type Δ R[ κ₁ `→ κ₂ ]) (oρ : Ordered ρ) → 
                  Ordered (map (λ (l , τ) → l , weakenₖ τ · (` Z)) ρ)

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
        `∀ τ ≡t `∀ υ

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

    eq-<$> : ∀ {τ₁ υ₁ : Type Δ (κ₁ `→ κ₂)} {τ₂ υ₂ : Type Δ R[ κ₁ ]} → 

        τ₁ ≡t υ₁ → τ₂ ≡t υ₂ →
        ---------------------
        τ₁ <$> τ₂ ≡t υ₁ <$> υ₂        

    eq-⌊⌋ : 

        τ ≡t υ →
        -------------
        ⌊ τ ⌋ ≡t ⌊ υ ⌋

    eq-⇒ :

         π₁ ≡p π₂ → τ₁ ≡t τ₂ →
        ------------------------
        (π₁ ⇒ τ₁) ≡t (π₂ ⇒ τ₂)

    eq-lab : 
           
           ℓ₁ ≡ ℓ₂ →
           -------------
           lab {Δ = Δ} ℓ₁ ≡t lab ℓ₂
    
    eq-row : 
        ∀ {ρ₁ ρ₂ : SimpleRow Type Δ R[ κ ]} {oρ₁ : True (ordered? ρ₁)} 
          {oρ₂ : True (ordered? ρ₂)} → 
  
        ρ₁ ≡r ρ₂ → 
        -------------------------------------------
        ⦅ ρ₁ ⦆ oρ₁ ≡t ⦅ ρ₂ ⦆ oρ₂

    eq-▹ : ∀ {l₁ l₂ : Type Δ L} {τ₁ τ₂ : Type Δ κ} → 
         
           l₁ ≡t l₂   →    τ₁ ≡t τ₂ → 
           ------------------------------------
           (l₁ ▹ τ₁) ≡t (l₂ ▹ τ₂)

    eq-─ : ∀ {ρ₂ ρ₁ υ₂ υ₁ : Type Δ R[ κ ]} → 
         
           ρ₂ ≡t υ₂   →    ρ₁ ≡t υ₁ → 
           ------------------------------------
           (ρ₂ ─ ρ₁) ≡t (υ₂ ─ υ₁)

  -- -------------------------------------
  -- η-laws  
         
    eq-η : ∀ {f : Type Δ (κ₁ `→ κ₂)} → 


        ----------------------------
        f ≡t `λ (weakenₖ f · (` Z))

  -- -------------------------------------
  -- Computational laws

    eq-β : ∀ {τ₁ : Type (Δ ,, κ₁) κ₂} {τ₂ : Type Δ κ₁} → 


        ----------------------------
        ((`λ τ₁) · τ₂) ≡t (τ₁ βₖ[ τ₂ ])

    eq-labTy : 

        l ≡t lab ℓ → 
        -------------------------------------------
        (l ▹ τ) ≡t ⦅ [ (ℓ  , τ) ] ⦆ tt

    eq-▹$ : ∀ {l} {τ : Type Δ κ₁} {F : Type Δ (κ₁ `→ κ₂)} → 

        ---------------------------------
        (F <$> (l ▹ τ)) ≡t (l ▹ (F · τ))

    eq-map : ∀ {F : Type Δ (κ₁ `→ κ₂)} {ρ : SimpleRow Type Δ R[ κ₁ ]} {oρ : True (ordered? ρ)} → 

         -------------------------------
         F <$> (⦅ ρ ⦆ oρ) ≡t ⦅ map (overᵣ (F ·_)) ρ ⦆ (fromWitness (map-overᵣ ρ (F ·_) (toWitness oρ)))
    
    eq-Π : ∀ {ρ : Type Δ R[ R[ κ ] ]} {nl : True (notLabel? κ)} → 

         ----------------------------
         Π {notLabel = nl} · ρ ≡t Π {notLabel = nl} <$> ρ

    eq-Σ : ∀ {ρ : Type Δ R[ R[ κ ] ]} {nl : True (notLabel? κ)} → 

         ----------------------------
         Σ {notLabel = nl} · ρ ≡t Σ {notLabel = nl} <$> ρ
        
    eq-Π-assoc : ∀ {ρ : Type Δ (R[ κ₁ `→ κ₂ ])} {τ : Type Δ κ₁} {nl : True (notLabel? κ₂)} → 

        ----------------------------
        (Π {notLabel = nl} · ρ) · τ ≡t Π {notLabel = nl} · (ρ ?? τ)

    eq-Σ-assoc : ∀ {ρ : Type Δ (R[ κ₁ `→ κ₂ ])} {τ : Type Δ κ₁} {nl : True (notLabel? κ₂)} → 

        ----------------------------
        (Σ {notLabel = nl} · ρ) · τ ≡t Σ {notLabel = nl} · (ρ ?? τ)
        

Ξλ-ordered [] oρ = tt
Ξλ-ordered (x ∷ []) oρ = tt
Ξλ-ordered ((l₁ , τ₁) ∷ (l₂ , τ₂) ∷ ρ) (l₁<l₂ , oρ) = l₁<l₂ , Ξλ-ordered ((l₂ , τ₂) ∷ ρ) oρ

-- -------------------------------------------------------------------------------
-- -- Lifting propositional equality to type equivalence

inst : ∀ {τ₁ τ₂ : Type Δ κ} → τ₁ ≡ τ₂ → τ₁ ≡t τ₂ 
inst refl = eq-refl

instᵣ :  ∀ {ρ₁ ρ₂ : SimpleRow Type Δ R[ κ ]} → ρ₁ ≡ ρ₂ → ρ₁ ≡r ρ₂
instᵣ {ρ₁ = []} refl = eq-[]
instᵣ {ρ₁ = x ∷ ρ₁} refl = eq-cons refl eq-refl (instᵣ refl)

-- -------------------------------------------------------------------------------
-- -- ≡r forms an equivalence relation

symᵣ : ∀ {xs ys : SimpleRow Type Δ R[ κ ]} → xs ≡r ys → ys ≡r xs
symᵣ eq-[] = eq-[]
symᵣ (eq-cons l x eq) = eq-cons (sym l) (eq-sym x) (symᵣ eq)

transᵣ : ∀ {xs ys zs : SimpleRow Type Δ R[ κ ]} → xs ≡r ys → ys ≡r zs → xs ≡r zs
transᵣ eq-[] eq-[] = eq-[]
transᵣ (eq-cons eq-l₁ eq-τ₁ eq-xs) (eq-cons eq-l₂ eq-τ₂ eq-ys) = eq-cons (trans eq-l₁ eq-l₂) (eq-trans eq-τ₁ eq-τ₂) (transᵣ eq-xs eq-ys)
