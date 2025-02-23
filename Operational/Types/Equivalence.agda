{-# OPTIONS --allow-unsolved-metas #-}
module Rome.Operational.Types.Equivalence where

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

    eq-<$> : ∀ {τ₁ υ₁ : Type Δ (κ₁ `→ κ₂)} {τ₂ υ₂ : Type Δ R[ κ₁ ]} → 

        τ₁ ≡t υ₁ → τ₂ ≡t υ₂ →
        ---------------------
        τ₁ <$> τ₂ ≡t υ₁ <$> υ₂        

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
  -- η-laws  
         
    eq-η : ∀ {f : Type Δ (κ₁ `→ κ₂)} → 


        ----------------------------
        f ≡t `λ (weaken f · (` Z))

  -- -------------------------------------
  -- Computational laws

    eq-β : ∀ {τ₁ : Type (Δ ,, κ₁) κ₂} {τ₂ : Type Δ κ₁} → 


        ----------------------------
        ((`λ τ₁) · τ₂) ≡t (τ₁ β[ τ₂ ])

    eq-Π : ∀ {l} {τ : Type Δ R[ κ ]} → 

         ----------------------------
         Π · (l ▹ τ) ≡t (l ▹ (Π · τ))
    
    eq-app-lift-Π : ∀ {τ : Type Δ R[ R[ κ ] ]} → 

         ----------------------------
         Π · τ ≡t Π <$> τ

    eq-Σ : ∀ {l} {τ : Type Δ R[ κ ]} → 

         ----------------------------
         Σ · (l ▹ τ) ≡t (l ▹ (Σ · τ))


    eq-Πλ : ∀ {l} {τ : Type (Δ ,, κ₁) κ₂} → 

        -------------------------------------------
        Π · (l ▹ `λ τ) ≡t `λ (Π · (weaken l ▹ τ))

    eq-▹$ : ∀ {l} {τ : Type Δ κ₁} {F : Type Δ (κ₁ `→ κ₂)} → 

        -------------------------------------------
        (F <$> (l ▹ τ)) ≡t (l ▹ (F · τ))
        
    -- TODO:
    -- using ?? for convenience here is causing headache later.
    eq-assoc-Π : ∀ {ρ : Type Δ (R[ κ₁ `→ κ₂ ])} {τ : Type Δ κ₁} → 

        ----------------------------
        (Π · ρ) · τ ≡t Π · (ρ ?? τ)

    eq-assoc-Σ : ∀ {ρ : Type Δ (R[ κ₁ `→ κ₂ ])} {τ : Type Δ κ₁} → 

        ----------------------------
        (Σ · ρ) · τ ≡t Σ · (ρ ?? τ)
        
-------------------------------------------------------------------------------
-- Lifting propositional equality to type equivalence

inst : ∀ {τ₁ τ₂ : Type Δ κ} → τ₁ ≡ τ₂ → τ₁ ≡t τ₂ 
inst refl = eq-refl


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