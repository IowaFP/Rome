{-# OPTIONS --safe #-}
module R2Mu.Equivalence.Syntax where

open import Agda.Primitive
open import Level

open import R2Mu.Kinds
open import R2Mu.Types
open import R2Mu.Types.Substitution

--------------------------------------------------------------------------------
-- Generalized vars.

private
  variable
    Δ : KEnv
    κ κ' κ₁ κ₂ κ₃ : Kind
    
    
--------------------------------------------------------------------------------
-- Type & Predicate equivalence.

data _≡p_ : (π₁ π₂ : Pred Δ κ) → Set
            
data _≡t_ : (τ υ : Type Δ κ) → Set

infix 0 _≡p_
infix 0 _≡t_

data _≡p_ where
  peq-≲ : ∀ {τ₁ τ₂ υ₁ υ₂ : Type Δ R[ κ ]} →

          τ₁ ≡t υ₁ → τ₂ ≡t υ₂ →
          ------------------------
          (τ₁ ≲ τ₂) ≡p υ₁ ≲ υ₂

  peq-· : ∀ {τ₁ τ₂ τ₃ υ₁ υ₂ υ₃ : Type Δ R[ κ ]} →

            τ₁ ≡t υ₁ → τ₂ ≡t υ₂ → τ₃ ≡t υ₃ →
            ----------------------------------
            τ₁ · τ₂ ~ τ₃ ≡p υ₁ · υ₂ ~ υ₃

data _≡t_ where
  teq-refl : {τ : Type Δ κ} →

             ---------------
             τ ≡t τ

  teq-sym : ∀ {τ₁ τ₂ : Type Δ κ} →
             
              τ₁ ≡t τ₂ →
              ---------------
              τ₂ ≡t τ₁            

  teq-trans : ∀ {τ₁ τ₂ τ₃ : Type Δ κ} →
             
                τ₁ ≡t τ₂ → τ₂ ≡t τ₃ →
                ----------------------
                τ₁ ≡t τ₃

  teq-⇒ : ∀ {τ₁ τ₂ : Type Δ ★} {π₁ π₂ : Pred Δ κ'} →
             
               π₁ ≡p π₂ → τ₁ ≡t τ₂ →
               -----------------------
               π₁ ⇒ τ₁ ≡t π₂ ⇒ τ₂

  teq-∀ : ∀ {τ υ : Type (Δ , κ) ★} →

            τ ≡t υ →
            ----------------
            `∀ κ τ ≡t `∀ κ υ

  teq-μ : ∀ {κ¹ : Kind¹ κ} {τ υ : Type Δ (★¹ `→ ★)} →
            
            -- n.b. if τ, υ : ★¹ → ★, then 
            -- they will be incomparable; we don't have equality
            -- between λ-bound terms.
            -- (I don't see why we couldn't, though, under the same rules as ∀?)
            τ ≡t υ →
            ----------------
            μ τ ≡t μ υ

  teq-β     : ∀ {κ¹ : Kind¹ κ} {τ : Type (Δ , κ) κ₁} {υ : Type Δ κ} →
                
                ------------------------------
                ((`λ κ¹ τ) ·[ υ ]) ≡t (τ β[ υ ])

  teq-· : ∀ {κ¹ : Kind¹ κ} {τ₁ υ₁ : Type Δ (κ¹ `→ κ')} {τ₂ υ₂ : Type Δ κ} → 

           τ₁ ≡t υ₁ → τ₂ ≡t υ₂ → 
           ------------------------
           τ₁ ·[ τ₂ ] ≡t υ₁ ·[ υ₂ ]

  teq-sing : ∀  {l₁ l₂ : Type Δ (L)} →
                {τ₁ τ₂ : Type Δ κ₁} →
                
                l₁ ≡t l₂ → τ₁ ≡t τ₂ →
                --------------------------------------
                (l₁ R▹ τ₁) ≡t (l₂ R▹ τ₂)

  teq-lift₁ : ∀ {κ¹ : Kind¹ κ} {l : Type Δ (L)} {υ : Type Δ κ} {τ : Type Δ (κ¹ `→ κ')} →
                
                --------------------------------------
                (l R▹ τ) ·⌈ υ ⌉ ≡t (l R▹ (τ ·[ υ ]))


  teq-lift₂ : ∀ {κ¹ : Kind¹ κ₁} {l : Type Δ (L)} {υ : Type Δ (κ¹ `→ κ₂)} {τ : Type Δ κ₁} →
                
                --------------------------------------
                ⌈ υ ⌉· (l R▹ τ) ≡t (l R▹ (υ ·[ τ ]))

  teq-⌊⌋    : ∀ {τ υ : Type Δ (L)} →

                τ ≡t υ → 
                -------------
                ⌊ τ ⌋ ≡t ⌊ υ ⌋

  teq-Π : ∀ {ρ₁ ρ₂ : Type Δ R[ ★ ] } →
          ρ₁ ≡t ρ₂ → 
          -------------
          Π ρ₁ ≡t Π ρ₂

  teq-Σ : ∀ {ρ₁ ρ₂ : Type Δ R[ ★ ] } →
          ρ₁ ≡t ρ₂ → 
          -------------
          Σ ρ₁ ≡t Σ ρ₂


