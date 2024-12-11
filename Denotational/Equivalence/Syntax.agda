
module Rome.Denotational.Equivalence.Syntax where

open import Preludes.Level
open import Preludes.Data
open import Preludes.Relation

open import Rome.Denotational.Kinds
open import Rome.Denotational.Types
open import Rome.Denotational.Types.Substitution
open import Rome.Denotational.GVars.Kinds

--------------------------------------------------------------------------------
-- Type & Predicate equivalence.

data _≡p_ : (π₁ : Pred Δ κ₁) (π₂ : Pred Δ κ₂) → Set

data _≡t_ : (τ υ : Type Δ κ) → Set

infix 0 _≡p_
infix 0 _≡t_

data _≡r_ : (m₁ m₂ : Row Δ κ) → Set where
  req-sing : {l₁ l₂ : Label} {τ₁ τ₂ : Type Δ κ} → 
             (l₁ ≡ l₂) → τ₁ ≡t τ₂ →
             -------------------------------
             (l₁ ▹ τ₁) ≡r (l₁ ▹ τ₁)

  req-▹ : {l₁ l₂ : Label} {τ₁ τ₂ : Type Δ κ} {m₁ m₂ : Row Δ κ} 
           {ev₁ : l₁ ∉ m₁} {ev₂ : l₂ ∉ m₂} → 
             (l₁ ≡ l₂) → τ₁ ≡t τ₂ → m₁ ≡r m₂ →
             ------------------------------------
             (l₁ ▹ τ₁ ， m₁) {ev₁} ≡r (l₂ ▹ τ₂ ， m₂) {ev₂}

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

  teq-→    : ∀ {τ₁ τ₂ : Type Δ (★ ℓ₁)}
                {υ₁ υ₂ : Type Δ (★ ℓ₂)} → 
               τ₁ ≡t τ₂ → υ₁ ≡t υ₂ →
               -----------------------
               τ₁ `→ υ₁ ≡t τ₂ `→ υ₂

  teq-⇒ : ∀ {τ₁ τ₂ : Type Δ (★ ℓ)} {π₁ π₂ : Pred Δ κ} →

               π₁ ≡p π₂ → τ₁ ≡t τ₂ →
               -----------------------
               π₁ ⇒ τ₁ ≡t π₂ ⇒ τ₂

  teq-∀ : ∀ {τ υ : Type (Δ ، κ) (★ ℓ)} →

            τ ≡t υ →
            ----------------
            `∀ κ τ ≡t `∀ κ υ

  teq-β     : ∀ {τ : Type (Δ ، κ) κ'} {υ : Type Δ κ} →

                ------------------------------
                ((`λ κ τ) ·[ υ ]) ≡t (τ β[ υ ])

  teq-· : ∀ {τ₁ υ₁ : Type Δ (κ `→ κ')} {τ₂ υ₂ : Type Δ κ} →

           τ₁ ≡t υ₁ → τ₂ ≡t υ₂ →
           ------------------------
           τ₁ ·[ τ₂ ] ≡t υ₁ ·[ υ₂ ]

  teq-sing : ∀  {l₁ l₂ : Type Δ (L ℓ)} →
                {τ₁ τ₂ : Type Δ κ₁} →

                l₁ ≡t l₂ → τ₁ ≡t τ₂ →
                --------------------------------------
                (l₁ R▹ τ₁) ≡t (l₂ R▹ τ₂)

  teq-lift₁ : ∀ {l : Type Δ (L ℓ)} {υ : Type Δ κ} {τ : Type Δ (κ `→ κ')} →

                --------------------------------------
                (↑ (l R▹ τ)) ·[ υ ] ≡t (l R▹ (τ ·[ υ ]))


  teq-lift₂ : ∀ {l : Type Δ (L ℓ)} {υ : Type Δ (κ₁ `→ κ₂)} {τ : Type Δ κ₁} →

                --------------------------------------
                (υ ↑) ·[ l R▹ τ ] ≡t (l R▹ (υ ·[ τ ]))

  teq-⌊⌋    : ∀ {τ υ : Type Δ (L ℓ)} →

                τ ≡t υ →
                -------------
                ⌊_⌋ {ℓ = ℓ} τ ≡t ⌊_⌋ {ℓ = ℓ} υ

  teq-Π : ∀ {ρ₁ ρ₂ : Type Δ R[ ★ ℓκ ] } →
          ρ₁ ≡t ρ₂ →
          -------------
          Π ρ₁ ≡t Π ρ₂

  teq-Σ : ∀ {ρ₁ ρ₂ : Type Δ R[ ★ ℓκ ] } →
          ρ₁ ≡t ρ₂ →
          -------------
          Σ ρ₁ ≡t Σ ρ₂

  teq-lift-Σ : ∀ {ρ₁ : Type Δ R[ κ `→ ★ ℓκ ] } {τ : Type Δ κ} →

                ---------------------------
                Σ ρ₁ ·[ τ ] ≡t Σ ((↑ ρ₁) ·[ τ ])

  teq-lift-Π : ∀ {ρ₁ : Type Δ R[ κ `→ ★ ℓκ ] } {τ : Type Δ κ} →

                ---------------------------
                Π ρ₁ ·[ τ ] ≡t Π ((↑ ρ₁) ·[ τ ])

  teq-id-↑ :  ∀ {x : Type Δ R[ κ ]} → 
  
            ---------------------------
            (`λ κ (tvar Z)) ↑ ·[ x ] ≡t x

  --------------------------------------------------------------------------------
  -- The simple row theory.

  teq-labTy-row :  ∀ {l : Label} {τ : Type Δ κ} →
  
                   -----------------------
                   (lab {ℓ = ℓ} l R▹ τ) ≡t ⦃- l ▹ τ -⦄

  teq-row : ∀ {m₁ m₂ : Row Δ κ} →

           m₁ ≡r m₂ → 
           ----------------
           ⦃- m₁ -⦄ ≡t ⦃- m₂ -⦄
