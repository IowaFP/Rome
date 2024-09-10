module Rωμ.Entailment.Syntax where


open import Preludes.Data
open import Preludes.Level
open import Preludes.Relation

open import Rωμ.Kinds
open import Rωμ.Types
open import Rωμ.Types.Substitution
open import Rωμ.Equivalence.Syntax
open import Rωμ.GVars.Kinds

--------------------------------------------------------------------------------
-- Environments & weakening.

data PEnv : KEnv → Set where
  ε : PEnv Δ 
  _,_ : {κ : Kind} →
        PEnv Δ → Pred Δ κ → PEnv Δ


weakΦ : PEnv Δ → PEnv (Δ ، κ)
weakΦ ε = ε
weakΦ (Φ , π) = weakΦ Φ , renamePred S π

--------------------------------------------------------------------------------
-- Predicate variables.

data PVar : PEnv Δ → Pred Δ κ → Set where
  Z : ∀ {Φ : PEnv Δ} {π : Pred Δ κ} →
        PVar (Φ , π) π

  S : ∀ {Φ : PEnv Δ}
        {π : Pred Δ κ₁} {ϕ : Pred Δ κ₂} →
        PVar Φ π → PVar (Φ , ϕ) π

--------------------------------------------------------------------------------
-- Entailment.

data Ent (Δ : KEnv) (Φ : PEnv Δ) : Pred Δ κ → Set where

  n-var : ∀ {π : Pred Δ κ} →
           PVar Φ π →
           -----------
           Ent Δ Φ π

  n-refl : ∀  {τ : Type Δ R[ κ ]}  →

          --------------
          Ent Δ Φ (τ ≲ τ)

  n-trans : ∀  {τ₁ τ₂ τ₃ : Type Δ R[ κ ]} →

          Ent Δ Φ (τ₁ ≲ τ₂) → Ent Δ Φ (τ₂ ≲ τ₃) →
          ---------------------------------------
          Ent Δ Φ (τ₁ ≲ τ₃)

  n-≡ : ∀ {π₁ π₂ : Pred Δ κ} →

        π₁ ≡p π₂ → Ent Δ Φ π₁ →
        ------------------------
        Ent Δ Φ π₂

  n-≲lift₁ : ∀ {ρ₁ ρ₂ : Type Δ R[ κ₁ `→ κ₂ ]}
             {τ : Type Δ κ₁} →

             Ent Δ Φ (ρ₁ ≲ ρ₂) →
             ---------------------
             Ent Δ Φ ((↑ ρ₁ ·[ τ ]) ≲ (↑ ρ₂ ·[ τ ]))

  n-≲lift₂ : ∀ {ρ₁ ρ₂ : Type Δ R[ κ₁ ]}
               {ϕ : Type Δ (κ₁ `→ κ₂)} →

             Ent Δ Φ (ρ₁ ≲ ρ₂) →
             ---------------------
             Ent Δ Φ ((ϕ ↑ ·[ ρ₁ ]) ≲ (ϕ ↑ ·[ ρ₂ ]))

  n-·lift₁ : ∀ {ρ₁ ρ₂ ρ₃ : Type Δ R[ κ₁ `→ κ₂ ]}
               {τ : Type Δ κ₁} →

             Ent Δ Φ (ρ₁ · ρ₂ ~ ρ₃) →
             ---------------------
             Ent Δ Φ ((↑ ρ₁ ·[ τ ]) · (↑ ρ₂ ·[ τ ]) ~ (↑ ρ₃ ·[ τ ]))

  n-·lift₂ : ∀  {κ₁ : Kind}
             {ρ₁ ρ₂ ρ₃ : Type Δ R[ κ₁ ]}
             {τ : Type Δ (κ₁ `→ κ₂)} →

             Ent Δ Φ (ρ₁ · ρ₂ ~ ρ₃) →
             ---------------------
             Ent Δ Φ ((τ ↑ ·[ ρ₁ ]) · (τ ↑ ·[ ρ₂ ]) ~ (τ ↑ ·[ ρ₃ ]))

  n-·≲L : ∀ {ρ₁ ρ₂ ρ₃ : Type Δ R[ κ ]} →

        Ent Δ Φ (ρ₁ · ρ₂ ~ ρ₃) →
        ---------------------
        Ent Δ Φ (ρ₁ ≲ ρ₃)


  n-·≲R : ∀ {ρ₁ ρ₂ ρ₃ : Type Δ R[ κ ]} →

        Ent Δ Φ (ρ₁ · ρ₂ ~ ρ₃) →
        ---------------------
        Ent Δ Φ (ρ₂ ≲ ρ₃)

  n-ε-R : ∀  {κ₁ : Kind}
             {ρ : Type Δ R[ κ₁ ]} →

             -------------------------
             Ent Δ Φ (ρ · ε ~ ρ)

  n-ε-L : ∀  {κ₁ : Kind}
             {ρ : Type Δ R[ κ₁ ]} →

             -------------------------
             Ent Δ Φ (ε · ρ ~ ρ)

  ----------------------------------------
  -- Simple rows.

  n-row≲ : ∀ (m₁ m₂ : Row Δ κ) → 

           m₁ ⊆ m₂ → 
           ------------------------
           Ent Δ Φ (⦃- m₁ -⦄ ≲ ⦃- m₂ -⦄)
