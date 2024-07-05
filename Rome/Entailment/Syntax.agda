-- {-# OPTIONS --allow-unsolved-metas #-}
module Rome.Entailment.Syntax where


open import Preludes.Data
open import Preludes.Level
open import Preludes.Relation

open import Rome.Kinds
open import Rome.Types
open import Rome.Types.Substitution
open import Rome.Equivalence.Syntax
open import Rome.GVars.Kinds

--------------------------------------------------------------------------------
-- Environments & weakening.

data PEnv : KEnv ℓ → Level → Set where
  ε : PEnv Δ lzero
  _,_ : {κ : Kind ℓκ} →
        PEnv Δ ℓΦ → Pred Δ κ → PEnv Δ (ℓΦ ⊔ ℓκ)


weakΦ : PEnv Δ ℓΦ → PEnv (Δ ، κ) ℓΦ
weakΦ ε = ε
weakΦ (Φ , π) = weakΦ Φ , renamePred S π

--------------------------------------------------------------------------------
-- Predicate variables.

data PVar : PEnv Δ ℓΦ → Pred Δ κ → Set where
  Z : ∀ {Φ : PEnv Δ ℓΦ} {π : Pred Δ κ} →
        PVar (Φ , π) π

  S : ∀ {Φ : PEnv Δ ℓΦ}
        {π : Pred Δ κ₁} {ϕ : Pred Δ κ₂} →
        PVar Φ π → PVar (Φ , ϕ) π

--------------------------------------------------------------------------------
-- Entailment in the "Simple Rows" theory.

data _∈_ : Type Δ R[ κ ] → Row Δ κ → Set
_⊆_ : Row Δ κ → Row Δ κ → Set

data _∈_ where
  here : ∀ {ℓ}{l}{τ : Type Δ κ} →
         (lab {ℓ = ℓ} l R▹ τ) ∈ (l ▹ τ)
  here-again : ∀ {ℓ}{l}{τ : Type Δ κ} {m : Row Δ κ} {ev : l ∉ m} → 
               (lab {ℓ = ℓ} l R▹ τ) ∈ (l ▹ τ ， m) {ev}
  there  : ∀ {ℓ}{l₁ l₂}{τ₁ τ₂ : Type Δ κ} {m : Row Δ κ} {ev : l₂ ∉ m} → 
            (lab {ℓ = ℓ} l₁ R▹ τ₁) ∈ m  → (lab {ℓ = ℓ} l₁ R▹ τ₁) ∈ ((l₂ ▹ τ₂ ， m) {ev})

--data _⊆_ where


_⊆_ {Δ = Δ} {κ = κ} m₁ m₂ =
  ∀ {ℓ} (l : Label) (τ : Type Δ κ) → (lab {ℓ = ℓ} l R▹ τ) ∈ m₁ → (lab {ℓ = ℓ} l R▹ τ) ∈ m₂

-- ε ∈ m = ⊤₀
-- (lab l₁ R▹ τ₁) ∈ (l₂ ▹ τ₂) with l₁ ≟ l₂
-- ... | yes _ = ∀ (eq : τ₁ ≡t τ₂) → ⊤
-- ... | no  _ = ⊥₀
-- ((lab {ℓ = ℓ} l₁) R▹ τ₁) ∈ (l₂ ▹ τ₂ ， m) with l₁ ≟ l₂
-- ... | yes _ = ∀ (eq : τ₁ ≡t τ₂) → ⊤
-- ... | no  _ = (lab {ℓ = ℓ} l₁ R▹ τ₁) ∈ m
-- (_ R▹ τ) ∈ m = ⊥₀
-- Row (l₁ ▹ τ₁) ∈ (l₂ ▹ τ₂)  with l₁ ≟ l₂
-- ... | yes _ = ∀ (eq : τ₁ ≡t τ₂) → ⊤
-- ... | no  _ = ⊥₀
-- (Row (l₁ ▹ τ₁)) ∈ (l₂ ▹ τ₂ ， m)  with l₁ ≟ l₂
-- ... | yes _ = ∀ (eq : τ₁ ≡t τ₂) → ⊤
-- ... | no  _ = Row (l₁ ▹ τ₁) ∈ m
-- Row (l₁ ▹ τ₁ ， m') ∈ m = ⊥₀
-- (τ ▹ τ₁) ∈ m = ⊥₀
-- (τ ·[ τ₁ ]) ∈ m =  ⊥₀
-- tvar x ∈ m = ⊥₀
-- Π τ ∈ m = ⊥₀
-- Σ τ ∈ m = ⊥₀

data Ent (Δ : KEnv ℓΔ) (Φ : PEnv Δ ℓΦ) : Pred Δ κ → Set where

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

  n-·lift₂ : ∀  {κ₁ : Kind ℓκ}
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

  n-ε-R : ∀  {κ₁ : Kind ℓκ}
             {ρ : Type Δ R[ κ₁ ]} →

             -------------------------
             Ent Δ Φ (ρ · ε ~ ρ)

  n-ε-L : ∀  {κ₁ : Kind ℓκ}
             {ρ : Type Δ R[ κ₁ ]} →

             -------------------------
             Ent Δ Φ (ε · ρ ~ ρ)

  ----------------------------------------
  -- Simple rows.

  n-row≲ : 
           ∀ (m₁ m₂ : Row Δ κ) → m₁ ⊆ m₂ → 

           ------------------------
           Ent Δ Φ (⦃- m₁ -⦄ ≲ ⦃- m₂ -⦄)
