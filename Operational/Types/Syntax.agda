module Rome.Operational.Types.Syntax where

open import Rome.Operational.Prelude
open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

--------------------------------------------------------------------------------
-- Types


infixl 5 _·_
infixr 5 _≲_
data Pred Δ : Kind → Set
data Type Δ : Kind → Set 

data Pred Δ where
  _·_~_ : 

       (ρ₁ ρ₂ ρ₃ : Type Δ R[ κ ]) → 
       --------------------- 
       Pred Δ R[ κ ]

  _≲_ : 

       (ρ₁ ρ₂ : Type Δ R[ κ ]) →
       ----------
       Pred Δ R[ κ ]  
       
data Type Δ where

  ` : 
      (α : KVar Δ κ) →
      --------
      Type Δ κ

  `λ : 
      
      (τ : Type (Δ ,, κ₁) κ₂) → 
      ---------------
      Type Δ (κ₁ `→ κ₂)

  _·_ : 
      
      (τ₁ : Type Δ (κ₁ `→ κ₂)) → 
      (τ₂ : Type Δ κ₁) → 
      ----------------
      Type Δ κ₂

  _`→_ : 

         (τ₁ : Type Δ ★) →
         (τ₂ : Type Δ ★) → 
         --------
         Type Δ ★

  `∀    :
      
         {κ : Kind} → (τ : Type (Δ ,, κ) ★) →
         -------------
         Type Δ ★

  μ     :
      
         (φ : Type Δ (★ `→ ★)) → 
         -------------
         Type Δ ★

  ------------------------------------------------------------------
  -- Qualified types

  _⇒_ : 

         (π : Pred Δ R[ κ₁ ]) → (τ : Type Δ ★) → 
         ---------------------
         Type Δ ★       


  ------------------------------------------------------------------
  -- Rω business

  -- labels
  lab :
    
        (l : Label) → 
        --------
        Type Δ L

  -- label constant formation
  ⌊_⌋ :
        (τ : Type Δ L) →
        ----------
        Type Δ ★

  ε : 

    ------------
    Type Δ R[ κ ]

  -- Row formation
  _▹_ :
         (l : Type Δ L) → (τ : Type Δ κ) → 
         -------------------
         Type Δ R[ κ ]

  _<$>_ : 

       (φ : Type Δ (κ₁ `→ κ₂)) → (τ : Type Δ R[ κ₁ ]) → 
       ----------------------------------------
       Type Δ R[ κ₂ ]

  -- Record formation
  Π     :

          ----------------
          Type Δ (R[ κ ] `→ κ)

  -- Variant formation
  Σ     :

          ----------------
          Type Δ (R[ κ ] `→ κ)

  _─_ : Type Δ R[ κ ] → Type Δ R[ κ ] →
        Type Δ R[ κ ]

--------------------------------------------------------------------------------
-- Lifting of type operators over predicates

_·P_ : ∀ (f : Type Δ (κ₁ `→ κ₂)) (π : Pred Δ R[ κ₁ ]) → 
       Pred Δ R[ κ₂ ] 
f ·P (ρ₁ · ρ₂ ~ ρ₃) = (f <$> ρ₁) · f <$> ρ₂ ~ (f <$> ρ₃)
f ·P (ρ₁ ≲ ρ₂) = f <$> ρ₁ ≲ f <$> ρ₂

--------------------------------------------------------------------------------
-- Type constant smart-ish constructors

-- Record formation
`Π : Type Δ R[ κ ] → Type Δ κ 
`Π τ = Π · τ 

-- Variant formation
`Σ : Type Δ R[ κ ] → Type Δ κ 
`Σ τ = Σ · τ 

--------------------------------------------------------------------------------
-- Admissable constants

-- for partial application of infix fmap.
`↑ : Type Δ ((κ₁ `→ κ₂) `→ R[ κ₁ ] `→ R[ κ₂ ])
`↑ = `λ (`λ (` (S Z) <$> ` Z))

-- Flapping. See https://hoogle.haskell.org/?hoogle=f%20(a%20-%3E%20b)%20-%3E%20a%20-%3E%20f%20b%20
flap : Type Δ (R[ κ₁ `→ κ₂ ] `→ κ₁ `→ R[ κ₂ ])
flap = `λ (`λ ((`λ ((` Z) · (` (S Z)))) <$> (` (S Z))))

_??_ : Type Δ (R[ κ₁ `→ κ₂ ]) → Type Δ κ₁ → Type Δ R[ κ₂ ]
f ?? a = flap · f · a

Unit : Type Δ ★
Unit = Π · ε
