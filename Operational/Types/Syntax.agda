module Rome.Operational.Types.Syntax where

open import Rome.Operational.Prelude
open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

--------------------------------------------------------------------------------
-- Types


infixl 5 _·_
data Type Δ : Kind → Set where

  Unit :

      --------
      Type Δ ★

  ` : 
      KVar Δ κ →
      --------
      Type Δ κ

  `λ : 
      
      Type (Δ ,, κ₁) κ₂ → 
      ---------------
      Type Δ (κ₁ `→ κ₂)

  _·_ : 
      
      Type Δ (κ₁ `→ κ₂) → 
      Type Δ κ₁ → 
      ----------------
      Type Δ κ₂

  _`→_ : 

         Type Δ ★ →
         Type Δ ★ → 
         --------
         Type Δ ★

  `∀    :
      
         (κ : Kind) → Type (Δ ,, κ) ★ →
         -------------
         Type Δ ★

  μ     :
      
         Type Δ (★ `→ ★) → 
         -------------
         Type Δ ★

  ------------------------------------------------------------------
  -- Rω business
  
  -- labels
  lab :
    
        Label → 
        --------
        Type Δ L

  -- Row singleton formation
  `▹` :

         -------------------
         Type Δ (L `→ κ `→ R[ κ ])

  -- label constant formation
  ⌊_⌋ :
        Type Δ L →
        ----------
        Type Δ ★

  -- Record formation
  Π     :

          ----------------
          Type Δ (R[ κ ] `→ κ)

  -- Variant formation
  Σ     :


          ----------------
          Type Δ (R[ κ ] `→ κ)

  -- ↑_ : 

  --      Type Δ R[ κ₁ `→ κ₂ ] →
  --      ------------------------------
  --      Type Δ (κ₁ `→ R[ κ₂ ])


  _<$>_ : 

       Type Δ (κ₁ `→ κ₂) → Type Δ R[ κ₁ ] → 
       ----------------------------------------
       Type Δ R[ κ₂ ]



--------------------------------------------------------------------------------
-- Type constant smart-ish constructors

-- row formation
_`▹_ : Type Δ L → Type Δ κ → Type Δ R[ κ ] 
l `▹ t = `▹` · l · t

-- Record formation
`Π : Type Δ R[ κ ] → Type Δ κ 
`Π τ = Π · τ 

-- Variant formation
`Σ : Type Δ R[ κ ] → Type Δ κ 
`Σ τ = Σ · τ 

-- Lifting
-- `↑ : Type Δ (κ₁ `→ κ₂) → Type Δ (R[ κ₁ ] `→ R[ κ₂ ])
-- `↑ f = ↑ · f

-- rmap (lifting with an argument)
-- _<$>_ : Type Δ (κ₁ `→ κ₂) → Type Δ R[ κ₁ ] → Type Δ R[ κ₂ ]
-- f <$> m = ↑ · f · m 

--------------------------------------------------------------------------------
-- Admissable constants

-- Flapping. See https://hoogle.haskell.org/?hoogle=f%20(a%20-%3E%20b)%20-%3E%20a%20-%3E%20f%20b%20
flap : Type Δ (R[ κ₁ `→ κ₂ ] `→ κ₁ `→ R[ κ₂ ])
flap = `λ (`λ ((`λ ((` Z) · (` (S Z)))) <$> (` (S Z))))

_??_ : Type Δ (R[ κ₁ `→ κ₂ ]) → Type Δ κ₁ → Type Δ R[ κ₂ ]
f ?? a = flap · f · a
