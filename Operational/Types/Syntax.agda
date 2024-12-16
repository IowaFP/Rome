module Rome.Operational.Types.Syntax where

open import Rome.Operational.Prelude
open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

--------------------------------------------------------------------------------
-- 2.4 Types


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
  _▹_ :
         Type Δ L → Type Δ κ →
         -------------------
         Type Δ R[ κ ]

  -- label constant formation
  ⌊_⌋ :
        Type Δ L →
        ----------
        Type Δ ★

  -- Record formation
  Π     :

          Type Δ R[ κ ] → 
          ----------------
          Type Δ κ

  -- Variant formation
  Σ     :

          Type Δ R[ κ ] → 
          ----------------
          Type Δ κ

  ↑_ : 

       Type Δ R[ κ₁ `→ κ₂ ] →
       ------------------------------
       Type Δ (κ₁ `→ R[ κ₂ ])


  _↑ : 

       Type Δ (κ₁ `→ κ₂) →
       ------------------------------
       Type Δ (R[ κ₁ ] `→ R[ κ₂ ])
