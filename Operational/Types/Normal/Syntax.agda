module Rome.Operational.Types.Normal.Syntax where

open import Rome.Operational.Prelude
open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

open import Rome.Operational.Types.Syntax
open import Rome.Operational.Types.Renaming using (lift ; Renaming)
open import Rome.Operational.Types.Properties



--------------------------------------------------------------------------------
-- 3.1. NormalType types
--
-- - NeutralType types are either 
--    (i)  variables, or
--    (ii) applications with variables stuck in head position. 
--         (And hence cannot reduce).
-- - NormalType types are types precluded from any applications (barring neutral forms).

infixr 1 _▹_
data NormalType (Δ : KEnv) : Kind → Set
data Row Δ : Kind → Set
data NeutralType Δ : Kind → Set where

  ` : 
      KVar Δ κ →
      ---------------
      NeutralType Δ κ

  _·_ : 
      
      NeutralType Δ (κ₁ `→ κ) → 
      NormalType Δ κ₁ → 
      ---------------------------
      NeutralType Δ κ

--   _▹_ : 
--       NormalType Δ L → 
--       NeutralType Δ (κ₁ `→ κ₂) →
--       ---------------------------
--       NeutralType Δ R[ κ₁ `→ κ₂ ] 

  Π : 

      NeutralType Δ R[ κ ] → 
      ------------
      NeutralType Δ κ

  Σ : 

      NeutralType Δ R[ κ ] → 
      ------------
      NeutralType Δ κ


  _<$>_ : 

       NormalType Δ (κ₁ `→ κ₂) → NeutralType Δ R[ κ₁ ] → 
       -------------------------------------------------
       NeutralType Δ (R[ κ₂ ])


data Row Δ where

  _▹_ : 
      
      NormalType Δ L → 
      NormalType Δ κ → 
      ---------------------------
      Row Δ R[ κ ]


--   Π▹ : 

--       NormalType Δ L → 
--       NormalType Δ κ → 
--       ------------
--       Row Δ κ

--   Σ▹ : 

--       NormalType Δ L → 
--       NormalType Δ κ → 
--       ------------
--       Row Δ κ
    
  

data NormalType Δ where

  Unit :
       
      --------------
      NormalType Δ ★ 

  ne : 

      NeutralType Δ κ → 
      --------------
      NormalType Δ κ

  row :

      Row Δ R[ κ ] → 
      -------------------
      NormalType Δ R[ κ ]

  `λ :

      NormalType (Δ ,, κ₁) κ₂ → 
      --------------------------
      NormalType Δ (κ₁ `→ κ₂)

  _`→_ : 

      NormalType Δ ★ →
      NormalType Δ ★ → 
      -----------------
      NormalType Δ ★

  `∀    :
      
      (κ : Kind) → NormalType (Δ ,, κ) ★ →
      --------------------------------------
      NormalType Δ ★

  μ     :
      
      NormalType Δ (★ `→ ★) →
      -------------------------
      NormalType Δ ★

  ------------------------------------------------------------------
  -- Rω business

  -- labels
  lab :
    
      Label → 
      --------
      NormalType Δ L

  -- label constant formation
  ⌊_⌋ :
      NormalType Δ L →
      -----------------
      NormalType Δ ★

  Π  : 

      Row Δ R[ ★ ] →
      ------------------
      NormalType Δ ★

  ΠL  : 

      Row Δ R[ L ] →
      ------------------
      NormalType Δ L


  Σ  : 

      Row Δ R[ ★ ] →
      ---------------
      NormalType Δ ★

  ΣL  : 

      Row Δ R[ L ] →
      ------------------
      NormalType Δ L


--------------------------------------------------------------------------------
-- Rows are either neutral or labeled types

row-canonicity : (ρ : NormalType Δ R[ κ ]) → ∃[ x ] (ρ ≡ ne x) or 
                                             ∃[ l ] Σ[ τ ∈ NormalType Δ κ ] ((ρ ≡ row (l ▹ τ)))
row-canonicity (ne x) = left (x , refl)
row-canonicity (row (l ▹ τ)) = right (l , τ , refl)

--------------------------------------------------------------------------------
-- 3.4 Soundness of Type Normalization
--
-- (OMITTED).

⇑ : NormalType Δ κ → Type Δ κ
⇑NE : NeutralType Δ κ → Type Δ κ
⇑Row : Row Δ R[ κ ] → Type Δ R[ κ ]

⇑ Unit   = Unit
⇑ (ne x) = ⇑NE x
⇑ (row x) = ⇑Row x
⇑ (`λ τ) = `λ (⇑ τ)
⇑ (τ₁ `→ τ₂) = ⇑ τ₁ `→ ⇑ τ₂
⇑ (`∀ κ τ) = `∀ κ (⇑ τ)
⇑ (μ τ) = μ (⇑ τ)
⇑ (lab l) = lab l
⇑ ⌊ τ ⌋ = ⌊ ⇑ τ ⌋
⇑ (Π x) = Π · ⇑Row x
⇑ (ΠL x) = Π · ⇑Row x
⇑ (Σ x) = Σ · ⇑Row x
⇑ (ΣL x) = Σ · ⇑Row x

⇑NE (` x) = ` x
⇑NE (τ₁ · τ₂) = (⇑NE τ₁) · (⇑ τ₂)
⇑NE (Π ρ) = Π · ⇑NE ρ
⇑NE (Σ ρ) = Σ · ⇑NE ρ
⇑NE (F <$> τ) = (⇑ F) <$> (⇑NE τ) 

⇑Row (l ▹ τ) = (⇑ l) ▹ (⇑ τ)


--------------------------------------------------------------------------------
