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

  Π : 

      NeutralType Δ R[ κ ] → 
      ------------
      NeutralType Δ κ

  Σ : 

      NeutralType Δ R[ κ ] → 
      ------------
      NeutralType Δ κ

--   _▹_ : 
      
--       NormalType Δ L → 
--       NeutralType Δ κ → 
--       ---------------------------
--       NeutralType Δ R[ κ ]

data Row Δ where

  _▹_ : 
      
      NormalType Δ L → 
      NormalType Δ κ → 
      ---------------------------
      Row Δ R[ κ ]


  Π▹ : 

      NormalType Δ L → 
      NormalType Δ κ → 
      ------------
      Row Δ κ

  Σ▹ : 

      NormalType Δ L → 
      NormalType Δ κ → 
      ------------
      Row Δ κ
    
  

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


  Σ  : 

      Row Δ R[ ★ ] →
      ---------------
      NormalType Δ ★


--------------------------------------------------------------------------------
-- Rows have the following canonical forms:
--  - Variables or neutral applications
--  - Variables/neutral applications nested under Π and/or Σ 
--  - Labeled rows (ℓ ▹ τ), possibly nested e.g. (ℓ₁ ▹ (ℓ₂ ▹ τ))
--  - Nested labeled rows under Π/Σ e.g. Π (ℓ ▹ τ) for τ : R[ ★ ]

all-rows-neutral-or-row : (τ : NormalType Δ R[ κ ]) → (∃[ x ] (ne x ≡ τ) or ∃[ r ] (row r ≡ τ))
all-rows-neutral-or-row (ne x) = left (x , refl)
all-rows-neutral-or-row (row x) = right (x , refl)

row-canonicity : ∀ (r : Row Δ R[ κ ]) → ∃[ l ] (∃[ τ ] (r ≡ (l ▹ τ))) or
                                         ∃[ l ] (∃[ τ ] (r ≡ (Π▹ l τ))) or
                                         ∃[ l ] (∃[ τ ] (r ≡ (Σ▹ l τ)))
row-canonicity (l ▹ τ) = left (l , τ , refl)
row-canonicity (Π▹ l τ) = right (left (l , τ , refl))
row-canonicity (Σ▹ l τ) = right (right (l , τ , refl))

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
⇑ (Σ x) = Σ · ⇑Row x


⇑NE (` x) = ` x
⇑NE (τ₁ · τ₂) = (⇑NE τ₁) · (⇑ τ₂)
-- ⇑NE (τ₁ ▹ τ₂) = `▹` · (⇑ τ₁) · (⇑NE τ₂)
⇑NE (Π ρ) = Π · ⇑NE ρ
⇑NE (Σ ρ) = Σ · ⇑NE ρ

⇑Row (l ▹ τ) = (`▹` · (⇑ l)) · (⇑ τ)
⇑Row (Π▹ l τ) = Π · (`▹` · (⇑ l) · (⇑ τ))
⇑Row (Σ▹ l τ) = Σ · (`▹` · (⇑ l) · (⇑ τ))

--------------------------------------------------------------------------------
-- problems

-- fuck₁ : NormalType Δ (★ `→ ★)
-- fuck₁ = `λ (ne (Π (Π ((lab "l") ▹ ((lab "l2") ▹ ` Z)))))

fuck₂ : NormalType Δ (★ `→ ★)
fuck₂ = `λ (Π ((lab "l") ▹ (Π ((lab "l2") ▹ (ne (` Z))))))