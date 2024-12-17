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

data NormalType (Δ : KEnv) : Kind → Set
data NeutralType Δ : Kind → Set where

  ` : 
      KVar Δ κ →
      --------
      NeutralType Δ κ

  _·_ : 
      
        NeutralType Δ (κ₁ `→ κ) → 
        NormalType Δ κ₁ → 
        ------------
        NeutralType Δ κ

  _▹_ :
    
      -- change this to neutral.
      NormalType Δ L → 
      NeutralType Δ κ →
      ------------------
      NeutralType Δ R[ κ ]

  Π  : 

      NeutralType Δ R[ κ ] →
      ------------------
      NeutralType Δ κ

  Σ  : 

      NeutralType Δ R[ κ ] →
      ------------------
      NeutralType Δ κ
  
  ↑_ : 

       NeutralType Δ R[ κ₁ `→ κ₂ ] →
       ------------------------------
       NeutralType Δ (κ₁ `→ R[ κ₂ ])


  _↑ : 

       NeutralType Δ (κ₁ `→ κ₂) →
       ------------------------------
       NeutralType Δ (R[ κ₁ ] `→ R[ κ₂ ])

data NormalType Δ where

  Unit :
       
        --------------
        NormalType Δ ★ 
  ne : 
       NeutralType Δ κ → 
       --------------
       NormalType Δ κ

  `λ :

      NormalType (Δ ,, κ₁) κ₂ → 
      ---------------
      NormalType Δ (κ₁ `→ κ₂)

  _`→_ : 

         NormalType Δ ★ →
         NormalType Δ ★ → 
         --------
         NormalType Δ ★

  `∀    :
      
         (κ : Kind) → NormalType (Δ ,, κ) ★ →
         -------------
         NormalType Δ ★

  μ     :
      
         NormalType Δ (★ `→ ★) →
         -------------
         NormalType Δ ★

  ------------------------------------------------------------------
  -- Rω business

  -- labels
  lab :
    
        Label → 
        --------
        NormalType Δ L

  -- Row singleton formation
  _▹_ :
         NormalType Δ L → NormalType Δ κ →
         -------------------
         NormalType Δ R[ κ ]

  -- label constant formation
  ⌊_⌋ :
        NormalType Δ L →
        -----------------
        NormalType Δ ★

  Π     :

          NormalType Δ R[ κ ] → 
          ----------------
          NormalType Δ κ

  Σ     :

          NormalType Δ R[ κ ] → 
          ----------------
          NormalType Δ κ

  ↑_ : 

       NormalType Δ R[ κ₁ `→ κ₂ ] →
       ------------------------------
       NormalType Δ (κ₁ `→ R[ κ₂ ])


  _↑ : 

       NormalType Δ (κ₁ `→ κ₂) →
       ------------------------------
       NormalType Δ (R[ κ₁ ] `→ R[ κ₂ ])


--------------------------------------------------------------------------------
-- 

-- isNE : NormalType Δ κ → Set
-- isNE (ne x)     = ⊤
-- isNE (`λ τ)     = ⊤
-- isNE (`∀ κ τ)   = ⊤
-- isNE (lab x)    = ⊥
-- isNE Unit       = ⊥
-- isNE (τ₁ ▹ τ₂)  = ⊥
-- isNE (μ τ)      = ⊥
-- isNE (τ₁ `→ τ₂) = isNE τ₁ × isNE τ₂
-- isNE ⌊ τ ⌋      = isNE τ
-- isNE (Π τ)      = isNE τ
-- isNE (Σ τ)      = isNE τ
-- isNE (↑ τ)      = isNE τ
-- isNE (τ ↑)      = isNE τ

-- row-canonicity : (r : NormalType Δ R[ κ ]) → isNE r or ∃[ x ] ∃[ τ ] (r ≡ (x ▹ τ))
-- row-canonicity (ne x)       = left tt
-- row-canonicity (ℓ ▹ τ)      = right ⟨ ℓ , ⟨ τ , refl ⟩ ⟩
-- row-canonicity (Π (ne x))   = left tt
-- row-canonicity (Π (ℓ ▹ τ)) with row-canonicity τ
-- ... | left x                   = {!!}
-- ... | right ⟨ x , ⟨ τ' , eq ⟩ ⟩ rewrite eq = right ⟨ ℓ , ⟨ Π (x ▹ τ') , {!!} ⟩ ⟩
-- -- I think terms at this type are simply uninhabitable.
-- row-canonicity (Π t) with row-canonicity t
-- ... | left x = left x
-- ... | right ⟨ l , ⟨ t , snd₁ ⟩ ⟩ = {!!}
-- row-canonicity (Σ r)        = {!right!}

--------------------------------------------------------------------------------
-- 3.4 Soundness of Type NormalTypeization
--
-- (OMITTED).

⇑ : NormalType Δ κ → Type Δ κ
⇑NE : NeutralType Δ κ → Type Δ κ

⇑ Unit   = Unit
⇑ (ne x) = ⇑NE x
⇑ (`λ τ) = `λ (⇑ τ)
⇑ (τ₁ `→ τ₂) = ⇑ τ₁ `→ ⇑ τ₂
⇑ (`∀ κ τ) = `∀ κ (⇑ τ)
⇑ (μ τ) = μ (⇑ τ)
⇑ (Π τ) = Π (⇑ τ)
⇑ (Σ τ) = Σ (⇑ τ)
⇑ (lab l) = lab l
⇑ (τ₁ ▹ τ₂) = (⇑ τ₁) ▹ (⇑ τ₂)
⇑ ⌊ τ ⌋ = ⌊ ⇑ τ ⌋
⇑ (↑ τ) = ↑ (⇑ τ)
⇑ (τ ↑) = (⇑ τ) ↑

⇑NE (` x) = ` x
⇑NE (τ₁ · τ₂) = (⇑NE τ₁) · (⇑ τ₂)
⇑NE (τ₁ ▹ τ₂) = (⇑ τ₁) ▹ (⇑NE τ₂)
⇑NE (Π τ) = Π (⇑NE τ)
⇑NE (Σ τ) = Σ (⇑NE τ)
⇑NE (↑ F) = ↑ (⇑NE F)
⇑NE (F ↑) = (⇑NE F) ↑

--------------------------------------------------------------------------------
