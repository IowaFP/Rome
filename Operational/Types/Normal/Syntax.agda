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
data NormalPred (Δ : KEnv) : Kind → Set
data NeutralType Δ : Kind → Set where

  ` : 
      (α : KVar Δ κ) → 
      ---------------------------
      NeutralType Δ κ

  _·_ : 
      
      (f : NeutralType Δ (κ₁ `→ κ)) → 
      (τ : NormalType Δ κ₁) → 
      ---------------------------
      NeutralType Δ κ

  _<$>_ : 

       (φ : NormalType Δ (κ₁ `→ κ₂)) → (τ : NeutralType Δ R[ κ₁ ]) → 
       -------------------------------------------------
       NeutralType Δ (R[ κ₂ ])

data NormalPred Δ where

  _·_~_ : 

       (ρ₁ ρ₂ ρ₃ : NormalType Δ R[ κ ]) → 
       --------------------- 
       NormalPred Δ R[ κ ]

  _≲_ : 

       (ρ₁ ρ₂ : NormalType Δ R[ κ ]) →
       ----------
       NormalPred Δ R[ κ ]  

-- data Row Δ where

--   _▹_ : 
      
--       (l : NormalType Δ L) → 
--       (τ : NormalType Δ κ) → 
--       ---------------------------
--       Row Δ R[ κ ]


data NormalType Δ where

  Unit :
       
      --------------
      NormalType Δ ★ 

  ne : 

      (x : NeutralType Δ κ) → {ground : True (ground? κ)} → 
      --------------
      NormalType Δ κ

  _▹_ : 
      
      (l : NormalType Δ L) → 
      (τ : NormalType Δ κ) → 
      ---------------------------
      NormalType Δ R[ κ ]

  `λ :

      (τ : NormalType (Δ ,, κ₁) κ₂) → 
      --------------------------
      NormalType Δ (κ₁ `→ κ₂)

  _`→_ : 

      (τ₁ τ₂ : NormalType Δ ★) →
      -----------------
      NormalType Δ ★

  `∀    :
      
      (κ : Kind) → (τ : NormalType (Δ ,, κ) ★) →
      --------------------------------------
      NormalType Δ ★

  μ     :
      
      (φ : NormalType Δ (★ `→ ★)) →
      -------------------------
      NormalType Δ ★

  ------------------------------------------------------------------
  -- Qualified types

  _⇒_ : 

         (π : NormalPred Δ R[ κ₁ ]) → (τ : NormalType Δ ★) → 
         ---------------------
         NormalType Δ ★       

  ------------------------------------------------------------------
  -- Rω business

  -- labels
  lab :
    
      (l : Label) → 
      --------
      NormalType Δ L

  -- label constant formation
  ⌊_⌋ :
      (l : NormalType Δ L) →
      -----------------
      NormalType Δ ★

  Π  : 

      (ρ : NormalType Δ R[ ★ ]) →
      ------------------
      NormalType Δ ★

  ΠL  : 

      (ρ : NormalType Δ R[ L ]) →
      ------------------
      NormalType Δ L


  Σ  : 

      (ρ : NormalType Δ R[ ★ ]) →
      ---------------
      NormalType Δ ★

  ΣL  : 

      (ρ : NormalType Δ R[ L ]) →
      ------------------
      NormalType Δ L

--------------------------------------------------------------------------------
-- The year is 2025 and I have no generic way of deriving injectivity lemmas for 
-- constructors.

inj-ne : ∀ {e₁ e₂ : NeutralType Δ κ} {g : True (ground? κ)} → ne e₁ {ground = g} ≡ ne e₂ {ground = g} → e₁ ≡ e₂
inj-ne refl = refl

inj-▹ₗ : ∀ {l₁ l₂ : NormalType Δ L} {τ₁ τ₂ : NormalType Δ κ} → (l₁ ▹ τ₁) ≡ (l₂ ▹ τ₂) → l₁ ≡ l₂
inj-▹ₗ refl = refl

inj-▹ᵣ : ∀ {l₁ l₂ : NormalType Δ L} {τ₁ τ₂ : NormalType Δ κ} → (l₁ ▹ τ₁) ≡ (l₂ ▹ τ₂) → τ₁ ≡ τ₂
inj-▹ᵣ refl = refl

-- inj-row : ∀ {ρ₁ ρ₂ : Row Δ R[ κ ]} → row ρ₁ ≡ row ρ₂ → ρ₁ ≡ ρ₂
-- inj-row refl = refl


--------------------------------------------------------------------------------
-- Rows are either neutral or labeled types

row-canonicity : (ρ : NormalType Δ R[ κ ]) →  
    ∃[ l ] Σ[ τ ∈ NormalType Δ κ ] ((ρ ≡ (l ▹ τ))) or 
    Σ[ τ ∈ NeutralType Δ R[ κ ] ] ((ρ ≡ ne τ))
row-canonicity (ne τ) = right (τ , refl)
row-canonicity (l ▹ τ) = left (l , τ , refl)




--------------------------------------------------------------------------------
-- label-canonicity

-- label-canonicity : (ℓ : NormalType Δ L) → 
--   ∃[ l ] (ℓ ≡ lab l) or 
--   ∃[ l₁ ] (∃[ l₂ ] (ℓ ≡ ΠL (l₁ ▹ l₂))) or
--   ∃[ l₁ ] (∃[ l₂ ] (ℓ ≡ ΣL (l₁ ▹ l₂)))
-- label-canonicity (lab l) = left (l , refl)
-- label-canonicity (ΠL (l₁ ▹ l₂)) = right (left (l₁ , l₂ , refl))
-- label-canonicity (ΣL (l₁ ▹ l₂)) = right (right (l₁ , l₂ , refl))


--------------------------------------------------------------------------------
-- arrow-canonicity

arrow-canonicity : (f : NormalType Δ (κ₁ `→ κ₂)) → ∃[ τ ] (f ≡ `λ τ)
arrow-canonicity (`λ f) = f , refl


--------------------------------------------------------------------------------
-- 3.4 Soundness of Type Normalization
--
-- (OMITTED).

⇑ : NormalType Δ κ → Type Δ κ
⇑NE : NeutralType Δ κ → Type Δ κ
-- ⇑Row : Row Δ R[ κ ] → Type Δ R[ κ ]
⇑Pred : NormalPred Δ R[ κ ] → Pred Δ R[ κ ] 

⇑ Unit   = Unit
⇑ (ne x) = ⇑NE x
⇑ (l ▹ τ) = (⇑ l) ▹ (⇑ τ)
⇑ (`λ τ) = `λ (⇑ τ)
⇑ (τ₁ `→ τ₂) = ⇑ τ₁ `→ ⇑ τ₂
⇑ (`∀ κ τ) = `∀ κ (⇑ τ)
⇑ (μ τ) = μ (⇑ τ)
⇑ (lab l) = lab l
⇑ ⌊ τ ⌋ = ⌊ ⇑ τ ⌋
⇑ (Π x) = Π · ⇑ x
⇑ (ΠL x) = Π · ⇑ x
⇑ (Σ x) = Σ · ⇑ x
⇑ (ΣL x) = Σ · ⇑ x
⇑ (π ⇒ τ) = (⇑Pred π) ⇒ (⇑ τ)

⇑NE (` x) = ` x
⇑NE (τ₁ · τ₂) = (⇑NE τ₁) · (⇑ τ₂)
-- ⇑NE (Π ρ) = Π · ⇑NE ρ
-- ⇑NE (Σ ρ) = Σ · ⇑NE ρ
⇑NE (F <$> τ) = (⇑ F) <$> (⇑NE τ) 

-- ⇑Row (l ▹ τ) = (⇑ l) ▹ (⇑ τ)

⇑Pred (ρ₁ · ρ₂ ~ ρ₃) = (⇑ ρ₁) · (⇑ ρ₂) ~ (⇑ ρ₃)
⇑Pred (ρ₁ ≲ ρ₂) = (⇑ ρ₁) ≲ (⇑ ρ₂)



