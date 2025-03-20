module Rome.Operational.Types.Normal.Syntax where

open import Rome.Operational.Prelude
open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

open import Rome.Operational.Types.Syntax
open import Rome.Operational.Types.Renaming using (liftₖ ; Renamingₖ)



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

  _─₁_ : NeutralType Δ R[ κ ] → (NormalType Δ L × NormalType Δ κ) →
        NeutralType Δ R[ κ ]

  _─₂_ : (NormalType Δ L × NormalType Δ κ) → NeutralType Δ R[ κ ] →
        NeutralType Δ R[ κ ]

data NormalPred Δ where

  _·_~_ : 

       (ρ₁ ρ₂ ρ₃ : NormalType Δ R[ κ ]) → 
       --------------------- 
       NormalPred Δ R[ κ ]

  _≲_ : 

       (ρ₁ ρ₂ : NormalType Δ R[ κ ]) →
       ----------
       NormalPred Δ R[ κ ]  

data NormalType Δ where

  ne : 

      (x : NeutralType Δ κ) → {ground : True (ground? κ)} → 
      --------------
      NormalType Δ κ

  `λ :

      (τ : NormalType (Δ ,, κ₁) κ₂) → 
      --------------------------
      NormalType Δ (κ₁ `→ κ₂)

  _`→_ : 

      (τ₁ τ₂ : NormalType Δ ★) →
      -----------------
      NormalType Δ ★

  `∀    :
      
      (τ : NormalType (Δ ,, κ) ★) →
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

  ε : 

      ------------------  
      NormalType Δ R[ κ ]


  _▹_ : 
      
      (l : NormalType Δ L) → 
      (τ : NormalType Δ κ) → 
      ---------------------------
      NormalType Δ R[ κ ]

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
-- There are no neutral types in empty contexts

noNeutrals : NeutralType ∅ κ → ⊥
noNeutrals (n · τ) = noNeutrals n
noNeutrals (φ <$> n) = noNeutrals n
noNeutrals (n ─₁ x) = noNeutrals n
noNeutrals (x ─₂ n) = noNeutrals n

--------------------------------------------------------------------------------
-- Mapping type definitions over predicates 


mapPred : ∀ {Δ₁ Δ₂} {κ₁ κ₂} (P : NormalType Δ₁ R[ κ₁ ] → NormalType Δ₂ R[ κ₂ ]) → 
          NormalPred Δ₁ R[ κ₁ ] → NormalPred Δ₂ R[ κ₂ ]
mapPred P (ρ₁ · ρ₂ ~ ρ₃) = P ρ₁ · P ρ₂ ~ P ρ₃
mapPred P (ρ₁ ≲ ρ₂)      = P ρ₁ ≲ P ρ₂

-- -- predicate transformer
-- PredPT : ∀ {Δ₁ Δ₂} {κ₁ κ₂}
--             (P : NormalType Δ₁ R[ κ₁ ] → NormalType Δ₂ R[ κ₂ ]) → 
--             NormalPred Δ₁ R[ κ₁ ] → NormalPred 
-- PredPT P (ρ₁ · ρ₂ ~ ρ₃) = {! P ρ₁  !} -- P ρ₁ × P ρ₂ × P ρ₃
-- PredPT P (ρ₁ ≲ ρ₂) = {!   !} -- P ρ₁ × P ρ₂

mapPredHO : ∀ {Δ₁ Δ₂} {κ₁ κ₂}
            (P : NormalType Δ₁ R[ κ₁ ] → NormalType Δ₂ R[ κ₂ ]) (Q : NormalType Δ₁ R[ κ₁ ] → NormalType Δ₂ R[ κ₂ ]) → 
            (q : ∀ (τ : NormalType Δ₁ R[ κ₁ ]) → P τ ≡ Q τ) →
            (π : NormalPred Δ₁ R[ κ₁ ]) → mapPred P π ≡ mapPred Q π
mapPredHO P Q q (ρ₁ · ρ₂ ~ ρ₃) rewrite 
  q ρ₁ | q ρ₂ | q ρ₃ = refl
mapPredHO P Q q (ρ₁ ≲ ρ₂) rewrite 
  q ρ₁ | q ρ₂ = refl

mapPred-id : ∀ (π : NormalPred Δ R[ κ ]) → mapPred id π ≡ π
mapPred-id (ρ₁ · ρ₂ ~ ρ₃) = refl
mapPred-id (ρ₁ ≲ ρ₂) = refl


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
    Σ[ τ ∈ NeutralType Δ R[ κ ] ] ((ρ ≡ ne τ)) or 
    ρ ≡ ε 
row-canonicity (l ▹ τ) = left (l , τ , refl)
row-canonicity (ne τ) = right (left (τ , refl))
row-canonicity ε = right (right refl)

--------------------------------------------------------------------------------
-- arrow-canonicity

arrow-canonicity : (f : NormalType Δ (κ₁ `→ κ₂)) → ∃[ τ ] (f ≡ `λ τ)
arrow-canonicity (`λ f) = f , refl


--------------------------------------------------------------------------------
-- Embedding Normal/neutral types back to Types

⇑ : NormalType Δ κ → Type Δ κ
⇑NE : NeutralType Δ κ → Type Δ κ
⇑Pred : NormalPred Δ R[ κ ] → Pred Δ R[ κ ] 

⇑ ε   = ε
⇑ (ne x) = ⇑NE x
⇑ (l ▹ τ) = (⇑ l) ▹ (⇑ τ)
⇑ (`λ τ) = `λ (⇑ τ)
⇑ (τ₁ `→ τ₂) = ⇑ τ₁ `→ ⇑ τ₂
⇑ (`∀ τ) = `∀ (⇑ τ)
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
⇑NE (F <$> τ) = (⇑ F) <$> (⇑NE τ) 
⇑NE (n ─₁ τ) = ⇑NE n ─ ⇑ τ
⇑NE (τ ─₂ n) = ⇑ τ ─ ⇑NE n

⇑Pred (ρ₁ · ρ₂ ~ ρ₃) = (⇑ ρ₁) · (⇑ ρ₂) ~ (⇑ ρ₃)
⇑Pred (ρ₁ ≲ ρ₂) = (⇑ ρ₁) ≲ (⇑ ρ₂)

--------------------------------------------------------------------------------
-- Admissable constants

UnitNF : NormalType Δ ★
UnitNF = Π ε

