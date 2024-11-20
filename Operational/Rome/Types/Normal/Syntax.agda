module Operational.Rome.Types.Normal.Syntax where

open import Operational.Rome.Prelude
open import Operational.Rome.Kinds.Syntax
open import Operational.Rome.Kinds.GVars

open import Operational.Rome.Types.Syntax
open import Operational.Rome.Types.Renaming using (↑ ; Renaming)
open import Operational.Rome.Types.Properties



--------------------------------------------------------------------------------
-- 3.1. NormalType types
--
-- - NeutralType types are either 
--    (i)  variables, or
--    (ii) applications with variables stuck in head position. 
--         (And hence cannot reduce).
-- - NormalType types are types precluded from any applications (barring neutral forms).

data NormalType (Δ : KEnv) : Kind → Set
data NeutralType Δ κ : Set where

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
    
      NormalType Δ L → 
      NeutralType Δ κ →
      ------------------
      NeutralType Δ κ

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

  -- singleton formation
  _▹_ :
        NormalType Δ L → NormalType Δ κ →
        -------------------
        NormalType Δ κ

  -- Row singleton formation
  _R▹_ :
         NormalType Δ L → NormalType Δ κ →
         -------------------
         NormalType Δ R[ κ ]

  -- label constant formation
  ⌊_⌋ :
        NormalType Δ L →
        ----------
        NormalType Δ ★

  Π     :

          NormalType Δ R[ κ ] → 
          ----------------
          NormalType Δ κ

  Σ     :

          NormalType Δ R[ κ ] → 
          ----------------
          NormalType Δ κ


--------------------------------------------------------------------------------
-- 3.4 Soundness of Type NormalTypeization
--
-- (OMITTED).

embed : NormalType Δ κ → Type Δ κ
embedNE : NeutralType Δ κ → Type Δ κ

embed Unit   = Unit
embed (ne x) = embedNE x
embed (`λ τ) = `λ (embed τ)
embed (τ₁ `→ τ₂) = embed τ₁ `→ embed τ₂
embed (`∀ κ τ) = `∀ κ (embed τ)
embed (μ τ) = μ (embed τ)
embed (Π τ) = Π (embed τ)
embed (Σ τ) = Σ (embed τ)
embed (lab l) = lab l
embed (τ₁ ▹ τ₂) = (embed τ₁) ▹ (embed τ₂)
embed (τ₁ R▹ τ₂) = (embed τ₁) R▹ (embed τ₂)
embed ⌊ τ ⌋ = ⌊ embed τ ⌋

embedNE (` x) = ` x
embedNE (τ₁ · τ₂) = (embedNE τ₁) · (embed τ₂)
embedNE (τ₁ ▹ τ₂) = (embed τ₁) ▹ (embedNE τ₂)
