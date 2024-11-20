module SFFP.Types.Normal.Syntax where

open import SFFP.Prelude
open import SFFP.Kinds.Syntax
open import SFFP.Kinds.GVars

open import SFFP.Types.Syntax
open import SFFP.Types.Renaming using (↑ ; Renaming)
open import SFFP.Types.Properties



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

data NormalType Δ where
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
      
         NormalType (Δ ,, ★) ★ →
         -------------
         NormalType Δ ★

--------------------------------------------------------------------------------
-- 3.4 Soundness of Type NormalTypeization
--
-- (OMITTED).

embed : NormalType Δ κ → Type Δ κ
embedNE : NeutralType Δ κ → Type Δ κ

embed (ne x) = embedNE x
embed (`λ τ) = `λ (embed τ)
embed (τ₁ `→ τ₂) = embed τ₁ `→ embed τ₂
embed (`∀ κ τ) = `∀ κ (embed τ)
embed (μ τ) = μ (embed τ)

embedNE (` x) = ` x
embedNE (τ₁ · τ₂) = (embedNE τ₁) · (embed τ₂)
