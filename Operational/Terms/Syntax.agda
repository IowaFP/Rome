module Rome.Operational.Terms.Syntax where

open import Rome.Operational.Prelude
open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

open import Rome.Operational.Types.Syntax

open import Rome.Operational.Types.Equivalence

open import Rome.Operational.Types.Normal.Syntax
open import Rome.Operational.Types.Normal.Renaming
open import Rome.Operational.Types.Normal.Substitution
open import Rome.Operational.Types.Semantic.NBE

open import Rome.Operational.Types.Theorems.Soundness
open import Rome.Operational.Types.Theorems.Completeness

--------------------------------------------------------------------------------
-- 3.7 Terms with normal types

data Context : KEnv → Set where
  ε : Context ∅
  _,,_ : Context Δ → (κ : Kind) → Context (Δ ,, κ)
  _,_  : Context Δ → NormalType Δ ★ → Context Δ


data Var : Context Δ → NormalType Δ ★ → Set where
  Z : ∀ {Γ} {τ : NormalType Δ ★} → Var (Γ , τ) τ
  S : ∀ {Γ} {τ₁ τ₂ : NormalType Δ ★} → Var Γ τ₁  → Var (Γ , τ₂) τ₁
  T : ∀ {Γ} {τ : NormalType Δ ★} → Var Γ τ → Var (Γ ,, κ) (weakenₖNF τ)

private
  variable
    τ υ τ₁ τ₂ : NormalType Δ ★
    l l₁ l₂   : NormalType Δ L
    
data Term {Δ} Γ : NormalType Δ ★ → Set where
  ` : Var Γ τ → 
      --------
      Term Γ τ

  `λ : ∀ {τ₁ τ₂} → 

       Term (Γ , τ₁) τ₂ → 
       --------------
       Term Γ (τ₁ `→ τ₂)

  _·_ : ∀ {τ₁ τ₂} → 

       Term Γ (τ₁ `→ τ₂) → 
       Term Γ τ₁ → 
       ---------
       Term Γ τ₂
  
  ------------------------------------------------------------
  -- System Fω

  Λ : ∀ {τ} →

      Term (Γ ,, κ) τ →
      -----------
      Term Γ (`∀ κ τ)

  _·[_] : ∀ {τ₂} → 
  
          Term Γ (`∀ κ τ₂) →
          (τ₁ : NormalType Δ κ) → 
          ----------------
          Term Γ (τ₂ βₖNF[ τ₁ ])

  ------------------------------------------------------------
  -- Recursive types

  In : 
         ∀ (F : NormalType Δ (★ `→ ★)) → 
         Term Γ (F ·' (μ F)) → 
         -----------------
         Term Γ (μ F)

  Out : 
           ∀ F → 
           Term Γ (μ F) → 
           --------------
           Term Γ (F ·' (μ F))

  ------------------------------------------------------------
  -- Qualified types
  
  -- ...

  ------------------------------------------------------------
  -- Rω labels

  -- label constants
  # : 

        ∀ (l : Label) →
        -------------------
        Term Γ ⌊ lab l ⌋

  ------------------------------------------------------------
  -- Rω records

  -- Record singleton formation
  _Π▹_ : 
          (M₁ : Term Γ ⌊ l ⌋) (M₂ : Term Γ υ) →
          ----------------------------------------
          Term Γ (Π (l ▹ υ))

  -- Record singleton elimination
  _Π/_ :
          (M₁ : Term Γ (Π (l ▹ υ))) (M₂ : Term Γ ⌊ l ⌋) →
          ----------------------------------------
          Term Γ υ

  ------------------------------------------------------------
  -- Rω variants

  -- Record singleton formation
  _Σ▹_ : 
          (M₁ : Term Γ ⌊ l ⌋) (M₂ : Term Γ υ) →
          ----------------------------------------
          Term Γ (Σ (l ▹ υ))

  -- Record singleton elimination
  _Σ/_ :
          (M₁ : Term Γ (Σ (l ▹ υ))) (M₂ : Term Γ ⌊ l ⌋) →
          ----------------------------------------
          Term Γ υ


--------------------------------------------------------------------------------
-- Conversion helpers.

convVar : ∀ {Γ} {τ₁ τ₂ : NormalType Δ ★} → τ₁ ≡ τ₂ → Var Γ τ₁ → Var Γ τ₂
convVar refl v = v

conv : ∀ {Γ} {τ₁ τ₂ : NormalType Δ ★} → τ₁ ≡ τ₂ → Term Γ τ₁ → Term Γ τ₂
conv refl M = M

conv-t : ∀ {Γ} {τ₁ τ₂ : Type Δ ★} → τ₁ ≡t τ₂ → Term Γ (⇓ τ₁) → Term Γ (⇓ τ₂)
conv-t eq M = conv (completeness eq) M