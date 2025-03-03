module Rome.Operational.Terms.Normal.Syntax where

open import Rome.Operational.Prelude
open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

open import Rome.Operational.Types.Syntax

open import Rome.Operational.Types.Normal.Syntax
open import Rome.Operational.Types.Normal.Renaming
open import Rome.Operational.Types.Normal.Substitution
open import Rome.Operational.Types.Semantic.NBE

--------------------------------------------------------------------------------
-- 3.7 Terms with normal types

data Context : KEnv → Set where
  ε : Context ∅
  _,,_ : Context Δ → (κ : Kind) → Context (Δ ,, κ)
  _,_  : Context Δ → NormalType Δ ★ → Context Δ


data Var : Context Δ → NormalType Δ ★ → Set where
  Z : ∀ {Γ} {τ : NormalType Δ ★} → Var (Γ , τ) τ
  S : ∀ {Γ} {τ₁ τ₂ : NormalType Δ ★} → Var Γ τ₁  → Var (Γ , τ₂) τ₁
  T : ∀ {Γ} {τ : NormalType Δ ★} → Var Γ τ → Var (Γ ,, κ) (weaken τ)

private
  variable
    τ υ τ₁ τ₂ : NormalType Δ ★
    l l₁ l₂   : NormalType Δ L
    
data NormalTerm {Δ} Γ : NormalType Δ ★ → Set where
  ` : Var Γ τ → 
      --------
      NormalTerm Γ τ

  `λ : ∀ {τ₁ τ₂} → 

       NormalTerm (Γ , τ₁) τ₂ → 
       --------------
       NormalTerm Γ (τ₁ `→ τ₂)

  _·_ : ∀ {τ₁ τ₂} → 

       NormalTerm Γ (τ₁ `→ τ₂) → 
       NormalTerm Γ τ₁ → 
       ---------
       NormalTerm Γ τ₂
  
  ------------------------------------------------------------
  -- System Fω

  Λ : ∀ {τ} →

      NormalTerm (Γ ,, κ) τ →
      -----------
      NormalTerm Γ (`∀ κ τ)

  _·[_] : ∀ {τ₂} → 
  
          NormalTerm Γ (`∀ κ τ₂) →
          (τ₁ : NormalType Δ κ) → 
          ----------------
          NormalTerm Γ (τ₂ β[ τ₁ ])

  ------------------------------------------------------------
  -- Recursive types

  roll : 
         ∀ (F : NormalType Δ (★ `→ ★)) → 
         -- lol. Okay, neutrality is not quite accurate for our needs.
         NormalTerm Γ (F ·' (μ F)) → 
         -----------------
         NormalTerm Γ (μ F)

  unroll : 
           ∀ F → 
           NormalTerm Γ (μ F) → 
           --------------
           NormalTerm Γ (F ·' (μ F))

  ------------------------------------------------------------
  -- Qualified types
  
  -- ...

  ------------------------------------------------------------
  -- Rω labels

  -- labels
  lab : 

        ∀ (l : NormalType Δ L) →
        -------------------
        NormalTerm Γ ⌊ l ⌋

  ------------------------------------------------------------
  -- Rω records

  -- Record singleton formation
  _Π▹_ : 
          (M₁ : NormalTerm Γ ⌊ l ⌋) (M₂ : NormalTerm Γ υ) →
          ----------------------------------------
          NormalTerm Γ (Π (l ▹ υ))

  -- Record singleton elimination
  _Π/_ :
          (M₁ : NormalTerm Γ (Π (l ▹ υ))) (M₂ : NormalTerm Γ ⌊ l ⌋) →
          ----------------------------------------
          NormalTerm Γ υ

  ------------------------------------------------------------
  -- Rω variants

  -- Record singleton formation
  _Σ▹_ : 
          (M₁ : NormalTerm Γ ⌊ l ⌋) (M₂ : NormalTerm Γ υ) →
          ----------------------------------------
          NormalTerm Γ (Σ (l ▹ υ))

  -- Record singleton elimination
  _Σ/_ :
          (M₁ : NormalTerm Γ (Σ (l ▹ υ))) (M₂ : NormalTerm Γ ⌊ l ⌋) →
          ----------------------------------------
          NormalTerm Γ υ


--------------------------------------------------------------------------------
-- helpers.

convVar : ∀ {Γ} {τ₁ τ₂ : NormalType Δ ★} → τ₁ ≡ τ₂ → Var Γ τ₁ → Var Γ τ₂
convVar refl v = v

conv : ∀ {Γ} {τ₁ τ₂ : NormalType Δ ★} → τ₁ ≡ τ₂ → NormalTerm Γ τ₁ → NormalTerm Γ τ₂
conv refl M = M
