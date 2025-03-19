{-# OPTIONS --allow-unsolved-metas #-}
module Rome.Operational.Terms.Semantics.Reduction where

open import Rome.Operational.Prelude

open import Rome.Operational.Kinds.Syntax

import Rome.Operational.Types as Types
open import Rome.Operational.Types.Normal.Syntax
open import Rome.Operational.Types.Normal.Substitution
open import Rome.Operational.Types.Normal.Properties.Renaming
open import Rome.Operational.Types.Normal.Properties.Substitution

open import Rome.Operational.Terms.Syntax
open import Rome.Operational.Terms.Substitution

open import Rome.Operational.Kinds.GVars
open import Rome.Operational.Terms.GVars


--------------------------------------------------------------------------------
-- Values

data Value {Δ} {Γ : Context Δ} : ∀ {τ : NormalType Δ ★} → Term Γ τ → Set where
  V-λ : 
          (M : Term (Γ , τ₂) τ₁) → 
          Value (`λ M)

  V-Λ :
          (M : Term (Γ ,, κ) τ) → 
        --   Value M → 
          Value (Λ M)

  V-ƛ :
          (M : Term (Γ ,,, π) τ) → 
          Value (`ƛ M)

  V-In : ∀ (F : NormalType Δ (★ `→ ★)) 
             {M : Term Γ (F ·' (μ F))} → 
             Value M → 
             Value (In F M)

  V-# :
          Value (# l)

  V-Π   : ∀ (ℓ : Term Γ ⌊ l ⌋) 
            (M : Term Γ υ) → 

            Value M → 
            ---------------------
            Value (ℓ Π▹ M)

  V-⊹  : -- ∀ 
           {e : Ent Γ (ρ₁ · ρ₂ ~ ρ₃)} (M : Term Γ (Π ρ₁)) (N : Term Γ (Π ρ₂)) → 

            Value M → Value N → 
            ---------------------
            Value ((M ⊹ N) e)

  V-▿  : 
           {e : Ent Γ (ρ₁ · ρ₂ ~ ρ₃)} (M : Term Γ (Σ ρ₁ `→ τ)) (N : Term Γ (Σ ρ₂ `→ τ)) → 

            Value M → Value N → 
            ---------------------
            Value ((M ▿ N) e)

  V-Σ   : ∀ 
            (ℓ : Term Γ ⌊ l ⌋) → (M : Term Γ τ) → 

            Value M → 
            ---------------------
            Value (ℓ Σ▹ M)

  V-Unit : ∀ (M : Term Γ (Π ε)) → 
           -----------------------
           Value M 


--------------------------------------------------------------------------------
-- Canonicity of records


--------------------------------------------------------------------------------
-- Small step semantics.

infixr 0 _—→_
data _—→_ : ∀ {τ} → Term Γ τ → Term Γ τ → Set where
  -- congruence rules
  ξ-·1 : ∀ {M₁ M₂ : Term Γ (τ₁ `→ τ₂)} {N : Term Γ τ₁} →
           M₁ —→ M₂ →
           -----------------
           M₁ · N —→ M₂ · N

--   ξ-Λ : ∀ {M₁ M₂ : Term (Γ ,, κ) τ} →
--          M₁ —→ M₂ →
--          -----------------------
--          (Λ M₁) —→ (Λ M₂)

--   ξ-ƛ : ∀ {M₁ M₂ : Term (Γ ,,, π) τ} →

--          M₁ —→ M₂ →
--          -----------------------
--          (`ƛ M₁) —→ (`ƛ M₂)

  ξ-·[] : ∀ {τ'} {M₁ M₂ : Term Γ (`∀ κ τ)} →
            M₁ —→ M₂ →
            ------------------------
            M₁ ·[ τ' ] —→ M₂ ·[ τ' ]

  ξ-·⟨⟩ : ∀ {M₁ M₂ : Term Γ (π ⇒ τ)} {e : Ent Γ π} →
            M₁ —→ M₂ →
            ------------------------
            M₁ ·⟨ e ⟩ —→ M₂ ·⟨ e ⟩

  ξ-Out : ∀ {F} {M₁ M₂ : Term Γ (μ F)} →
               M₁ —→ M₂ →
               -----------------------
               Out F M₁ —→ Out F M₂

  ξ-In : ∀ {F} {M₁ M₂ : Term Γ (F ·' (μ F))} →
             M₁ —→ M₂ →
             -----------------------
             In F M₁ —→ In F M₂

  ξ-Π▹ : ∀ 
            (M₁ M₂ : Term Γ τ) (ℓ : Term Γ ⌊ l ⌋)  → 

             M₁ —→ M₂ → 
             -----------------------
             (ℓ Π▹ M₁) —→ (ℓ Π▹ M₂)

  ξ-Π/ : ∀ 
            (M₁ M₂ : Term Γ (Π (l ▹ τ))) (ℓ : Term Γ ⌊ l ⌋)  → 

             M₁ —→ M₂ → 
             -----------------------
             (M₁ Π/ ℓ) —→ (M₂ Π/ ℓ)        

  ξ-Σ▹ : ∀ 
            (M₁ M₂ : Term Γ τ) (ℓ : Term Γ ⌊ l ⌋)  → 

             M₁ —→ M₂ → 
             -----------------------
             (ℓ Σ▹ M₁) —→ (ℓ Σ▹ M₂)

  ξ-Σ/ : ∀ 
            (M₁ M₂ : Term Γ (Σ (l ▹ τ))) (ℓ : Term Γ ⌊ l ⌋)  → 

             M₁ —→ M₂ → 
             -----------------------
             (M₁ Σ/ ℓ) —→ (M₂ Σ/ ℓ)    

  ξ-prj : ∀ 
            (M₁ M₂ : Term Γ (Π ρ₂)) (e : Ent Γ (ρ₁ ≲ ρ₂)) → 

            M₁ —→ M₂ → 
            ------------ 
            prj M₁ e —→ prj M₂ e

  ξ-inj : ∀ 
            (M₁ M₂ : Term Γ (Σ ρ₁)) (e : Ent Γ (ρ₁ ≲ ρ₂)) → 

            M₁ —→ M₂ → 
            ------------ 
            inj M₁ e —→ inj M₂ e

  ξ-⊹₁ : ∀
         (M₁ M₂ : Term Γ (Π ρ₁)) (N : Term Γ (Π ρ₂)) 
         (e : Ent Γ (ρ₁ · ρ₂ ~ ρ₃)) → 
    
       (M₁ —→ M₂) → 
       (M₁ ⊹ N) e —→ (M₂ ⊹ N) e

  ξ-⊹₂ : ∀
         (M : Term Γ (Π ρ₁)) (N₁ N₂ : Term Γ (Π ρ₂)) 
         (e : Ent Γ (ρ₁ · ρ₂ ~ ρ₃)) → 
    
       (N₁ —→ N₂) → 
       (M ⊹ N₁) e —→ (M ⊹ N₂) e

  ξ-▿₁ : ∀
         (M₁ M₂ : Term Γ (Σ ρ₁ `→ τ)) (N : Term Γ (Σ ρ₂ `→ τ)) 
         (e : Ent Γ (ρ₁ · ρ₂ ~ ρ₃)) → 
    
       (M₁ —→ M₂) → 
       (M₁ ▿ N) e —→ (M₂ ▿ N) e

  ξ-▿₂ : ∀
         (M : Term Γ (Σ ρ₁ `→ τ)) (N₁ N₂ : Term Γ (Σ ρ₂ `→ τ)) 
         (e : Ent Γ (ρ₁ · ρ₂ ~ ρ₃)) → 
    
       (N₁ —→ N₂) → 
       (M ▿ N₁) e —→ (M ▿ N₂) e

  -- computational rules
  β-λ : ∀ {M : Term (Γ , τ₁) τ₂} {N : Term Γ τ₁} →
          
          -----------------------
          (`λ M) · N —→ M β[ N ]

  β-Λ : ∀ {τ₁ τ₂} {M : Term (Γ ,, κ) τ₂}  →

          --------------------------
          Λ M ·[ τ₁ ] —→ M β·[ τ₁ ]

  β-ƛ : ∀ {M : Term (Γ ,,, π) τ} {e : Ent Γ π} →
          
          -----------------------
          (`ƛ M) ·⟨ e ⟩ —→ (M βπ[ e ])

  β-In : ∀ {F} {M : Term Γ (F ·' μ F)} →

             -------------------------
             Out F (In F M) —→ M

  β-Π/ :  ∀ 
            (M : Term Γ τ) (ℓ₁ ℓ₂ : Term Γ ⌊ l ⌋) → 

             Value M →
             -----------------------
             ((ℓ₁ Π▹ M) Π/ ℓ₂) —→ M

  β-Σ/ :  ∀ 
            (M : Term Γ τ) (ℓ₁ ℓ₂ : Term Γ ⌊ l ⌋) → 

             Value M →
             -----------------------
             ((ℓ₁ Σ▹ M) Σ/ ℓ₂) —→ M

  β-prj : ∀  
            (M : Term Γ (Π ρ)) (e :  Ent Γ (ρ ≲ ρ)) → 
              
             Value M → 
             -----------------------
             prj M e —→ M

  β-inj : ∀ 
            (M : Term Γ (Σ ρ)) (e :  Ent Γ (ρ ≲ ρ)) → 
            
             Value M → 
             -----------------------
             inj M e —→ M


  β-Πε-right : ∀ 
        (M : Term Γ (Π ρ)) (E : Term Γ (Π ε)) 
        (e : Ent Γ (ρ · ε ~ ρ)) → 
        
        Value M → 
        ---------------------
        ((M ⊹ E) e) —→ M


  β-Πε-left : ∀ 
        (E : Term Γ (Π ε)) (M : Term Γ (Π ρ))  
        (e : Ent Γ (ε · ρ ~ ρ)) → 
        
        Value M → 
        ---------------------
        ((E ⊹ M) e) —→ M
