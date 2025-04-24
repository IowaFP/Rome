{-# OPTIONS --allow-unsolved-metas #-}
module Rome.Operational.Terms.Normal.Reduction where

open import Rome.Operational.Prelude

open import Rome.Operational.Kinds.Syntax

open import Rome.Operational.Types.Syntax
open import Rome.Operational.Types.SynAna
open import Rome.Operational.Types.Normal.Syntax
open import Rome.Operational.Types.Normal.Substitution
open import Rome.Operational.Types.Normal.Properties.Renaming
open import Rome.Operational.Types.Normal.Properties.Substitution

open import Rome.Operational.Terms.Normal.Syntax
open import Rome.Operational.Terms.Normal.Substitution

open import Rome.Operational.Types.Semantic.NBE

open import Rome.Operational.Kinds.GVars
open import Rome.Operational.Terms.Normal.GVars


--------------------------------------------------------------------------------
-- Values

data Value {Δ} {Γ : NormalContext Δ} : ∀ {τ : NormalType Δ ★} → NormalTerm Γ τ → Set where
  V-λ : 
          (M : NormalTerm (Γ , τ₂) τ₁) → 
          Value (`λ M)

  V-Λ :
          (M : NormalTerm (Γ ,, κ) τ) → 
        --   Value M → 
          Value (Λ M)

  V-ƛ :
          (M : NormalTerm (Γ ,,, π) τ) → 
          Value (`ƛ M)

  V-In : ∀ (F : NormalType Δ (★ `→ ★)) 
             {M : NormalTerm Γ (F ·' (μ F))} → 
             Value M → 
             Value (In F M)

  V-# :   ∀ {l : NormalType Δ L} → 
          Value (# l)

  V-Π   : ∀ (ℓ : NormalTerm Γ ⌊ l ⌋) 
            (M : NormalTerm Γ υ) → 

            Value M → 
            ---------------------
            Value (ℓ Π▹ M)

  V-⊹  : ∀ 
           {e : NormalEnt Γ (ρ₁ · ρ₂ ~ ρ₃)}  (M : NormalTerm Γ (Π ρ₁)) (N : NormalTerm Γ (Π ρ₂)) → 

            Value M → Value N → 
            ---------------------
            Value ((M ⊹ N) e)

  V-▿  : 
           {e : NormalEnt Γ (ρ₁ · ρ₂ ~ ρ₃)} (M : NormalTerm Γ (Σ ρ₁ `→ τ)) (N : NormalTerm Γ (Σ ρ₂ `→ τ)) → 

            Value M → Value N → 
            ---------------------
            Value ((M ▿ N) e)

  V-Σ   : ∀ 
            (ℓ : NormalTerm Γ ⌊ l ⌋) → (M : NormalTerm Γ τ) → 

            Value M → 
            ---------------------
            Value (ℓ Σ▹ M)

  V-Unit : ∀ (M : NormalTerm Γ (Π εNF)) → 

           -------
           Value M 

  V-fix : ∀ (M : NormalTerm Γ (τ `→ τ)) → 

          -------------
          Value (fix M)

  V-syn : ∀ (ρ : NormalType Δ R[ κ ]) → (φ : NormalType Δ (κ `→ ★)) (M : NormalTerm Γ (⇓ (SynT (⇑ ρ) (⇑ φ)))) → 

          -----------------
          Value (syn ρ φ M)

  V-ana : ∀ (ρ : NormalType Δ R[ κ ]) (φ : NormalType Δ (κ `→ ★)) (τ : NormalType Δ ★) (M : NormalTerm Γ (⇓ (AnaT (⇑ ρ) (⇑ φ) (⇑ τ)))) → 

          -----------------
          Value (ana ρ φ τ M)

--------------------------------------------------------------------------------
-- Small step semantics.

infixr 0 _—→_
data _—→_ : ∀ {τ} → NormalTerm Γ τ → NormalTerm Γ τ → Set where
  -- congruence rules
  ξ-·1 : ∀ {M₁ M₂ : NormalTerm Γ (τ₁ `→ τ₂)} {N : NormalTerm Γ τ₁} →
           M₁ —→ M₂ →
           -----------------
           M₁ · N —→ M₂ · N

--   ξ-Λ : ∀ {M₁ M₂ : NormalTerm (Γ ,, κ) τ} →
--          M₁ —→ M₂ →
--          -----------------------
--          (Λ M₁) —→ (Λ M₂)

--   ξ-ƛ : ∀ {M₁ M₂ : NormalTerm (Γ ,,, π) τ} →

--          M₁ —→ M₂ →
--          -----------------------
--          (`ƛ M₁) —→ (`ƛ M₂)

  ξ-·[] : ∀ {τ'} {M₁ M₂ : NormalTerm Γ (`∀ τ)} →
            M₁ —→ M₂ →
            ------------------------
            M₁ ·[ τ' ] —→ M₂ ·[ τ' ]

  ξ-·⟨⟩ : ∀ {M₁ M₂ : NormalTerm Γ (π ⇒ τ)} {e : NormalEnt Γ π} →
            M₁ —→ M₂ →
            ------------------------
            M₁ ·⟨ e ⟩ —→ M₂ ·⟨ e ⟩

  ξ-Out : ∀ {F} {M₁ M₂ : NormalTerm Γ (μ F)} →
               M₁ —→ M₂ →
               -----------------------
               Out F M₁ —→ Out F M₂

  ξ-In : ∀ {F} {M₁ M₂ : NormalTerm Γ (F ·' (μ F))} →
             M₁ —→ M₂ →
             -----------------------
             In F M₁ —→ In F M₂

  ξ-Π▹ : ∀ 
            (M₁ M₂ : NormalTerm Γ τ) (ℓ : NormalTerm Γ ⌊ l ⌋)  → 

             M₁ —→ M₂ → 
             -----------------------
             (ℓ Π▹ M₁) —→ (ℓ Π▹ M₂)

  ξ-Π/ : ∀ 
            (M₁ M₂ : NormalTerm Γ (Π (l ▹' τ))) (ℓ : NormalTerm Γ ⌊ l ⌋)  → 

             M₁ —→ M₂ → 
             -----------------------
             (M₁ Π/ ℓ) —→ (M₂ Π/ ℓ)        

  ξ-Σ▹ : ∀ 
            (M₁ M₂ : NormalTerm Γ τ) (ℓ : NormalTerm Γ ⌊ l ⌋)  → 

             M₁ —→ M₂ → 
             -----------------------
             (ℓ Σ▹ M₁) —→ (ℓ Σ▹ M₂)

  ξ-Σ/ : ∀ 
            (M₁ M₂ : NormalTerm Γ (Σ (l ▹' τ))) (ℓ : NormalTerm Γ ⌊ l ⌋)  → 

             M₁ —→ M₂ → 
             -----------------------
             (M₁ Σ/ ℓ) —→ (M₂ Σ/ ℓ)    

  ξ-prj : ∀ 
            (M₁ M₂ : NormalTerm Γ (Π ρ₂)) (e : NormalEnt Γ (ρ₁ ≲ ρ₂)) → 

            M₁ —→ M₂ → 
            ------------ 
            prj M₁ e —→ prj M₂ e

  ξ-inj : ∀ 
            (M₁ M₂ : NormalTerm Γ (Σ ρ₁)) (e : NormalEnt Γ (ρ₁ ≲ ρ₂)) → 

            M₁ —→ M₂ → 
            ------------ 
            inj M₁ e —→ inj M₂ e

  ξ-⊹₁ : ∀
         (M₁ M₂ : NormalTerm Γ (Π ρ₁)) (N : NormalTerm Γ (Π ρ₂)) 
         (e : NormalEnt Γ (ρ₁ · ρ₂ ~ ρ₃)) → 
    
       (M₁ —→ M₂) → 
       (M₁ ⊹ N) e —→ (M₂ ⊹ N) e

  ξ-⊹₂ : ∀
         (M : NormalTerm Γ (Π ρ₁)) (N₁ N₂ : NormalTerm Γ (Π ρ₂)) 
         (e : NormalEnt Γ (ρ₁ · ρ₂ ~ ρ₃)) → 
    
       (N₁ —→ N₂) → 
       (M ⊹ N₁) e —→ (M ⊹ N₂) e

  ξ-▿₁ : ∀
         (M₁ M₂ : NormalTerm Γ (Σ ρ₁ `→ τ)) (N : NormalTerm Γ (Σ ρ₂ `→ τ)) 
         (e : NormalEnt Γ (ρ₁ · ρ₂ ~ ρ₃)) → 
    
       (M₁ —→ M₂) → 
       (M₁ ▿ N) e —→ (M₂ ▿ N) e

  ξ-▿₂ : ∀
         (M : NormalTerm Γ (Σ ρ₁ `→ τ)) (N₁ N₂ : NormalTerm Γ (Σ ρ₂ `→ τ)) 
         (e : NormalEnt Γ (ρ₁ · ρ₂ ~ ρ₃)) → 
    
       (N₁ —→ N₂) → 
       (M ▿ N₁) e —→ (M ▿ N₂) e

  -- computational rules
  β-λ : ∀ {M : NormalTerm (Γ , τ₁) τ₂} {N : NormalTerm Γ τ₁} →
          
          -----------------------
          (`λ M) · N —→ M β[ N ]

  β-Λ : ∀ {τ₁ τ₂} {M : NormalTerm (Γ ,, κ) τ₂}  →

          --------------------------
          Λ M ·[ τ₁ ] —→ M β·[ τ₁ ]

  β-ƛ : ∀ {M : NormalTerm (Γ ,,, π) τ} {e : NormalEnt Γ π} →
          
          -----------------------
          (`ƛ M) ·⟨ e ⟩ —→ (M βπ[ e ])

  β-In : ∀ {F} {M : NormalTerm Γ (F ·' μ F)} →

             -------------------------
             Out F (In F M) —→ M

  β-Π/ :  ∀ 
            (M : NormalTerm Γ τ) (ℓ₁ ℓ₂ : NormalTerm Γ ⌊ l ⌋) → 


             -----------------------
             ((ℓ₁ Π▹ M) Π/ ℓ₂) —→ M

  β-Σ/ :  ∀ 
            (M : NormalTerm Γ τ) (ℓ₁ ℓ₂ : NormalTerm Γ ⌊ l ⌋) → 

             -----------------------
             ((ℓ₁ Σ▹ M) Σ/ ℓ₂) —→ M

  β-prj : ∀  
            (M : NormalTerm Γ (Π ρ)) (e :  NormalEnt Γ (ρ ≲ ρ)) → 
              
             Value M → 
             -----------------------
             prj M e —→ M

  β-inj : ∀ 
            (M : NormalTerm Γ (Σ ρ)) (e :  NormalEnt Γ (ρ ≲ ρ)) → 
            
             Value M → 
             -----------------------
             inj M e —→ M


  β-fix : ∀ (M : NormalTerm Γ (τ `→ τ)) → 

          -------------
          fix M —→ M · (fix M)

--   β-Πε-right : ∀ 
--         (M : NormalTerm Γ (Π ρ)) (E : NormalTerm Γ (Π ε)) 
--         (e : NormalEnt Γ (ρ · ε ~ ρ)) → 
        
--         Value M → 
--         ---------------------
--         ((M ⊹ E) e) —→ M


--   β-Πε-left : ∀ 
--         (E : NormalTerm Γ (Π ε)) (M : NormalTerm Γ (Π ρ))  
--         (e : NormalEnt Γ (ε · ρ ~ ρ)) → 
        
--         Value M → 
--         ---------------------
--         ((E ⊹ M) e) —→ M
