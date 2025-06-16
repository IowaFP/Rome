{-# OPTIONS --safe #-}
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
-- Small step semantics.

infixr 0 _—→_
data _—→_ : ∀ {τ} → NormalTerm Γ τ → NormalTerm Γ τ → Set where
  -- congruence rules
  ξ-·1 : ∀ {M₁ M₂ : NormalTerm Γ (τ₁ `→ τ₂)} {N : NormalTerm Γ τ₁} →
           M₁ —→ M₂ →
           -----------------
           M₁ · N —→ M₂ · N

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

  ξ-Π▹₁ : ∀ {l : Label}
            (M : NormalTerm Γ τ) (ℓ₁ ℓ₂ : NormalTerm Γ ⌊ lab l ⌋)  → 

             ℓ₁ —→ ℓ₂ → 
             -----------------------
             (ℓ Π▹ M) —→ (ℓ Π▹ M)

  ξ-Π▹₂ : ∀ {l : Label}
            (M₁ M₂ : NormalTerm Γ τ) (ℓ : NormalTerm Γ ⌊ lab l ⌋)  → 

             M₁ —→ M₂ → 
             -----------------------
             (ℓ Π▹ M₁) —→ (ℓ Π▹ M₂)

  ξ-Π/ : ∀  {l : Label}
            (M₁ M₂ : NormalTerm Γ (Π (l ▹' τ))) (ℓ : NormalTerm Γ ⌊ lab l ⌋)  → 

             M₁ —→ M₂ → 
             -----------------------
             (M₁ Π/ ℓ) —→ (M₂ Π/ ℓ)        

  ξ-Σ▹ : ∀  {l : Label}
            (M₁ M₂ : NormalTerm Γ τ) (ℓ : NormalTerm Γ ⌊ lab l ⌋)  → 

             M₁ —→ M₂ → 
             -----------------------
             (ℓ Σ▹ M₁) —→ (ℓ Σ▹ M₂)

  ξ-Σ/ : ∀ {l : Label}
            (M₁ M₂ : NormalTerm Γ (Σ (l ▹' τ))) (ℓ : NormalTerm Γ ⌊ lab l ⌋)  → 

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

  β-Π/ :  ∀ {l : Label}
            (M : NormalTerm Γ τ) (ℓ₁ ℓ₂ : NormalTerm Γ ⌊ lab l ⌋) → 


             -----------------------
             ((ℓ₁ Π▹ M) Π/ ℓ₂) —→ M

  β-Σ/ :  ∀ {l : Label}
            (M : NormalTerm Γ τ) (ℓ₁ ℓ₂ : NormalTerm Γ ⌊ lab l ⌋) → 

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
