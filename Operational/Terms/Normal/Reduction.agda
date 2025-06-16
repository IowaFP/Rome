{-# OPTIONS --allow-unsolved-metas #-}
module Rome.Operational.Terms.Normal.Reduction where

open import Rome.Operational.Prelude
open import Rome.Operational.Containment

open import Rome.Operational.Kinds.Syntax


open import Rome.Operational.Types.Syntax
open import Rome.Operational.Types.SynAna
open import Rome.Operational.Types.Normal.Syntax
open import Rome.Operational.Types.Normal.Substitution
open import Rome.Operational.Types.Normal.Properties.Renaming
open import Rome.Operational.Types.Normal.Properties.Substitution

open import Rome.Operational.Terms.Normal.Syntax
open import Rome.Operational.Terms.Normal.Entailment.Properties
open import Rome.Operational.Terms.Normal.Substitution

open import Rome.Operational.Types.Semantic.NBE

open import Rome.Operational.Kinds.GVars
open import Rome.Operational.Terms.Normal.GVars

--------------------------------------------------------------------------------
-- Defining projection

data _∈ᵣ_ : ∀ {xs : SimpleRow NormalType Δ R[ ★ ] } → (l : Label × NormalTerm Γ τ) → Record Γ xs → Set where
  Here : ∀ {l} {τ : NormalType Δ ★} {xs : SimpleRow NormalType Δ R[ ★ ]} {M : NormalTerm Γ τ} → 
           {rxs : Record Γ xs} → 
           (l , M) ∈ᵣ (l ▹ M ⨾ rxs)

  There : ∀ {l l'} {τ υ : NormalType Δ ★} 
            {xs : SimpleRow NormalType Δ R[ ★ ]} {M : NormalTerm Γ τ} {M' : NormalTerm Γ υ} → 
            {rxs : Record Γ xs} → 

           (l , M) ∈ᵣ rxs → (l , M) ∈ᵣ (l' ▹ M' ⨾ rxs)

get : ∀ {l : Label} {xs : SimpleRow NormalType Δ R[ ★ ]} (rxs : Record Γ xs) → 
      (l , τ) ∈ xs → 
      ∃[ M ] (_∈ᵣ_ {τ = τ} (l , M) rxs)
get ∅ ()
get {τ = τ} {l = l} {xs} (l ▹ M ⨾ rxs) (here refl) = M , Here
get (l ▹ M ⨾ rxs) (there i) with get rxs i 
... | M' , loc = M' , There loc

project :  ∀ {xs ys : SimpleRow NormalType Δ R[ ★ ]} → 
            {oxs : True (normalOrdered? xs)} {oys : True (normalOrdered? ys)} →
            (rys : Record Γ ys) → 
            xs ⊆ ys →
            Record Γ xs 
project {xs = []} rys i = ∅
project {xs = (l , τ) ∷ xs} {ys} {oxs} {oys} rys i with get rys (i (l , τ) (here refl))
... | M , M∈rys = 
  l ▹ M ⨾  project 
             {oxs = fromWitness (normalOrdered-tail (l , τ) xs (toWitness oxs))} 
             {oys} rys 
             (truncate-⊆ i)

--------------------------------------------------------------------------------
-- Reduction of entailments in an empty context

infixr 0 _=⇒_
data _=⇒_ : ∀ {π : NormalPred Δ R[ κ ]} → NormalEnt Γ π → NormalEnt Γ π → Set where

  


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
             (ℓ₁ Π▹ M) —→ (ℓ₂ Π▹ M)

  -- ξ-Π▹₂ : ∀ {l : Label}
  --           (M₁ M₂ : NormalTerm Γ τ) (ℓ : NormalTerm Γ ⌊ lab l ⌋)  → 

  --            M₁ —→ M₂ → 
  --            -----------------------
  --            (ℓ Π▹ M₁) —→ (ℓ Π▹ M₂)

  ξ-Π/₁ : ∀  {l : Label}
            (M₁ M₂ : NormalTerm Γ (Π (l ▹' τ))) (ℓ : NormalTerm Γ ⌊ lab l ⌋)  → 

             M₁ —→ M₂ → 
             -----------------------
             (M₁ Π/ ℓ) —→ (M₂ Π/ ℓ)        

  ξ-Π/₂ : ∀  {l : Label}
            (M : NormalTerm Γ (Π (l ▹' τ))) (ℓ₁ ℓ₂ : NormalTerm Γ ⌊ lab l ⌋)  → 

             ℓ₁ —→ ℓ₂ → 
             -----------------------
             (M Π/ ℓ₁) —→ (M Π/ ℓ₂)        

  ξ-Σ▹₁ : ∀ {l : Label}
            (M : NormalTerm Γ τ) (ℓ₁ ℓ₂ : NormalTerm Γ ⌊ lab l ⌋)  → 

             ℓ₁ —→ ℓ₂ → 
             -----------------------
             (ℓ₁ Σ▹ M) —→ (ℓ₂ Σ▹ M)

  -- ξ-Σ▹₂ : ∀ {l : Label}
  --           (M₁ M₂ : NormalTerm Γ τ) (ℓ : NormalTerm Γ ⌊ lab l ⌋)  → 

  --            M₁ —→ M₂ → 
  --            -----------------------
  --            (ℓ Σ▹ M₁) —→ (ℓ Σ▹ M₂)

  ξ-Σ/₁ : ∀  {l : Label}
            (M₁ M₂ : NormalTerm Γ (Σ (l ▹' τ))) (ℓ : NormalTerm Γ ⌊ lab l ⌋)  → 

             M₁ —→ M₂ → 
             -----------------------
             (M₁ Σ/ ℓ) —→ (M₂ Σ/ ℓ)        

  ξ-Σ/₂ : ∀  {l : Label}
            (M : NormalTerm Γ (Σ (l ▹' τ))) (ℓ₁ ℓ₂ : NormalTerm Γ ⌊ lab l ⌋)  → 

             ℓ₁ —→ ℓ₂ → 
             -----------------------
             (M Σ/ ℓ₁) —→ (M Σ/ ℓ₂)           

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

  ξ-Syn : (ρ : NormalType Δ R[ κ ]) → (φ : NormalType Δ (κ `→ ★)) → (M₁ M₂ : NormalTerm Γ (⇓ (SynT (⇑ ρ) (⇑ φ)))) →
          M₁ —→ M₂ → 
          ------------
          syn ρ φ M₁ —→ syn ρ φ M₂

  ξ-Ana : (ρ : NormalType Δ R[ κ ]) → (φ : NormalType Δ (κ `→ ★)) → 
          (τ : NormalType Δ ★) → 
          (M₁ M₂ : NormalTerm Γ (⇓ (AnaT (⇑ ρ) (⇑ φ) (⇑ τ)))) →
          M₁ —→ M₂ → 
          ------------
          ana ρ φ τ M₁ —→ ana ρ φ τ M₂          

  ----------------------------------------
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

  β-fix : ∀ (M : NormalTerm Γ (τ `→ τ)) → 

          -------------
          fix M —→ M · (fix M)

  β-Π▹ : ∀ {l : Label} → 
           (M : NormalTerm Γ τ) →
           ((# (lab l)) Π▹ M) —→ (⟨ (l ▹ M ⨾ ∅) ⟩)

  β-Σ▹ : ∀ {l : Label} → 
           (M : NormalTerm Γ τ) →
           ((# (lab l)) Σ▹ M) —→ (⟨ l ▹ M ⟩via (here refl))

  β-Π/ : ∀ {l : Label} (M : NormalTerm Γ τ) (ℓ : NormalTerm Γ ⌊ lab l ⌋) → 

        ---------------------------
        (⟨ l ▹ M ⨾ ∅ ⟩ Π/ ℓ) —→ M

  β-prj : ∀ {xs ys : SimpleRow NormalType Δ R[ ★ ]} → 
            {oxs : True (normalOrdered? xs)} {oys : True (normalOrdered? ys)} →
            (rys : Record Γ ys) → 
            (i : xs ⊆ ys) → 
            ---------------------------
            (prj (⟨_⟩ {oxs = oys} rys) (n-≲ {oxs = oxs} i) ) —→ ⟨ project {oxs = oxs} {oys = oys} rys i ⟩ 


  -- β-⊹ : 
      
  --        (⟨ r₁ ⟩ ⊹ ⟨ r₂ ⟩ n) —→ concat(r₁ , r₂ , n)

  -- β-Π/ :  ∀ {l : Label}
  --           (M : NormalTerm Γ τ) (ℓ₁ ℓ₂ : NormalTerm Γ ⌊ lab l ⌋) → 


  --            -----------------------
  --            ((ℓ₁ Π▹ M) Π/ ℓ₂) —→ M

  -- β-Σ/ :  ∀ {l : Label}
  --           (M : NormalTerm Γ τ) (ℓ₁ ℓ₂ : NormalTerm Γ ⌊ lab l ⌋) → 

  --            -----------------------
  --            ((ℓ₁ Σ▹ M) Σ/ ℓ₂) —→ M

  -- β-prj : ∀  
  --           (M : NormalTerm Γ (Π ρ)) (e :  NormalEnt Γ (ρ ≲ ρ)) → 
              
  --            Value M → 
  --            -----------------------
  --            prj M e —→ M

  -- β-inj : ∀ 
  --           (M : NormalTerm Γ (Σ ρ)) (e :  NormalEnt Γ (ρ ≲ ρ)) → 
            
  --            Value M → 
  --            -----------------------
  --            inj M e —→ M


