{-# OPTIONS --allow-unsolved-metas #-}
module Rome.Operational.Terms.Normal.Syntax where

open import Rome.Operational.Prelude
open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

open import Rome.Operational.Types.Syntax

open import Rome.Operational.Types.SynAna

open import Rome.Operational.Types.Equivalence

open import Rome.Operational.Types.Normal.Syntax
open import Rome.Operational.Types.Normal.Renaming
open import Rome.Operational.Types.Normal.Substitution
open import Rome.Operational.Types.Normal.Properties.Substitution
open import Rome.Operational.Types.Semantic.NBE

open import Rome.Operational.Types.Theorems.Soundness
open import Rome.Operational.Types.Theorems.Completeness
open import Rome.Operational.Types.Theorems.Stability


open import Rome.Operational.Containment

--------------------------------------------------------------------------------
-- First define contexts mapping variables to predicates, types, and kinds

data NormalContext : KEnv → Set where
  ∅ : NormalContext ∅
  _,_  : NormalContext Δ → NormalType Δ ★ → NormalContext Δ
  _,,_ : NormalContext Δ → (κ : Kind) → NormalContext (Δ ,, κ)
  _,,,_ : NormalContext Δ → NormalPred Δ R[ κ ] → NormalContext Δ

private
  variable
    Γ Γ₁ Γ₂ Γ₃ : NormalContext Δ
    τ υ τ₁ τ₂  : NormalType Δ ★
    l l₁ l₂    : NormalType Δ L
    ρ ρ₁ ρ₂ ρ₃ : NormalType Δ R[ κ ]
    π π₁ π₂ π₃ : NormalPred Δ R[ κ ]
    

data NormalPVar : NormalContext Δ → NormalPred Δ κ → Set where
  Z : NormalPVar (Γ ,,, π) π
  S : NormalPVar Γ π₁  → NormalPVar (Γ ,,, π₂) π₁
  T : NormalPVar Γ π → NormalPVar (Γ , τ) π
  K : NormalPVar Γ π → NormalPVar (Γ ,, κ₂) (weakenPredₖNF π)

data NormalVar : NormalContext Δ → NormalType Δ ★ → Set where
  Z : NormalVar (Γ , τ) τ
  S : NormalVar Γ τ₁  → NormalVar (Γ , τ₂) τ₁
  K : NormalVar Γ τ → NormalVar (Γ ,, κ) (weakenₖNF τ)
  P : NormalVar Γ τ → NormalVar (Γ ,,, π) τ

--------------------------------------------------------------------------------
-- No variable restriction on contexts

-- Does the context Γ have any term or entailment variables?
NoVar : NormalContext Δ → Set
NoVar ∅ = ⊤
NoVar (Γ ,,, _) = ⊥
NoVar (Γ ,, _) = NoVar Γ
NoVar (Γ , _) = ⊥

-- NormalContexts s.t. NoVar Γ is true indeed have no term variables,
noVar : NoVar Γ → ∀ {τ}(x : NormalVar Γ τ) → ⊥
noVar p (K x) = noVar p x

-- nor ent variables.
noPVar : NoVar Γ → ∀ {π : NormalPred Δ R[ κ ]}(x : NormalPVar Γ π) → ⊥
noPVar p (K x) = noPVar p x

--------------------------------------------------------------------------------
-- Entailment relation on predicates 

-- private
--   variable 
--       l l₁ l₂ l₃ : NormalType Δ L 
--       τ τ₁ τ₂ τ₃ : NormalType Δ κ 
--       υ υ₁ υ₂ υ₃ : NormalType Δ κ 
      
data NormalEnt (Γ : NormalContext Δ) : NormalPred Δ R[ κ ] → Set where 
  n-var : 
        NormalPVar Γ π → 
        -----------
        NormalEnt Γ π 

  n-≲ :  ∀ {xs ys : SimpleRow NormalType Δ R[ κ ]} → 

          xs ⊆ ys → 
          --------------------------------------------
          NormalEnt Γ (⦅ xs  ⦆ ≲ ⦅ ys ⦆)

  n-· : ∀ {xs ys zs : SimpleRow NormalType Δ R[ κ ]} → 
          xs ⊆ zs → 
          ys ⊆ zs → 
          zs ⊆[ xs ⊹ ys ]  → 
          --------------------------------------------
          NormalEnt Γ (⦅ xs ⦆ · ⦅ ys ⦆ ~ ⦅ zs ⦆)
  n-refl : 
          --------------
          NormalEnt Γ (ρ₁ ≲ ρ₁)

  n-trans : 
          NormalEnt Γ (ρ₁ ≲ ρ₂) → NormalEnt Γ (ρ₂ ≲ ρ₃) →
          ---------------------------------------
          NormalEnt Γ (ρ₁ ≲ ρ₃)

  n-·≲L : 
        NormalEnt Γ (ρ₁ · ρ₂ ~ ρ₃) →
        ---------------------
        NormalEnt Γ (ρ₁ ≲ ρ₃)

  n-·≲R : 
        NormalEnt Γ (ρ₁ · ρ₂ ~ ρ₃) →
        ---------------------
        NormalEnt Γ (ρ₂ ≲ ρ₃)

  n-ε-R : 
             
        -------------------------
        NormalEnt Γ (ρ · ⦅ [] ⦆ ~ ρ)

  n-ε-L : 

        -------------------------
        NormalEnt Γ (⦅ [] ⦆ · ρ ~ ρ)  

  n-≲lift : ∀ {ρ₁ ρ₂ : NormalType Δ R[ κ₁ ]}
               {F : NormalType Δ (κ₁ `→ κ₂)} →

             NormalEnt Γ (ρ₁ ≲ ρ₂) →
             {x y : NormalType Δ R[ κ₂ ]} → 
             x ≡ (F <$>' ρ₁) → 
             y ≡ F <$>' ρ₂ → 
             ---------------------------------
             NormalEnt Γ (x ≲ y)


  n-·lift : ∀ {ρ₁ ρ₂ ρ₃ : NormalType Δ R[ κ₁ ]}
               
               {F : NormalType Δ (κ₁ `→ κ₂)} →

             NormalEnt Γ (ρ₁ · ρ₂ ~ ρ₃) →
             {x y z : NormalType Δ R[ κ₂ ]} → 
             x ≡ (F <$>' ρ₁) → 
             y ≡ F <$>' ρ₂ → 
             z ≡ F <$>' ρ₃ → 
             ---------------------------------
             NormalEnt Γ (x · y ~ z)

--------------------------------------------------------------------------------
-- Terms with normal types


data NormalTerm {Δ} Γ : NormalType Δ ★ → Set where
  ` : NormalVar Γ τ → 
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
  
  --------------
  -- System Fω

  Λ : ∀ {τ} →

      NormalTerm (Γ ,, κ) τ →
      -----------
      NormalTerm Γ (`∀ τ)

  _·[_] : ∀ {τ₂} → 
  
          NormalTerm Γ (`∀ τ₂) →
          (τ₁ : NormalType Δ κ) → 
          ----------------
          NormalTerm Γ (τ₂ βₖNF[ τ₁ ])

  ------------------
  -- Recursive types

  In : 
         ∀ (F : NormalType Δ (★ `→ ★)) → 
         NormalTerm Γ (F ·' (μ F)) → 
         -----------------
         NormalTerm Γ (μ F)

  Out : 
           ∀ F → 
           NormalTerm Γ (μ F) → 
           --------------
           NormalTerm Γ (F ·' (μ F))

  fix : NormalTerm Γ (τ `→ τ) → 
        ------------------
        NormalTerm Γ τ 

  ------------------
  -- Qualified types

  `ƛ : 

       NormalTerm (Γ ,,, π) τ → 
       --------------
       NormalTerm Γ (π ⇒ τ)

  _·⟨_⟩ : ∀ {π : NormalPred Δ R[ κ ]} {τ : NormalType Δ ★} → 
  
        NormalTerm Γ (π ⇒ τ) →
        NormalEnt Γ π → 
        ----------------
        NormalTerm Γ τ

  ------------
  -- Rω labels

  -- label constants
  # : 

        ∀ (ℓ : NormalType Δ L) → 
        -------------------
        NormalTerm Γ ⌊ ℓ ⌋

  -------------
  -- Rω records

  -- Record singleton formation
  _Π▹_ : 
          (M₁ : NormalTerm Γ ⌊ l ⌋) (M₂ : NormalTerm Γ υ) →
          ----------------------------------------
          NormalTerm Γ (Π (l ▹' υ))

  -- Record singleton elimination
  _Π/_ :
          (M₁ : NormalTerm Γ (Π (l ▹' υ))) (M₂ : NormalTerm Γ ⌊ l ⌋) →
          ----------------------------------------
          NormalTerm Γ υ

  prj : 
   
       (M : NormalTerm Γ (Π ρ₂)) → NormalEnt Γ (ρ₁ ≲ ρ₂) → 
       -------------------------------------
       NormalTerm Γ (Π ρ₁)
  
  _⊹_ : 

       (M₁ : NormalTerm Γ (Π ρ₁)) → (M₂ : NormalTerm Γ (Π ρ₂)) → NormalEnt Γ (ρ₁ · ρ₂ ~ ρ₃) → 
       ---------------------------------------------------------------------
       NormalTerm Γ (Π ρ₃)

  syn : 
    
        (ρ : NormalType Δ R[ κ ]) → (φ : NormalType Δ (κ `→ ★)) → (M : NormalTerm Γ (⇓ (SynT (⇑ ρ) (⇑ φ)))) → 
        ------------------------------------------------------------------
        NormalTerm Γ (⇓ (Π · (⇑ φ <$> ⇑ ρ)))

  ana : 
    
        (ρ : NormalType Δ R[ κ ]) (φ : NormalType Δ (κ `→ ★)) (τ : NormalType Δ ★) → (M : NormalTerm Γ (⇓ (AnaT (⇑ ρ) (⇑ φ) (⇑ τ)))) → 
        ------------------------------------------------------------------
        NormalTerm Γ ((⇓ (Σ · (⇑ φ <$> ⇑ ρ))) `→ τ)

  --------------
  -- Rω variants

  -- Record singleton formation
  _Σ▹_ : 
          (M₁ : NormalTerm Γ ⌊ l ⌋) (M₂ : NormalTerm Γ υ) →
          ----------------------------------------
          NormalTerm Γ (Σ (l ▹' υ))

  -- Record singleton elimination
  _Σ/_ :
          (M₁ : NormalTerm Γ (Σ (l ▹' υ))) (M₂ : NormalTerm Γ ⌊ l ⌋) →
          ----------------------------------------
          NormalTerm Γ υ

  inj : 
   
       (M : NormalTerm Γ (Σ ρ₁)) → NormalEnt Γ (ρ₁ ≲ ρ₂) → 
       -------------------------------------
       NormalTerm Γ (Σ ρ₂)
       
  _▿_ : 

       (M₁ : NormalTerm Γ (Σ ρ₁ `→ τ)) → (M₂ : NormalTerm Γ (Σ ρ₂ `→ τ)) → NormalEnt Γ (ρ₁ · ρ₂ ~ ρ₃) → 
       ---------------------------------------------------------------------
       NormalTerm Γ (Σ ρ₃ `→ τ)

  comp : 
  
        (M : NormalTerm Γ ((ρ₁ · ρ₂ ~ ρ₃) ⇒ τ)) → NormalEnt Γ (ρ₁ ≲ ρ₃) → 
        NormalTerm Γ τ

--------------------------------------------------------------------------------
-- Conversion helpers.

convVar : ∀ {Γ} {τ₁ τ₂ : NormalType Δ ★} → τ₁ ≡ τ₂ → NormalVar Γ τ₁ → NormalVar Γ τ₂
convVar refl v = v

convVar-≡t : ∀ {Γ} {τ₁ τ₂ : Type Δ ★} → τ₁ ≡t τ₂ → NormalVar Γ (⇓ τ₁) → NormalVar Γ (⇓ τ₂)
convVar-≡t eq x = convVar (completeness eq) x 

convPVar : ∀ {Γ} {π₁ π₂ : NormalPred Δ R[ κ ]} → π₁ ≡ π₂ → NormalPVar Γ π₁ → NormalPVar Γ π₂
convPVar refl v = v

conv : ∀ {Γ} {τ₁ τ₂ : NormalType Δ ★} → τ₁ ≡ τ₂ → NormalTerm Γ τ₁ → NormalTerm Γ τ₂
conv refl M = M

convEnt : ∀ {Γ} {π₁ π₂ : NormalPred Δ R[ κ ]} → π₁ ≡ π₂ → NormalEnt Γ π₁ → NormalEnt Γ π₂
convEnt refl e = e

conv-≡t : ∀ {Γ} {τ₁ τ₂ : Type Δ ★} → τ₁ ≡t τ₂ → NormalTerm Γ (⇓ τ₁) → NormalTerm Γ (⇓ τ₂)
conv-≡t eq = conv (completeness eq)

--------------------------------------------------------------------------------
-- Admissable constants


ll : NormalType Δ L 
ll = ΠL εNF

-- Unit term
uu : NormalTerm Γ UnitNF
uu = prj (# ll Π▹ (# ll)) (n-≲ λ { x () }) -- (♯l Π▹ ♯l) (n-≲ λ { x () })

-- shit : NormalTerm Γ UnitNF 
-- shit = (♯l Π▹ uu) Π/ ♯l

-- shit₂ : NormalTerm Γ ((Π ⦅ [ UnitNF ] ⦆) `→ UnitNF) 
-- shit₂ = `λ ((` Z) Π/ ♯l)

-- withLabelVar : NormalTerm Γ 
--   (`∀ {κ = L} 
--     (`∀ {κ = ★} 
--       (`∀ {κ = R[ ★ ]} ((⦅ [ (ne (` (S Z))) ] ⦆ ≲ ne (` Z)) ⇒ (⌊ (ne (` (S (S Z)))) ⌋ `→ (Π (ne (` Z))) `→ (ne (` (S Z)))))))) 
-- withLabelVar = Λ (Λ (Λ (`ƛ (`λ (`λ ((prj (` Z) (n-var (T (T Z)))) Π/ ♯l)))))) 

-- hmm : NormalTerm Γ 
--   (`∀  
--     (`∀  
--       (((lab "a" ▹ UnitNF) · (lab "b" ▹ UnitNF) ~ ne (` Z)) ⇒ 
--         (((ne (` Z)) · ((lab "c" ▹ UnitNF)) ~ (ne (` (S Z)))) ⇒ 
--         Π (ne (` (S Z)))))))
-- hmm = Λ (Λ (`ƛ (`ƛ (((((# (lab "a") Π▹ uu) ⊹ (# (lab "b") Π▹ uu)) (n-var (S Z))) ⊹ (# (lab "c") Π▹ uu)) (n-var Z)))))

-- -- The small problem here is that there do not exist any types to give...
-- -- I can't actually express Π ("a" ▹ ⊤ , "b" ▹ ⊤ , "c" ▹ ⊤).
-- -- I am in a bit of trouble if I need to extend to the simple row theory.
-- hmm₂ : NormalTerm Γ (Π {!   !})
-- hmm₂ = ((((hmm ·[ {! ε !} ]) ·[ {!   !} ]) ·⟨ {!   !} ⟩) ·⟨ {!   !} ⟩)


-- shit : NormalTerm ∅ (((lab "a" ▹ UnitNF) · (lab "b" ▹ UnitNF) ~ ρ₃) ⇒ Π ρ₃) 
-- shit = `ƛ ((((# (lab "a")) Π▹ uu) ⊹ ((# (lab "b")) Π▹ uu)) (n-var Z))
