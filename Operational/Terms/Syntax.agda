{-# OPTIONS --allow-unsolved-metas #-}
module Rome.Operational.Terms.Syntax where

open import Rome.Operational.Prelude
open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

open import Rome.Operational.Types.Syntax
open import Rome.Operational.Types.SynAna
open import Rome.Operational.Types.Substitution
open import Rome.Operational.Types.Renaming

open import Rome.Operational.Types.Equivalence
open import Rome.Operational.Types.Properties.Equivalence

open import Rome.Operational.Types.Semantic.NBE

open import Rome.Operational.Types.Theorems.Soundness
open import Rome.Operational.Types.Theorems.Completeness
open import Rome.Operational.Types.Theorems.Stability

open import Rome.Operational.Containment

--------------------------------------------------------------------------------
-- First define contexts mapping variables to predicates, types, and kinds

data Context : KEnv → Set where
  ∅ : Context ∅
  _,_  : Context Δ → Type Δ ★ → Context Δ
  _,,_ : Context Δ → (κ : Kind) → Context (Δ ,, κ)
  _,,,_ : Context Δ → Pred Type Δ R[ κ ] → Context Δ

private
  variable
    Γ Γ₁ Γ₂ Γ₃ : Context Δ
    τ υ τ₁ τ₂  : Type Δ ★
    l l₁ l₂    : Type Δ L
    ρ ρ₁ ρ₂ ρ₃ : Type Δ R[ κ ]
    π π₁ π₂ π₃ : Pred Type Δ R[ κ ]
    

data PVar : Context Δ → Pred Type Δ κ → Set where
  Z : PVar (Γ ,,, π) π
  S : PVar Γ π₁  → PVar (Γ ,,, π₂) π₁
  T : PVar Γ π → PVar (Γ , τ) π
  K : PVar Γ π → PVar (Γ ,, κ₂) (weakenPredₖ π)

data Var : Context Δ → Type Δ ★ → Set where
  Z : Var (Γ , τ) τ
  S : Var Γ τ₁  → Var (Γ , τ₂) τ₁
  K : Var Γ τ → Var (Γ ,, κ) (weakenₖ τ)
  P : Var Γ τ → Var (Γ ,,, π) τ

--------------------------------------------------------------------------------
-- No variable restriction on contexts

-- Does the context Γ have any term or entailment variables?
NoVar : Context Δ → Set
NoVar ∅ = ⊤
NoVar (Γ ,,, _) = ⊥
NoVar (Γ ,, _) = NoVar Γ
NoVar (Γ , _) = ⊥

-- Contexts s.t. NoVar Γ is true indeed have no term variables,
noVar : NoVar Γ → ∀ {τ}(x : Var Γ τ) → ⊥
noVar p (K x) = noVar p x

-- nor ent variables.
noPVar : NoVar Γ → ∀ {π : Pred Type Δ R[ κ ]}(x : PVar Γ π) → ⊥
noPVar p (K x) = noPVar p x

--------------------------------------------------------------------------------
-- Entailment relation on predicates 

-- private
--   variable 
--       l l₁ l₂ l₃ : Type Δ L 
--       τ τ₁ τ₂ τ₃ : Type Δ κ 
--       υ υ₁ υ₂ υ₃ : Type Δ κ 
      
data Ent (Γ : Context Δ) : Pred Type Δ R[ κ ] → Set where 
  n-var : 
        PVar Γ π → 
        -----------
        Ent Γ π 

  n-≲ :  ∀ {xs ys : SimpleRow Type Δ R[ κ ]} → 

          xs ⊆ ys → 
          --------------------------------------------
          Ent Γ (⦅ xs  ⦆ ≲ ⦅ ys ⦆)

  n-· : ∀ {xs ys zs : SimpleRow Type Δ R[ κ ]} → 
          xs ⊆ zs → 
          ys ⊆ zs → 
          zs ⊆[ xs ⊹ ys ]  → 
          --------------------------------------------
          Ent Γ (⦅ xs ⦆ · ⦅ ys ⦆ ~ ⦅ zs ⦆)
  n-refl : 
          --------------
          Ent Γ (ρ₁ ≲ ρ₁)

  n-trans : 
          Ent Γ (ρ₁ ≲ ρ₂) → Ent Γ (ρ₂ ≲ ρ₃) →
          ---------------------------------------
          Ent Γ (ρ₁ ≲ ρ₃)

  n-·≲L : 
        Ent Γ (ρ₁ · ρ₂ ~ ρ₃) →
        ---------------------
        Ent Γ (ρ₁ ≲ ρ₃)

  n-·≲R : 
        Ent Γ (ρ₁ · ρ₂ ~ ρ₃) →
        ---------------------
        Ent Γ (ρ₂ ≲ ρ₃)

  n-ε-R : 
             
        -------------------------
        Ent Γ (ρ · ⦅ [] ⦆ ~ ρ)

  n-ε-L : 

        -------------------------
        Ent Γ (⦅ [] ⦆ · ρ ~ ρ)  

  n-≲lift : ∀ {ρ₁ ρ₂ : Type Δ R[ κ₁ ]}
               {F : Type Δ (κ₁ `→ κ₂)} →

             Ent Γ (ρ₁ ≲ ρ₂) →
             ---------------------------------
             Ent Γ (F <$> ρ₁ ≲ F <$> ρ₂)


  n-·lift : ∀ {ρ₁ ρ₂ ρ₃ : Type Δ R[ κ₁ ]}
               
               {F : Type Δ (κ₁ `→ κ₂)} →

             Ent Γ (ρ₁ · ρ₂ ~ ρ₃) →
             ---------------------------------
             Ent Γ ((F <$> ρ₁) · (F <$> ρ₂) ~ (F <$> ρ₃))

  convert : π₁ ≡p π₂ → Ent Γ π₁ → 
            -----------------------
            Ent Γ π₂

--------------------------------------------------------------------------------
-- Terms indexed by Type

data Term {Δ} Γ : Type Δ ★ → Set where
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
  
  --------------
  -- System Fω

  Λ : ∀ {τ} →

      Term (Γ ,, κ) τ →
      -----------
      Term Γ (`∀ τ)

  _·[_] : ∀ {τ₂} → 
  
          Term Γ (`∀ τ₂) →
          (τ₁ : Type Δ κ) → 
          ----------------
          Term Γ (τ₂ βₖ[ τ₁ ])

  ------------------
  -- Recursive types

  In : 
         ∀ (F : Type Δ (★ `→ ★)) → 
         Term Γ (F · (μ F)) → 
         -----------------
         Term Γ (μ F)

  Out : 
           ∀ F → 
           Term Γ (μ F) → 
           --------------
           Term Γ (F · (μ F))

  fix : Term Γ (τ `→ τ) → 
        ------------------
        Term Γ τ 

  ------------------
  -- Qualified types

  `ƛ : 

       Term (Γ ,,, π) τ → 
       --------------
       Term Γ (π ⇒ τ)

  _·⟨_⟩ : ∀ {π : Pred Type Δ R[ κ ]} {τ : Type Δ ★} → 
  
        Term Γ (π ⇒ τ) →
        Ent Γ π → 
        ----------------
        Term Γ τ

  ------------
  -- Rω labels

  -- label constants
  # : 

        (ℓ : Type Δ L) → 
        -------------------
        Term Γ ⌊ ℓ ⌋

  -------------
  -- Rω records

  -- Record singleton formation
  _Π▹_ : 
          (M₁ : Term Γ ⌊ l ⌋) (M₂ : Term Γ υ) →
          ----------------------------------------
          Term Γ (Π · (l ▹ υ))

  -- Record singleton elimination
  _Π/_ :
          (M₁ : Term Γ (Π · (l ▹ υ))) (M₂ : Term Γ ⌊ l ⌋) →
          ----------------------------------------
          Term Γ υ

  prj : 
   
       (M : Term Γ (Π · ρ₂)) → Ent Γ (ρ₁ ≲ ρ₂) → 
       -------------------------------------
       Term Γ (Π · ρ₁)
  
  _⊹_ : 

       (M₁ : Term Γ (Π · ρ₁)) → (M₂ : Term Γ (Π · ρ₂)) → Ent Γ (ρ₁ · ρ₂ ~ ρ₃) → 
       ---------------------------------------------------------------------
       Term Γ (Π · ρ₃)

  syn : 
    
        (ρ : Type Δ R[ κ ]) → (φ : Type Δ (κ `→ ★)) → (M : Term Γ (SynT ρ φ)) → 
        ------------------------------------------------------------------
        Term Γ (Π · (φ <$> ρ))

  ana : 
    
        (ρ : Type Δ R[ κ ]) (φ : Type Δ (κ `→ ★)) (τ : Type Δ ★) → (M : Term Γ (AnaT ρ φ τ)) → 
        ------------------------------------------------------------------
        Term Γ ((Σ · (φ <$> ρ)) `→ τ)

  --------------
  -- Rω variants

  -- Record singleton formation
  _Σ▹_ : 
          (M₁ : Term Γ ⌊ l ⌋) (M₂ : Term Γ υ) →
          ----------------------------------------
          Term Γ (Σ · (l ▹ υ))

  -- Record singleton elimination
  _Σ/_ :
          (M₁ : Term Γ (Σ · (l ▹ υ))) (M₂ : Term Γ ⌊ l ⌋) →
          ----------------------------------------
          Term Γ υ

  inj : 
   
       (M : Term Γ (Σ · ρ₁)) → Ent Γ (ρ₁ ≲ ρ₂) → 
       -------------------------------------
       Term Γ (Σ · ρ₂)
       
  _▿_ : 

       (M₁ : Term Γ ((Σ · ρ₁) `→ τ)) → (M₂ : Term Γ ((Σ · ρ₂) `→ τ)) → Ent Γ (ρ₁ · ρ₂ ~ ρ₃) → 
       ---------------------------------------------------------------------
       Term Γ ((Σ · ρ₃) `→ τ)

  comp : 
  
        (M : Term Γ ((ρ₁ · ρ₂ ~ ρ₃) ⇒ τ)) → Ent Γ (ρ₁ ≲ ρ₃) → 
        Term Γ τ

  ----------------------------------------
  -- Conversion
  convert : τ₁ ≡t τ₂ → Term Γ τ₁ → 
            ------------------------
            Term Γ τ₂

--------------------------------------------------------------------------------
-- Conversion lemmas

convVar' : ∀ {Γ} {τ₁ τ₂ : Type Δ ★} → τ₁ ≡ τ₂ → Var Γ τ₁ → Var Γ τ₂
convVar' refl v = v

conv' : ∀ {Γ} {τ₁ τ₂ : Type Δ ★} → τ₁ ≡ τ₂ → Term Γ τ₁ → Term Γ τ₂
conv' refl v = v

convPVar' : ∀ {Γ} {π₁ π₂ : Pred Type Δ R[ κ ]} → π₁ ≡ π₂ → PVar Γ π₁ → PVar Γ π₂
convPVar' refl v = v

convEnt' : ∀ {Γ} {π₁ π₂ : Pred Type Δ R[ κ ]} → π₁ ≡ π₂ → Ent Γ π₁ → Ent Γ π₂
convEnt' refl e = e
