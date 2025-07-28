-- {-# OPTIONS --safe #-}
module Rome.Both.Terms.Normal.Syntax where

open import Rome.Both.Prelude
open import Rome.Both.Kinds.Syntax
open import Rome.Both.Kinds.GVars

open import Rome.Both.Types.Syntax

open import Rome.Both.Types.SynAna

open import Rome.Both.Types.Equivalence.Relation

open import Rome.Both.Types.Normal.Syntax
open import Rome.Both.Types.Normal.Renaming
open import Rome.Both.Types.Normal.Substitution
open import Rome.Both.Types.Normal.Properties.Substitution
open import Rome.Both.Types.Semantic.NBE

open import Rome.Both.Types.Theorems.Soundness
open import Rome.Both.Types.Theorems.Completeness
open import Rome.Both.Types.Theorems.Stability


open import Rome.Both.Containment

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
    l l₁ l₂    : NeutralType Δ L
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
      
data NormalEnt (Γ : NormalContext Δ) : NormalPred Δ R[ κ ] → Set where 
  n-var : 
        NormalPVar Γ π → 
        -----------
        NormalEnt Γ π 

  n-incl :  ∀ {xs ys : SimpleRow NormalType Δ R[ κ ]} → 
           {oxs : True (normalOrdered? xs)} 
           {oys : True (normalOrdered? ys)} → 

          xs ⊆ ys → 
          --------------------------------------------
          NormalEnt Γ ((⦅ xs  ⦆ oxs) ≲ (⦅ ys ⦆ oys))

  n-plus : ∀ {xs ys zs : SimpleRow NormalType Δ R[ κ ]} → 
           {oxs : True (normalOrdered? xs)} 
           {oys : True (normalOrdered? ys)} 
           {ozs : True (normalOrdered? zs)} → 
          xs ⊆ zs → 
          ys ⊆ zs → 
          zs ⊆[ xs ⊹ ys ]  → 
          --------------------------------------------
          NormalEnt Γ ((⦅ xs ⦆ oxs) · (⦅ ys ⦆ oys) ~ (⦅ zs ⦆ ozs))
  n-refl : 
          --------------
          NormalEnt Γ (ρ₁ ≲ ρ₁)

  _n-⨾_ : 
          NormalEnt Γ (ρ₁ ≲ ρ₂) → NormalEnt Γ (ρ₂ ≲ ρ₃) →
          ---------------------------------------
          NormalEnt Γ (ρ₁ ≲ ρ₃)

  n-plusL≲ : 
        NormalEnt Γ (ρ₁ · ρ₂ ~ ρ₃) →
        ---------------------
        NormalEnt Γ (ρ₁ ≲ ρ₃)

  n-plusR≲ : 
        NormalEnt Γ (ρ₁ · ρ₂ ~ ρ₃) →
        ---------------------
        NormalEnt Γ (ρ₂ ≲ ρ₃)

  n-emptyR : 
             
        -------------------------
        NormalEnt Γ (ρ · εNF ~ ρ)

  n-emptyL : 

        -------------------------
        NormalEnt Γ (εNF · ρ ~ ρ)  

  n-map≲ : ∀ {ρ₁ ρ₂ : NormalType Δ R[ κ₁ ]}
               {F : NormalType Δ (κ₁ `→ κ₂)} →

             NormalEnt Γ (ρ₁ ≲ ρ₂) →
             {x y : NormalType Δ R[ κ₂ ]} → 
             x ≡ (F <$>' ρ₁) → 
             y ≡ F <$>' ρ₂ → 
             ---------------------------------
             NormalEnt Γ (x ≲ y)


  n-map· : ∀ {ρ₁ ρ₂ ρ₃ : NormalType Δ R[ κ₁ ]}
               
               {F : NormalType Δ (κ₁ `→ κ₂)} →

             NormalEnt Γ (ρ₁ · ρ₂ ~ ρ₃) →
             {x y z : NormalType Δ R[ κ₂ ]} → 
             x ≡ (F <$>' ρ₁) → 
             y ≡ F <$>' ρ₂ → 
             z ≡ F <$>' ρ₃ → 
             ---------------------------------
             NormalEnt Γ (x · y ~ z)

  n-complR-inert : ∀ {nsr : True (notSimpleRows? ρ₂ ρ₁)} → 
    
             NormalEnt Γ (ρ₁ ≲ ρ₂) → 
             ----------------------
             NormalEnt Γ (ρ₁ · ((ρ₂ ─ ρ₁) {nsr}) ~ ρ₂)

  n-complR :  ∀ {xs ys : SimpleRow NormalType Δ R[ κ ]} → 
                  {oxs : True (normalOrdered? xs)} 
                  {oys : True (normalOrdered? ys)} → 
                  {ozs : True (normalOrdered? (⇓Row (⇑Row ys ─s ⇑Row xs)))} → 
    
             NormalEnt Γ (⦅ xs ⦆ oxs ≲ ⦅ ys ⦆ oys) → 
             ----------------------
             NormalEnt Γ (⦅ xs ⦆ oxs · ⦅ ⇓Row (⇑Row ys ─s ⇑Row xs) ⦆ ozs ~ ⦅ ys ⦆ oys)

  n-complL-inert : ∀ {nsr : True (notSimpleRows? ρ₂ ρ₁)} → 
    
             NormalEnt Γ (ρ₁ ≲ ρ₂) → 
             ----------------------
             NormalEnt Γ (((ρ₂ ─ ρ₁) {nsr}) · ρ₁ ~ ρ₂)

  n-complL :  ∀ {xs ys : SimpleRow NormalType Δ R[ κ ]} → 
                  {oxs : True (normalOrdered? xs)} 
                  {oys : True (normalOrdered? ys)} → 
                  {ozs : True (normalOrdered? (⇓Row (⇑Row ys ─s ⇑Row xs)))} → 
    
             NormalEnt Γ (⦅ xs ⦆ oxs ≲ ⦅ ys ⦆ oys) → 
             ----------------------
             NormalEnt Γ (⦅ ⇓Row (⇑Row ys ─s ⇑Row xs) ⦆ ozs · ⦅ xs ⦆ oxs ~ ⦅ ys ⦆ oys)

data EntValue (Γ : NormalContext Δ) : (π : NormalPred Δ R[ κ ]) → NormalEnt Γ π → Set where 

  n-incl :  ∀ {xs ys : SimpleRow NormalType Δ R[ κ ]} → 
           {oxs : True (normalOrdered? xs)} 
           {oys : True (normalOrdered? ys)} → 

          (i : xs ⊆ ys) → 
          -----------------------
          EntValue Γ (⦅ xs ⦆ oxs ≲ ⦅ ys ⦆ oys) (n-incl i)

  n-plus : ∀ {xs ys zs : SimpleRow NormalType Δ R[ κ ]} → 
           {oxs : True (normalOrdered? xs)} 
           {oys : True (normalOrdered? ys)} 
           {ozs : True (normalOrdered? zs)} → 
          (i₁ : xs ⊆ zs) → 
          (i₂ : ys ⊆ zs) → 
          (i₃ : zs ⊆[ xs ⊹ ys ])  → 
          --------------------------------------------------------------------

          EntValue Γ ((⦅ xs ⦆ oxs) · (⦅ ys ⦆ oys) ~ (⦅ zs ⦆ ozs)) (n-plus i₁ i₂ i₃)
          
          

--------------------------------------------------------------------------------
-- Terms with normal types

data NormalTerm {Δ} Γ : NormalType Δ ★ → Set
data Value {Δ} {Γ : NormalContext Δ} : ∀ {τ : NormalType Δ ★} → NormalTerm Γ τ → Set
data Record {Δ} (Γ : NormalContext Δ) : SimpleRow NormalType Δ R[ ★ ] → Set where
  ∅   : Record Γ []
  _▹_⨾_ : ∀ {xs : SimpleRow NormalType Δ R[ ★ ]} → (l : Label)  → NormalTerm Γ τ → 
            Record Γ xs → Record Γ ((l , τ) ∷ xs)

data RecordValue {Δ} (Γ : NormalContext Δ) : (xs : SimpleRow NormalType Δ R[ ★ ]) → Record Γ xs → Set where
  ∅   : RecordValue Γ [] ∅
  _▹_⨾_ : ∀ {xs : SimpleRow NormalType Δ R[ ★ ]} {r : Record Γ xs} → 
          (l : Label)  → {M : NormalTerm Γ τ} → Value M → 
          RecordValue Γ xs r → RecordValue Γ ((l , τ) ∷ xs) (l ▹ M ⨾ r) 


data NormalTerm {Δ} Γ where
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
  _Π▹ne_ : 
          (M₁ : NormalTerm Γ ⌊ ne l ⌋) (M₂ : NormalTerm Γ υ) →
          ----------------------------------------
          NormalTerm Γ (Π (l ▹ₙ υ))

  _Π▹_ : ∀ {l : Label}
          (M₁ : NormalTerm Γ ⌊ lab l ⌋) (M₂ : NormalTerm Γ υ) →
          ----------------------------------------
          NormalTerm Γ (Π (l ▹' υ))

  -- Record singleton elimination
  _Π/ne_ :
          (M₁ : NormalTerm Γ (Π (l ▹ₙ υ))) (M₂ : NormalTerm Γ ⌊ ne l ⌋) →
          ----------------------------------------
          NormalTerm Γ υ

  _Π/_ : ∀ {l : Label} → 
          (M₁ : NormalTerm Γ (Π (l ▹' υ))) (M₂ : NormalTerm Γ ⌊ lab l ⌋) →
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
    
        (ρ : NormalType Δ R[ κ ]) → (φ : NormalType Δ (κ `→ ★)) → (M : NormalTerm Γ (SynT' ρ φ)) → 
        ------------------------------------------------------------------
        NormalTerm Γ (Π (φ <$>' ρ))

  ana : 
    
        (ρ : NormalType Δ R[ κ ]) 
        (φ : NormalType Δ (κ `→ ★)) 
        (τ : NormalType Δ ★)
        {τ₁ τ₂ : _}
        (eq₁ : (⇓ (AnaT (⇑ ρ) (⇑ φ) (⇑ τ))) ≡ τ₁) → 
        (eq₂ : (⇓ (Σ · (⇑ φ <$> ⇑ ρ))) ≡ τ₂) → 
        (M : NormalTerm Γ τ₁) → 
        
        ------------------------------------------------------------------
        NormalTerm Γ (τ₂ `→ τ)

  --------------
  -- Rω variants

  -- Variant singleton formation
  _Σ▹ne_ : 
          (M₁ : NormalTerm Γ ⌊ ne l ⌋) (M₂ : NormalTerm Γ υ) →
          ----------------------------------------
          NormalTerm Γ (Σ (l ▹ₙ υ))

  _Σ▹_ : ∀ {l : Label}
          (M₁ : NormalTerm Γ ⌊ lab l ⌋) (M₂ : NormalTerm Γ υ) →
          ----------------------------------------
          NormalTerm Γ (Σ (⦅ [ (l , υ) ] ⦆ tt))

  -- Variant singleton elimination
  _Σ/ne_ :
          (M₁ : NormalTerm Γ (Σ (l ▹ₙ υ))) (M₂ : NormalTerm Γ ⌊ ne l ⌋) →
          ----------------------------------------
          NormalTerm Γ υ

  _Σ/_ : ∀ {l : Label} → 
          (M₁ : NormalTerm Γ (Σ (⦅ [ (l , υ) ] ⦆ tt))) (M₂ : NormalTerm Γ ⌊ lab l ⌋) →
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

  ----------------------------------------
  -- Values

  ⟨_⟩ : ∀ {xs : SimpleRow NormalType Δ R[ ★ ]} {oxs : True (normalOrdered? xs)} → 
          Record Γ xs → 
          ----------------------
          NormalTerm Γ (Π (⦅ xs ⦆ oxs))

  ⟨_▹_⟩via_ : ∀ {xs : SimpleRow NormalType Δ R[ ★ ]} {oxs : True (normalOrdered? xs)} → 
        (l : Label) → (M : NormalTerm Γ τ) → (l , τ) ∈ xs → 
        -------------------------------------------
        NormalTerm Γ (Σ (⦅ xs ⦆ oxs)) 

--------------------------------------------------------------------------------
-- Values

data Value {Δ} {Γ} where
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

  V-Π : {xs : SimpleRow NormalType Δ R[ ★ ]} {oxs : True (normalOrdered? xs)} → 
          (r : Record Γ xs) → 
          RecordValue Γ xs r → 
          Value (⟨_⟩ {xs = xs} {oxs} r)

  V-Σ : ∀  {xs : SimpleRow NormalType Δ R[ ★ ]} {oxs : True (normalOrdered? xs)} → 
        (l : Label) → {M : NormalTerm Γ τ} → (V : Value M) → (i : (l , τ) ∈ xs) → 
        -------------------------------------------
        Value (⟨_▹_⟩via_ {oxs = oxs} l M i)       

  V-ana : (ρ : NormalType Δ R[ κ ]) 
          (φ : NormalType Δ (κ `→ ★)) 
          (τ : NormalType Δ ★) 
          {τ₁ τ₂ : _}
          (eq₁ : (⇓ (AnaT (⇑ ρ) (⇑ φ) (⇑ τ))) ≡ τ₁) → 
          (eq₂ : (⇓ (Σ · (⇑ φ <$> ⇑ ρ))) ≡ τ₂) → 
          (M : NormalTerm Γ τ₁) → 
        
          Value M → 
          ------------------------------------
          Value (ana ρ φ τ eq₁ eq₂ M)

  V-▿  : 
           {e : NormalEnt Γ (ρ₁ · ρ₂ ~ ρ₃)} 
           (M : NormalTerm Γ (Σ ρ₁ `→ τ)) (N : NormalTerm Γ (Σ ρ₂ `→ τ)) → 

            Value M → Value N → 
            ---------------------
            Value ((M ▿ N) e)


  -- V-Π   : ∀ {l : Label} (ℓ : NormalTerm Γ ⌊ lab l ⌋) 
  --           (M : NormalTerm Γ υ) → 

  --           Value M → 
  --           ---------------------
  --           Value (ℓ Π▹ M)

  -- V-⊹  : ∀ 
  --          {e : NormalEnt Γ (ρ₁ · ρ₂ ~ ρ₃)}  (M : NormalTerm Γ (Π ρ₁)) (N : NormalTerm Γ (Π ρ₂)) → 

  --           Value M → Value N → 
  --           ---------------------
  --           Value ((M ⊹ N) e)


  -- V-Σ   : ∀ {l : Label}
  --           (ℓ : NormalTerm Γ ⌊ lab l ⌋) → (M : NormalTerm Γ τ) → 

  --           Value M → 
  --           ---------------------
  --           Value (ℓ Σ▹ M)

  -- V-Unit : ∀ (M : NormalTerm Γ (Π εNF)) → 

  --          -------
  --          Value M 

  -- V-syn : ∀ (ρ : NormalType Δ R[ κ ]) → (φ : NormalType Δ (κ `→ ★)) (M : NormalTerm Γ (⇓ (SynT (⇑ ρ) (⇑ φ)))) → 

  --         -----------------
  --         Value (syn ρ φ M)

  -- V-ana : ∀ (ρ : NormalType Δ R[ κ ]) (φ : NormalType Δ (κ `→ ★)) (τ : NormalType Δ ★) (M : NormalTerm Γ (⇓ (AnaT (⇑ ρ) (⇑ φ) (⇑ τ)))) → 

  --         -----------------
  --         Value (ana ρ φ τ M)

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


-- ll : NormalType Δ L 
-- ll = ΠL εNF

-- -- Unit term
-- uu : NormalTerm Γ UnitNF
-- uu = prj (# ll Π▹ (# ll)) (n-incl λ { x () }) -- (♯l Π▹ ♯l) (n-incl λ { x () })

-- -- shit : NormalTerm Γ UnitNF 
-- -- shit = (♯l Π▹ uu) Π/ ♯l

-- -- shit₂ : NormalTerm Γ ((Π ⦅ [ UnitNF ] ⦆) `→ UnitNF) 
-- -- shit₂ = `λ ((` Z) Π/ ♯l)

-- -- withLabelVar : NormalTerm Γ 
-- --   (`∀ {κ = L} 
-- --     (`∀ {κ = ★} 
-- --       (`∀ {κ = R[ ★ ]} ((⦅ [ (ne (` (S Z))) ] ⦆ ≲ ne (` Z)) ⇒ (⌊ (ne (` (S (S Z)))) ⌋ `→ (Π (ne (` Z))) `→ (ne (` (S Z)))))))) 
-- -- withLabelVar = Λ (Λ (Λ (`ƛ (`λ (`λ ((prj (` Z) (n-var (T (T Z)))) Π/ ♯l)))))) 

-- -- hmm : NormalTerm Γ 
-- --   (`∀  
-- --     (`∀  
-- --       (((lab "a" ▹ UnitNF) · (lab "b" ▹ UnitNF) ~ ne (` Z)) ⇒ 
-- --         (((ne (` Z)) · ((lab "c" ▹ UnitNF)) ~ (ne (` (S Z)))) ⇒ 
-- --         Π (ne (` (S Z)))))))
-- -- hmm = Λ (Λ (`ƛ (`ƛ (((((# (lab "a") Π▹ uu) ⊹ (# (lab "b") Π▹ uu)) (n-var (S Z))) ⊹ (# (lab "c") Π▹ uu)) (n-var Z)))))

-- -- -- The small problem here is that there do not exist any types to give...
-- -- -- I can't actually express Π ("a" ▹ ⊤ , "b" ▹ ⊤ , "c" ▹ ⊤).
-- -- -- I am in a bit of trouble if I need to extend to the simple row theory.
-- -- hmm₂ : NormalTerm Γ (Π {!   !})
-- -- hmm₂ = ((((hmm ·[ {! ε !} ]) ·[ {!   !} ]) ·⟨ {!   !} ⟩) ·⟨ {!   !} ⟩)


-- -- shit : NormalTerm ∅ (((lab "a" ▹ UnitNF) · (lab "b" ▹ UnitNF) ~ ρ₃) ⇒ Π ρ₃) 
-- -- shit = `ƛ ((((# (lab "a")) Π▹ uu) ⊹ ((# (lab "b")) Π▹ uu)) (n-var Z))
