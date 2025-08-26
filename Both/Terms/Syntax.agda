-- {-# OPTIONS --safe #-}
module Rome.Both.Terms.Syntax where

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
-- open import Rome.Both.Types.Theorems.Stability


open import Rome.Both.Containment

--------------------------------------------------------------------------------
-- First define environments mapping variables to predicates and types

data Env : KEnv ιΔ → Level → Set where
  ∅ : Env Δ lzero
  _,_  : Env Δ ιΓ → NormalType Δ (★ {ι}) → Env Δ (ιΓ ⊔ ι)
  _,,_ : Env Δ ιΓ → (κ : Kind ικ) → Env (Δ ,, κ) (ιΓ ⊔ ικ)
  _,,,_ : ∀ {κ : Kind ικ} → Env Δ ιΓ → NormalPred Δ R[ κ ] → Env Δ (ιΓ ⊔ lsuc ικ)

private
  variable
    Γ Γ₁ Γ₂ Γ₃ : Env Δ ιΓ
    τ υ τ₁ τ₂  : NormalType Δ ★
    l l₁ l₂    : NeutralType Δ L
    ρ ρ₁ ρ₂ ρ₃ : NormalType Δ R[ κ ]
    π π₁ π₂ π₃ : NormalPred Δ R[ κ ]
    

data PVar : Env Δ ιΓ → NormalPred Δ κ → Set where
  Z : PVar (Γ ,,, π) π
  S : PVar Γ π₁  → PVar (Γ ,,, π₂) π₁
  T : PVar Γ π → PVar (Γ , τ) π 
  K : PVar Γ π → PVar (Γ ,, κ₂) (weakenPredₖNF π) 

data Var : Env Δ ιΓ → NormalType Δ (★ {ι}) → Set where
  Z : Var (Γ , τ) τ
  S : Var Γ τ₁  → Var (Γ , τ₂) τ₁
  K : Var Γ τ → Var (Γ ,, κ) (weakenₖNF τ) 
  P : Var Γ τ → Var (Γ ,,, π) τ 

--------------------------------------------------------------------------------
-- Entailment relation on predicates 
      
data Ent (Δ : KEnv ιΔ) (Γ : Env Δ ιΓ)  : NormalPred Δ R[ κ ] → Set where 
  n-var : 
        PVar Γ π → 
        -----------
        Ent Δ Γ π 

  n-incl :  ∀ {xs ys : SimpleRow (NormalType Δ κ)} → 
           {oxs : True (normalOrdered? xs)} 
           {oys : True (normalOrdered? ys)} → 

          xs ⊆ ys → 
          --------------------------------------------
          Ent Δ Γ ((⦅ xs  ⦆ oxs) ≲ (⦅ ys ⦆ oys))

  n-plus : ∀ {xs ys zs : SimpleRow (NormalType Δ κ)} → 
           {oxs : True (normalOrdered? xs)} 
           {oys : True (normalOrdered? ys)} 
           {ozs : True (normalOrdered? zs)} → 
          xs ⊆ zs → 
          ys ⊆ zs → 
          zs ⊆[ xs ⊹ ys ]  → 
          --------------------------------------------
          Ent Δ Γ ((⦅ xs ⦆ oxs) · (⦅ ys ⦆ oys) ~ (⦅ zs ⦆ ozs))
  n-refl : 
          --------------
          Ent Δ Γ (ρ₁ ≲ ρ₁)

  _n-⨾_ : 
          Ent Δ Γ (ρ₁ ≲ ρ₂) → Ent Δ Γ (ρ₂ ≲ ρ₃) →
          ---------------------------------------
          Ent Δ Γ (ρ₁ ≲ ρ₃)

  n-plusL≲ : 
        Ent Δ Γ (ρ₁ · ρ₂ ~ ρ₃) →
        ---------------------
        Ent Δ Γ (ρ₁ ≲ ρ₃)

  n-plusR≲ : 
        Ent Δ Γ (ρ₁ · ρ₂ ~ ρ₃) →
        ---------------------
        Ent Δ Γ (ρ₂ ≲ ρ₃)

  n-emptyR : 
             
        -------------------------
        Ent Δ Γ (ρ · εNF ~ ρ)

  n-emptyL : 

        -------------------------
        Ent Δ Γ (εNF · ρ ~ ρ)  

  n-map≲ : ∀ {ρ₁ ρ₂ : NormalType Δ R[ κ₁ ]}
               {F : NormalType Δ (κ₁ `→ κ₂)} →

             Ent Δ Γ (ρ₁ ≲ ρ₂) →
             {x y : NormalType Δ R[ κ₂ ]} → 
             x ≡ (F <$>' ρ₁) → 
             y ≡ F <$>' ρ₂ → 
             ---------------------------------
             Ent Δ Γ (x ≲ y)


  n-map· : ∀ {ρ₁ ρ₂ ρ₃ : NormalType Δ R[ κ₁ ]}
               
               {F : NormalType Δ (κ₁ `→ κ₂)} →

             Ent Δ Γ (ρ₁ · ρ₂ ~ ρ₃) →
             {x y z : NormalType Δ R[ κ₂ ]} → 
             x ≡ (F <$>' ρ₁) → 
             y ≡ F <$>' ρ₂ → 
             z ≡ F <$>' ρ₃ → 
             ---------------------------------
             Ent Δ Γ (x · y ~ z)

  n-complR-inert : ∀ {nsr : True (notSimpleRows? ρ₂ ρ₁)} → 
    
             Ent Δ Γ (ρ₁ ≲ ρ₂) → 
             ----------------------
             Ent Δ Γ (ρ₁ · ((ρ₂ ∖ ρ₁) {nsr}) ~ ρ₂)

  n-complR :  ∀ {xs ys : SimpleRow (NormalType Δ κ)} → 
                  {oxs : True (normalOrdered? xs)} 
                  {oys : True (normalOrdered? ys)} → 
                  {ozs : True (normalOrdered? (⇓Row (⇑Row ys ∖s ⇑Row xs)))} → 
    
             Ent Δ Γ (⦅ xs ⦆ oxs ≲ ⦅ ys ⦆ oys) → 
             ----------------------
             Ent Δ Γ (⦅ xs ⦆ oxs · ⦅ ⇓Row (⇑Row ys ∖s ⇑Row xs) ⦆ ozs ~ ⦅ ys ⦆ oys)

  n-complL-inert : ∀ {nsr : True (notSimpleRows? ρ₂ ρ₁)} → 
    
             Ent Δ Γ (ρ₁ ≲ ρ₂) → 
             ----------------------
             Ent Δ Γ (((ρ₂ ∖ ρ₁) {nsr}) · ρ₁ ~ ρ₂)

  n-complL :  ∀ {xs ys : SimpleRow (NormalType Δ κ)} → 
                  {oxs : True (normalOrdered? xs)} 
                  {oys : True (normalOrdered? ys)} → 
                  {ozs : True (normalOrdered? (⇓Row (⇑Row ys ∖s ⇑Row xs)))} → 
    
             Ent Δ Γ (⦅ xs ⦆ oxs ≲ ⦅ ys ⦆ oys) → 
             ----------------------
             Ent Δ Γ (⦅ ⇓Row (⇑Row ys ∖s ⇑Row xs) ⦆ ozs · ⦅ xs ⦆ oxs ~ ⦅ ys ⦆ oys)

data EntValue  (Δ : KEnv ιΔ) (Γ : Env Δ ιΓ) : (π : NormalPred Δ R[ κ ]) → Ent Δ Γ π → Set where 

  n-incl :  ∀ {xs ys : SimpleRow (NormalType Δ κ)} → 
           {oxs : True (normalOrdered? xs)} 
           {oys : True (normalOrdered? ys)} → 

          (i : xs ⊆ ys) → 
          -----------------------
          EntValue Δ Γ (⦅ xs ⦆ oxs ≲ ⦅ ys ⦆ oys) (n-incl i)

  n-plus : ∀ {xs ys zs : SimpleRow (NormalType Δ κ)} → 
           {oxs : True (normalOrdered? xs)} 
           {oys : True (normalOrdered? ys)} 
           {ozs : True (normalOrdered? zs)} → 
          (i₁ : xs ⊆ zs) → 
          (i₂ : ys ⊆ zs) → 
          (i₃ : zs ⊆[ xs ⊹ ys ])  → 
          --------------------------------------------------------------------

          EntValue Δ Γ ((⦅ xs ⦆ oxs) · (⦅ ys ⦆ oys) ~ (⦅ zs ⦆ ozs)) (n-plus i₁ i₂ i₃)
          
          

--------------------------------------------------------------------------------
-- Terms with normal types

data Term (Δ : KEnv ιΔ) (Γ : Env Δ ιΓ) : NormalType Δ (★ {ι}) → Set
data Value {Δ : KEnv ιΔ}  {Γ : Env Δ ιΓ} : ∀ {τ : NormalType Δ (★ {ι})} → Term Δ Γ τ → Set
data Record {Δ : KEnv ιΔ} (Γ : Env Δ ιΓ) : SimpleRow (NormalType Δ (★ {ι})) → Set where
  ∅   : Record Γ {ι = ι} []
  _▹_⨾_ : ∀ {xs : SimpleRow (NormalType Δ ★)} → (l : Label)  → Term Δ Γ τ → 
            Record Γ xs → Record Γ ((l , τ) ∷ xs)

data RecordValue {Δ : KEnv ιΔ} (Γ : Env Δ ιΓ) : (xs : SimpleRow (NormalType Δ (★ {ι}))) → Record Γ xs → Set where
  ∅   : RecordValue Γ {ι = ι} [] ∅
  _▹_⨾_ : ∀ {xs : SimpleRow (NormalType Δ ★)} {r : Record Γ xs} → 
          (l : Label)  → {M : Term Δ Γ τ} → Value M → 
          RecordValue Γ xs r → RecordValue Γ ((l , τ) ∷ xs) (l ▹ M ⨾ r) 


data Term Δ Γ   where
  ` : Var Γ τ → 
      --------
      Term Δ Γ τ

  `λ : 

       Term Δ (Γ , τ₁) {ι = ι} τ₂ → 
       --------------
       Term Δ Γ (τ₁ `→ τ₂)

  _·_ :

       Term Δ Γ (τ₁ `→ τ₂) → 
       Term Δ Γ τ₁ → 
       ---------
       Term Δ Γ τ₂
  
  --------------
  -- System Fω

  Λ : 

      Term (Δ ,, κ) (Γ ,, κ) τ →
      -----------
      Term Δ Γ (`∀ τ)

  _·[_] : 
  
          Term Δ Γ (`∀ τ₂) →
          (τ₁ : NormalType Δ κ) → 
          ----------------
          Term Δ Γ (τ₂ βₖNF[ τ₁ ])

  ------------------
  -- Qualified types

  `ƛ : 

       Term Δ (Γ ,,, π) τ → 
       --------------
       Term Δ Γ (π ⇒ τ)

  _·⟨_⟩ : ∀ {π : NormalPred Δ R[ κ ]} {τ : NormalType Δ (★ {ι})} → 
  
        Term Δ Γ (π ⇒ τ) →
        Ent Δ Γ π → 
        ----------------
        Term Δ Γ τ

  ------------
  -- Rω labels

  -- label constants
  # : 

        ∀ (ℓ : NormalType Δ (L {ι})) → 
        -------------------
        Term Δ Γ ⌊ ℓ ⌋

  -------------
  -- Rω records

  -- Record singleton formation
  _Π▹ne_ : 
          (M₁ : Term Δ Γ ⌊ ne l ⌋) (M₂ : Term Δ Γ υ) →
          ----------------------------------------
          Term Δ Γ (Π (l ▹ₙ υ))

  _Π▹_ : ∀ {l : Label}
          (M₁ : Term Δ Γ {ι = ι} ⌊ lab l ⌋) (M₂ : Term Δ Γ υ) →
          ----------------------------------------
          Term Δ Γ (Π (l ▹' υ))

  -- Record singleton elimination
  _Π/ne_ :
          (M₁ : Term Δ Γ (Π (l ▹ₙ υ))) (M₂ : Term Δ Γ ⌊ ne l ⌋) →
          ----------------------------------------
          Term Δ Γ υ

  _Π/_ : ∀ {l : Label} → 
          (M₁ : Term Δ Γ (Π (l ▹' υ))) (M₂ : Term Δ Γ {ι = ι} ⌊ lab l ⌋) →
          ----------------------------------------
          Term Δ Γ υ

  prj : 
   
       (M : Term Δ Γ (Π ρ₂)) → Ent Δ Γ (ρ₁ ≲ ρ₂) → 
       -------------------------------------
       Term Δ Γ (Π ρ₁)
  
  _⊹_ : 

       (M₁ : Term Δ Γ (Π ρ₁)) → (M₂ : Term Δ Γ (Π ρ₂)) → Ent Δ Γ (ρ₁ · ρ₂ ~ ρ₃) → 
       ---------------------------------------------------------------------
       Term Δ Γ (Π ρ₃)

  syn : 
    
        (ρ : NormalType Δ R[ κ ]) → (φ : NormalType Δ (κ `→ (★ {ι}))) → (M : Term Δ Γ (SynT' ρ φ)) → 
        ------------------------------------------------------------------
        Term Δ Γ (Π (φ <$>' ρ))

  ana : 
    
        (ρ : NormalType Δ R[ κ ]) 
        (φ : NormalType Δ (κ `→ ★)) 
        (τ : NormalType Δ ★)

        (eq₁ : (⇓ (AnaT (⇑ ρ) (⇑ φ) (⇑ τ))) ≡ τ₁) → 
        (eq₂ : (⇓ (Σ · (⇑ φ <$> ⇑ ρ))) ≡ τ₂) → 
        (M : Term Δ Γ τ₁) → 
        
        ------------------------------------------------------------------
        Term Δ Γ (τ₂ `→ τ)

  --------------
  -- Rω variants

  -- Variant singleton formation
  _Σ▹ne_ : 
          (M₁ : Term Δ Γ ⌊ ne l ⌋) (M₂ : Term Δ Γ υ) →
          ----------------------------------------
          Term Δ Γ (Σ (l ▹ₙ υ))

  _Σ▹_ : ∀ {l : Label}
          (M₁ : Term Δ Γ {ι = ι} ⌊ lab l ⌋) (M₂ : Term Δ Γ υ) →
          ----------------------------------------
          Term Δ Γ (Σ (⦅ [ (l , υ) ] ⦆ tt))

  -- Variant singleton elimination
  _Σ/ne_ :
          (M₁ : Term Δ Γ (Σ (l ▹ₙ υ))) (M₂ : Term Δ Γ ⌊ ne l ⌋) →
          ----------------------------------------
          Term Δ Γ υ

  _Σ/_ : ∀ {l : Label} → 
          (M₁ : Term Δ Γ (Σ (⦅ [ (l , υ) ] ⦆ tt))) (M₂ : Term Δ Γ {ι = ι} ⌊ lab l ⌋) →
          ----------------------------------------
          Term Δ Γ υ

  inj : 
   
       (M : Term Δ Γ (Σ ρ₁)) → Ent Δ Γ (ρ₁ ≲ ρ₂) → 
       -------------------------------------
       Term Δ Γ (Σ ρ₂)
       
  _▿_ : 

       (M₁ : Term Δ Γ (Σ ρ₁ `→ τ)) → (M₂ : Term Δ Γ (Σ ρ₂ `→ τ)) → Ent Δ Γ (ρ₁ · ρ₂ ~ ρ₃) → 
       ---------------------------------------------------------------------
       Term Δ Γ (Σ ρ₃ `→ τ)

  ----------------------------------------
  -- Values

  ⟨_⟩ : ∀ {xs : SimpleRow (NormalType Δ (★ {ι}))} {oxs : True (normalOrdered? xs)} → 
          Record Γ xs → 
          ----------------------
          Term Δ Γ (Π (⦅ xs ⦆ oxs))

  ⟨_▹_⟩via_ : ∀ {xs : SimpleRow (NormalType Δ ★)} {oxs : True (normalOrdered? xs)} → 
        (l : Label) → (M : Term Δ Γ τ) → (l , τ) ∈ xs → 
        -------------------------------------------
        Term Δ Γ (Σ (⦅ xs ⦆ oxs)) 

--------------------------------------------------------------------------------
-- Values

data Value {Δ = Δ} {Γ} where
  V-λ : 
          (M : Term Δ (Γ , τ₂) τ₁) → 
          Value (`λ M)

  V-Λ :
          (M : Term (Δ ,, κ) (Γ ,, κ) τ) → 
        --   Value M → 
          Value (Λ M)

  V-ƛ :
          (M : Term Δ (Γ ,,, π) τ) → 
          Value (`ƛ M)

  V-# :   ∀ {l : NormalType Δ (L {ι})} → 
          Value (# l)

  V-Π : {xs : SimpleRow (NormalType Δ (★ {ι}))} {oxs : True (normalOrdered? xs)} → 
          (r : Record Γ xs) → 
          RecordValue Γ xs r → 
          Value (⟨_⟩ {xs = xs} {oxs} r)

  V-Σ : ∀  {xs : SimpleRow (NormalType Δ ★)} {oxs : True (normalOrdered? xs)} → 
        (l : Label) → {M : Term Δ Γ τ} → (V : Value M) → (i : (l , τ) ∈ xs) → 
        -------------------------------------------
        Value (⟨_▹_⟩via_ {oxs = oxs} l M i)       

  V-ana : (ρ : NormalType Δ R[ κ ]) 
          (φ : NormalType Δ (κ `→ ★)) 
          (τ : NormalType Δ ★) 
          (eq₁ : (⇓ (AnaT (⇑ ρ) (⇑ φ) (⇑ τ))) ≡ τ₁) → 
          (eq₂ : (⇓ (Σ · (⇑ φ <$> ⇑ ρ))) ≡ τ₂) → 
          (M : Term Δ Γ τ₁) → 
        
          Value M → 
          ------------------------------------
          Value (ana ρ φ τ eq₁ eq₂ M)

  V-▿  : 
           {e : Ent Δ Γ (ρ₁ · ρ₂ ~ ρ₃)} 
           (M : Term Δ Γ (Σ ρ₁ `→ τ)) (N : Term Δ Γ (Σ ρ₂ `→ τ)) → 

            Value M → Value N → 
            ---------------------
            Value ((M ▿ N) e)


--------------------------------------------------------------------------------
-- Conversion helpers.

convVar : ∀ {τ₁ τ₂ : NormalType Δ (★ {ι})} → τ₁ ≡ τ₂ → Var Γ τ₁ → Var Γ τ₂
convVar refl v = v

convVar-≡t : ∀ {τ₁ τ₂ : Type Δ (★ {ι})} → τ₁ ≡t τ₂ → Var Γ (⇓ τ₁) → Var Γ (⇓ τ₂)
convVar-≡t eq x = convVar (soundness eq) x 

convPVar : ∀ {π₁ π₂ : NormalPred Δ R[ κ ]} → π₁ ≡ π₂ → PVar Γ π₁ → PVar Γ π₂
convPVar refl v = v

conv : ∀ {τ₁ τ₂ : NormalType Δ (★ {ι})} → τ₁ ≡ τ₂ → Term Δ Γ τ₁ → Term Δ Γ τ₂
conv refl M = M

convEnt : ∀ {π₁ π₂ : NormalPred Δ R[ κ ]} → π₁ ≡ π₂ → Ent Δ Γ π₁ → Ent Δ Γ π₂
convEnt refl e = e

conv-≡t : ∀ {τ₁ τ₂ : Type Δ (★ {ι})} → τ₁ ≡t τ₂ → Term Δ Γ (⇓ τ₁) → Term Δ Γ (⇓ τ₂)
conv-≡t eq = conv (soundness eq)
