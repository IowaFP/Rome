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

open import Rome.Both.Types.Theorems.Consistency
open import Rome.Both.Types.Theorems.Soundness
open import Rome.Both.Types.Theorems.Stability


open import Rome.Both.Containment

--------------------------------------------------------------------------------
-- First define environments mapping variables to predicates and types

data Env : KEnv ιΔ → Level → Set where
  ∅ : Env Δ lzero
  _,_  : Env Δ ιΓ → NormalType Δ (★ {ι}) → Env Δ (ιΓ ⊔ ι)

data PEnv : KEnv ιΔ → Level → Set where
  ∅ : PEnv Δ lzero
  _,_ : ∀ {κ : Kind ικ} → PEnv Δ ιΓ → NormalPred Δ R[ κ ] → PEnv Δ (ιΓ ⊔ lsuc ικ)

weakΦ : PEnv Δ ιΦ → PEnv (Δ ,, κ) ιΦ 
weakΦ ∅ = ∅
weakΦ (Φ , x) = (weakΦ Φ) , (weakenPredₖNF x)

weakΓ : Env Δ ιΓ → Env (Δ ,, κ) ιΓ 
weakΓ ∅ = ∅
weakΓ (Γ , x) = weakΓ Γ , weakenₖNF x

private
  variable
    Γ Γ₁ Γ₂ Γ₃ : Env Δ ιΓ
    Φ Φ₁ Φ₂ Φ₃ : PEnv Δ ιΦ
    τ υ τ₁ τ₂  : NormalType Δ ★
    l l₁ l₂    : NeutralType Δ L
    ρ ρ₁ ρ₂ ρ₃ : NormalType Δ R[ κ ]
    π π₁ π₂ π₃ : NormalPred Δ R[ κ ]
    

data PVar : PEnv Δ ιΓ → NormalPred Δ κ → Set where
  Z : PVar (Φ , π) π
  S : PVar Φ π₁  → PVar (Φ , π₂) π₁

data Var : Env Δ ιΓ → NormalType Δ (★ {ι}) → Set where
  Z : Var (Γ , τ) τ
  S : Var Γ τ₁  → Var (Γ , τ₂) τ₁

--------------------------------------------------------------------------------
-- Entailment relation on predicates 
      
data NormalEnt (Δ : KEnv ιΔ) (Φ : PEnv Δ ιΦ)  : NormalPred Δ R[ κ ] → Set where 
  n-var : 
        PVar Φ π → 
        -----------
        NormalEnt Δ Φ π 

  n-incl :  ∀ {xs ys : SimpleRow (NormalType Δ κ)} → 
           {oxs : True (normalOrdered? xs)} 
           {oys : True (normalOrdered? ys)} → 

          xs ⊆ ys → 
          --------------------------------------------
          NormalEnt Δ Φ ((⦅ xs  ⦆ oxs) ≲ (⦅ ys ⦆ oys))

  n-plus : ∀ {xs ys zs : SimpleRow (NormalType Δ κ)} → 
           {oxs : True (normalOrdered? xs)} 
           {oys : True (normalOrdered? ys)} 
           {ozs : True (normalOrdered? zs)} → 
          xs ⊆ zs → 
          ys ⊆ zs → 
          zs ⊆[ xs ⊹ ys ]  → 
          --------------------------------------------
          NormalEnt Δ Φ ((⦅ xs ⦆ oxs) · (⦅ ys ⦆ oys) ~ (⦅ zs ⦆ ozs))
  n-refl : 
          --------------
          NormalEnt Δ Φ (ρ₁ ≲ ρ₁)

  _n-⨾_ : 
          NormalEnt Δ Φ (ρ₁ ≲ ρ₂) → NormalEnt Δ Φ (ρ₂ ≲ ρ₃) →
          ---------------------------------------
          NormalEnt Δ Φ (ρ₁ ≲ ρ₃)

  n-plusL≲ : 
        NormalEnt Δ Φ (ρ₁ · ρ₂ ~ ρ₃) →
        ---------------------
        NormalEnt Δ Φ (ρ₁ ≲ ρ₃)

  n-plusR≲ : 
        NormalEnt Δ Φ (ρ₁ · ρ₂ ~ ρ₃) →
        ---------------------
        NormalEnt Δ Φ (ρ₂ ≲ ρ₃)

  n-emptyR : 
             
        -------------------------
        NormalEnt Δ Φ (ρ · εNF ~ ρ)

  n-emptyL : 

        -------------------------
        NormalEnt Δ Φ (εNF · ρ ~ ρ)  

  n-map≲ : ∀ {ρ₁ ρ₂ : NormalType Δ R[ κ₁ ]}
               {F : NormalType Δ (κ₁ `→ κ₂)} →

             NormalEnt Δ Φ (ρ₁ ≲ ρ₂) →
             {x y : NormalType Δ R[ κ₂ ]} → 
             x ≡ (F <$>' ρ₁) → 
             y ≡ F <$>' ρ₂ → 
             ---------------------------------
             NormalEnt Δ Φ (x ≲ y)


  n-map· : ∀ {ρ₁ ρ₂ ρ₃ : NormalType Δ R[ κ₁ ]}
               
               {F : NormalType Δ (κ₁ `→ κ₂)} →

             NormalEnt Δ Φ (ρ₁ · ρ₂ ~ ρ₃) →
             {x y z : NormalType Δ R[ κ₂ ]} → 
             x ≡ (F <$>' ρ₁) → 
             y ≡ F <$>' ρ₂ → 
             z ≡ F <$>' ρ₃ → 
             ---------------------------------
             NormalEnt Δ Φ (x · y ~ z)

  n-complR-inert : ∀ {nsr : True (notSimpleRows? ρ₂ ρ₁)} → 
    
             NormalEnt Δ Φ (ρ₁ ≲ ρ₂) → 
             ----------------------
             NormalEnt Δ Φ (ρ₁ · ((ρ₂ ─ ρ₁) {nsr}) ~ ρ₂)

  n-complR :  ∀ {xs ys : SimpleRow (NormalType Δ κ)} → 
                  {oxs : True (normalOrdered? xs)} 
                  {oys : True (normalOrdered? ys)} → 
                  {ozs : True (normalOrdered? (⇓Row (⇑Row ys ─s ⇑Row xs)))} → 
    
             NormalEnt Δ Φ (⦅ xs ⦆ oxs ≲ ⦅ ys ⦆ oys) → 
             ----------------------
             NormalEnt Δ Φ (⦅ xs ⦆ oxs · ⦅ ⇓Row (⇑Row ys ─s ⇑Row xs) ⦆ ozs ~ ⦅ ys ⦆ oys)

  n-complL-inert : ∀ {nsr : True (notSimpleRows? ρ₂ ρ₁)} → 
    
             NormalEnt Δ Φ (ρ₁ ≲ ρ₂) → 
             ----------------------
             NormalEnt Δ Φ (((ρ₂ ─ ρ₁) {nsr}) · ρ₁ ~ ρ₂)

  n-complL :  ∀ {xs ys : SimpleRow (NormalType Δ κ)} → 
                  {oxs : True (normalOrdered? xs)} 
                  {oys : True (normalOrdered? ys)} → 
                  {ozs : True (normalOrdered? (⇓Row (⇑Row ys ─s ⇑Row xs)))} → 
    
             NormalEnt Δ Φ (⦅ xs ⦆ oxs ≲ ⦅ ys ⦆ oys) → 
             ----------------------
             NormalEnt Δ Φ (⦅ ⇓Row (⇑Row ys ─s ⇑Row xs) ⦆ ozs · ⦅ xs ⦆ oxs ~ ⦅ ys ⦆ oys)

data EntValue  (Δ : KEnv ιΔ) (Φ : PEnv Δ ιΦ) : (π : NormalPred Δ R[ κ ]) → NormalEnt Δ Φ π → Set where 

  n-incl :  ∀ {xs ys : SimpleRow (NormalType Δ κ)} → 
           {oxs : True (normalOrdered? xs)} 
           {oys : True (normalOrdered? ys)} → 

          (i : xs ⊆ ys) → 
          -----------------------
          EntValue Δ Φ (⦅ xs ⦆ oxs ≲ ⦅ ys ⦆ oys) (n-incl i)

  n-plus : ∀ {xs ys zs : SimpleRow (NormalType Δ κ)} → 
           {oxs : True (normalOrdered? xs)} 
           {oys : True (normalOrdered? ys)} 
           {ozs : True (normalOrdered? zs)} → 
          (i₁ : xs ⊆ zs) → 
          (i₂ : ys ⊆ zs) → 
          (i₃ : zs ⊆[ xs ⊹ ys ])  → 
          --------------------------------------------------------------------

          EntValue Δ Φ ((⦅ xs ⦆ oxs) · (⦅ ys ⦆ oys) ~ (⦅ zs ⦆ ozs)) (n-plus i₁ i₂ i₃)
          
          

--------------------------------------------------------------------------------
-- Terms with normal types

data NormalTerm (Δ : KEnv ιΔ) (Φ : PEnv Δ ιΦ) (Γ : Env Δ ιΓ) : NormalType Δ (★ {ι}) → Set
data Value {Δ : KEnv ιΔ} {Φ : PEnv Δ ιΦ} {Γ : Env Δ ιΓ} : ∀ {τ : NormalType Δ (★ {ι})} → NormalTerm Δ Φ Γ τ → Set
data Record {Δ : KEnv ιΔ} (Γ : Env Δ ιΓ) : SimpleRow (NormalType Δ (★ {ι})) → Set where
  ∅   : Record Γ {ι = ι} []
  _▹_⨾_ : ∀ {xs : SimpleRow (NormalType Δ ★)} → (l : Label)  → NormalTerm Δ Φ Γ τ → 
            Record Γ xs → Record Γ ((l , τ) ∷ xs)

data RecordValue {Δ : KEnv ιΔ} (Γ : Env Δ ιΓ) : (xs : SimpleRow (NormalType Δ (★ {ι}))) → Record Γ xs → Set where
  ∅   : RecordValue Γ {ι = ι} [] ∅
  _▹_⨾_ : ∀ {xs : SimpleRow (NormalType Δ ★)} {r : Record Γ xs} → 
          (l : Label)  → {M : NormalTerm Δ Φ Γ τ} → Value M → 
          RecordValue Γ xs r → RecordValue Γ ((l , τ) ∷ xs) (l ▹ M ⨾ r) 


data NormalTerm Δ Φ Γ   where
  ` : Var Γ τ → 
      --------
      NormalTerm Δ Φ Γ τ

  `λ : 

       NormalTerm Δ Φ (Γ , τ₁) {ι = ι} τ₂ → 
       --------------
       NormalTerm Δ Φ Γ (τ₁ `→ τ₂)

  _·_ :

       NormalTerm Δ Φ Γ (τ₁ `→ τ₂) → 
       NormalTerm Δ Φ Γ τ₁ → 
       ---------
       NormalTerm Δ Φ Γ τ₂
  
  --------------
  -- System Fω

  Λ : 

      NormalTerm (Δ ,, κ) (weakΦ Φ) (weakΓ Γ) τ →
      -----------
      NormalTerm Δ Φ Γ (`∀ τ)

  _·[_] : 
  
          NormalTerm Δ Φ Γ (`∀ τ₂) →
          (τ₁ : NormalType Δ κ) → 
          ----------------
          NormalTerm Δ Φ Γ (τ₂ βₖNF[ τ₁ ])

  ------------------
  -- Qualified types

  `ƛ : 

       NormalTerm Δ (Φ , π) Γ τ → 
       --------------
       NormalTerm Δ Φ Γ (π ⇒ τ)

  _·⟨_⟩ : ∀ {π : NormalPred Δ R[ κ ]} {τ : NormalType Δ (★ {ι})} → 
  
        NormalTerm Δ Φ Γ (π ⇒ τ) →
        NormalEnt Δ Φ π → 
        ----------------
        NormalTerm Δ Φ Γ τ

  ------------
  -- Rω labels

  -- label constants
  # : 

        ∀ (ℓ : NormalType Δ (L {ι})) → 
        -------------------
        NormalTerm Δ Φ Γ ⌊ ℓ ⌋

  -------------
  -- Rω records

  -- Record singleton formation
  _Π▹ne_ : 
          (M₁ : NormalTerm Δ Φ Γ ⌊ ne l ⌋) (M₂ : NormalTerm Δ Φ Γ υ) →
          ----------------------------------------
          NormalTerm Δ Φ Γ (Π (l ▹ₙ υ))

  _Π▹_ : ∀ {l : Label}
          (M₁ : NormalTerm Δ Φ Γ {ι = ι} ⌊ lab l ⌋) (M₂ : NormalTerm Δ Φ Γ υ) →
          ----------------------------------------
          NormalTerm Δ Φ Γ (Π (l ▹' υ))

  -- Record singleton elimination
  _Π/ne_ :
          (M₁ : NormalTerm Δ Φ Γ (Π (l ▹ₙ υ))) (M₂ : NormalTerm Δ Φ Γ ⌊ ne l ⌋) →
          ----------------------------------------
          NormalTerm Δ Φ Γ υ

  _Π/_ : ∀ {l : Label} → 
          (M₁ : NormalTerm Δ Φ Γ (Π (l ▹' υ))) (M₂ : NormalTerm Δ Φ Γ {ι = ι} ⌊ lab l ⌋) →
          ----------------------------------------
          NormalTerm Δ Φ Γ υ

  prj : 
   
       (M : NormalTerm Δ Φ Γ (Π ρ₂)) → NormalEnt Δ Φ (ρ₁ ≲ ρ₂) → 
       -------------------------------------
       NormalTerm Δ Φ Γ (Π ρ₁)
  
  _⊹_ : 

       (M₁ : NormalTerm Δ Φ Γ (Π ρ₁)) → (M₂ : NormalTerm Δ Φ Γ (Π ρ₂)) → NormalEnt Δ Φ (ρ₁ · ρ₂ ~ ρ₃) → 
       ---------------------------------------------------------------------
       NormalTerm Δ Φ Γ (Π ρ₃)

  syn : 
    
        (ρ : NormalType Δ R[ κ ]) → (φ : NormalType Δ (κ `→ (★ {ι}))) → (M : NormalTerm Δ Φ Γ (SynT' ρ φ)) → 
        ------------------------------------------------------------------
        NormalTerm Δ Φ Γ (Π (φ <$>' ρ))

  ana : 
    
        (ρ : NormalType Δ R[ κ ]) 
        (φ : NormalType Δ (κ `→ ★)) 
        (τ : NormalType Δ ★)

        (eq₁ : (⇓ (AnaT (⇑ ρ) (⇑ φ) (⇑ τ))) ≡ τ₁) → 
        (eq₂ : (⇓ (Σ · (⇑ φ <$> ⇑ ρ))) ≡ τ₂) → 
        (M : NormalTerm Δ Φ Γ τ₁) → 
        
        ------------------------------------------------------------------
        NormalTerm Δ Φ Γ (τ₂ `→ τ)

  --------------
  -- Rω variants

  -- Variant singleton formation
  _Σ▹ne_ : 
          (M₁ : NormalTerm Δ Φ Γ ⌊ ne l ⌋) (M₂ : NormalTerm Δ Φ Γ υ) →
          ----------------------------------------
          NormalTerm Δ Φ Γ (Σ (l ▹ₙ υ))

  _Σ▹_ : ∀ {l : Label}
          (M₁ : NormalTerm Δ Φ Γ {ι = ι} ⌊ lab l ⌋) (M₂ : NormalTerm Δ Φ Γ υ) →
          ----------------------------------------
          NormalTerm Δ Φ Γ (Σ (⦅ [ (l , υ) ] ⦆ tt))

  -- Variant singleton elimination
  _Σ/ne_ :
          (M₁ : NormalTerm Δ Φ Γ (Σ (l ▹ₙ υ))) (M₂ : NormalTerm Δ Φ Γ ⌊ ne l ⌋) →
          ----------------------------------------
          NormalTerm Δ Φ Γ υ

  _Σ/_ : ∀ {l : Label} → 
          (M₁ : NormalTerm Δ Φ Γ (Σ (⦅ [ (l , υ) ] ⦆ tt))) (M₂ : NormalTerm Δ Φ Γ {ι = ι} ⌊ lab l ⌋) →
          ----------------------------------------
          NormalTerm Δ Φ Γ υ

  inj : 
   
       (M : NormalTerm Δ Φ Γ (Σ ρ₁)) → NormalEnt Δ Φ (ρ₁ ≲ ρ₂) → 
       -------------------------------------
       NormalTerm Δ Φ Γ (Σ ρ₂)
       
  _▿_ : 

       (M₁ : NormalTerm Δ Φ Γ (Σ ρ₁ `→ τ)) → (M₂ : NormalTerm Δ Φ Γ (Σ ρ₂ `→ τ)) → NormalEnt Δ Φ (ρ₁ · ρ₂ ~ ρ₃) → 
       ---------------------------------------------------------------------
       NormalTerm Δ Φ Γ (Σ ρ₃ `→ τ)

  ----------------------------------------
  -- Values

  ⟨_⟩ : ∀ {xs : SimpleRow (NormalType Δ (★ {ι}))} {oxs : True (normalOrdered? xs)} → 
          Record Γ xs → 
          ----------------------
          NormalTerm Δ Φ Γ (Π (⦅ xs ⦆ oxs))

  ⟨_▹_⟩via_ : ∀ {xs : SimpleRow (NormalType Δ ★)} {oxs : True (normalOrdered? xs)} → 
        (l : Label) → (M : NormalTerm Δ Φ Γ τ) → (l , τ) ∈ xs → 
        -------------------------------------------
        NormalTerm Δ Φ Γ (Σ (⦅ xs ⦆ oxs)) 

--------------------------------------------------------------------------------
-- Values

data Value {Δ = Δ} {Φ} {Γ} where
  V-λ : 
          (M : NormalTerm Δ Φ (Γ , τ₂) τ₁) → 
          Value (`λ M)

  V-Λ :
          (M : NormalTerm (Δ ,, κ) (weakΦ Φ) (weakΓ Γ) τ) → 
        --   Value M → 
          Value (Λ M)

  V-ƛ :
          (M : NormalTerm Δ (Φ , π) Γ τ) → 
          Value (`ƛ M)

  V-# :   ∀ {l : NormalType Δ (L {ι})} → 
          Value (# l)

  V-Π : {xs : SimpleRow (NormalType Δ (★ {ι}))} {oxs : True (normalOrdered? xs)} → 
          (r : Record Γ xs) → 
          RecordValue Γ xs r → 
          Value (⟨_⟩ {xs = xs} {oxs} r)

  V-Σ : ∀  {xs : SimpleRow (NormalType Δ ★)} {oxs : True (normalOrdered? xs)} → 
        (l : Label) → {M : NormalTerm Δ Φ Γ τ} → (V : Value M) → (i : (l , τ) ∈ xs) → 
        -------------------------------------------
        Value (⟨_▹_⟩via_ {oxs = oxs} l M i)       

  V-ana : (ρ : NormalType Δ R[ κ ]) 
          (φ : NormalType Δ (κ `→ ★)) 
          (τ : NormalType Δ ★) 
          (eq₁ : (⇓ (AnaT (⇑ ρ) (⇑ φ) (⇑ τ))) ≡ τ₁) → 
          (eq₂ : (⇓ (Σ · (⇑ φ <$> ⇑ ρ))) ≡ τ₂) → 
          (M : NormalTerm Δ Φ Γ τ₁) → 
        
          Value M → 
          ------------------------------------
          Value (ana ρ φ τ eq₁ eq₂ M)

  V-▿  : 
           {e : NormalEnt Δ Φ (ρ₁ · ρ₂ ~ ρ₃)} 
           (M : NormalTerm Δ Φ Γ (Σ ρ₁ `→ τ)) (N : NormalTerm Δ Φ Γ (Σ ρ₂ `→ τ)) → 

            Value M → Value N → 
            ---------------------
            Value ((M ▿ N) e)


--------------------------------------------------------------------------------
-- Conversion helpers.

convVar : ∀ {τ₁ τ₂ : NormalType Δ (★ {ι})} → τ₁ ≡ τ₂ → Var Γ τ₁ → Var Γ τ₂
convVar refl v = v

convVar-≡t : ∀ {τ₁ τ₂ : Type Δ (★ {ι})} → τ₁ ≡t τ₂ → Var Γ (⇓ τ₁) → Var Γ (⇓ τ₂)
convVar-≡t eq x = convVar (soundness eq) x 

convPVar : ∀ {π₁ π₂ : NormalPred Δ R[ κ ]} → π₁ ≡ π₂ → PVar Φ π₁ → PVar Φ π₂
convPVar refl v = v

conv : ∀ {τ₁ τ₂ : NormalType Δ (★ {ι})} → τ₁ ≡ τ₂ → NormalTerm Δ Φ Γ τ₁ → NormalTerm Δ Φ Γ τ₂
conv refl M = M

convEnt : ∀ {π₁ π₂ : NormalPred Δ R[ κ ]} → π₁ ≡ π₂ → NormalEnt Δ Φ π₁ → NormalEnt Δ Φ π₂
convEnt refl e = e

conv-≡t : ∀ {τ₁ τ₂ : Type Δ (★ {ι})} → τ₁ ≡t τ₂ → NormalTerm Δ Φ Γ (⇓ τ₁) → NormalTerm Δ Φ Γ (⇓ τ₂)
conv-≡t eq = conv (soundness eq)
