{-# OPTIONS --safe #-}
module Rome.Terms.Syntax where

open import Agda.Primitive

open import Rome.Kinds
open import Rome.Types
open import Rome.Types.Substitution
open import Rome.Equivalence.Syntax

open import Rome.Entailment.Syntax

--------------------------------------------------------------------------------
-- Environments.

data Env : KEnv → Set where
  ε : ∀ {Δ : KEnv} →
        Env Δ
  _,_ : ∀ {Δ : KEnv} →
          Env Δ → Type Δ ★ → Env Δ

-- Weakening of the kinding env.
weakΓ : ∀ {Δ : KEnv} {κ : Kind} →
        Env Δ → Env (Δ , κ)
weakΓ ε = ε
weakΓ (Γ , τ) = weakΓ Γ , rename S τ

--------------------------------------------------------------------------------
-- Variables.

data Var : ∀ {Δ : KEnv} {κ : Kind} →
           Env Δ → Type Δ κ → Set where
  Z : ∀ {Δ : KEnv}
        {Γ : Env Δ} {τ : Type Δ ★} →
        Var (Γ , τ) τ
  S : ∀ {Δ : KEnv} 
        {Γ : Env Δ}
        {τ : Type Δ ★} {υ : Type Δ ★} →
         Var Γ υ → Var (Γ , τ) υ        

--------------------------------------------------------------------------------
-- Synonyms, used later.

SynT : ∀ {Δ : KEnv}
         (κ : Kind) 
     → (ρ : Type Δ R[ κ ]) →
       (φ : Type Δ (κ `→ ★)) → Type Δ ★
SynT κ ρ φ =
  `∀ L (`∀ κ (`∀ R[ κ ] ((l R▹ u) · y ~ ρ' ⇒
    (⌊_⌋ l `→ φ' ·[ u ]))))
    where
      ρ' = weaken (weaken (weaken ρ))
      φ' = weaken (weaken (weaken φ))
      y = tvar Z
      u = tvar (S Z)
      l = tvar (S (S Z))

AnaT : ∀ {Δ : KEnv}
         (κ : Kind) → 
         (ρ : Type Δ R[ κ ])
         (φ : Type Δ (κ `→ ★)) (τ : Type Δ ★) →
         Type Δ ★
AnaT κ ρ φ τ =
  `∀ L (`∀ κ (`∀ R[ κ ] ((l R▹ u) · y ~ ρ' ⇒
    ⌊_⌋ l `→ φ' ·[ u ] `→ τ')))
    where
      ρ' = weaken (weaken (weaken ρ))
      φ' = weaken (weaken (weaken φ))
      τ' = weaken (weaken (weaken τ))
      y = tvar Z
      u = tvar (S Z)
      l = tvar (S (S Z))

FoldT : ∀ {Δ : KEnv } →
       (ρ : Type Δ R[ ★  ])(υ : Type Δ (★ )) →
       Type Δ ★
FoldT ρ υ =
  `∀ L (`∀ (★ ) (`∀ R[ ★  ] ((l R▹ t) · y ~ ρ' ⇒
    ⌊_⌋ l `→ t `→ υ')))
    where
      ρ' = weaken (weaken (weaken ρ))
      υ' = weaken (weaken (weaken υ))
      y = tvar Z
      t = tvar (S Z)
      l = tvar (S (S Z))

--------------------------------------------------------------------------------
-- Terms.


data Term : ∀ (Δ : KEnv) → PEnv Δ  → Env Δ → Set where
  ------------------------------------------------------------
  -- System Fω.
  
  var : ∀ {Δ : KEnv } {Φ : PEnv Δ } {Γ : Env Δ}{τ : Type Δ ★} →

           Var Γ τ →
           -------------
           Term Δ Φ Γ
  
  `λ : ∀ {Δ : KEnv} {Φ : PEnv Δ } {Γ : Env Δ }
  
             (τ : Type Δ (★ )) → Term Δ Φ (Γ , τ) →
             -------------------------------------
             Term Δ Φ Γ
  
  _·_ : ∀ {Δ : KEnv } {Φ : PEnv Δ } {Γ : Env Δ } {τ : Type Δ (★ )} {υ : Type Δ (★ )} →
  
             Term Δ Φ Γ → Term Δ Φ Γ →
             ----------------------------
             Term Δ Φ Γ
  
  `Λ : ∀ {Δ : KEnv }  {Φ : PEnv Δ } {Γ : Env Δ }
            (κ : Kind ) {τ : Type (Δ , κ) (★ )} →
  
         Term (Δ , κ) (weakΦ Φ) (weakΓ Γ) →
         ----------------------------------------------------
         Term Δ Φ Γ
  
  
  _·[_] : ∀ {Δ : KEnv } {Φ : PEnv Δ } {Γ : Env Δ }
            {κ : Kind } {τ : Type (Δ , κ) (★ )} →
  
           Term Δ Φ Γ → (υ : Type Δ κ) →
           ----------------------------------
           Term Δ Φ Γ
  
  ------------------------------------------------------------
  -- Qualified types.
  
  `ƛ : ∀ {Δ : KEnv} {Φ : PEnv Δ} {Γ : Env Δ}
         {κ : Kind} {τ : Type Δ ★} →

           (π : Pred Δ κ) → Term Δ (Φ , π) Γ →
           -------------------------------------
           Term Δ Φ Γ

  _·⟨_⟩ : ∀ {Δ : KEnv} {Φ : PEnv Δ} {Γ : Env Δ}
           {κ : Kind} {π : Pred Δ κ} {τ : Type Δ (★ )} →

         Term Δ Φ Γ → Ent Δ Φ π →
         ----------------------------------
         Term Δ Φ Γ
              
  ------------------------------------------------------------
  -- System Rω.

  -- labels.
  lab : ∀ {Δ : KEnv} {Γ : Env Δ} {Φ : PEnv Δ }
          (l : Type Δ L) →
          ----------------------------------------
          Term Δ Φ Γ
  

  -- singleton introduction.
  _▹_ : ∀ {Δ : KEnv } {Γ : Env Δ } {Φ : PEnv Δ }
          {τ : Type Δ L} {υ : Type Δ (★ )} →
          (M₁ : Term Δ Φ Γ) (M₂ : Term Δ Φ Γ) →
          ----------------------------------------
          Term Δ Φ Γ          

  -- singleton elimination.
  _/_ : ∀ {Δ : KEnv } {Γ : Env Δ} {Φ : PEnv Δ}
          {τ : Type Δ L} {υ : Type Δ ★} →
          (M₁ : Term Δ Φ Γ) (M₂ : Term Δ Φ Γ) →
          ----------------------------------------
          Term Δ Φ Γ

  -- The empty record.
  -- (Not a part of pen-and-paper calculus.)
  ∅ : ∀ {Δ : KEnv} {Γ : Env Δ} {Φ : PEnv Δ} →
         -----------
        Term Δ Φ Γ

  -- record introduction.
  _⊹_ : ∀ {Δ : KEnv} {Γ : Env Δ} {Φ : PEnv Δ}
        {ρ₁ ρ₂ ρ₃ : Type Δ (R[ ★ ])} →
      
          (M : Term Δ Φ Γ) (N : Term Δ Φ Γ) →
          (π : Ent Δ Φ (ρ₁ · ρ₂ ~ ρ₃)) →
          ------------------------------
          Term Δ Φ Γ
  
  -- record "elimination".
  prj : ∀ {Δ : KEnv} {Γ : Env Δ} {Φ : PEnv Δ}
        {ρ₁ ρ₂ : Type Δ (R[ ★ ])} →
        
          (M : Term Δ Φ Γ) → (π : Ent Δ Φ (ρ₂ ≲ ρ₁)) →
          ------------------------------
          Term Δ Φ Γ

  -- Singleton → Singleton Record.
  Π : ∀ {Δ : KEnv} {Γ : Env Δ} {Φ : PEnv Δ}
        {τ : Type Δ (L )} {υ : Type Δ ★} →
        
          Term Δ Φ Γ →
          ---------------------
          Term Δ Φ Γ

  -- Singleton Record → Singleton.
  Π⁻¹ : ∀ {Δ : KEnv} {Γ : Env Δ} {Φ : PEnv Δ}
        {τ : Type Δ (L )} {υ : Type Δ ★} →
        
          (M : Term Δ Φ Γ) →
          ----------------------------------------
          Term Δ Φ Γ
          
  -- Subsumption.
  t-≡ : ∀ { Δ : KEnv} {Φ : PEnv Δ} {Γ : Env Δ}
        {τ υ : Type Δ ★}  →

          (M : Term Δ Φ Γ) → τ ≡t υ →
          ----------------------------
          Term Δ Φ Γ

  -- Variant introduction.
  inj : ∀ {Δ : KEnv} {Γ : Env Δ} {Φ : PEnv Δ}
        {ρ₁ ρ₂ : Type Δ (R[ ★ ])} →
      
          (M : Term Δ Φ Γ) → (Ent Δ Φ (ρ₁ ≲ ρ₂)) →
          ----------------------------------------------
          Term Δ Φ Γ

  -- Singleton Record → Singleton.
  Σ : ∀ {Δ : KEnv} {Γ : Env Δ} {Φ : PEnv Δ}
        {τ : Type Δ (L )} {υ : Type Δ ★} →
        
          Term Δ Φ Γ →
          ---------------------
          Term Δ Φ Γ
          
  -- Singleton Variant → Singleton.
  Σ⁻¹ : ∀ {Δ : KEnv} {Γ : Env Δ} {Φ : PEnv Δ}
        {τ : Type Δ (L )} {υ : Type Δ ★} →
        
          (M : Term Δ Φ Γ) →
          ----------------------------------------
          Term Δ Φ Γ
           
  -- Variant elimination.
  _▿_ : ∀ {Δ : KEnv} {Γ : Env Δ} {Φ : PEnv Δ}
        {ρ₁ ρ₂ ρ₃ : Type Δ (R[ ★ ])} {τ : Type Δ ★} →
      
          Term Δ Φ Γ →
          Term Δ Φ Γ →
          Ent Δ Φ (ρ₁ · ρ₂ ~ ρ₃) →
          ------------------------------
          Term Δ Φ Γ
           
  -- Synthesis.
  syn : ∀ {Δ : KEnv} {Γ : Env Δ} {Φ : PEnv Δ} {κ : Kind}
         
          (ρ : Type Δ R[ κ ]) →
          (φ : Type Δ (κ `→ ★)) →
          Term Δ Φ Γ →
          --------------------------
          Term Δ Φ Γ

  -- -- Analysis.
  ana : ∀ {Δ : KEnv} {Γ : Env Δ} {Φ : PEnv Δ} {κ : Kind}
         
          (ρ : Type Δ R[ κ ]) →
          (φ : Type Δ (κ `→ ★)) →
          (τ : Type Δ ★) →
          Term Δ Φ Γ →
          --------------------------
          Term Δ Φ Γ

  -- Fold.
  fold : ∀ {Δ : KEnv} {Γ : Env Δ} {Φ : PEnv Δ}
         {ρ : Type Δ R[ ★ ]} {υ : Type Δ ★} →
         (M₁ : Term Δ Φ Γ) →
         (M₂ : Term Δ Φ Γ) →
         (M₃ : Term Δ Φ Γ) →
         (N  : Term Δ Φ Γ) →
         ------------------------
         Term Δ Φ Γ

  In : ∀ {Δ : KEnv} {Γ : Env Δ} {Φ : PEnv Δ}
         {F : Type Δ (★ `→ ★)} {A : Type Δ ★} →
         Term Δ Φ Γ

  Out : ∀ {Δ : KEnv} {Γ : Env Δ} {Φ : PEnv Δ}
          {F : Type Δ (★ `→ ★)} →
          Term Δ Φ Γ

  
  --------------------------------------------------------------------------------
  -- admissable rules.
  
-- private
--   variable
--     Δ : KEnv
--     Γ : Env Δ
--     Φ : PEnv Δ
--     κ : Kind
--     Ł : Type Δ L
--     τ : Type  Δ κ
  
-- prj▹ : {ρ : Type Δ R[ ★ ]} →          
--         Term Δ Φ Γ → Ent Δ Φ ((Ł R▹ τ) ≲ ρ) →
--         ------------------------------------------
--         Term Δ Φ Γ
-- prj▹ r e = Π⁻¹ (prj r e)          

-- inj▹ : {ρ : Type Δ R[ ★ ]} →          
--         Term Δ Φ Γ → Ent Δ Φ ((Ł R▹ τ) ≲ ρ) →
--         ---------------------------------------------
--         Term Δ Φ Γ
-- inj▹ s e = inj (Σ s) e
  
                       
