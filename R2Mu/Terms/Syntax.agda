{-# OPTIONS --safe #-}
module R2Mu.Terms.Syntax where

open import Agda.Primitive

open import R2Mu.Kinds
open import R2Mu.Types
open import R2Mu.Types.Substitution
open import R2Mu.Equivalence.Syntax

open import R2Mu.Entailment.Syntax

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
         (κ : Kind) {κ¹ : Kind¹ κ} 
     → (ρ : Type Δ R[ κ ]) →
       (φ : Type Δ (κ¹ `→ ★)) → Type Δ ★
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
         (κ : Kind) {κ¹ : Kind¹ κ} → 
         (ρ : Type Δ R[ κ ])
         (φ : Type Δ (κ¹ `→ ★)) (τ : Type Δ ★) →
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
module TermSyntax 
  (Ent : 
    ∀ 
      {κ : Kind }
      (Δ : KEnv ) → PEnv Δ  → Pred Δ κ → Set) where

  data Term : ∀ (Δ : KEnv) → PEnv Δ  → Env Δ  → Type Δ ★ → Set where
    ------------------------------------------------------------
    -- System Fω.
  
    var : ∀ {Δ : KEnv } {Φ : PEnv Δ } {Γ : Env Δ} {τ : Type Δ (★ )} →
  
             Var Γ τ →
             -------------
             Term Δ Φ Γ τ
  
    `λ : ∀ {Δ : KEnv} {Φ : PEnv Δ } {Γ : Env Δ } {υ : Type Δ (★ )}
  
             (τ : Type Δ (★ )) → Term Δ Φ (Γ , τ) υ →
             -------------------------------------
             Term Δ Φ Γ (τ `→ υ)
  
    _·_ : ∀ {Δ : KEnv } {Φ : PEnv Δ } {Γ : Env Δ } {τ : Type Δ (★ )} {υ : Type Δ (★ )} →
  
             Term Δ Φ Γ (τ `→ υ) → Term Δ Φ Γ τ →
             ----------------------------
             Term Δ Φ Γ υ
  
    `Λ : ∀ {Δ : KEnv }  {Φ : PEnv Δ } {Γ : Env Δ }
            (κ : Kind ) {τ : Type (Δ , κ) (★ )} →
  
         Term (Δ , κ) (weakΦ Φ) (weakΓ Γ) τ →
         ----------------------------------------------------
         Term Δ Φ Γ (`∀ κ τ)
  
  
    _·[_] : ∀ {Δ : KEnv } {Φ : PEnv Δ } {Γ : Env Δ }
              {κ : Kind } {τ : Type (Δ , κ) (★ )} →
  
             Term Δ Φ Γ (`∀ κ τ) → (υ : Type Δ κ) →
             ----------------------------------
             Term Δ Φ Γ (τ β[ υ ])
  
    ------------------------------------------------------------
    -- Qualified types.
  
    `ƛ : ∀ {Δ : KEnv} {Φ : PEnv Δ} {Γ : Env Δ}
           {κ : Kind} {τ : Type Δ ★} →
  
             (π : Pred Δ κ) → Term Δ (Φ , π) Γ τ →
             -------------------------------------
             Term Δ Φ Γ (π ⇒ τ)
  
    _·⟨_⟩ : ∀ {Δ : KEnv} {Φ : PEnv Δ} {Γ : Env Δ}
             {κ : Kind} {π : Pred Δ κ} {τ : Type Δ (★ )} →
  
           Term Δ Φ Γ (π ⇒ τ) → Ent Δ Φ π →
           ----------------------------------
           Term Δ Φ Γ τ
                
    ------------------------------------------------------------
    -- System Rω.
  
    -- labels.
    lab : ∀ {Δ : KEnv} {Γ : Env Δ} {Φ : PEnv Δ }
            (l : Type Δ L) →
            ----------------------------------------
            Term Δ Φ Γ (⌊_⌋ l)
    
  
    -- singleton introduction.
    _▹_ : ∀ {Δ : KEnv } {Γ : Env Δ } {Φ : PEnv Δ }
            {τ : Type Δ L} {υ : Type Δ (★ )} →
            (M₁ : Term Δ Φ Γ (⌊_⌋ τ)) (M₂ : Term Δ Φ Γ υ) →
            ----------------------------------------
            Term Δ Φ Γ (τ ▹ υ)          
  
    -- singleton elimination.
    _/_ : ∀ {Δ : KEnv } {Γ : Env Δ} {Φ : PEnv Δ}
            {τ : Type Δ (L )} {υ : Type Δ ★} →
            (M₁ : Term Δ Φ Γ (τ ▹ υ)) (M₂ : Term Δ Φ Γ (⌊_⌋ τ)) →
            ----------------------------------------
            Term Δ Φ Γ υ
  
    -- The empty record.
    -- (Not a part of pen-and-paper calculus.)
    ∅ : ∀ {Δ : KEnv} {Γ : Env Δ} {Φ : PEnv Δ} →

          -----------
          Term Δ Φ Γ (∅)
  
    -- record introduction.
    _⊹_ : ∀ {Δ : KEnv} {Γ : Env Δ} {Φ : PEnv Δ}
          {ρ₁ ρ₂ ρ₃ : Type Δ (R[ ★ ])} →
        
            (M : Term Δ Φ Γ (Π ρ₁)) (N : Term Δ Φ Γ (Π ρ₂)) →
            (π : Ent Δ Φ (ρ₁ · ρ₂ ~ ρ₃)) →
            ------------------------------
            Term Δ Φ Γ (Π ρ₃)
    
    -- record "elimination".
    prj : ∀ {Δ : KEnv} {Γ : Env Δ} {Φ : PEnv Δ}
          {ρ₁ ρ₂ : Type Δ (R[ ★ ])} →
          
            (M : Term Δ Φ Γ (Π ρ₁)) → (π : Ent Δ Φ (ρ₂ ≲ ρ₁)) →
            ------------------------------
            Term Δ Φ Γ (Π ρ₂)
  
    -- Singleton → Singleton Record.
    Π : ∀ {Δ : KEnv} {Γ : Env Δ} {Φ : PEnv Δ}
          {τ : Type Δ (L )} {υ : Type Δ ★} →
          
            Term Δ Φ Γ (τ ▹ υ) →
            ---------------------
            Term Δ Φ Γ (Π (τ R▹ υ))
  
    -- Singleton Record → Singleton.
    Π⁻¹ : ∀ {Δ : KEnv} {Γ : Env Δ} {Φ : PEnv Δ}
          {τ : Type Δ (L )} {υ : Type Δ ★} →
          
            (M : Term Δ Φ Γ (Π (τ R▹ υ))) →
            ----------------------------------------
            Term Δ Φ Γ (τ ▹ υ)
            
    -- Subsumption.
    t-≡ : ∀ { Δ : KEnv} {Φ : PEnv Δ} {Γ : Env Δ}
          {τ υ : Type Δ ★}  →
  
            (M : Term Δ Φ Γ τ) → τ ≡t υ →
            ----------------------------
            Term Δ Φ Γ υ
  
    -- Variant introduction.
    inj : ∀ {Δ : KEnv} {Γ : Env Δ} {Φ : PEnv Δ}
          {ρ₁ ρ₂ : Type Δ (R[ ★ ])} →
        
            (M : Term Δ Φ Γ (Σ ρ₁)) → (Ent Δ Φ (ρ₁ ≲ ρ₂)) →
            ----------------------------------------------
            Term Δ Φ Γ (Σ ρ₂)
  
    -- Singleton Record → Singleton.
    Σ : ∀ {Δ : KEnv} {Γ : Env Δ} {Φ : PEnv Δ}
          {τ : Type Δ (L )} {υ : Type Δ ★} →
          
            Term Δ Φ Γ (τ ▹ υ) →
            ---------------------
            Term Δ Φ Γ (Σ (τ R▹ υ))
            
    -- Singleton Variant → Singleton.
    Σ⁻¹ : ∀ {Δ : KEnv} {Γ : Env Δ} {Φ : PEnv Δ}
          {τ : Type Δ (L )} {υ : Type Δ ★} →
          
            (M : Term Δ Φ Γ (Σ (τ R▹ υ))) →
            ----------------------------------------
            Term Δ Φ Γ (τ ▹ υ)
             
    -- Variant elimination.
    _▿_ : ∀ {Δ : KEnv} {Γ : Env Δ} {Φ : PEnv Δ}
          {ρ₁ ρ₂ ρ₃ : Type Δ (R[ ★ ])} {τ : Type Δ ★} →
        
            Term Δ Φ Γ ((Σ ρ₁) `→ τ) →
            Term Δ Φ Γ ((Σ ρ₂) `→ τ) →
            Ent Δ Φ (ρ₁ · ρ₂ ~ ρ₃) →
            ------------------------------
            Term Δ Φ Γ ((Σ ρ₃) `→ τ)
             
    -- Synthesis.
    syn : ∀ {Δ : KEnv} {Γ : Env Δ} {Φ : PEnv Δ} {κ : Kind}
            {κ¹ : Kind¹ κ}
            (ρ : Type Δ R[ κ ]) →
            (φ : Type Δ (κ¹ `→ ★)) →
            Term Δ Φ Γ (SynT κ ρ φ) →
            --------------------------
            Term Δ Φ Γ (Π (⌈ φ ⌉· ρ))
  
    -- -- Analysis.
    ana : ∀ {Δ : KEnv} {Γ : Env Δ} {Φ : PEnv Δ} {κ : Kind}
            {κ¹ : Kind¹ κ}
            (ρ : Type Δ R[ κ ]) →
            (φ : Type Δ (κ¹ `→ ★)) →
            (τ : Type Δ ★) →
            Term Δ Φ Γ (AnaT κ ρ φ τ) →
            --------------------------
            Term Δ Φ Γ (Σ (⌈ φ ⌉· ρ) `→ τ)
  
    -- Fold.
    fold : ∀ {Δ : KEnv} {Γ : Env Δ} {Φ : PEnv Δ}
           {ρ : Type Δ R[ ★ ]} {υ : Type Δ ★} →
           (M₁ : Term Δ Φ Γ (FoldT ρ υ)) →
           (M₂ : Term Δ Φ Γ (υ `→ (υ `→ υ))) →
           (M₃ : Term Δ Φ Γ υ) →
           (N  : Term Δ Φ Γ (Π ρ)) →
           ------------------------
           Term Δ Φ Γ υ
  
  --------------------------------------------------------------------------------
  -- admissable rules.
  
  private
    variable
      Δ : KEnv
      Γ : Env Δ
      Φ : PEnv Δ
      κ : Kind
      Ł : Type Δ L
      τ : Type  Δ κ
  
  prj▹ : {ρ : Type Δ R[ ★ ]} →          
          Term Δ Φ Γ (Π ρ) → Ent Δ Φ ((Ł R▹ τ) ≲ ρ) →
          ------------------------------------------
          Term Δ Φ Γ (Ł ▹ τ)
  prj▹ r e = Π⁻¹ (prj r e)          
  
  inj▹ : {ρ : Type Δ R[ ★ ]} →          
          Term Δ Φ Γ (Ł ▹ τ) → Ent Δ Φ ((Ł R▹ τ) ≲ ρ) →
          ---------------------------------------------
          Term Δ Φ Γ (Σ ρ)
  inj▹ s e = inj (Σ s) e
  
