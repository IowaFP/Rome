module Rome.Operational.Types.Syntax where

open import Rome.Operational.Prelude
open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

open import Data.List.Membership.DecPropositional (_≟_) using (_∈_ ; _∈?_ ; _∉_ ; _∉?_) public


--------------------------------------------------------------------------------
-- Types


infixl 5 _·_
infixr 5 _≲_
data Pred (Ty : KEnv → Kind → Set) Δ : Kind → Set
data Type Δ : Kind → Set 
data SimpleRow (Ty : KEnv → Kind → Set) Δ : Kind → Set
       

--------------------------------------------------------------------------------
-- Simple rows
--
-- Simple rows are indexed by an abstract Ty : KEnv → Kind → Set
-- so that they can be reused later by NormalType.

labels : ∀ {Ty : KEnv → Kind → Set} → SimpleRow Ty Δ R[ κ ] → List Label 

noDuplicate :  ∀ {Ty : KEnv → Kind → Set} → Label → SimpleRow Ty Δ R[ κ ] → Set
noDuplicate ℓ ρ = True (ℓ ∉? labels ρ)

MereProp : ∀ (A : Set) → Set 
MereProp A = (p₁ p₂ : A) → p₁ ≡ p₂

noDuplicateMereProp : ∀ {Ty : KEnv → Kind → Set} (ℓ : Label) → (ρ : SimpleRow Ty Δ R[ κ ]) → 
                      MereProp (True (ℓ ∉? labels ρ))
noDuplicateMereProp ℓ ρ p₁ p₂ with ℓ ∈? labels ρ 
... | yes p = refl                      
... | no  p = refl                      

infixr 0 _▹_⸴_
data SimpleRow Ty Δ where 
       _▹_ : 
              (ℓ : Label) → (τ : Ty Δ κ)  → 
              ------------------------
              SimpleRow Ty Δ R[ κ ]

       _▹_⸴_ : ∀ (ℓ : Label) → 
                  (τ : Ty Δ κ) →
                  (ρ : SimpleRow Ty Δ R[ κ ]) → {noDup : True (ℓ ∉? labels ρ)} → 
                  ----------------------------------------------- 
                  SimpleRow Ty Δ R[ κ ]

labels (ℓ ▹ τ) = ℓ ∷ []
labels (ℓ ▹ τ ⸴ ρ) = ℓ ∷ labels ρ 


-- It is easy to show that mapping preserves labels, but won't be possible to *use* mapSimpleRow
-- without violating termination checking.
mapSimpleRow : ∀ {Ty : KEnv → Kind → Set} → 
                 (f : Ty Δ₁ κ₁ → Ty Δ₂ κ₂)  → 
                 SimpleRow Ty Δ₁ R[ κ₁ ] → SimpleRow Ty Δ₂ R[ κ₂ ]
labelsFixedByMap : ∀ {Ty : KEnv → Kind → Set} → 
                     (f : Ty Δ₁ κ₁ → Ty Δ₂ κ₂) → 
                     (sr : SimpleRow Ty Δ₁ R[ κ₁ ]) → 
                     labels (mapSimpleRow f sr) ≡ labels sr

mapSimpleRow f (ℓ ▹ τ) = ℓ ▹ (f τ)
mapSimpleRow f ((ℓ ▹ τ ⸴ ρ) {noDup}) = 
       (ℓ ▹ (f τ) ⸴ mapSimpleRow f ρ) 
       {subst 
         (λ x → True (ℓ ∉? x)) 
         (sym (labelsFixedByMap f ρ)) 
         noDup}
labelsFixedByMap f (ℓ ▹ τ) = refl
labelsFixedByMap f (ℓ ▹ τ ⸴ ρ) rewrite labelsFixedByMap f ρ = refl

--------------------------------------------------------------------------------
-- Predicates

data Pred Ty Δ where
  _·_~_ : 

       (ρ₁ ρ₂ ρ₃ : Ty Δ R[ κ ]) → 
       --------------------- 
       Pred Ty Δ R[ κ ]

  _≲_ : 

       (ρ₁ ρ₂ : Ty Δ R[ κ ]) →
       ----------
       Pred Ty Δ R[ κ ]  
       
data Type Δ where

  ` : 
      (α : KVar Δ κ) →
      --------
      Type Δ κ

  `λ : 
      
      (τ : Type (Δ ,, κ₁) κ₂) → 
      ---------------
      Type Δ (κ₁ `→ κ₂)

  _·_ : 
      
      (τ₁ : Type Δ (κ₁ `→ κ₂)) → 
      (τ₂ : Type Δ κ₁) → 
      ----------------
      Type Δ κ₂

  _`→_ : 

         (τ₁ : Type Δ ★) →
         (τ₂ : Type Δ ★) → 
         --------
         Type Δ ★

  `∀    :
      
         {κ : Kind} → (τ : Type (Δ ,, κ) ★) →
         -------------
         Type Δ ★

  μ     :
      
         (φ : Type Δ (★ `→ ★)) → 
         -------------
         Type Δ ★

  ------------------------------------------------------------------
  -- Qualified types

  _⇒_ : 

         (π : Pred Type Δ R[ κ₁ ]) → (τ : Type Δ ★) → 
         ---------------------
         Type Δ ★       


  ------------------------------------------------------------------
  -- Rω business

  ⦅_⦆ : SimpleRow Type Δ R[ κ ] → 
        ----------------------
        Type Δ R[ κ ]

  -- labels
  lab :
    
        (l : Label) → 
        --------
        Type Δ L

  -- label constant formation
  ⌊_⌋ :
        (τ : Type Δ L) →
        ----------
        Type Δ ★

  ε : 

    ------------
    Type Δ R[ κ ]

  -- Row formation
  _▹_ :
         (l : Type Δ L) → (τ : Type Δ κ) → 
         -------------------
         Type Δ R[ κ ]

  _<$>_ : 

       (φ : Type Δ (κ₁ `→ κ₂)) → (τ : Type Δ R[ κ₁ ]) → 
       ----------------------------------------
       Type Δ R[ κ₂ ]

  -- Record formation
  Π     :

          ----------------
          Type Δ (R[ κ ] `→ κ)

  -- Variant formation
  Σ     :

          ----------------
          Type Δ (R[ κ ] `→ κ)


--------------------------------------------------------------------------------
-- Type constant smart-ish constructors

-- Record formation
`Π : Type Δ R[ κ ] → Type Δ κ 
`Π τ = Π · τ 

-- Variant formation
`Σ : Type Δ R[ κ ] → Type Δ κ 
`Σ τ = Σ · τ 

--------------------------------------------------------------------------------
-- Admissable constants

-- for partial application of infix fmap.
`↑ : Type Δ ((κ₁ `→ κ₂) `→ R[ κ₁ ] `→ R[ κ₂ ])
`↑ = `λ (`λ (` (S Z) <$> ` Z))

-- Flapping. See https://hoogle.haskell.org/?hoogle=f%20(a%20-%3E%20b)%20-%3E%20a%20-%3E%20f%20b%20
flap : Type Δ (R[ κ₁ `→ κ₂ ] `→ κ₁ `→ R[ κ₂ ])
flap = `λ (`λ ((`λ ((` Z) · (` (S Z)))) <$> (` (S Z))))

_??_ : Type Δ (R[ κ₁ `→ κ₂ ]) → Type Δ κ₁ → Type Δ R[ κ₂ ]
f ?? a = flap · f · a

Unit : Type Δ ★
Unit = Π · ε

-- Example simple row
sr : Type Δ R[ ★ ] 
sr = ⦅ "a" ▹ Unit ⸴ "b" ▹ (Σ · ε) ⸴ "c" ▹ ((`λ (` Z)) · Unit) ⸴ "d" ▹ Unit ⦆
  