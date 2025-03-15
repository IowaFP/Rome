{-# OPTIONS --allow-unsolved-metas #-}
module Rome.Operational.Terms.Syntax where

open import Rome.Operational.Prelude
open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

open import Rome.Operational.Types.Syntax

open import Rome.Operational.Types.Equivalence

open import Rome.Operational.Types.Normal.Syntax
open import Rome.Operational.Types.Normal.Renaming
open import Rome.Operational.Types.Normal.Substitution
open import Rome.Operational.Types.Normal.Properties.Substitution
open import Rome.Operational.Types.Semantic.NBE

open import Rome.Operational.Types.Theorems.Soundness
open import Rome.Operational.Types.Theorems.Completeness
open import Rome.Operational.Types.Theorems.Stability

--------------------------------------------------------------------------------
-- First define contexts mapping variables to predicates, types, and kinds

data Context : KEnv → Set where
  ∅ : Context ∅
  _,_  : Context Δ → NormalType Δ ★ → Context Δ
  _,,_ : Context Δ → (κ : Kind) → Context (Δ ,, κ)
  _,,,_ : Context Δ → NormalPred Δ R[ κ ] → Context Δ

private
  variable
    Γ Γ₁ Γ₂ Γ₃ : Context Δ
    τ υ τ₁ τ₂  : NormalType Δ ★
    l l₁ l₂    : NormalType Δ L
    ρ ρ₁ ρ₂ ρ₃ : NormalType Δ R[ κ ]
    π π₁ π₂ π₃ : NormalPred Δ R[ κ ]
    

data PVar : Context Δ → NormalPred Δ κ → Set where
  Z : PVar (Γ ,,, π) π
  S : PVar Γ π₁  → PVar (Γ ,,, π₂) π₁
  T : PVar Γ π → PVar (Γ , τ) π
  K : PVar Γ π → PVar (Γ ,, κ₂) (weakenPredₖNF π)

data Var : Context Δ → NormalType Δ ★ → Set where
  Z : Var (Γ , τ) τ
  S : Var Γ τ₁  → Var (Γ , τ₂) τ₁
  K : Var Γ τ → Var (Γ ,, κ) (weakenₖNF τ)
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
noPVar : NoVar Γ → ∀ {π : NormalPred Δ R[ κ ]}(x : PVar Γ π) → ⊥
noPVar p (K x) = noPVar p x

--------------------------------------------------------------------------------
-- Entailment relation on predicates 

-- private
--   variable 
--       l l₁ l₂ l₃ : NormalType Δ L 
--       τ τ₁ τ₂ τ₃ : NormalType Δ κ 
--       υ υ₁ υ₂ υ₃ : NormalType Δ κ 
      
data Ent (Γ : Context Δ) : NormalPred Δ R[ κ ] → Set where 
  n-var : 
        PVar Γ π → 
        -----------
        Ent Γ π 

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
        Ent Γ (ρ · ε ~ ρ)

  n-ε-L : 

        -------------------------
        Ent Γ (ε · ρ ~ ρ)  

  n-≲lift : ∀ {ρ₁ ρ₂ : NormalType Δ R[ κ₁ ]}
               {F : NormalType Δ (κ₁ `→ κ₂)} →

             Ent Γ (ρ₁ ≲ ρ₂) →
             {x y : NormalType Δ R[ κ₂ ]} → 
             x ≡ (F <$>' ρ₁) → 
             y ≡ F <$>' ρ₂ → 
             ---------------------------------
             Ent Γ (x ≲ y)


  n-·lift : ∀ {ρ₁ ρ₂ ρ₃ : NormalType Δ R[ κ₁ ]}
               
               {F : NormalType Δ (κ₁ `→ κ₂)} →

             Ent Γ (ρ₁ · ρ₂ ~ ρ₃) →
             {x y z : NormalType Δ R[ κ₂ ]} → 
             x ≡ (F <$>' ρ₁) → 
             y ≡ F <$>' ρ₂ → 
             z ≡ F <$>' ρ₃ → 
             ---------------------------------
             Ent Γ (x · y ~ z)

--------------------------------------------------------------------------------
-- Terms with normal types


data Term {Δ} Γ : NormalType Δ ★ → Set where
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
      Term Γ (`∀ κ τ)

  _·[_] : ∀ {τ₂} → 
  
          Term Γ (`∀ κ τ₂) →
          (τ₁ : NormalType Δ κ) → 
          ----------------
          Term Γ (τ₂ βₖNF[ τ₁ ])

  ------------------
  -- Recursive types

  In : 
         ∀ (F : NormalType Δ (★ `→ ★)) → 
         Term Γ (F ·' (μ F)) → 
         -----------------
         Term Γ (μ F)

  Out : 
           ∀ F → 
           Term Γ (μ F) → 
           --------------
           Term Γ (F ·' (μ F))

  ------------------
  -- Qualified types

  `ƛ : 

       Term (Γ ,,, π) τ → 
       --------------
       Term Γ (π ⇒ τ)

  _·⟨_⟩ : ∀ {π : NormalPred Δ R[ κ ]} {τ : NormalType Δ ★} → 
  
        Term Γ (π ⇒ τ) →
        Ent Γ π → 
        ----------------
        Term Γ τ

  ------------
  -- Rω labels

  -- label constants
  # : 

        ∀ (l : NormalType Δ L) →
        -------------------
        Term Γ ⌊ l ⌋

  -------------
  -- Rω records

  -- Record singleton formation
  _Π▹_ : 
          (M₁ : Term Γ ⌊ l ⌋) (M₂ : Term Γ υ) →
          ----------------------------------------
          Term Γ (Π (l ▹ υ))

  -- Record singleton elimination
  _Π/_ :
          (M₁ : Term Γ (Π (l ▹ υ))) (M₂ : Term Γ ⌊ l ⌋) →
          ----------------------------------------
          Term Γ υ

  prj : 
   
       (M : Term Γ (Π ρ₂)) → Ent Γ (ρ₁ ≲ ρ₂) → 
       -------------------------------------
       Term Γ (Π ρ₁)

  --------------
  -- Rω variants

  -- Record singleton formation
  _Σ▹_ : 
          (M₁ : Term Γ ⌊ l ⌋) (M₂ : Term Γ υ) →
          ----------------------------------------
          Term Γ (Σ (l ▹ υ))

  -- Record singleton elimination
  _Σ/_ :
          (M₁ : Term Γ (Σ (l ▹ υ))) (M₂ : Term Γ ⌊ l ⌋) →
          ----------------------------------------
          Term Γ υ

  inj : 
   
       (M : Term Γ (Σ ρ₁)) → Ent Γ (ρ₁ ≲ ρ₂) → 
       -------------------------------------
       Term Γ (Σ ρ₁)


--------------------------------------------------------------------------------
-- Conversion helpers.

convVar : ∀ {Γ} {τ₁ τ₂ : NormalType Δ ★} → τ₁ ≡ τ₂ → Var Γ τ₁ → Var Γ τ₂
convVar refl v = v

convPVar : ∀ {Γ} {π₁ π₂ : NormalPred Δ R[ κ ]} → π₁ ≡ π₂ → PVar Γ π₁ → PVar Γ π₂
convPVar refl v = v

conv : ∀ {Γ} {τ₁ τ₂ : NormalType Δ ★} → τ₁ ≡ τ₂ → Term Γ τ₁ → Term Γ τ₂
conv refl M = M

convEnt : ∀ {Γ} {π₁ π₂ : NormalPred Δ R[ κ ]} → π₁ ≡ π₂ → Ent Γ π₁ → Ent Γ π₂
convEnt refl e = e

conv-≡t : ∀ {Γ} {τ₁ τ₂ : Type Δ ★} → τ₁ ≡t τ₂ → Term Γ (⇓ τ₁) → Term Γ (⇓ τ₂)
conv-≡t eq = conv (completeness eq)

--------------------------------------------------------------------------------
-- Admissable constants

♯l : Term Γ (⌊ lab "l" ⌋)
♯l = # (lab "l")

-- Unit term
uu : Term Γ UnitNF
uu = prj (♯l Π▹ ♯l) (n-·≲L n-ε-L)

--------------------------------------------------------------------------------
-- Monoidal properties of entailment

·-impossible :  ∀ {l₁ l₂ l₃ : NormalType ∅ L} {τ₁ τ₂ τ₃ :  NormalType ∅ κ} → Ent ∅ ((l₁ ▹ τ₁) · (l₂ ▹ τ₂) ~ (l₃ ▹ τ₃)) → ⊥ 
·-impossible  (n-·lift {ρ₁ = l₁ ▹ τ₁} {l₂ ▹ τ₂} {l₃ ▹ τ₃} e x x₁ x₂) = ·-impossible e

refl-inversion : ∀ (ρ :  NormalType ∅ R[ κ ]) → Ent ∅ (ρ ≲ ρ) → ρ ≡ ρ
refl-inversion (ne x) e = ⊥-elim (noNeutrals x)
refl-inversion ε e = refl
refl-inversion (l ▹ τ) e = refl 

ε-sum : Ent ∅ (ρ₁ · ρ₂ ~ ε) → ρ₁ ≡ ε × ρ₂ ≡ ε 
ε-sum (n-var ())
ε-sum n-ε-R = refl , refl
ε-sum n-ε-L = refl , refl
ε-sum {ρ₁ = ρ₁} {ρ₂ = ρ₂} (n-·lift {ρ₁ = ne x} {ρ₄} {ε} e ρ₁-eq ρ₂-eq ρ₃-eq) = ⊥-elim (noNeutrals x)
ε-sum {ρ₁ = ρ₁} {ρ₂ = ρ₂} (n-·lift {ρ₁ = ε} {ne x} {ε} e ρ₁-eq ρ₂-eq ρ₃-eq) = ⊥-elim (noNeutrals x)
ε-sum {ρ₁ = ρ₁} {ρ₂ = ρ₂} (n-·lift {ρ₁ = ε} {ε} {ε} e ρ₁-eq ρ₂-eq ρ₃-eq) = ρ₁-eq , ρ₂-eq
ε-sum {ρ₁ = ρ₁} {ρ₂ = ρ₂} (n-·lift {ρ₁ = ε} {l ▹ τ} {ε} e ρ₁-eq ρ₂-eq ρ₃-eq) with ε-sum e 
... | () 
ε-sum {ρ₁ = ρ₁} {ρ₂ = ρ₂} (n-·lift {ρ₁ = ρ₃ ▹ ρ₅} {ρ₄} {ε} e ρ₁-eq ρ₂-eq ρ₃-eq) with ε-sum e 
... | ()

ε-minimum :  Ent ∅ (ρ ≲ ε) → ρ ≡ ε
ε-minimum (n-var ())
ε-minimum n-refl = refl
ε-minimum (n-trans e e₁) rewrite ε-minimum e₁ = ε-minimum e -- rewrite ε-minimum p e₁ = ε-minimum p e
ε-minimum (n-·≲L e) =  fst (ε-sum e)
ε-minimum (n-·≲R e) = snd (ε-sum e)
ε-minimum {ρ = ρ} (n-≲lift {ρ₁ = ne x₁} {ε} {F} e x y) = ⊥-elim (noNeutrals x₁) -- trans x {! x₁  !}
ε-minimum {ρ = ρ} (n-≲lift {ρ₁ = ε} {ε} {F} e x y) = x
ε-minimum {ρ = ρ} (n-≲lift {ρ₁ = l ▹ τ} {ε} {f} e x y) with ε-minimum e
... | () 

ε-right-unique : Ent ∅ (ρ₁ · ρ₂ ~ ρ₁) → ρ₂ ≡ ε
ε-right-unique {ρ₁ = ρ₁} {ρ₂} n-ε-R = refl
ε-right-unique {ρ₁ = ρ₁} {ρ₂} n-ε-L = refl
ε-right-unique {ρ₁ = ne x} {_} (n-·lift e _ _ _) = ⊥-elim (noNeutrals x)
ε-right-unique {ρ₁ = _} {ne x} (n-·lift e _ _ _ ) = ⊥-elim (noNeutrals x)
ε-right-unique {ρ₁ = ε} {ε} (n-·lift e x x₁ x₂) = refl
ε-right-unique {ρ₁ = ε} {l ▹ τ} (n-·lift {ρ₁ = ε} {ρ₂ = l' ▹ τ'} {ε} {F = `λ F} e x x₁ x₂) with ε-right-unique e
... | () 
ε-right-unique {ρ₁ = ρ₁ ▹ ρ₂} {ε} (n-·lift e x x₁ x₂) = refl
ε-right-unique {ρ₁ = l₁ ▹ τ₁} {l₂ ▹ τ₂} (n-·lift {ρ₁ = l₃ ▹ τ₃} {ρ₂ ▹ ρ₃} {l₄ ▹ τ₄} e x x₁ x₂) = ⊥-elim (·-impossible e) 

≲-refl :  ∀ (l₁ l₂ : NormalType ∅ L) (τ₁ τ₂ :  NormalType ∅ κ) → Ent ∅ ((l₁ ▹ τ₁) ≲ (l₂ ▹ τ₂)) → (l₁ ▹ τ₁) ≡ (l₂ ▹ τ₂)
ε-right-identity : Ent ∅ (ρ₁ · ε ~ ρ₂) → ρ₁ ≡ ρ₂
ε-left-identity : Ent ∅ (ε · ρ₁ ~ ρ₂) → ρ₁ ≡ ρ₂

ε-right-identity n-ε-R = refl
ε-right-identity n-ε-L = refl
ε-right-identity (n-·lift {ρ₁ = ne x₃} {ρ₂ = ε} e x x₁ x₂) = ⊥-elim (noNeutrals x₃)
ε-right-identity {ρ₁ = ε} {ρ₂ = ne x₃} (n-·lift {ρ₁ = ε} {ρ₂ = ε} {ρ₃} e x x₁ x₂) = ⊥-elim (noNeutrals x₃)
ε-right-identity {ρ₁ = ε} {ρ₂ = ε} (n-·lift {ρ₁ = ε} {ρ₂ = ε} {ρ₃} e x x₁ x₂) = refl
ε-right-identity {ρ₁ = ε} {ρ₂ = ρ₂ ▹ ρ₄} (n-·lift {ρ₁ = ε} {ρ₂ = ε} {ρ₃ ▹ ρ₅} e x x₁ x₂) with ε-right-identity e
... | () 
ε-right-identity {ρ₁ = ρ₁ ▹ ρ₂} {ne x₃} (n-·lift {ρ₁ = l ▹ τ} {ρ₂ = ε} e x x₁ x₂) = ⊥-elim (noNeutrals x₃)
ε-right-identity {ρ₁ = l₁ ▹ τ₁} {ε} (n-·lift {ρ₁ = l ▹ τ} {ρ₂ = ε} e x x₁ x₂) with trans (ε-right-identity e) (ε-<$>' (sym x₂))
... | () 
ε-right-identity {ρ₁ = l₁ ▹ τ₁} {l₂ ▹ τ₂} (n-·lift {ρ₁ = l₃ ▹ τ₃} {ρ₂ = ε} {l₄ ▹ τ₄} {F} e x x₁ x₂) = 
  trans x (trans (cong₂ _▹_ (inj-▹ₗ (ε-right-identity e)) (cong (F ·'_) (inj-▹ᵣ (ε-right-identity e)))) (sym x₂))


ε-left-identity e = {!   !} 



≲-refl l₁ l₂ τ υ (n-var ())
≲-refl l₁ l₂ τ υ n-refl = refl
≲-refl l₁ l₂ τ υ (n-trans {ρ₂ = ne x} e e₁) = ⊥-elim (noNeutrals x) 
≲-refl l₁ l₂ τ υ (n-trans {ρ₂ = ε} e e₁) with ε-minimum e
... | () 
≲-refl l₁ l₃ τ₁ τ₃ (n-trans {ρ₂ = l₂ ▹ τ₂} e e₁) = trans (≲-refl l₁ l₂ τ₁ τ₂ e) (≲-refl l₂ l₃ τ₂ τ₃ e₁)
≲-refl l₁ l₂ τ υ (n-·≲L {ρ₂ = ne x} e) = ⊥-elim (noNeutrals x)
≲-refl l₁ l₂ τ υ (n-·≲L {ρ₂ = ε} e) = ε-right-identity e
≲-refl l₁ l₂ τ₁ τ₂ (n-·≲L {ρ₂ = l₃ ▹ τ₃} e) = ⊥-elim (·-impossible e)  
≲-refl l₁ l₂ τ υ (n-·≲R {ρ₁ = ne x} e) = ⊥-elim (noNeutrals x)
≲-refl l₁ l₂ τ υ (n-·≲R {ρ₁ = ε} e) = ε-left-identity e
≲-refl l₁ l₂ τ₁ τ₂ (n-·≲R {ρ₁ = l₃ ▹ τ₃} e) = ⊥-elim (·-impossible e) 
≲-refl l₁ l₂ τ₁ τ₂ (n-≲lift {ρ₁ = l₃ ▹ τ₃} {l₄ ▹ τ₄} {F} e x x₁) = 
  trans 
    x 
    (trans 
      (cong₂ _▹_ 
        (inj-▹ₗ (≲-refl _ _ _ _ e)) 
        (cong (F ·'_) (inj-▹ᵣ (≲-refl _ _ _ _ e)))) 
      (sym x₁))     