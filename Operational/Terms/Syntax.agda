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
          Ent Γ ((l ▹ τ) ≲ (l ▹ τ))

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
             ---------------------------------
             Ent Γ (⇓ (⇑ F <$> ⇑ ρ₁) ≲ ⇓ (⇑ F <$> ⇑ ρ₂))


  n-·lift : ∀ {ρ₁ ρ₂ ρ₃ : NormalType Δ R[ κ₁ ]}
               
               {F : NormalType Δ (κ₁ `→ κ₂)} →

             Ent Γ (ρ₁ · ρ₂ ~ ρ₃) →
             ---------------------
             Ent Γ (⇓ (⇑ F <$> ⇑ ρ₁) · ⇓ (⇑ F <$> ⇑ ρ₂) ~ ⇓ (⇑ F <$> ⇑ ρ₃))


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

        ∀ (l : Label) →
        -------------------
        Term Γ ⌊ lab l ⌋

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

-- Unit term
uu : Term Γ UnitNF
uu = prj ((# "l") Π▹ (# "l")) (n-·≲L n-ε-L)

--------------------------------------------------------------------------------
-- Properties of entailment

-- ε-unique-· : NoVar Γ → Ent Γ (ρ₁ · ρ₂ ~ ε) → ρ₁ ≡ ε × ρ₂ ≡ ε 
-- ε-unique-· p (n-var x) = ⊥-elim (noPVar p x)
-- ε-unique-· p n-ε-R = refl , refl
-- ε-unique-· p n-ε-L = refl , refl
-- ε-unique-· {ρ₁ = ρ₁} {ρ₂ = ρ₂} p (n-·lift {ρ₁ = ρ₃} {ρ₄} {ρ₅} e ρ₁-eq ρ₂-eq ρ₃-eq) = {!   !}

-- -- I suspect this isn't true in general, but rather w.r.t. ≡t
-- ε-unique-≲ : NoVar Γ → Ent Γ (ρ ≲ ε) → (⇑ ρ) ≡t ε
-- ε-unique-≲ p (n-var x) = ⊥-elim (noPVar p x)
-- ε-unique-≲ p n-refl = eq-refl
-- ε-unique-≲ p (n-trans e e₁) = {!   !} -- ewrite ε-unique-≲ p e₁ = ε-unique-≲ p e
-- ε-unique-≲ p (n-·≲L e) = {!   !} -- fst (ε-unique-· p e)
-- ε-unique-≲ p (n-·≲R e) = {!   !} -- snd (ε-unique-· p e)
-- ε-unique-≲ {ρ = ρ} p (n-≲lift {ρ₁ = ρ₁} {ρ₂} {F} e x y) with trans x (sym (stability-<$> F ρ₁)) | trans y (sym (stability-<$> F ρ₂))
-- ε-unique-≲ {ρ = ne x₁} p (n-≲lift {ρ₁ = ne x₂} {ε} {F} e x y) | c | d  = {!   !} -- eq-trans {! inst {τ₁ = ⇑NE x₁} {τ₂ = ⇑ F <$> ⇑NE x₂}   !} {! c  !}
-- ε-unique-≲ {ρ = ε} p (n-≲lift {ρ₁ = ρ₁} {ε} {F} e x y) | c | d = {!   !}
-- ε-unique-≲ {ρ = ρ ▹ ρ₂} p (n-≲lift {ρ₁ = ρ₁} {ε} {F} e x y) | c | d = {!   !}

-- ≲-refl : NoVar Γ → ∀ (l₁ l₂ : NormalType Δ L) (τ υ :  NormalType Δ R[ κ ]) → Ent Γ ((l₁ ▹ τ) ≲ (l₂ ▹ υ)) → (l₁ ▹ τ) ≡ (l₂ ▹ υ)
-- ≲-refl p l₁ l₂ τ υ (n-var x) = ⊥-elim (noPVar p x)
-- ≲-refl p l₁ l₂ τ υ n-refl = refl
-- ≲-refl p l₁ l₂ τ υ (n-trans {ρ₂ = ne x} e e₁) = {!   !} 
-- ≲-refl p l₁ l₂ τ υ (n-trans {ρ₂ = ε} e e₁) = {!   !}
-- ≲-refl p l₁ l₃ τ₁ τ₃ (n-trans {ρ₂ = l₂ ▹ τ₂} e e₁) = trans (≲-refl p l₁ l₂ τ₁ τ₂ e) (≲-refl p l₂ l₃ τ₂ τ₃ e₁)
-- ≲-refl p l₁ l₂ τ υ (n-·≲L e) = {!   !}  
-- ≲-refl p l₁ l₂ τ υ (n-·≲R e) = {!   !}
-- -- ≲-refl p l₁ l₂ τ υ (n-≲lift e x y) = {!   !} 

-- _<$>E_ :  ∀ {ρ₁ ρ₂ : NormalType Δ R[ κ₁ ]}
--             (F : NormalType Δ (κ₁ `→ κ₂)) →
--             Ent Γ (ρ₁ ≲ ρ₂) → 
--             ---------------------------------
--             Ent Γ (F <$>' ρ₁ ≲ F <$>' ρ₂)
-- _<$>E_ {ρ₁ = ρ₁} {ρ₂} F en@(n-var x) = {! convEnt   !}
-- _<$>E_ {ρ₁ = ρ₁} {ρ₂} F n-refl = {!   !}
-- _<$>E_ {ρ₁ = ρ₁} {ρ₂} F (n-trans e e₁) = {!   !}
-- _<$>E_ {ρ₁ = ρ₁} {ρ₂} F (n-·≲L e) = {!   !}
-- _<$>E_ {ρ₁ = ρ₁} {ρ₂} F (n-·≲R e) = {!   !}
  