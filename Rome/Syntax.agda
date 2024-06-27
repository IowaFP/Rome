module Rome.Syntax where

open import Preludes.Level
open import Preludes.Data
open import Preludes.Relation

open import Rome.Kinds
open import Rome.GVars.Levels


--------------------------------------------------------------------------------
-- infix OOP.

infixr 9 _`→_
infixr 9 _⇒_
infixr 10 _▹_
infixr 10 _R▹_
infixr 10 _≲_
infix 10 _·_~_
infixl 11 _·[_]

infix 12 ↑_ _↑

--------------------------------------------------------------------------------
-- Labels are Strings.

Label : Set
Label = String

--------------------------------------------------------------------------------
-- Types and type vars.

data Env : Level → Set 
data Pred : Env ℓ → (κ : Kind ι) → Set 
data Type : (Δ : Env ℓ) → Kind ι →  Set


data Ent  : {κ : Kind ℓ} → (Δ : Env ℓ) → Pred Δ κ → Set
data _≡p_ : {κ : Kind ℓ} {Δ : Env ℓ} → (π₁ π₂ : Pred Δ κ) → Set
data _≡t_ : ∀ {κ : Kind ℓ} {Δ : Env ℓ} → (τ υ : Type Δ κ) → Set

data Env where
  ε   : Env ℓ
  _،_ : Env ℓΔ → (Kind ℓκ) → Env (ℓΔ ⊔ ℓκ)
  _∶_ : {κ : Kind ℓκ} → (Δ : Env ℓΔ) →  Type Δ κ → Env (ℓΔ ⊔ ℓκ)
  _؛_ : {κ : Kind ℓκ} → (Δ : Env ℓΔ) → Pred Δ κ → Env (ℓΔ ⊔ ℓκ)

data TVar : Env ℓ → Kind ι → Set
data PVar : {κ : Kind ℓ} → (Δ : Env ℓ) → Pred Δ κ → Set
data Var  : {κ : Kind ℓ} → (Δ : Env ℓ) → Type Δ κ → Set

private
  variable
    Δ : Env ℓ
    κ κ₁ κ₂ κ₃ : Kind ℓκ

data TVar where
  Z : TVar (Δ ، κ) κ
  S : TVar Δ κ₁ → TVar (Δ ، κ₂) κ₁
  Sₜ : ∀ {κ : Kind ℓκ} → (Δ : Env ℓΔ) → {τ : Type Δ (★ ℓ)} →  TVar Δ κ → TVar (Δ ∶ τ) κ

--------------------------------------------------------------------------------
-- Predicates.

data Pred where
  _≲_ : ∀ {κ : Kind ι} →
          (ρ₁ : Type Δ R[ κ ]) →
          (ρ₂ : Type Δ R[ κ ]) →
          Pred Δ κ

  _·_~_ : ∀ {κ : Kind ι} →
            (ρ₁ : Type Δ R[ κ ]) →
            (ρ₂ : Type Δ R[ κ ]) →
            (ρ₃ : Type Δ R[ κ ]) →
            Pred Δ κ

-- -----------------------
-- -- Predicate variables.

-- data PVar where
--   Z : ∀ {Δ} {π : Pred Δ κ} →
--         PVar (Δ ؛ π) π

--   S : ∀ 
--         {π : Pred Δ κ₁} {ϕ : Pred Δ κ₂} →
--         PVar Δ π → PVar (Δ ؛ ϕ) π


--------------------------------------------------------------------------------

data Type where

  ------------------------------------------------------------
  -- System Fω.

  tvar :

         TVar Δ κ →
         -----------
         Type Δ κ

  _`→_ :
          Type Δ (★ ℓ₁) → Type Δ (★ ℓ₂) →
          -----------------------------------
          Type Δ (★ (ℓ₁ ⊔ ℓ₂))

  `∀ :
          (κ : Kind ℓκ) → Type (Δ ، κ) (★ ℓ) →
          -------------------------------------
          Type Δ (★ (ℓ ⊔ (lsuc ℓκ)))

  `λ :
          (κ₁ : Kind ℓκ₁) → Type (Δ ، κ₁) κ₂ →
          -----------------------------------------
          Type Δ (κ₁ `→ κ₂)

  _·[_] :
          Type Δ (κ₁ `→ κ₂) → Type Δ κ₁ →
          -----------------------------
          Type Δ κ₂

  ------------------------------------------------------------
  -- Qualified types.

  _⇒_ : ∀ {κ : Kind ℓκ} →
         (π : Pred Δ κ) → Type Δ (★ ℓ) →
         --------------------------------
         Type Δ (★ (lsuc ℓκ ⊔ ℓ))

  ------------------------------------------------------------
  -- System Rω.

  -- The empty row.
  ε : Type Δ R[ κ ]

  -- Row complement
  _─_ : 
        (ρ₂ : Type Δ R[ κ ]) → (ρ₁ : Type Δ R[ κ ]) →
        ---------------------------------------------
        Type Δ R[ κ ]


  -- Labels.
  lab :
        Label →
        ----------
        Type Δ (L ℓ)

  -- singleton formation.
  _▹_ :
        Type Δ (L ℓ) → Type Δ κ →
        -------------------
        Type Δ κ

  -- Row singleton formation.
  _R▹_ :
         Type Δ (L ℓ) → Type Δ κ →
         ---------------------------
         Type Δ R[ κ ]

  -- label constant formation.
  ⌊_⌋ :
        Type Δ (L ℓ) →
        ----------
        Type Δ (★ ℓ)

  -- Record formation.
  Π :
      Type Δ R[ κ ] →
      -------------
      Type Δ  κ

  -- Variant formation.
  Σ :
      Type Δ R[ κ ] →
      -------------
      Type Δ κ

  -- Lifting/mapping operations... I claim the kinds are at least
  -- self-evident now, even if the placement of arrows is a little bit
  -- arbitrary...

  ↑_ : {κ₁ : Kind ℓ₁} {κ₂ : Kind ℓ₂} →
       Type Δ R[ κ₁ `→ κ₂ ] →
       ------------------------------
       Type Δ (κ₁ `→ R[ κ₂ ])


  _↑ : {κ₁ : Kind ℓ₁} {κ₂ : Kind ℓ₂} →
       Type Δ (κ₁ `→ κ₂) →
       ------------------------------
       Type Δ (R[ κ₁ ] `→ R[ κ₂ ])

  ------------------------------------------------------------
  -- System Rωμ.

  -- μ formation.
  μ : ∀ {ℓ} →
      (τ : Type Δ ((★ ℓ) `→ (★ ℓ))) →
      -----------------------------------------------
      Type Δ (★ ℓ)


ex : ∀ {ℓ} → Env ℓ
ex {ℓ} = (((ε ∶ (lab "s")) ، R[ ★ ℓ ]) ؛ (tvar Z  ≲ tvar Z)) ؛ ({!!} ≲ {!!}) -- (tvar Z  ≲ tvar Z)
