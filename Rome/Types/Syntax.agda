{-# OPTIONS --allow-unsolved-metas #-}
module Rome.Types.Syntax where

open import Preludes.Level
open import Preludes.Data
open import Preludes.Relation

open import Rome.GVars.Kinds
open import Rome.Kinds.Syntax


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

data Pred : (Δ : KEnv ℓ) → (κ : Kind ι) → Set 
data PEnv : KEnv ℓ → Level → Set 
data Type : (Δ : KEnv ℓ) → Kind ι →  Set


data TVar : KEnv ℓ → Kind ι → Set where
  Z : TVar (Δ ، κ) κ
  S : TVar Δ κ₁ → TVar (Δ ، κ₂) κ₁

S² : TVar Δ κ → TVar (Δ ، κ₁ ، κ₂) κ
S³ : TVar Δ κ → TVar (Δ ، κ₁ ، κ₂ ، κ₃) κ
S⁴ : TVar Δ κ → TVar (Δ ، κ₁ ، κ₂ ، κ₃ ، κ₄) κ
S⁵ : TVar Δ κ → TVar (Δ ، κ₁ ، κ₂ ، κ₃ ، κ₄ ، κ₅) κ

S² x = S (S x)
S³ x = S (S² x)
S⁴ x = S (S³ x)
S⁵ x = S (S⁴ x)

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

--------------------------------------
-- Predicate Environments & weakening.

data PEnv where
  ε : PEnv Δ lzero
  _,_ : {κ : Kind ℓκ} →
        PEnv Δ ℓΦ → Pred Δ κ → PEnv Δ (ℓΦ ⊔ ℓκ)
  _؛_  : {κ : Kind ℓκ} →
         PEnv Δ ℓΦ → (κ : Kind ι) → PEnv (Δ ، κ) (ℓΦ ⊔ ℓκ)

-----------------------
-- Predicate variables.

data PVar : PEnv Δ ℓΦ → Pred Δ κ → Set where
  Z : ∀ {Φ : PEnv Δ ℓΦ} {π : Pred Δ κ} →
        PVar (Φ , π) π

  S : ∀ {Φ : PEnv Δ ℓΦ}
        {π : Pred Δ κ₁} {ϕ : Pred Δ κ₂} →
        PVar Φ π → PVar (Φ , ϕ) π


--------------------------------------------------------------------------------
-- Types.

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
