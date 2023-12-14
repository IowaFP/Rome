module Mix.Mix where

open import Preludes.Data
open import Data.List
open import Preludes.Relation

--------------------------------------------------------------------------------
-- Declare contexts and judgements.
-- (mutually recursive.)

data Sort : Set where
  ★ : Sort
  □ : Sort

private
  variable
    -- Todo: establish a better meta-naming convention to distinguish
    -- pre-terms denoting terms, pre-terms denoting types,
    -- intrinsic types, and intrinsic terms.
    σ σ' σ₁ σ₂ σ₃ : Sort

data Context : Set
data Type : Context → Sort → Set
data Term : (Γ : Context) → Type Γ σ  → Set

-- data _==_ : ∀ {σ : Sort M} → Type Γ σ → Type Γ σ → Set

-- open Pre.Term
-- open Pre.Sort

-- Context house assumptions 
data Context where
  ε : Context
  _,_ : (Γ : Context) → Type Γ σ → Context

private
  variable
    Γ Γ' : Context

weakenTy : ∀ {A : Type Γ σ₁} → 
         Type Γ σ₂ → Type (Γ , A) σ₂
weaken : ∀ {A : Type Γ σ₁} {B : Type Γ σ₂} → 
         Term Γ A → Term (Γ , B) (weakenTy A)

_β[_]t : ∀ {A : Type Γ σ₁} → 
         Type (Γ , A) σ₂ → Term Γ A → Type Γ σ₂
_β[_] : ∀ {A : Type Γ σ₁} {B : Type Γ σ₂} → 
          Term (Γ , A) (weakenTy B) → Term Γ A → Term Γ B

--------------------------------------------------------------------------------
-- Lookup 
infix 4 _∋_

-- N.b.: don't need type-level vars, but do need
-- "cascading" environments.
data _∋_ : ∀ (Γ : Context) → Type Γ σ → Set where

  Z : ∀ {A : Type Γ σ} →

      -----------
      (Γ , A) ∋ (weakenTy A)

  S : ∀ {A : Type Γ σ} {B : Type Γ σ'}
      → Γ ∋ A
      ------------------
    → (Γ , B) ∋ (weakenTy A)

-- -- --------------------------------------------------------------------------------
-- -- -- Typing judgements.

data Type where
  ★ : Type Γ □
--   --
  var : ∀ 
        {A : Type Γ σ}  →  Γ ∋ A →
        ---------------------------
        Type Γ σ
--   --
  ⊤ : (σ : Sort) → Type Γ σ
--   --
  Nat : {Γ : Context} → Type Γ ★
--   --
  Ix  : Term Γ Nat → Type Γ ★
--   --
  `∀ : 
       (A : Type Γ σ₁)   →   Type (Γ , A) σ₂ → 
       -------------------------------------------        
       Type Γ σ₂
  `∃ : 
       (A : Type Γ σ₁)   →   Type (Γ , A) σ₂ → 
       -------------------------------------------        
       Type Γ σ₂

  _Or_ : 
        Type Γ σ   →   Type Γ σ → 
        ---------------------------
        Type Γ σ

  _~_  : 
        Type Γ σ → Type Γ σ → 
        -----------------------
        Type Γ σ

_`→_ : Type Γ σ → Type Γ σ' → Type Γ σ'
A `→ B = `∀ A (weakenTy B)

_`×_ : Type Γ σ → Type Γ σ' → Type Γ σ'
A `× B = `∃ A (weakenTy B)

-- --------------------------------------------------------------------------------
-- -- Sanity-checking

idF : Type ε □
idF = `∀ ★ (var Z)

-- --------------------------------------------------------------------------------
-- -- Terms.

data Term where
  -- Variables.
  var : 
        {A : Type Γ σ}  →  Γ ∋ A →
        ---------------------------
        Term Γ A

  -- The unit.
  tt : 
       ------------
       Term Γ (⊤ σ)

  -- ℕ. (todo: natelim)
  Zero : 
       ------------
       Term Γ Nat

  Suc : 
        Term Γ Nat → 
        -------------
        Term Γ Nat

  -- Ix. (todo IxElim)
  FZero : ∀ {n} → 
          -------------
          Term Γ (Ix n)

  FSuc  : ∀ {n} → 
          Term Γ (Ix n) → 
          ------------------
          Term Γ (Ix (Suc n))
  ƛ⦅⦆   : 
          (A : Type Γ σ) → 
          -----------------------
          Term Γ ((Ix Zero) `→ A)

  -- `∀.
  `λ : 
         (A : Type Γ σ)   →   {B : Type (Γ , A) σ'}   →   (M : Term (Γ , A) B) →
         ------------------------------------------------------------------------
         Term Γ (`∀ A B)

  _·_ :
        {A : Type Γ σ}{B : Type (Γ , A) σ'} → 
        Term Γ (`∀ A B)   →   (N : Term Γ A) → 
        ---------------------------------------
        Term Γ (B β[ N ]t)

  -- ∃.
  ⟪_,_⟫ : 
            {A : Type Γ σ} → (m : Term Γ A) → {B : Type (Γ , A) σ'} → Term Γ (B β[ m ]t) →
            -------------------------------------------------------------------------------
            Term Γ (`∃ A B)

  Case_of⟪_⟫ : 
                 {A : Type Γ σ₁} {B : Type (Γ , A) σ₂} {C : Type Γ σ₃} →
               Term Γ (`∃ A B) → Term Γ (`∀ A (B `→ (weakenTy C))) → 
               -----------------------------------------------------
               Term Γ C

  -- Sums. todo elim.
  left : ∀ {A : Type Γ σ} {B : Type Γ σ} → 
         Term Γ A → 
         ---------------
         Term Γ (A Or B)

  right : ∀ {A : Type Γ σ} {B : Type Γ σ} → 
         Term Γ B → 
         --------------
         Term Γ (A Or B)

  -- Identity. Todo elim.
  Refl : ∀ {A : Type Γ σ} → 
         
         --------------
         Term Γ (A ~ A)

--------------------------------------------------------------------------------
-- Weakening & substitution.
-- (here likely be dragons.)

weakenTy ★ = ★
weakenTy (var x) = {!!}
weakenTy (⊤ σ) = ⊤ σ
weakenTy Nat = Nat
weakenTy (Ix x) = Ix (weaken x)
weakenTy (`∀ A B) = {!!}
weakenTy (`∃ A B) = {!!}
weakenTy (A Or B) = weakenTy A Or weakenTy B
weakenTy (A ~ B) = weakenTy A ~ weakenTy B

weaken m = {!!}

--------------------------------------------------------------------------------
-- Substitution.

★ β[ m ]t = ★
var x β[ m ]t = {!!}
⊤ σ β[ m ]t = ⊤ σ
Nat β[ m ]t = Nat
Ix x β[ m ]t = Ix {!!}
`∀ τ τ₁ β[ m ]t = {!!}
`∃ τ τ₁ β[ m ]t = {!!}
(A Or B) β[ m ]t = (A β[ m ]t) Or (B β[ m ]t) 
(A ~ B) β[ m ]t = (A β[ m ]t) ~ (B β[ m ]t)

_β[_] = {!!}

--------------------------------------------------------------------------------
-- Translation.

module Rμ where
 open import Rome.Kinds.Syntax public
 open import Rome.Types.Syntax public
 open import Rome.Terms.Syntax public
 open import Rome.Entailment.Syntax public

⟦_⟧σ : (κ : Rμ.Kind) → Sort
⟦ Rμ.★ ⟧σ = ★
⟦ Rμ.L ⟧σ = □
⟦ Rμ.R[ κ ] ⟧σ =  □
⟦ _ Rμ.`→ κ ⟧σ =  ⟦ κ ⟧σ

⟦_⟧κ : (κ : Rμ.Kind) → Type Γ □
⟦ Rμ.★ ⟧κ = ★
⟦ Rμ.L ⟧κ = ⊤ □
⟦ Rμ.R[ κ ] ⟧κ = `∃ Nat (`∀ (Ix (var Z)) ⟦ κ ⟧κ) 
⟦ κ₁ Rμ.`→ κ₂ ⟧κ = ⟦ κ₁ ⟧κ `→ ⟦ κ₂ ⟧κ

-- My spidey senses are tell me that the collapse of these envs
-- into one might make life a fucking nightmare.
⟦_∣_∣_⟧ : (Δ : Rμ.KEnv) → Rμ.PEnv Δ → Rμ.Env Δ → Context

⟦_⟧τ-L : ∀ {Δ : Rμ.KEnv} → Rμ.Type Δ Rμ.L →  Type ⟦ Δ ∣ Rμ.PEnv.ε ∣ Rμ.Env.ε ⟧ ★
⟦_⟧τ-★ : ∀ {Δ : Rμ.KEnv} {κ} → Rμ.Type Δ κ → Rμ.Star κ →  Type ⟦ Δ ∣ Rμ.PEnv.ε ∣ Rμ.Env.ε ⟧ ★
⟦_⟧τ-ρ : ∀ {Δ : Rμ.KEnv} {κ} → Rμ.Type Δ Rμ.R[ κ ] →  Term ⟦ Δ ∣ Rμ.PEnv.ε ∣ Rμ.Env.ε ⟧ ⟦ κ ⟧κ
⟦_⟧p : ∀ {Δ : Rμ.KEnv} {κ} → Rμ.Pred Δ κ → Type ⟦ Δ ∣ Rμ.PEnv.ε ∣ Rμ.Env.ε ⟧ ⟦ κ ⟧σ

⟦ Rμ.tvar x ⟧τ-L = {!!}
⟦ τ Rμ.·[ υ ] ⟧τ-L = {!!}
⟦ Rμ.lab l ⟧τ-L = ⊤ ★
⟦ _ Rμ.▹ τ ⟧τ-L = ⟦ τ ⟧τ-L

⟦ Δ ∣ Φ ∣ Γ ⟧ = {!!}
⟦ Rμ.U ⟧τ-★ s = ⊤ ★
⟦ Rμ.tvar x ⟧τ-★ s = {!!}
⟦ τ Rμ.`→ υ ⟧τ-★ s = ⟦ τ ⟧τ-★ Rμ.★ `→ ⟦ υ ⟧τ-★ Rμ.★
⟦ Rμ.`∀ κ τ ⟧τ-★ s = {!!}
⟦ Rμ.`λ κ₁ τ ⟧τ-★ s = {!!}
⟦ τ Rμ.·[ τ₁ ] ⟧τ-★ s = {!!}
⟦ Rμ.μ τ ⟧τ-★ s = {!!}
⟦ Rμ.ν τ ⟧τ-★ s = {!!}
⟦ π Rμ.⇒ τ ⟧τ-★ s = ⟦ π ⟧p `→ (⟦ τ ⟧τ-★ Rμ.★)
⟦ τ Rμ.▹ τ₁ ⟧τ-★ s = {!!}
⟦ Rμ.⌊ τ ⌋ ⟧τ-★ s = {!!}
⟦ Rμ.Π τ ⟧τ-★ s = {!!}
⟦ Rμ.Σ τ ⟧τ-★ s = {!!}

⟦ Rμ.tvar x ⟧τ-ρ = {!!}
⟦ τ Rμ.·[ τ₁ ] ⟧τ-ρ = {!!}
⟦ τ Rμ.▹ τ₁ ⟧τ-ρ = {!!}
⟦ τ Rμ.R▹ τ₁ ⟧τ-ρ = {!!}
⟦ Rμ.ε ⟧τ-ρ = {!!}
⟦ τ Rμ.·⌈ τ₁ ⌉ ⟧τ-ρ = {!!}
⟦ Rμ.⌈ τ ⌉· τ₁ ⟧τ-ρ = {!!}

⟦_⟧p = {!!} 

-- ⟦_⟧ : ∀ {Δ : Rμ.KEnv} {Φ : Rμ.PEnv Δ} {Γ : Rμ.Env Δ} {τ : Rμ.Type Δ Rμ.★} → 
--         Rμ.Term Δ Φ Γ τ → Term ⟦ Δ ∣ Φ ∣ Γ ⟧ ⟦ τ ⟧τ
-- ⟦ M ⟧ = {!!}

