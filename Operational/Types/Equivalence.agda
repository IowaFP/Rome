module Rome.Operational.Types.Equivalence where

open import Rome.Operational.Prelude
open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

open import Rome.Operational.Types.Syntax
open import Rome.Operational.Types.Substitution

-------------------------------------------------------------------------------
-- (Declarative) Equivalence on types.
--
-- We declare an equivalence relation on types (as is presented in e.g. Hubers & Morris 2023)
-- so that we may show normalization is sound and complete w.r.t. the equivalence relation.
-- That is to say: normalization precisely characterizes equivalent forms.
-- 

private
    variable
        τ τ₁ τ₂ τ₃ υ υ₁ υ₂ : Type Δ κ 

infix 0 _≡t_
data _≡t_ :  (τ₁ τ₂ : Type Δ κ) → Set where

    eq-β : ∀ {τ₁ : Type (Δ ,, κ₁) κ₂} {τ₂ : Type Δ κ₁} → 

        ----------------------------
        (`λ τ₁) · τ₂ ≡t (τ₁ β[ τ₂ ])
    
    eq-refl : 

        ------
        τ ≡t τ 

    eq-sym : 
    
        τ₁ ≡t τ₂ →
        ----------
        τ₂ ≡t τ₁

    eq-trans : 
    
        τ₁ ≡t τ₂ → τ₂ ≡t τ₃ → 
        ---------------------
        τ₁ ≡t τ₃

    eq-→ : 

        τ₁ ≡t τ₂ → υ₁ ≡t υ₂ →
        -----------------------
        τ₁ `→ υ₁ ≡t τ₂ `→ υ₂

    eq-∀ : 

        τ ≡t υ →
        ----------------
        `∀ κ τ ≡t `∀ κ υ

    eq-· :

        τ₁ ≡t υ₁ → τ₂ ≡t υ₂ →
        ---------------------
        τ₁ · τ₂ ≡t υ₁ · υ₂

    eq-⌊⌋ : 

        τ ≡t υ →
        -------------
        ⌊ τ ⌋ ≡t ⌊ υ ⌋


        


    