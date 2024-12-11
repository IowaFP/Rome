
module Rome.Denotational.Types.Admissible where

open import Preludes.Level
open import Preludes.Data

import IndexCalculus as Ix

open import Rome.Denotational.Kinds
open import Rome.Denotational.Types.Syntax
open import Rome.Denotational.Types.Substitution

--------------------------------------------------------------------------------
-- Admissible types.

-- The unit type.
-- N.b. it's most elegant to let ⊤ = Π ε and ⊥ = Σ ε, but this definition of ⊤
-- doesn't behave like a unit:
--   - Π ε has infinite inhabitants (any record can project to Π ε).
--   - The denotation of Π ε is not ⊤ in the Index Calculus.
-- The definition below, on the other hand, has just one inhabitant and 
-- translates semantically to the identity.
Unit : ∀ {ℓ ℓΔ}{Δ : KEnv ℓΔ} → Type Δ (★ ℓ)
Unit = ⌊ lab "unit" ⌋

-- The empty record. (See above).
∅ : ∀ {ℓ ℓΔ} {Δ : KEnv ℓΔ} → Type Δ (★ ℓ)
∅ = Π ε

-- The impossible variant.
False : ∀ {ℓ ℓΔ} {Δ : KEnv ℓΔ} → Type Δ (★ ℓ)
False = Σ ε

μΣ : ∀ {ℓ ℓΔ} {Δ : KEnv ℓΔ} → Type Δ R[ (★ ℓ) `→ (★ ℓ) ] → Type Δ (★ ℓ)
μΣ {ℓ} ρ = μ (Σ ρ)

--------------------------------------------------------------------------------
-- Encoding the boolean type.

Tru Fls : ∀ {ℓΔ} {Δ : KEnv ℓΔ} →
          Type Δ (L lzero)
Tru = lab "True"
Fls = lab "False"

Bool : ∀ {ℓ} {ℓΔ} {Δ : KEnv ℓΔ} →
       Type Δ (★ (lsuc ℓ))
Bool {ℓ} = Σ ⦃- "True" ▹ Unit ， "False" ▹ Unit -⦄

--------------------------------------------------------------------------------
-- type of fmap : ∀ t s → F t → F s

Functor : ∀ {ℓ ℓΔ} {Δ : KEnv ℓΔ} → 
          Type Δ (((★ ℓ) `→ (★ ℓ)) `→ ★ (lsuc ℓ))
Functor {ℓ = ℓ} = `λ (★ ℓ `→ ★ ℓ) -- F
               (`∀ (★ ℓ)           -- t
               (`∀ (★ ℓ)           -- s
               ((t `→ s) `→ (F ·[ t ]) `→ F ·[ s ])))
      where
        F = tvar (S (S Z))
        t = tvar (S Z)
        s = tvar Z

--------------------------------------------------------------------------------
-- Bounded algebras.

BAlg : ∀ {ℓ₁ ℓ₂ ℓΔ} {Δ : KEnv ℓΔ} → 
             Type Δ (R[ ★ ℓ₁ `→ ★ ℓ₁ ]) → Type Δ (R[ ★ ℓ₁ `→ ★ ℓ₁ ] `→ ★ ℓ₂) →
             -----------------------------------
             Type Δ (★ (lsuc ℓ₁ ⊔ ℓ₂))
BAlg  {ℓ} {ι} ρ  f = 
  (`∀ R[ ★ ℓ `→ ★ ℓ ]  
    ((K ρ ≲ w) ⇒
      ((Σ (K ρ)) ·[ μΣ w ] `→ (((μΣ w) `→ K f ·[ w ]) `→ Functor ·[ Σ w ] `→ K f ·[ w ]))))
  where
    w = tvar Z
