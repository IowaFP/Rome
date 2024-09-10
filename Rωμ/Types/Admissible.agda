
module Rωμ.Types.Admissible where

open import Preludes.Level
open import Preludes.Data

import IndexCalculus as Ix

open import Rωμ.Kinds
open import Rωμ.Types.Syntax
open import Rωμ.Types.Substitution

--------------------------------------------------------------------------------
-- Admissible types.

-- The unit type.
-- N.b. it's most elegant to let ⊤ = Π ε and ⊥ = Σ ε, but this definition of ⊤
-- doesn't behave like a unit:
--   - Π ε has infinite inhabitants (any record can project to Π ε).
--   - The denotation of Π ε is not ⊤ in the Index Calculus.
-- The definition below, on the other hand, has just one inhabitant and 
-- translates semantically to the identity.
Unit : ∀ {Δ : KEnv} → Type Δ ★
Unit = ⌊ lab "unit" ⌋

-- The empty record. (See above).
∅ : ∀  {Δ : KEnv} → Type Δ ★
∅ = Π ε

-- The impossible variant.
False : ∀  {Δ : KEnv} → Type Δ ★
False = Σ ε

μΣ : ∀  {Δ : KEnv} → Type Δ R[ ★ `→ ★ ] → Type Δ ★
μΣ {ℓ} ρ = μ (Σ ρ)

--------------------------------------------------------------------------------
-- Encoding the boolean type.

Tru Fls : ∀ {Δ : KEnv} →
          Type Δ L
Tru = lab "True"
Fls = lab "False"

Bool : ∀ {Δ : KEnv} →
       Type Δ (★)
Bool {ℓ} = Σ ⦃- "True" ▹ Unit ， "False" ▹ Unit -⦄

--------------------------------------------------------------------------------
-- type of fmap : ∀ t s → F t → F s

Functor : ∀  {Δ : KEnv} → 
          Type Δ ((★ `→ ★) `→ ★)
Functor = `λ (★ `→ ★) -- F
               (`∀ ★           -- t
               (`∀ ★           -- s
               ((t `→ s) `→ (F ·[ t ]) `→ F ·[ s ])))
      where
        F = tvar (S (S Z))
        t = tvar (S Z)
        s = tvar Z

--------------------------------------------------------------------------------
-- Bounded algebras.

BAlg : ∀  {Δ : KEnv} → 
             Type Δ (R[ ★ `→ ★ ]) → Type Δ (R[ ★ `→ ★ ] `→ ★) →
             -----------------------------------
             Type Δ ★
BAlg ρ  f = 
  (`∀ R[ ★ `→ ★ ]  
    ((K ρ ≲ w) ⇒
      ((Σ (K ρ)) ·[ μΣ w ] `→ (((μΣ w) `→ K f ·[ w ]) `→ Functor ·[ Σ w ] `→ K f ·[ w ]))))
  where
    w = tvar Z
