
module Rome.Types.Admissible where

open import Preludes.Level
open import Preludes.Data

import IndexCalculus as Ix

open import Rome.Kinds
open import Rome.Types.Syntax
open import Rome.Types.Substitution

--------------------------------------------------------------------------------
-- Permissable types.

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

BoolP : ∀ {ℓ ℓΔ} {Δ : KEnv ℓΔ} → Pred (Δ ، R[ ★ ℓ ]) (★ ℓ)
BoolP = (Tru R▹ Unit) · (Fls R▹ Unit) ~ tvar Z

Bool : ∀ {ℓ} {ℓΔ} {Δ : KEnv ℓΔ} →
       Type Δ (★ (lsuc ℓ))
Bool {ℓ} = `∀ (R[ ★ ℓ ]) (BoolP ⇒ Σ (tvar Z))

--------------------------------------------------------------------------------
-- Encoding the natural number type.

Zr Sc : ∀ {ℓΔ} {Δ : KEnv ℓΔ} →
  Type Δ (L lzero)
Zr = lab "Zero"
Sc = lab "Succ"

NatP : ∀ {ℓ ℓΔ} {Δ : KEnv ℓΔ} → Pred (Δ ، R[ ★ ℓ `→ ★ ℓ ]) (★ ℓ `→ ★ ℓ)
NatP {ℓ} = (Zr R▹ `λ (★ ℓ) Unit) · (Sc R▹ `λ (★ ℓ) (tvar Z)) ~ tvar Z


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

-- FmapT-ρ : ∀ {ℓ ℓΔ} {Δ : KEnv ℓΔ} → 
--           Type Δ (R[ ★ ℓ `→ ★ ℓ ] `→ ★ (lsuc ℓ))
-- FmapT-ρ {ℓ = ℓ} = `λ (R[ ★ ℓ `→ ★ ℓ ]) (Π (⌈ FmapT ⌉· (tvar Z)))

--------------------------------------------------------------------------------
-- "Mendler" algebras.

MAlg : ∀ {ℓ ι ℓΔ} {Δ : KEnv ℓΔ} →
       Type Δ (R[ ★ ℓ `→ ★ ℓ ]) → Type Δ (★ ι) → Type Δ (★ (lsuc ℓ ⊔ ι))
MAlg {ℓ} {ι} ρ  τ = 
  (`∀ R[ ★ ℓ `→ ★ ℓ ]  -- w
  (`∀ R[ ★ ℓ `→ ★ ℓ ]  -- y
    ((K² ρ · y ~ w) ⇒
      ((Σ (K² ρ)) ·[ μΣ w ] `→ (((μΣ w) `→ K² τ) `→ K² τ)))))
  where
    y = tvar Z
    w = tvar (S Z)


--------------------------------------------------------------------------------
-- ↪ synonym for recursive eliminators.

_↪_ : ∀ {ℓ₁ ℓ₂ ℓΔ} {Δ : KEnv ℓΔ} → 
             Type Δ (R[ ★ ℓ₁ `→ ★ ℓ₁ ]) → Type Δ (★ ℓ₂) →
             -----------------------------------
             Type Δ (★ (lsuc ℓ₁ ⊔ ℓ₂))
_↪_ {ℓ₁} {ℓ₂} ρ τ = MAlg ρ τ

_↪₂_ : ∀ {ℓ₁ ℓ₂ ℓΔ} {Δ : KEnv ℓΔ} → 
             Type Δ (R[ ★ ℓ₁ `→ ★ ℓ₁ ]) → Type Δ (★ ℓ₂) →
             -----------------------------------
             Type Δ (★ (lsuc ℓ₁ ⊔ ℓ₂))
_↪₂_  {ℓ} {ι} ρ  τ = 
  (`∀ R[ ★ ℓ `→ ★ ℓ ]  -- w
    ((K ρ ≲ w) ⇒
      ((Σ (K ρ)) ·[ μΣ w ] `→ (((μΣ w) `→ K τ) `→ K τ))))
  where
    w = tvar Z

