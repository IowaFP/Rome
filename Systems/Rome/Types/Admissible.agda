
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
U : ∀ {ℓ ℓΔ}{Δ : KEnv ℓΔ} → Type Δ (★ ℓ)
U = ⌊ lab "unit" ⌋

-- The empty record.
∅ : ∀ {ℓ ℓΔ} {Δ : KEnv ℓΔ} → Type Δ (★ ℓ)
∅ = Π ε

-- The impossible variant.
False : ∀ {ℓ ℓΔ} {Δ : KEnv ℓΔ} → Type Δ (★ ℓ)
False = Σ ε

μΣ : ∀ {ℓ ℓΔ} {Δ : KEnv ℓΔ} → Type Δ R[ (★ ℓ) `→ (★ ℓ) ] → Type Δ (★ ℓ)
μΣ {ℓ} ρ = μ (`λ (★ ℓ) (Σ ((K ρ) ·⌈ tvar Z ⌉)))

--------------------------------------------------------------------------------
-- type of fmap : ∀ t s → F t → F s

Functor : ∀ {ℓ ℓΔ} {Δ : KEnv ℓΔ} → 
          Type Δ (((★ ℓ) `→ (★ ℓ)) `→ ★ (lsuc ℓ))
Functor {ℓ = ℓ} = `λ (★ ℓ `→ ★ ℓ) -- F
               (`∀ (★ ℓ)         -- t
               (`∀ (★ ℓ)         -- s
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
       Type Δ (R[ ★ ℓ `→ ★ ℓ ] `→ ★ ι `→ ★ (lsuc ℓ ⊔ ι))
MAlg {ℓ} {ι} = 
  `λ R[ ★ ℓ `→ ★ ℓ ]   -- ρ
  (`λ (★ ι)             -- τ
  (`∀ R[ ★ ℓ `→ ★ ℓ ]  -- w
  (`∀ R[ ★ ℓ `→ ★ ℓ ]  -- y
    ((ρ · y ~ w) ⇒
      ((Σ ρ) ·[ (μΣ w) ] `→ (((μΣ w) `→ τ) `→ τ))))))
  where
    y = tvar Z
    w = tvar (S Z)
    τ = tvar (S² Z)
    ρ = tvar (S³ Z)


--------------------------------------------------------------------------------
-- ↪ synonym for recursive eliminators.

_↪_ : ∀ {ℓ₁ ℓ₂ ℓΔ} {Δ : KEnv ℓΔ} → 
             Type Δ (R[ ★ ℓ₁ `→ ★ ℓ₁ ]) → Type Δ (★ ℓ₂) →
             -----------------------------------
             Type Δ (★ (lsuc ℓ₁ ⊔ ℓ₂))
_↪_ {ℓ₁} {ℓ₂} ρ τ = ((MAlg {ℓ₁} {ℓ₂}) ·[ ρ ]) ·[ τ ]

