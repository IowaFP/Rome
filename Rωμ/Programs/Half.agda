module Rωμ.Programs.Half where

open import Preludes.Level
open import Preludes.Relation
open import Preludes.Data
open import Rωμ
open import Rωμ.GVars
open import Data.String.Properties using (_≟_)

--------------------------------------------------------------------------------
-- Encoding the natural number type.

Zr Sc : ∀ {ℓΔ} {Δ : KEnv} →
  Type Δ L
Zr = lab "Zero"
Sc = lab "Succ"

NatP : Pred (Δ ، R[ ★ `→ ★ ]) (★ `→ ★)
NatP  = (Zr R▹ `λ ★ Unit) · (Sc R▹ `λ ★ (tvar Z)) ~ tvar Z

NatRow : Type Δ R[ ★ `→ ★ ]
NatRow  = Row ("Zero" ▹ `λ ★ Unit ， ("Succ" ▹ `λ ★ (tvar Z)))

NatRowFunctor : ∀ {Γ : Env Δ} {Φ : PEnv Δ} → Term Δ Φ Γ (Functor  ·[ Σ NatRow ])
NatRowFunctor  = t-≡ (teq-sym teq-β)
  (`Λ ★ 
  (`Λ ★
  (`λ (tvar (S Z) `→ tvar Z)
  (`λ ((Σ NatRow) ·[ tvar (S Z) ])
    body
  ))))
  where
    A : Type (Δ ، ★ ، ★) _
    A = tvar (S Z)
    B : Type (Δ ، ★ ، ★) _
    B = tvar Z
    body : ∀ {Γ : Env Δ} {Φ : PEnv Δ} → Term
      (Δ ، ★ ، ★)
      (weakΦ (weakΦ Φ))
      (weakΓ (weakΓ Γ) ، A `→ B ، Σ NatRow ·[ A ])
      (Σ NatRow ·[ B ])
    body = {!   !}

-- have: Σ ((↑ NatRow) ·[ A ]) {by teq-lift-Σ}
-- have:  {by teq-lift₁-multi}

-- ↑ (Row ...) ·[ υ ] ≡t Row ( blah ·[ υ ])

μNatZero : {Γ : Env Δ} {Φ : PEnv Δ} → Term Δ Φ Γ (μΣ  NatRow)
μNatZero = In {!   !} NatRowFunctor

--------------------------------------------------------------------------------
-- Examples involving NatP.

-- NatPFunctorT : Type Δ (★)
-- NatPFunctorT  = `∀ (R[ ★ `→ ★ ]) (NatP ⇒ Functor ·[ Σ (tvar Z) ])

-- NatPFunctor : ∀ {Γ : Env Δ} {Φ : PEnv Δ} → Term Δ Φ Γ (NatPFunctorT )
-- NatPFunctor  =
--   `Λ (R[ ★ `→ ★ ])
--   (`ƛ NatP ((t-≡ (teq-sym teq-β)
--   (`Λ ★
--   (`Λ ★
--   (`λ (tvar (S Z) `→ tvar Z)
--   (`λ (Σ (tvar (S (S Z))) ·[ tvar (S Z)])
--     body
--   )))))))
--   where
--     body : ∀ {Γ : Env Δ} {Φ : PEnv Δ} →
--       Term (Δ ، R[ ★ `→ ★ ] ، ★ ، ★)
--       (weakΦ (weakΦ (weakΦ Φ)) ,
--         ((lab "Zero" R▹ `λ ★ ⌊ lab "unit" ⌋) · lab "Succ" R▹ `λ ★ (tvar Z) ~ tvar (S (S Z))))
--       (weakΓ (weakΓ (weakΓ Γ)) ، tvar (S Z) `→ tvar Z ، Σ (tvar (S (S Z))) ·[ tvar (S Z) ])
--       (Σ (tvar (S (S Z))) ·[ tvar Z ])
--     body = (ana (tvar (S (S Z))) (`λ _ ((tvar Z) ·[ tvar (S Z) ])) (Σ (tvar (S (S Z))) ·[ tvar Z ])
--       (`Λ _ (`Λ _ (`ƛ _ (`λ _ (`λ _ {!   !}))))))
--       · {!   !}

-- zeroT : ∀  {Δ : KEnv} → Type Δ (★)
-- zeroT {ℓ} = `∀ (R[ ★ `→ ★ ]) (NatP ⇒ μ (Σ (tvar Z)))

-- zero_NatP : ∀ {ℓ ℓΓ ℓΦ} {Γ : Env Δ} {Φ : PEnv Δ} → Term Δ Φ Γ (zeroT {ℓ})
-- zero_NatP = `Λ _ (`ƛ _ (In a1 a2))
--   where
--     i1 : {Γ : Env Δ} {Φ : PEnv Δ} →
--       Ent (Δ ، R[ ★ `→ ★ ]) (weakΦ Φ , NatP) ((Zr R▹ Unit) ≲ ↑ tvar Z ·[ μ (Σ (tvar Z)) ])
--     i1 = n-≡ (peq-≲ (teq-trans teq-lift₁ (teq-sing teq-refl (teq-β {τ = Unit} {υ = μ (Σ (tvar Z))}))) teq-refl)
--       (n-≲lift₁ (n-·≲L (n-var Z)))
--     a1 : ∀ {Γ : Env Δ} {Φ : PEnv Δ} →
--       Term (Δ ، R[ ★ `→ ★ ]) (weakΦ Φ , NatP) (weakΓ Γ) (Σ (tvar Z) ·[ μ (Σ (tvar Z)) ])
--     a1 = t-≡ (teq-sym (teq-lift-Σ)) (inj (Σ (lab Zr ▹ u)) i1)
--     a2 : ∀ {Γ : Env Δ} {Φ : PEnv Δ} →
--       Term (Δ ، R[ ★ `→ ★ ]) (weakΦ Φ , NatP) (weakΓ Γ) (Functor ·[ Σ (tvar Z) ])
--     a2 = (NatPFunctor ·[ tvar Z ]) ·⟨ n-var Z ⟩
