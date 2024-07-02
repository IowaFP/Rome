module Rome.Programs.Half where

open import Preludes.Level
open import Rome
open import Rome.GVars

--------------------------------------------------------------------------------
-- Encoding the natural number type.

Zr Sc : ∀ {ℓΔ} {Δ : KEnv ℓΔ} →
  Type Δ (L lzero)
Zr = lab "Zero"
Sc = lab "Succ"

NatP : Pred (Δ ، R[ ★ ℓ `→ ★ ℓ ]) (★ ℓ `→ ★ ℓ)
NatP {ℓ = ℓ} = (Zr R▹ `λ (★ ℓ) Unit) · (Sc R▹ `λ (★ ℓ) (tvar Z)) ~ tvar Z

--------------------------------------------------------------------------------
-- Examples involving NatP.

NatPFunctorT : Type Δ (★ (lsuc ℓ))
NatPFunctorT {ℓ = ℓ} = `∀ (R[ ★ ℓ `→ ★ ℓ ]) (NatP ⇒ Functor ·[ Σ (tvar Z) ])

NatPFunctor : ∀ {Γ : Env Δ ℓΓ} {Φ : PEnv Δ ℓΦ} → Term Δ Φ Γ (NatPFunctorT {ℓ = ℓ})
NatPFunctor {ℓ = ℓ} = 
  `Λ _ 
  (`ƛ _ {!!})
  
  -- `Λ _ (`ƛ _ (t-≡ (teq-sym teq-β) (`Λ _ (`Λ _ (`λ _ (`λ _
  -- {!   !}
  -- ))))))

zeroT : ∀ {ℓ ℓΔ} {Δ : KEnv ℓΔ} → Type Δ (★ (lsuc ℓ))
zeroT {ℓ} = `∀ (R[ ★ ℓ `→ ★ ℓ ]) (NatP ⇒ μ (Σ (tvar Z)))

zero_NatP : ∀ {ℓ ℓΓ ℓΦ} {Γ : Env Δ ℓΓ} {Φ : PEnv Δ ℓΦ} → Term Δ Φ Γ (zeroT {ℓ})
zero_NatP = `Λ _ (`ƛ _ (In a1 a2))
  where
    i1 : {Γ : Env Δ ℓΓ} {Φ : PEnv Δ ℓΦ} →
      Ent (Δ ، R[ ★ ℓ `→ ★ ℓ ]) (weakΦ Φ , NatP) ((Zr R▹ Unit) ≲ ↑ tvar Z ·[ μ (Σ (tvar Z)) ])
    i1 = n-≡ (peq-≲ (teq-trans teq-lift₁ (teq-sing teq-refl (teq-β {τ = Unit} {υ = μ (Σ (tvar Z))}))) teq-refl)
      (n-≲lift₁ (n-·≲L (n-var Z)))
    a1 : ∀ {Γ : Env Δ ℓΓ} {Φ : PEnv Δ ℓΦ} →
      Term (Δ ، R[ ★ ℓ `→ ★ ℓ ]) (weakΦ Φ , NatP) (weakΓ Γ) (Σ (tvar Z) ·[ μ (Σ (tvar Z)) ])
    a1 = t-≡ (teq-sym (teq-lift-Σ)) (inj (Σ (lab Zr ▹ u)) i1)
    a2 : ∀ {Γ : Env Δ ℓΓ} {Φ : PEnv Δ ℓΦ} →
      Term (Δ ، R[ ★ ℓ `→ ★ ℓ ]) (weakΦ Φ , NatP) (weakΓ Γ) (Functor ·[ Σ (tvar Z) ])
    a2 = (NatPFunctor ·[ tvar Z ]) ·⟨ n-var Z ⟩
