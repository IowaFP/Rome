module Rome.Operational.Terms.Semantics.Progress where

open import Rome.Operational.Prelude

open import Rome.Operational.Kinds.Syntax

import Rome.Operational.Types as Types

open import Rome.Operational.Types.Normal.Syntax
open import Rome.Operational.Types.Normal.Properties.Renaming

open import Rome.Operational.Terms.Syntax
open import Rome.Operational.Terms.Substitution
open import Rome.Operational.Terms.Semantics.Reduction

open import Rome.Operational.Kinds.GVars
open import Rome.Operational.Terms.GVars

--------------------------------------------------------------------------------
-- Proof of progress.

data Progress {τ} (M : Term Γ τ) : Set where
  Done : 
         Value M → 
         ----------
         Progress M

  Steps : 
          (M' : Term Γ τ) → (M —→ M') → 
          --------------------------------------
          Progress M

progress : ∀ {τ} (M : Term ∅ τ) → Progress M
-- progress (` x) with noVar p x 
-- ... | ()

progress (`λ M) = Done (V-λ M)
progress (Λ M) = Done (V-Λ M)
-- with progress M 
-- ... | Done V = Done (V-Λ M V)
-- ... | Steps M' x = Steps (Λ M') (ξ-Λ x)
progress (M · N) with progress M
progress (.(`λ M) · N) | Done (V-λ M)   = Steps (M β[ N ]) β-λ
progress (M · N)       | Steps M' steps = Steps (M' · N) (ξ-·1 steps)
progress (M ·[ τ ]) with progress M
progress (.(Λ _) ·[ τ ]) | Done (V-Λ M) = Steps _ β-Λ
progress (M ·[ τ ])      | Steps M' steps = Steps _ (ξ-·[] steps)
progress (In τ M) with progress M 
... | Done V         = Done (V-In τ V) 
... | Steps M' steps = Steps (In τ M') (ξ-In steps) 
progress (Out τ M) with progress M
progress (Out τ .(In τ _)) | Done (V-In F M) = Steps _ β-In
progress (Out τ M)           | Steps M' steps = Steps _ (ξ-Out steps)
progress (# l) = Done V-#
progress (ℓ Π▹ M) with progress M 
... | Done VM = Done (V-Π ℓ M VM)
... | Steps M' M—→M' = Steps (ℓ Π▹ M') (ξ-Π▹ M M' ℓ M—→M')
progress (_Π/_ {l} M ℓ) with progress M
... | Done (V-Π ℓ₁ N VN)  = Steps N (β-Π/ N ℓ₁ ℓ VN)
... | Steps M' M—→M' = Steps (M' Π/ ℓ) (ξ-Π/₁ M M' ℓ M—→M')
progress (ℓ Σ▹ M) with progress M 
... | Done VM = Done (V-Σ ℓ M VM)
... | Steps M' M—→M' = Steps (ℓ Σ▹ M') (ξ-Σ▹ M M' ℓ M—→M')
progress (_Σ/_ {l} M ℓ) with progress M
... | Done (V-Σ ℓ₁ N VN)  = Steps N (β-Σ/ N ℓ₁ ℓ VN)
... | Steps M' M—→M' = Steps (M' Σ/ ℓ) (ξ-Σ/₁ M M' ℓ M—→M')
progress (`ƛ M) = Done (V-ƛ M)
progress (M ·⟨ e ⟩) with progress M 
... | Done (V-ƛ M₁) = Steps (M₁ βπ[ e ]) β-ƛ
... | Steps M' x = Steps (M' ·⟨ e ⟩) (ξ-·⟨⟩ x)
-- permitting ρ₁ to be a neutral variable I believe leads to stuckness here?
progress (prj {ρ₁ = ne x} M e₁) = ⊥-elim (noNeutrals x)
progress (prj {ρ₁ = ε} M e) = Done (V-Unit (prj M e))
progress (prj {ρ₁ = l₂ ▹ τ} M e₁) with progress M 
progress (prj {_} {.(_ ▹ _)} .(_Π▹_ ℓ N) e) | Done (V-Π ℓ N VN) with ≲-refl _ _ _ _ e
progress (prj {_} {.(_ ▹ _)} .(_Π▹_ ℓ N) e) | Done (V-Π ℓ N VN) | refl = Steps (ℓ Π▹ N) (β-prj ℓ N e)
progress (prj {_} {.(_ ▹ _)} M e) | Done (V-Unit .M) with ε-minimum e 
... | ()
progress (prj {ρ₁ = l₂ ▹ τ} M e) | Steps M' x = Steps _ (ξ-prj M M' e  x)
progress (inj M e) with progress M 
progress (inj {ρ₂ = ne x₁} M e) | Done (V-Σ ℓ M₁ x) = ⊥-elim (noNeutrals x₁)
progress (inj {ρ₂ = ε} M e) | Done (V-Σ ℓ M₁ x) with ε-minimum e
progress (inj {ρ₂ = ε} M e) | Done (V-Σ ℓ M₁ x) | () 
progress (inj {ρ₂ = ρ₂ ▹ ρ₃} M e) | Done (V-Σ ℓ M₁ x) with ≲-refl _ _ _ _ e 
... | refl = Steps M (β-inj ℓ M₁ e)
progress (inj {ρ₂ = ρ₂} M e) | Steps M' x = Steps (inj M' e) (ξ-inj M M' e x)

-- progress-ε : ∀ {τ} (M : Term ε τ) →
--              Progress M
-- progress-ε = progress tt

-------------------------------------------------------------------------------
-- Tinkering

{-# TERMINATING #-}
eval : ∀ {τ} → Term ∅ τ → Term ∅ τ 
eval M with progress M 
... | Done x = M
... | Steps M' x = eval M'
   
_ : eval uu ≡ uu 
_ = refl
    
_ : eval ((♯l Π▹ # (lab "r")) Π/ ♯l) ≡ (# (lab "r"))
_ = refl

_ : eval (prj (♯l Π▹ ♯l) n-refl) ≡ ((♯l Π▹ ♯l))
_ = refl
 
_ : eval (((((Λ (Λ (`ƛ (`λ (prj {ρ₂ = ne ((` Z))} {ne (` (S Z))}  (` Z) (n-var (T Z))))))) ·[ lab "l" ▹ UnitNF ]) ·[ lab "l" ▹ UnitNF ]) ·⟨ n-refl ⟩) · (♯l Π▹ uu))   ≡ ((♯l Π▹ uu)) 
_ = refl