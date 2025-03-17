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
open import Rome.Operational.Terms.Entailment.Properties

--------------------------------------------------------------------------------
-- Proof of progress

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

progress (`ƛ M) = Done (V-ƛ M)
progress (M ·⟨ e ⟩) with progress M 
... | Done (V-ƛ M₁) = Steps (M₁ βπ[ e ]) β-ƛ
... | Steps M' x = Steps (M' ·⟨ e ⟩) (ξ-·⟨⟩ x)

progress (# l) = Done V-#
progress (ℓ Π▹ M) with progress M 
... | Done VM = Done (V-Π ℓ M VM)
... | Steps M' M—→M' = Steps (ℓ Π▹ M') (ξ-Π▹ M M' ℓ M—→M')

progress (_Π/_ {l} M ℓ) with progress M
... | Done (V-Π ℓ₁ N VN)  = Steps N (β-Π/ N ℓ₁ ℓ VN)
... | Done (V-⊹ {e = e} M₁ N v v₁) = {!   !}
... | Steps M' M—→M' = Steps (M' Π/ ℓ) (ξ-Π/₁ M M' ℓ M—→M')

progress (prj {ρ₁ = ne x} M e₁) = ⊥-elim (noNeutrals x)
progress (prj {ρ₁ = ε} M e) = Done (V-Unit (prj M e))
progress (prj {ρ₁ = l₂ ▹ τ} M e₁) with progress M
progress (prj {_} {.(_ ▹ _)} _ e) | Done (V-⊹ M N VM VN) = {!e  !}
progress (prj  .(_Π▹_ ℓ N) e)     | Done (V-Π ℓ N VN) with ≲-refl e
progress (prj  .(_Π▹_ ℓ N) e)     | Done (V-Π ℓ N VN) | refl = Steps (ℓ Π▹ N) (β-prj ℓ N e)
progress (prj  M e)               | Done (V-Unit .M) with ε-minimum e 
... | ()
-- progress (prj {ℓ₃ ▹ τ₃} {.(_ ▹ _)} .(((ℓ₁ Π▹ M₁) ⊹ (ℓ₂ Π▹ N)) e') e) | Done (V-⊹ {ℓ₁ = ℓ₁} {ℓ₂} {e = e'} M₁ N x x₁) with ≲-refl e | ≲-refl (n-·≲L e')
-- ... | refl | refl = ⊥-elim (·-impossible e')
-- progress (prj {ρ₁ = l₂ ▹ τ} M e) | Steps M' x = Steps _ (ξ-prj M M' e  x)

progress ((M ⊹ N) e) with progress M | progress N 
... | c | d = {!   !}
-- ... | Done (V-Π ℓ₁ M VM) | Done (V-Π ℓ₂ N VN) = Done (V-⊹ M N VM VN)
-- ... | Done (V-Π ℓ M₁ x) | Done (V-⊹ M₂ N₁ y y₁) = Done {! V-⊹  !}
-- ... | Done (V-Π ℓ M₁ x) | Done (V-Unit .N) with (ε-right-identity e)
-- ... | refl  = Steps M (β-Πε-right ℓ M₁ N e)
-- progress ((M ⊹ N) e) | Done (V-Unit .M) | Done (V-Π ℓ M₁ x₁) = {!   !}
-- progress ((M ⊹ N) e) | Done (V-Unit .M) | Done (V-⊹ M₁ N₁ x₁ x₂) = {!   !}
-- progress ((M ⊹ N) e) | Done (V-Unit .M) | Done (V-Unit .N) = {!   !}
-- progress ((M ⊹ N) e) | Done x | Steps M' x₁ = {!  x !}
-- progress ((M ⊹ N) e) | Steps M' x | Done x₁ = {!   !}
-- progress ((M ⊹ N) e) | Steps M' x | Steps M'' x₁ = {!   !}

progress (ℓ Σ▹ M) with progress M 
... | Done VM = Done (V-Σ ℓ M VM)
... | Steps M' M—→M' = Steps (ℓ Σ▹ M') (ξ-Σ▹ M M' ℓ M—→M')

progress (_Σ/_ {l} M ℓ) with progress M
... | Done (V-Σ ℓ₁ N VN)  = Steps N (β-Σ/ N ℓ₁ ℓ VN)
... | Steps M' M—→M' = Steps (M' Σ/ ℓ) (ξ-Σ/₁ M M' ℓ M—→M')

progress (inj M e) with progress M 
progress (inj {ρ₂ = ne x₁} M e) | Done (V-Σ ℓ M₁ x) = ⊥-elim (noNeutrals x₁)
progress (inj {ρ₂ = ε} M e) | Done (V-Σ ℓ M₁ x) with ε-minimum e
progress (inj {ρ₂ = ε} M e) | Done (V-Σ ℓ M₁ x) | () 
progress (inj {ρ₂ = ρ₂ ▹ ρ₃} M e) | Done (V-Σ ℓ M₁ x) with ≲-refl e 
... | refl = Steps M (β-inj ℓ M₁ e)
progress (inj {ρ₂ = ρ₂} M e) | Steps M' x = Steps (inj M' e) (ξ-inj M M' e x)

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

_ : eval (`ƛ (prj (((♯l Π▹ uu) ⊹ (♯l Π▹ uu)) (n-var Z)) (n-·≲L (n-var Z)))) ≡ {! eval (`ƛ (prj (((♯l Π▹ uu) ⊹ (♯l Π▹ uu)) (n-var Z)) (n-·≲L (n-var Z))))  !}
_ = {!   !} 
   
_ : eval (((((Λ (Λ (`ƛ (`λ (prj {ρ₂ = ne ((` Z))} {ne (` (S Z))}  (` Z) (n-var (T Z))))))) ·[ lab "l" ▹ UnitNF ]) ·[ lab "l" ▹ UnitNF ]) ·⟨ n-refl ⟩) · (♯l Π▹ uu))   ≡ ((♯l Π▹ uu)) 
_ = refl